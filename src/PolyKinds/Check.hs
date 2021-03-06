{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PolyKinds.Check where

import Prelude hiding (log)

import Control.Monad ((<=<), join, unless, void, when)
import Control.Monad.Except (MonadError, catchError, throwError)
import Control.Monad.State (MonadState, get, gets, modify, state)
import Data.Bitraversable (bitraverse)
import Data.Coerce (coerce)
import Data.Foldable (for_, toList, traverse_)
import Data.Graph (SCC(..), stronglyConnComp)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import Data.Maybe (isJust, mapMaybe)
import qualified Data.Set as S
import Data.Traversable (for)
import PolyKinds.Context
import PolyKinds.StateExcM
import PolyKinds.Type

data CheckError
  = KindDoesNotResultIn [Type] Type
  | SigUnknownVars (S.Set Var)
  | CycleInSignature Name
  | CycleInBinderList [Var]
  | UnknownNotInScope Unknown
  | VarNotInScope Var
  | TypeNotInScope Name
  | InfiniteKind Unknown Type
  | DoesNotUnify Type Type
  | CannotApplyType (Type, Type) Type
  | CannotApplyKind (Type, Type) Type
  | ElaboratedKindIsNotStar Type
  | QuantificationCheckFailure Var
  | InternalError String (Maybe Type)
  | InvalidKind Type
  | InvalidType Type
  deriving (Show, Eq)

data Log = Log
  { logLabel :: String
  , logInputCtx :: Context
  , logInputs :: [Type]
  , logChildren :: [Log]
  , logOutputs :: [Type]
  , logOutputCtx :: Context
  }

data CheckState = CheckState
  { chkLog :: [Log]
  , chkContext :: !Context
  }

newtype CheckM a = CheckM (StateExcM CheckError CheckState a)
  deriving (Functor, Applicative, Monad, MonadError CheckError)

runCheckM :: CheckM a -> (Either CheckError a, CheckState)
runCheckM  = runStateExcM (CheckState [] emptyContext) . coerce

instance MonadState Context CheckM where
  get = CheckM $ gets chkContext
  state k = CheckM $ state $ \(CheckState lg ctx) ->
    CheckState lg <$> k ctx

throw :: CheckError -> CheckM void
throw = CheckM . throwError

note :: CheckError -> Maybe a -> CheckM a
note err = \case
  Just a -> pure a
  Nothing -> throw err

logCheck :: (a -> String) -> (a -> [Type]) -> (b -> [Type]) -> (a -> CheckM b) -> (a -> CheckM b)
logCheck klbl kin kout k = \a -> CheckM $ do
  (prev, inputCtx) <- state $ \(CheckState log ctx) -> ((log, ctx), CheckState [] ctx)
  let
    restore b =
      modify $ \(CheckState children ctx) -> do
        let
          entry = Log
            { logLabel = klbl a
            , logInputCtx = inputCtx
            , logInputs = kin a
            , logChildren = children
            , logOutputs = maybe [] kout b
            , logOutputCtx = ctx
            }
        CheckState (entry : prev) ctx
  b <- do
    let CheckM z = k a
    catchError z $ \e -> do
      restore Nothing
      throwError e
  restore (Just b)
  pure b

kindResultsIn :: [Type] -> Type -> CheckM ()
kindResultsIn tys ty = go ty
  where
  go = \case
    Forall _ ty' -> go ty'
    TypeApp (TypeApp Arrow _) ty' -> go ty'
    ty' | ty' `elem` tys -> pure ()
    ty' -> throw $ KindDoesNotResultIn tys ty'

guardKind :: Type -> CheckM Type
guardKind kd = do
  unless (isKind kd) $ throw $ InvalidKind kd
  pure kd

guardType :: Type -> CheckM Type
guardType ty = do
  unless (isType ty) $ throw $ InvalidType ty
  pure ty

generalizeUnknowns :: IM.IntMap ScopeValue -> Type -> Type
generalizeUnknowns unks ty
  | IM.null unks = ty
  | otherwise = foldr consForall (go ty) bs
  where
  bs =
    fmap (\(a, b) -> (unknownVar (Unknown a), Just (scType b)))
      $ IM.toList unks

  go = rewrite $ \case
    TypeUnknown unk | IM.member (getUnknown unk) unks ->
      TypeVar $ unknownVar unk
    ty' ->
      ty'

data SortedDecl
  = SortedSig Name Type
  | SortedDecl [SortedGroup]

data SortedGroup
  = SortedData Name BinderList [Ctr]
  | SortedClass [Type] Name BinderList [ClassMember]

declSort :: [Decl] -> CheckM [SortedDecl]
declSort decls =
  for sorted $ \case
    AcyclicSCC (Data n vs cs) ->
      pure $ SortedDecl [SortedData n vs cs]
    AcyclicSCC (Class ss n vs cs) ->
      pure $ SortedDecl [SortedClass ss n vs cs]
    AcyclicSCC (Sig s t) ->
      pure $ SortedSig s t
    CyclicSCC ds ->
      fmap SortedDecl $ for ds $ \case
        Data n vs cs ->
          pure $ SortedData n vs cs
        Class ss n vs cs ->
          pure $ SortedClass ss n vs cs
        Sig n _ ->
          throw $ CycleInSignature n
  where
  sorted =
    stronglyConnComp
      . fmap declDeps
      $ decls

  sigNames =
    flip mapMaybe decls $ \case
      Sig n _ -> Just n
      _ -> Nothing

  nameKey name =
    (name `elem` sigNames, name)

  declDeps decl = do
    let
      name = declName decl
      sigKey = nameKey name
      tyNames =
        fmap nameKey
          . toList
          . foldMap names
          . declTypes
          $ decl
      deps
        | not (isSig decl) && fst sigKey =
            sigKey : tyNames
        | otherwise = tyNames
    (decl, (isSig decl, name), deps)

checkProgram :: [Decl] -> Type -> CheckM Type
checkProgram ds ty = do
  checkDecls =<< declSort ds
  (ty', unks) <- scopedWithUnsolved $ do
    apply =<< checkKind ty Star
  guardType $ generalizeUnknowns unks ty'

checkDecls :: [SortedDecl] -> CheckM ()
checkDecls = traverse_ $ \case
  -- a-pgm-sig
  SortedSig name k -> do
    void . extendType name =<< inferSignature name k
  -- a-pgm-dt-ttS
  -- a-pgm-dt-tt
  SortedDecl group
    | [SortedData name vs cs] <- group -> do
        hasSig <- isJust <$> lookupType name
        if hasSig then
          traverse_ (uncurry (extendTerm CtrFn)) =<< inferDataDecl name vs cs
        else
          inferDataDeclGroup group
    | [SortedClass ss name vs cs] <- group -> do
        hasSig <- isJust <$> lookupType name
        if hasSig then
          traverse_ (uncurry (extendTerm ClassFn)) =<< inferClassDecl ss name vs cs
        else
          inferDataDeclGroup group
    | otherwise ->
        inferDataDeclGroup group

inferSignature :: Name -> Type -> CheckM Type
inferSignature = curry . logCheck (("inferSignature: " <>) . getName . fst) (pure . snd) pure $ \(_, o) -> do
  kindResultsIn [Star, Constraint] o
  let fv = freeVars o
  unless (S.null fv) . throw . SigUnknownVars $ fv
  (n, unks) <- scopedWithUnsolved $ do
    apply =<< snd <$> inferKind o
  let o' = generalizeUnknowns unks n
  unless (isKindDecl o') $ throw $ InvalidKind o
  pure o'

inferDataDeclGroup :: [SortedGroup] -> CheckM ()
inferDataDeclGroup group = do
  as <- scoped $ do
    as <- for group $ \case
      SortedData t _ _ -> do
        a' <- unknown
        extendUnsolved Nothing a' Star
        extendType t (TypeUnknown a')
        pure (t, a')
      SortedClass _ t _ _ -> do
        a' <- unknown
        extendUnsolved Nothing a' Star
        extendType t (TypeUnknown a')
        pure (t, a')

    tcs <- for group $ \case
      SortedData t vs cs -> do
        (CtrFn,) <$> inferDataDecl t vs cs
      SortedClass ss t vs cs ->
        (ClassFn,) <$> inferClassDecl ss t vs cs

    for (zip as tcs) $ \((t, a'), tc) -> do
      a'' <- apply (TypeUnknown a')
      pure (t, tc, a'', coerce . IS.toList $ unknowns a'')

  let
    unkSubs =
      IM.fromList
        . fmap (\a' -> (getUnknown a', TypeVar (unknownVar a')))
        . foldMap (\(_, _, _, qc') -> qc')
        $ as

    tySubs =
      M.fromList
        . fmap (\(t, _, _, qc') -> do
            let kapp t' = KindApp t' . TypeVar . unknownVar
            (t, foldl kapp (TypeName t) qc'))
        $ as

  for_ as $ \(t, (tv, tc), a'', qc') -> do
    let qc'' = fmap (\a' -> (unknownVar a', Just Star)) qc'

    extendType t
      . mkForall qc''
      . substUnknowns unkSubs
      $ a''

    for_ tc $ \(c, w) -> do
      let
        w' =
          mkForall qc''
            . substTypeNames tySubs
            . substUnknowns unkSubs
            $ w
      extendTerm tv c w'
      when (tv == CtrFn && isKindDecl w') $
        extendType (Name . ("'" <>) . getName $ c) w'

inferDataDecl :: Name -> BinderList -> [Ctr] -> CheckM [(Name, Type)]
inferDataDecl = curry . curry . logCheck (("inferDataDecl: " <>) . getName . fst . fst) (const []) (const []) $ \((t, as), ds) -> do
  ty <- note (TypeNotInScope t) . fmap scType =<< lookupType t
  (qc, w) <- note (InternalError "inferDataDecl: incomplete binder list" (Just ty)) . completeBinderList $ ty
  scoped $ do
    for_ qc $ uncurry extendVar
    as' <- for as $ \case
      (a, Nothing) -> do
        a' <- unknown
        extendUnsolved Nothing a' Star
        pure (a, TypeUnknown a')
      (a, Just k) ->
         fmap (a,) . guardKind =<< checkKind k Star

    unify w $ foldr (TypeApp . TypeApp Arrow . snd) Star as'

    as'' <- for as' $ \(a, a') -> do
      a_ <- apply a'
      extendVar a a_
      pure (a, a_)

    let
      p' = foldl (\t' -> KindApp t' . TypeVar . fst) (TypeName t) qc
      p  = foldl (\t' -> TypeApp t' . TypeVar . fst) p' as''

    ds' <- for ds $ \d@(Ctr _ _ name _) -> do
      u <- inferConstructor p d
      pure (name, mkForall (fmap Just <$> qc <> as'') u)
    traverse (traverse apply) ds'

inferConstructor :: Type -> Ctr -> CheckM Type
inferConstructor = curry . logCheck (("inferConstructor: " <>) . getName . ctrName . snd) (const []) (const []) $ \(p, (Ctr q cs _ ts)) -> do
  (u, qc') <- scopedWithUnsolved $ do
    (_, u) <-
      inferKind
        . mkForall q
        . flip (foldr (TypeApp . TypeApp ConstraintArrow)) cs
        . flip (foldr (TypeApp . TypeApp Arrow)) ts
        $ p
    apply u
  pure $ generalizeUnknowns qc' u

inferClassDecl :: [Type] -> Name -> BinderList -> [ClassMember] -> CheckM [(Name, Type)]
inferClassDecl ss = curry . curry . logCheck (("inferClassDecl: " <>) . getName . fst . fst) (const []) (const []) $ \((t, as), ds) -> do
  ty <- note (TypeNotInScope t) . fmap scType =<< lookupType t
  (qc, w) <- note (InternalError "inferClassDecl: incomplete binder list" (Just ty)) . completeBinderList $ ty
  scoped $ do
    for_ qc $ uncurry extendVar
    as' <- for as $ \case
      (a, Nothing) -> do
        a' <- unknown
        extendUnsolved Nothing a' Star
        pure (a, TypeUnknown a')
      (a, Just k) ->
        fmap (a,) . guardKind =<< checkKind k Star

    unify w $ foldr (TypeApp . TypeApp Arrow . snd) Constraint as'

    as'' <- for as' $ \(a, a') -> do
      a_ <- apply a'
      extendVar a a_
      pure (a, a_)

    for_ ss $ \s -> do
      void $ checkKind s Constraint

    ds' <- for ds $ \(ClassMember name d) -> do
      u <- checkKind d Star
      let
        qvars = fmap Just <$> qc <> as''
        u' = case u of
          Forall bs u'' ->
            Forall (qvars <> bs)
              . mkConstraintArrow t (TypeVar . fst <$> as)
              $ u''
          _ ->
            mkForall qvars
              . mkConstraintArrow t (TypeVar . fst <$> as)
              $ u
      pure (name, u')
    traverse (traverse (guardType <=< apply)) ds'

inferKind :: Type -> CheckM (Type, Type)
inferKind = logCheck (const "inferKind") pure (\(a, b) -> [a, b]) $ \case
  -- a-ktt-kstar
  Star ->
    pure (Star, Star)
  Constraint ->
    pure (Star, Constraint)
  -- a-ktt-nat
  Lit ->
    pure (Star, Lit)
  -- a-ktt-arrow
  Arrow ->
    pure (TypeApp (TypeApp Arrow Star) (TypeApp (TypeApp Arrow Star) Star), Arrow)
  ConstraintArrow ->
    pure (TypeApp (TypeApp Arrow Constraint) (TypeApp (TypeApp Arrow Star) Star), ConstraintArrow)
  -- a-ktt-uvar
  TypeUnknown a' -> do
    n <- note (UnknownNotInScope a') . fmap scType =<< lookupUnsolved a'
    pure (n, TypeUnknown a')
  -- a-ktt-var
  TypeVar a -> do
    w <- note (VarNotInScope a) . fmap scType =<< lookupVar a
    pure (w, TypeVar a)
  -- a-ktt-tcon
  TypeName t -> do
    n <- note (TypeNotInScope t) . fmap scType =<< lookupType t
    pure (n, TypeName t)
  -- a-ktt-app
  TypeApp t1 t2 -> do
    (n1, p1) <- inferKind t1
    inferAppKind (p1, n1) t2
  -- a-ktt-kapp
  KindApp t1 t2 -> do
    (n, p1) <- bitraverse apply pure =<< inferKind t1
    case unconsForall n of
      Just ((a, Just w), n2) -> do
        p2 <- checkKind t2 w
        pure (substVar a p2 n2, KindApp p1 p2)
      _ ->
        throw $ InternalError "inferKind: unkinded forall binder" $ Just n
  -- a-ktt-forall
  -- a-ktt-foralli
  ty | Just ((a, k), o) <- unconsForall ty -> do
    w <- case k of
      Just k' ->
        checkKind k' Star
      Nothing -> do
        a' <- unknown
        extendUnsolved Nothing a' Star
        pure $ TypeUnknown a'
    (u, uns) <- scopedWithUnsolved $ do
      extendVar a w
      apply =<< checkKind o Star
    unless (S.notMember a $ foldMap (freeVars . scType) uns) $
      throw $ QuantificationCheckFailure a
    for_ (IM.toList uns) $ \(b', ScopeValue _ k' _) ->
      extendUnsolved Nothing (Unknown b') k'
    pure (Star, consForall (a, Just w) u)
  ty ->
    throw $ InternalError "inferKind: unreachable case" $ Just ty

inferAppKind :: (Type, Type) -> Type -> CheckM (Type, Type)
inferAppKind = curry . logCheck (const "inferAppKind") (\((a, b), c) -> [a,b,c]) (\(a, b) -> [a, b]) $ \case
  -- a-kapp-tt-arrow
  ((p1, TypeApp (TypeApp Arrow w1) w2), t) -> do
    p2 <- checkKind t w1
    pure (w2, TypeApp p1 p2)
  ((p1, TypeApp (TypeApp ConstraintArrow w1) w2), t) -> do
    p2 <- checkKind t w1
    pure (w2, TypeApp p1 p2)
  -- a-kapp-tt-kuvar
  ((p1, TypeUnknown a'), t) -> do
    ScopeValue lvl w _ <- note (UnknownNotInScope a') =<< lookupUnsolved a'
    a1' <- unknown
    a2' <- unknown
    extendUnsolved (Just lvl) a1' Star
    extendUnsolved (Just lvl) a2' Star
    solve a' w $ TypeApp (TypeApp Arrow (TypeUnknown a1')) (TypeUnknown a2')
    p2 <- checkKind t $ TypeUnknown a1'
    pure (TypeUnknown a2', TypeApp p1 p2)
  -- a-kapp-tt-forall
  ((p1, ty), t) | Just ((a, Just w1), n) <- unconsForall ty -> do
    a' <- unknown
    extendUnsolved Nothing a' w1
    inferAppKind (KindApp p1 (TypeUnknown a'), substVar a (TypeUnknown a') n) t
  (a, b) ->
    throw $ CannotApplyType a b

checkKind :: Type -> Type -> CheckM Type
checkKind = curry . logCheck (const "checkKind") (\(a, b) -> [a,b]) pure $ \(o, w) -> do
  (n, u1) <- inferKind o
  n_ <- apply n
  w_ <- apply w
  instantiate (u1, n_) w_

instantiate :: (Type, Type) -> Type -> CheckM Type
instantiate = curry . logCheck (const "instantiate") (\((a, b), c) -> [a,b,c]) pure $ \case
  -- a-inst-forall
  ((u1, ty), w2) | Just ((a, Just w1), n) <- unconsForall ty -> do
    a' <- unknown
    extendUnsolved Nothing a' w1
    instantiate (KindApp u1 (TypeUnknown a'), substVar a (TypeUnknown a') n) w2
  -- a-inst-refl
  ((u, w1), w2) -> do
    unify w1 w2
    pure u

unify :: Type -> Type -> CheckM ()
unify = curry . logCheck (const "unify") (\(a, b) -> [a,b]) (const []) $ \case
  -- a-u-app
  (TypeApp p1 p2, TypeApp p3 p4) -> do
    unify p1 p3
    join $ unify <$> apply p2 <*> apply p4
  -- a-u-kapp
  (KindApp p1 p2, KindApp p3 p4) -> do
    unify p1 p3
    join $ unify <$> apply p2 <*> apply p4
  -- a-u-refl-tt
  (w1, w2) | w1 == w2 ->
    pure ()
  -- a-u-kvarL-tt
  (TypeUnknown a', p1) -> do
    p2 <- promote a' p1
    w1 <- note (UnknownNotInScope a') . fmap scType =<< lookupUnsolved a'
    join $ unify <$> apply w1 <*> elaboratedKind p2
    solve a' w1 p2
  -- a-u-kvarR-tt
  (p1, TypeUnknown a') -> do
    p2 <- promote a' p1
    w1 <- note (UnknownNotInScope a') . fmap scType =<< lookupUnsolved a'
    join $ unify <$> apply w1 <*> elaboratedKind p2
    solve a' w1 p2
  (w1, w2) ->
    throw $ DoesNotUnify w1 w2

promote :: Unknown -> Type -> CheckM Type
promote = curry . logCheck (const "promote") (\(a, b) -> [TypeUnknown a, b]) pure $ \case
  --a-pr-star
  (_, Star) ->
    pure Star
  (_, Constraint) ->
    pure Constraint
  --a-pr-arrow
  (_, Arrow) ->
    pure Arrow
  (_, ConstraintArrow) ->
    pure ConstraintArrow
  --a-pr-nat
  (_, Lit) ->
    pure Lit
  -- a-pr-tcon
  (a', TypeName t) -> do
    ScopeValue lvl1 _ _ <- note (TypeNotInScope t) =<< lookupType t
    ScopeValue lvl2 _ _ <- note (UnknownNotInScope a') =<< lookupUnsolved a'
    unless (lvl1 < lvl2) . throw $ TypeNotInScope t
    pure $ TypeName t
  -- a-pr-tvar
  (a', TypeVar a) -> do
    ScopeValue lvl1 _ _ <- note (VarNotInScope a) =<< lookupVar a
    ScopeValue lvl2 _ _ <- note (UnknownNotInScope a') =<< lookupUnsolved a'
    unless (lvl1 < lvl2) . throw $ VarNotInScope a
    pure $ TypeVar a
  -- a-pr-app
  (a', TypeApp w1 w2) -> do
    p1 <- promote a' w1
    p2 <- promote a' =<< apply w2
    pure $ TypeApp p1 p2
  -- a-pr-kapp
  (a', KindApp w1 w2) -> do
    p1 <- promote a' w1
    p2 <- promote a' =<< apply w2
    pure $ KindApp p1 p2
  -- a-pr-kuvarL
  -- a-pr-kuvarR-tt
  (a', TypeUnknown b') | a' /= b' -> do
    ScopeValue lvl1 p _ <- note (UnknownNotInScope b') =<< lookupUnsolved b'
    ScopeValue lvl2 _ _ <- note (UnknownNotInScope a') =<< lookupUnsolved a'
    if lvl1 < lvl2 then
      pure $ TypeUnknown b'
    else do
      p1  <- promote a' =<< apply p
      b1' <- unknown
      extendUnsolved (Just lvl2) b1' p1
      solve b' p $ TypeUnknown b1'
      pure $ TypeUnknown b1'
  (a', b') ->
    throw $ InfiniteKind a' b'

elaboratedKind :: Type -> CheckM Type
elaboratedKind = logCheck (const "elaboratedKind") pure pure $ \case
  -- a-ela-star
  Star ->
    pure Star
  Constraint ->
    pure Star
  -- a-ela-nat
  Lit ->
    pure Star
  -- a-ela-arrow
  Arrow ->
    pure $ TypeApp (TypeApp Arrow Star) (TypeApp (TypeApp Arrow Star) Star)
  ConstraintArrow ->
    pure $ TypeApp (TypeApp Arrow Constraint) (TypeApp (TypeApp Arrow Star) Star)
  -- a-ela-kuvar
  TypeUnknown a' -> do
    w <- note (UnknownNotInScope a') . fmap scType =<< lookupUnsolved a'
    apply w
  -- a-ela-var
  TypeVar a -> do
    w <- note (VarNotInScope a) . fmap scType =<< lookupVar a
    apply w
  -- a-ela-tcon
  TypeName t -> do
    n <- note (TypeNotInScope t) . fmap scType =<< lookupType t
    apply n
  -- a-ela-app
  TypeApp p1 p2 -> do
    p1Kind <- elaboratedKind p1
    case p1Kind of
      TypeApp (TypeApp Arrow w1) w2 -> do
        p2Kind <- elaboratedKind p2
        unless (p2Kind == w1) $
          throw $ CannotApplyType (p1, p2) p2Kind
        pure w2
      _ ->
        throw $ CannotApplyType (p1, p2) p1Kind
  -- a-ela-kapp
  KindApp p1 p2 -> do
    p1Kind <- elaboratedKind p1
    case unconsForall p1Kind of
      Just ((a, Just w), n) -> do
        p2Kind <- elaboratedKind p2
        unless (p2Kind == w) $
          throw $ CannotApplyKind (p1, p2) p2Kind
        flip (substVar a) n <$> apply p2
      _ ->
        throw $ CannotApplyKind (p1, p2) p1
  -- a-ela-forall
  ty | Just ((a, Just w), u) <- unconsForall ty -> do
    wIsStar <- elaboratedKind w
    unless (wIsStar == Star) $
      throw $ ElaboratedKindIsNotStar w
    uIsStar <- scoped $ do
      extendVar a w
      elaboratedKind u
    unless (uIsStar == Star) $
      throw $ ElaboratedKindIsNotStar w
    pure Star
  ty ->
    throw $ InternalError "elaboratedKind: Unreachable case" $ Just ty
