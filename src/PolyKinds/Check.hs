{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PolyKinds.Check where

import Prelude hiding (log)

import Control.Monad (join, unless, void)
import Control.Monad.Except (ExceptT, MonadError, throwError)
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

import Debug.Trace

data CheckError
  = KindDoesNotResultInStar Type
  | SigUnknownVars (S.Set Var)
  | CycleInSignature Name
  | CycleInBinderList [Var]
  | UnknownNotInScope Unknown
  | VarNotInScope Var
  | TypeNotInScope Name
  | CycleInSubstitution Type
  | DoesNotUnify Type Type
  | CannotApplyType (Type, Type) Type
  | CannotApplyKind (Type, Type) Type
  | ElaboratedKindIsNotStar Type
  | QuantificationCheckFailure Var
  | InternalError String (Maybe Type)
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

log :: (a -> String) -> (a -> [Type]) -> (b -> [Type]) -> (a -> CheckM b) -> (a -> CheckM b)
log klbl kin kout k = \a -> CheckM $ do
  (prev, inputCtx) <- state $ \(CheckState log ctx) -> ((log, ctx), CheckState [] ctx)
  b <- let CheckM z = k a in z
  modify $ \(CheckState children ctx) -> do
    let
      entry = Log
        { logLabel = klbl a
        , logInputCtx = inputCtx
        , logInputs = kin a
        , logChildren = children
        , logOutputs = kout b
        , logOutputCtx = ctx
        }
    CheckState (entry : prev) ctx
  pure b

apply' :: Type -> CheckM Type
apply' t = note (CycleInSubstitution t) =<< apply t

kindResultsInStar :: Type -> CheckM ()
kindResultsInStar ty = go ty
  where
  go = \case
    Forall _ k -> go k
    TypeApp (TypeApp Arrow _) k -> go k
    Star -> pure ()
    k -> throw $ KindDoesNotResultInStar ty

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

type SortedDecl = Either (Name, Type) [(Name, [Var], [Ctr])]

declSort :: [Decl] -> CheckM [SortedDecl]
declSort decls =
  for sorted $ \case
    AcyclicSCC (Data n vs cs) ->
      pure $ Right [(n, vs, cs)]
    AcyclicSCC (Sig s t) ->
      pure $ Left (s, t)
    CyclicSCC ds ->
      fmap Right $ for ds $ \case
        Data n vs cs ->
          pure (n, vs, cs)
        Sig n _ ->
          throw $ CycleInSignature n
  where
  sorted =
    stronglyConnComp . fmap deps $ decls

  sigs =
    flip mapMaybe decls $ \case
      Sig n _ -> Just n
      _ -> Nothing

  nameKey n =
    (n `elem` sigs, n)

  deps d = case d of
    Sig n ty ->
      (d, (True, n), nameKey <$> toList (names ty))
    Data n _ ctrs -> do
      let
        sig@(hasSig, _) =
          nameKey n
        ns = nameKey <$> do
          Ctr bs _ tys <- ctrs
          foldMap (foldMap (foldMap (toList . names))) bs
            <> foldMap (toList . names) tys
      (d, (False, n), if hasSig then sig : ns else ns)

checkProgram :: [Decl] -> CheckM ()
checkProgram ds = declSort ds >>= checkDecls

checkDecls :: [SortedDecl] -> CheckM ()
checkDecls = traverse_ $ \case
  -- a-pgm-sig
  Left (name, k) -> do
    void . extendType name =<< inferSignature name k
  -- a-pgm-dt-ttS
  -- a-pgm-dt-tt
  Right group@[(name, vars, ctrs)] -> do
    hasSig <- isJust <$> lookupType name
    if hasSig then
      traverse_ (uncurry extendTerm) =<< inferDataDecl name vars ctrs
    else
      inferDataDeclGroup group
  -- a-pgm-dt-tt
  Right group ->
    inferDataDeclGroup group

inferSignature :: Name -> Type -> CheckM Type
inferSignature = curry . log (("inferSignature: " <>) . getName . fst) (pure . snd) pure $ \(t, o) -> do
  kindResultsInStar o
  let fv = freeVars o
  unless (S.null fv) . throw . SigUnknownVars $ fv
  (n, unks) <- scopedWithUnsolved $ do
    apply' =<< snd <$> inferKind o
  pure $ generalizeUnknowns unks n

inferDataDeclGroup :: [(Name, [Var], [Ctr])] -> CheckM ()
inferDataDeclGroup group = do
  as <- scoped $ do
    as <- for group $ \(t, _, _) -> do
      a' <- unknown
      extendUnsolved Nothing a' Star
      extendType t (TypeUnknown a')
      pure (t, a')

    tcs <- for group $ \(t, vs, cs) ->
      inferDataDecl t vs cs

    for (zip as tcs) $ \((t, a'), tc) -> do
      a'' <- apply' (TypeUnknown a')
      pure (t, tc, a'', coerce . IS.toList $ unknowns a'')

  let subs = foldMap (\(_, _, _, qc') -> qc') as
  for_ as $ \(t, tc, a'', qc') -> do
    let
      mkQc = fmap (\a' -> (unknownVar a', Just Star))
      substAll = flip (foldr (\a' -> substUnknown a' (TypeVar (unknownVar a')))) subs

    extendType t
      . mkForall (mkQc qc')
      . substAll
      $ a''

    for_ tc $ \(c, w) ->
      extendTerm c
        . mkForall (mkQc qc')
        . flip (foldr (\(t, _, _, qc') ->
                  substTypeName t (foldl (\t' -> KindApp t' . TypeVar . unknownVar) (TypeName t) qc'))) as
        . substAll
        $ w

inferDataDecl :: Name -> [Var] -> [Ctr] -> CheckM [(Name, Type)]
inferDataDecl = curry . curry . log (("inferDataDecl: " <>) . getName . fst . fst) (const []) (const []) $ \((t, as), ds) -> do
  ty <- note (TypeNotInScope t) . fmap scType =<< lookupType t
  (qc, w) <- note (InternalError "inferDataDecl: incomplete binder list" (Just ty)) . completeBinderList $ ty
  w_ <- apply' w
  scoped $ do
    for_ qc $ uncurry extendVar

    as' <- for as $ \a -> do
      a' <- unknown
      extendUnsolved Nothing a' Star
      pure (a, a')

    unify w_
      . foldr (\(_, a') -> TypeApp (TypeApp Arrow (TypeUnknown a'))) Star
      $ as'

    as'' <- for as' $ \(a, a') -> do
      a_ <- apply' (TypeUnknown a')
      extendVar a a_
      pure (a, a_)

    let
      p' = foldl (\t' -> KindApp t' . TypeVar . fst) (TypeName t) qc
      p  = foldl (\t' -> TypeApp t' . TypeVar . fst) p' as''

    for ds $ \d@(Ctr _ name _) -> do
      u <- inferConstructor p d
      as''' <- traverse (traverse apply') as''
      pure (name, mkForall (fmap Just <$> (qc <> as''')) u)

inferConstructor :: Type -> Ctr -> CheckM Type
inferConstructor = curry . log (("inferConstructor: " <>) . getName . ctrName . snd) (const []) (const []) $ \(p, (Ctr q d ts)) -> do
  (u, qc') <- scopedWithUnsolved $ do
    (_, u) <- inferKind . mkForall q $ foldr (\ti -> TypeApp (TypeApp Arrow ti)) p ts
    apply' u
  pure $ generalizeUnknowns qc' u

inferKind :: Type -> CheckM (Type, Type)
inferKind = log (const "inferKind") pure (\(a, b) -> [a, b]) $ \case
  -- a-ktt-kstar
  Star ->
    pure (Star, Star)
  -- a-ktt-nat
  Lit ->
    pure (Star, Lit)
  -- a-ktt-arrow
  Arrow ->
    pure (TypeApp (TypeApp Arrow Star) (TypeApp (TypeApp Arrow Star) Star), Arrow)
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
    (n, p1) <- bitraverse apply' pure =<< inferKind t1
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
      apply' =<< checkKind o Star
    unless (S.notMember a $ foldMap (freeVars . scType) uns) $
      throw $ QuantificationCheckFailure a
    for_ (IM.toList uns) $ \(b', ScopeValue _ k) ->
      extendUnsolved Nothing (Unknown b') k
    pure (Star, consForall (a, Just w) u)
  ty ->
    throw $ InternalError "inferKind: unreachable case" $ Just ty

inferAppKind :: (Type, Type) -> Type -> CheckM (Type, Type)
inferAppKind = curry . log (const "inferAppKind") (\((a, b), c) -> [a,b,c]) (\(a, b) -> [a, b]) $ \case
  -- a-kapp-tt-arrow
  ((p1, TypeApp (TypeApp Arrow w1) w2), t) -> do
    p2 <- checkKind t w1
    pure (w2, TypeApp p1 p2)
  -- a-kapp-tt-kuvar
  ((p1, TypeUnknown a'), t) -> do
    ScopeValue lvl w <- note (UnknownNotInScope a') =<< lookupUnsolved a'
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
  _ ->
    throw $ InternalError "Unreachable case: inferAppKind" Nothing

checkKind :: Type -> Type -> CheckM Type
checkKind = curry . log (const "checkKind") (\(a, b) -> [a,b]) pure $ \(o, w) -> do
  (n, u1) <- inferKind o
  n_ <- apply' n
  w_ <- apply' w
  instantiate (u1, n_) w_

instantiate :: (Type, Type) -> Type -> CheckM Type
instantiate = curry . log (const "instantiate") (\((a, b), c) -> [a,b,c]) pure $ \case
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
unify = curry . log (const "unify") (\(a, b) -> [a,b]) (const []) $ \case
  -- a-u-app
  (TypeApp p1 p2, TypeApp p3 p4) -> do
    unify p1 p3
    join $ unify <$> apply' p2 <*> apply' p4
  -- a-u-kapp
  (KindApp p1 p2, KindApp p3 p4) -> do
    unify p1 p3
    join $ unify <$> apply' p2 <*> apply' p4
  -- a-u-refl-tt
  (w1, w2) | w1 == w2 ->
    pure ()
  -- a-u-kvarL-tt
  (TypeUnknown a', p1) -> do
    p2 <- promote a' p1
    w1 <- note (UnknownNotInScope a') . fmap scType =<< lookupUnsolved a'
    join $ unify <$> apply' w1 <*> elaboratedKind p2
    solve a' w1 p2
  -- a-u-kvarR-tt
  (p1, TypeUnknown a') -> do
    p2 <- promote a' p1
    w1 <- note (UnknownNotInScope a') . fmap scType =<< lookupUnsolved a'
    join $ unify <$> apply' w1 <*> elaboratedKind p2
    solve a' w1 p2
  (w1, w2) ->
    throw $ DoesNotUnify w1 w2

promote :: Unknown -> Type -> CheckM Type
promote = curry . log (const "promote") (\(a, b) -> [TypeUnknown a, b]) pure $ \case
  --a-pr-star
  (_, Star) ->
    pure Star
  --a-pr-arrow
  (_, Arrow) ->
    pure Arrow
  --a-pr-nat
  (_, Lit) ->
    pure Lit
  -- a-pr-tcon
  (a', TypeName t) -> do
    ScopeValue lvl1 _ <- note (TypeNotInScope t) =<< lookupType t
    ScopeValue lvl2 _ <- note (UnknownNotInScope a') =<< lookupUnsolved a'
    unless (lvl1 < lvl2) . throw $ TypeNotInScope t
    pure $ TypeName t
  -- a-pr-tvar
  (a', TypeVar a) -> do
    ScopeValue lvl1 _ <- note (VarNotInScope a) =<< lookupVar a
    ScopeValue lvl2 _ <- note (UnknownNotInScope a') =<< lookupUnsolved a'
    unless (lvl1 < lvl2) . throw $ VarNotInScope a
    pure $ TypeVar a
  -- a-pr-app
  (a', TypeApp w1 w2) -> do
    p1 <- promote a' w1
    p2 <- promote a' =<< apply' w2
    pure $ TypeApp p1 p2
  -- a-pr-kapp
  (a', KindApp w1 w2) -> do
    p1 <- promote a' w1
    p2 <- promote a' =<< apply' w2
    pure $ KindApp p1 p2
  -- a-pr-kuvarL
  -- a-pr-kuvarR-tt
  (a', TypeUnknown b') | a' /= b' -> do
    ScopeValue lvl1 p <- note (UnknownNotInScope b') =<< lookupUnsolved b'
    ScopeValue lvl2 w <- note (UnknownNotInScope a') =<< lookupUnsolved a'
    if lvl1 < lvl2 then
      pure $ TypeUnknown b'
    else do
      p1  <- promote a' =<< apply' p
      b1' <- unknown
      extendUnsolved (Just lvl2) b1' p1
      solve b' p $ TypeUnknown b1'
      pure $ TypeUnknown b1'
  (a', b') ->
    throw $ CycleInSubstitution b'

elaboratedKind :: Type -> CheckM Type
elaboratedKind = log (const "elaboratedKind") pure pure $ \case
  -- a-ela-star
  Star ->
    pure Star
  -- a-ela-nat
  Lit ->
    pure Star
  -- a-ela-arrow
  Arrow ->
    pure $ TypeApp (TypeApp Arrow Star) (TypeApp (TypeApp Arrow Star) Star)
  -- a-ela-kuvar
  TypeUnknown a' -> do
    w <- note (UnknownNotInScope a') . fmap scType =<< lookupUnsolved a'
    apply' w
  -- a-ela-var
  TypeVar a -> do
    w <- note (VarNotInScope a) . fmap scType =<< lookupVar a
    apply' w
  -- a-ela-tcon
  TypeName t -> do
    n <- note (TypeNotInScope t) . fmap scType =<< lookupType t
    apply' n
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
        flip (substVar a) n <$> apply' p2
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
