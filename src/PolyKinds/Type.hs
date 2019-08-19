{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module PolyKinds.Type where

import Data.Foldable (toList)
import Data.Functor.Identity (Identity(..))
import Data.Maybe (mapMaybe)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Set as S

data Type
  = Star
  | Lit
  | Arrow
  | Constraint
  | ConstraintArrow
  | TypeUnknown Unknown
  | TypeVar Var
  | TypeName Name
  | TypeApp Type Type
  | KindApp Type Type
  | Forall BinderList Type
  deriving (Show, Eq)

type BinderList = [(Var, Maybe Type)]

type KindBinderList = [(Unknown, Type)]

newtype Name = Name { getName :: String }
  deriving (Show, Eq, Ord)

newtype Var = Var { getVar :: String }
  deriving (Show, Eq, Ord)

newtype Unknown = Unknown { getUnknown :: Int }
  deriving (Show, Eq, Ord)

data Decl
  = Sig Name Type
  | Data Name [Var] [Ctr]
  | Class Name [Var] [ClassMember]
  deriving (Show, Eq)

data Ctr = Ctr
  { ctrExists :: BinderList
  , ctrName :: Name
  , ctrArgs :: [Type]
  } deriving (Show, Eq)

data ClassMember = ClassMember
  { memName :: Name
  , memType :: Type
  } deriving (Show, Eq)

isSig :: Decl -> Bool
isSig = \case
  Sig _ _ -> True
  _ -> False

declName :: Decl -> Name
declName = \case
  Sig n _ -> n
  Data n _ _ -> n
  Class n _ _ -> n

declTypes :: Decl -> [Type]
declTypes = \case
  Sig _ t -> [t]
  Data _ _ cs ->
    foldMap (\(Ctr bs _ as) -> foldMap (foldMap pure . snd) bs <> as) cs
  Class _ _ cs ->
    foldMap (pure . memType) cs

{-# INLINE foldTypeWithScope #-}
foldTypeWithScope :: Semigroup m => (S.Set Var -> Type -> m) -> S.Set Var -> Type -> m
foldTypeWithScope k = go
  where
  go seen ty = case ty of
    Forall bs ty' ->
      k seen ty <> goBinders seen ty' bs
    TypeApp a b ->
      k seen ty <> (go seen a <> go seen b)
    KindApp a b ->
      k seen ty <> (go seen a <> go seen b)
    _ ->
      k seen ty

  goBinders seen ty = \case
    [] -> go seen ty
    (var, mbK) : bs -> do
      let rest = goBinders (S.insert var seen) ty bs
      maybe rest ((<> rest) . go seen) mbK

{-# INLINE foldType #-}
foldType :: Semigroup m => (Type -> m) -> Type -> m
foldType k = go
  where
  go ty = case ty of
    Forall bs ty' ->
      k ty <> goBinders ty' bs
    TypeApp a b ->
      k ty <> (go a <> go b)
    KindApp a b ->
      k ty <> (go a <> go b)
    _ ->
      k ty

  goBinders ty = \case
    [] -> go ty
    (_, mbK) : bs ->
      case mbK of
        Just ty' ->
          go ty' <> goBinders ty bs
        Nothing ->
          goBinders ty bs

{-# INLINE rewrite #-}
rewrite :: (Type -> Type) -> Type -> Type
rewrite k = runIdentity . rewriteM (Identity . k)

{-# INLINE rewriteM #-}
rewriteM :: Monad m => (Type -> m Type) -> Type -> m Type
rewriteM k = go
  where
  go = \case
    Forall bs ty -> do
      bs' <- traverse (traverse (traverse go)) bs
      ty' <- go ty
      k (Forall bs' ty')
    TypeApp a b -> do
      a' <- go a
      b' <- go b
      k $ TypeApp a' b'
    KindApp a b -> do
      a' <- go a
      b' <- go b
      k $ KindApp a' b'
    ty ->
      k ty

{-# INLINE rewriteWithScope #-}
rewriteWithScope :: (S.Set Var -> Type -> Type) -> S.Set Var -> Type -> Type
rewriteWithScope k vars = runIdentity . rewriteWithScopeM ((Identity .) . k) vars

{-# INLINE rewriteWithScopeM #-}
rewriteWithScopeM :: Monad m => (S.Set Var -> Type -> m Type) -> S.Set Var -> Type -> m Type
rewriteWithScopeM k = go
  where
  go seen ty = case ty of
    Forall bs ty' ->
      k seen =<< goForall seen ty' [] bs
    TypeApp a b -> do
      a' <- go seen a
      b' <- go seen b
      k seen $ TypeApp a' b'
    KindApp a b -> do
      a' <- go seen a
      b' <- go seen b
      k seen $ KindApp a' b'
    _ ->
      k seen ty

  goForall seen ty bs' = \case
    [] ->
      Forall (reverse bs') <$> go seen ty
    (var, mbK) : bs ->
      case mbK of
        Just ty' -> do
          ty'' <- go seen ty'
          goForall (S.insert var seen) ty ((var, Just ty'') : bs') bs
        Nothing ->
          goForall (S.insert var seen) ty ((var, Nothing) : bs') bs

names :: Type -> S.Set Name
names = foldType $ \case
  TypeName n ->
    S.singleton n
  _ ->
    mempty

varsAndUnknowns :: Type -> S.Set (Either Var Unknown)
varsAndUnknowns = flip foldTypeWithScope mempty $ \scope ty ->
  case ty of
    TypeUnknown unk ->
      S.singleton (Right unk)
    TypeVar var | not (S.member var scope) ->
      S.singleton (Left var)
    _ ->
      mempty

freeVars :: Type -> S.Set Var
freeVars = S.fromDistinctAscList . mapMaybe go . toList . varsAndUnknowns
  where
  go = \case
    Left var -> Just var
    _ -> Nothing

substUnknowns :: IM.IntMap Type -> Type -> Type
substUnknowns unks = rewrite $ \case
  TypeUnknown (Unknown i)
    | Just ty <- IM.lookup i unks -> ty
  ty -> ty

substTypeNames :: M.Map Name Type -> Type -> Type
substTypeNames ns = rewrite $ \case
  TypeName name
    | Just ty <- M.lookup name ns -> ty
  ty -> ty

substVar :: Var -> Type -> Type -> Type
substVar var ty = rewriteWithScope go mempty
  where
  go scope = \case
    TypeVar var'
      | var' == var && not (S.member var scope) -> ty
    ty' -> ty'

substVars :: M.Map Var Type -> Type -> Type
substVars vars = rewriteWithScope go mempty
  where
  go scope = \case
    TypeVar var
      | S.notMember var scope
      , Just ty <- M.lookup var vars -> ty
    ty -> ty

mkForall :: BinderList -> Type -> Type
mkForall = curry $ \case
  ([], ty) -> ty
  (bs, Forall bs' ty) -> Forall (bs <> bs') ty
  (bs, ty) -> Forall bs ty

unconsForall :: Type -> Maybe ((Var, Maybe Type), Type)
unconsForall = \case
  Forall (b : bs) ty -> Just (b, mkForall bs ty)
  _ -> Nothing

consForall :: (Var, Maybe Type) -> Type -> Type
consForall b = \case
  Forall bs ty' -> Forall (b : bs) ty'
  ty' -> Forall [b] ty'

mkTypeApp :: Type -> [Type] -> Type
mkTypeApp = foldl TypeApp

mkConstraintArrow :: Name -> [Type] -> Type -> Type
mkConstraintArrow n = TypeApp . TypeApp ConstraintArrow . mkTypeApp (TypeName n)

completeBinderList :: Type -> Maybe ([(Var, Type)], Type)
completeBinderList = go []
  where
  go bs ty =
    case unconsForall ty of
      Just ((_, Nothing), _) ->
        Nothing
      Just ((var, Just k), ty') ->
        go ((var, k) : bs) ty'
      Nothing ->
        Just ((reverse bs), ty)

unknownVar :: Unknown -> Var
unknownVar = Var . ("u" <>) . show . getUnknown

unknowns :: Type -> IS.IntSet
unknowns = foldType $ \case
  TypeUnknown (Unknown i) ->
    IS.singleton i
  _ ->
    mempty
