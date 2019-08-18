{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PolyKinds.Context where

import Control.Applicative ((<|>))
import Control.Monad (when)
import Control.Monad.State (MonadState, get, gets, modify, put, state)
import Control.Monad.State.Strict (State, runState)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map.Strict as M
import PolyKinds.Type

data Level
  = LvlAt !Int
  | LvlBefore !Level !Int
  deriving (Show, Eq)

instance Ord Level where
  compare = curry $ \case
    (LvlAt a, LvlAt b) ->
      compare a b
    (LvlBefore a1 a2, LvlBefore b1 b2) ->
      compare a2 b2 <> compare a1 b1
    (LvlBefore _ a2, LvlAt b) ->
      compare a2 b <> LT
    (LvlAt a, LvlBefore _ b2) ->
      compare a b2 <> GT

shallowLt :: Int -> Level -> Bool
shallowLt i = \case
  LvlAt i' -> i' < i
  LvlBefore _ i' -> i' < i

shallowLevel :: Level -> Int
shallowLevel = \case
  LvlAt i -> i
  LvlBefore _ i -> i

before :: Int -> Level -> Level
before i = \case
  LvlAt i1 ->
    LvlBefore (LvlAt i) i1
  LvlBefore (LvlAt i1) i2 ->
    LvlBefore (LvlBefore (LvlAt i) i1) i2
  LvlBefore (LvlBefore (LvlAt i1) i2) i3 ->
    LvlBefore (LvlBefore (LvlBefore (LvlAt i) i1) i2) i3
  LvlBefore (LvlBefore (LvlBefore a i1) i2) i3 ->
    LvlBefore (LvlBefore (LvlBefore (go a) i1) i2) i3
  where
  go = \case
    LvlAt i' ->
      LvlBefore (LvlAt i) i'
    LvlBefore a i' ->
      LvlBefore (go a) i'

mkLevel :: Int -> Maybe Level -> Level
mkLevel i = maybe (LvlAt i) (before i)

data Solution = Solution
  { solKind :: !Type
  , solType :: !Type
  , solUnsolved :: IS.IntSet
  } deriving (Show, Eq)

data Context = Context
  { ctxFresh :: !Int
  , ctxLevel :: !Int
  , ctxScope :: NE.NonEmpty TypeScope
  , ctxSolutions :: !(IM.IntMap Solution)
  , ctxTypes :: !(M.Map Name ScopeValue)
  , ctxValues :: !(M.Map Name Type)
  } deriving (Show, Eq)

data TypeScope = TypeScope
  { tsLevel :: !Int
  , tsUnsolved :: !(IM.IntMap ScopeValue)
  , tsVars :: !(M.Map Var ScopeValue)
  } deriving (Show, Eq)

data ScopeValue = ScopeValue
  { scLevel :: !Level
  , scType :: !Type
  , scUnsolved :: IS.IntSet
  } deriving (Show, Eq)

emptyContext :: Context
emptyContext = Context
  { ctxFresh = 0
  , ctxLevel = 0
  , ctxScope = pure (TypeScope 0 mempty mempty)
  , ctxSolutions = mempty
  , ctxTypes = mempty
  , ctxValues = mempty
  }

modifyScope :: (TypeScope -> TypeScope) -> Level -> NE.NonEmpty TypeScope -> NE.NonEmpty TypeScope
modifyScope k lvl = NE.fromList . go . NE.toList
  where
  bound =
    shallowLevel lvl

  go = \case
    [] -> []
    (ts : tss)
      | tsLevel ts <= bound -> k ts : tss
      | otherwise -> ts : go tss

insertUnsolved :: Int -> ScopeValue -> TypeScope -> TypeScope
insertUnsolved i value ts = ts { tsUnsolved = IM.insert i value $ tsUnsolved ts }

insertVar :: Var -> ScopeValue -> TypeScope -> TypeScope
insertVar var value ts = ts { tsVars = M.insert var value $ tsVars ts }

lookupType :: MonadState Context m => Name -> m (Maybe ScopeValue)
lookupType n =
  gets (M.lookup n . ctxTypes) >>= \case
    Nothing -> pure Nothing
    Just sc -> do
      solved <- gets ctxSolutions
      let (sc', solved') = applyScopeValue solved sc
      when (IS.size (scUnsolved sc') < IS.size (scUnsolved sc)) $ do
        modify $ \ctx -> ctx
          { ctxSolutions = solved'
          , ctxTypes = M.insert n sc' (ctxTypes ctx)
          }
      pure $ Just sc'

lookupCtr :: MonadState Context m => Name -> m (Maybe Type)
lookupCtr n = gets (M.lookup n . ctxValues)

lookupUnsolved :: MonadState Context m => Unknown -> m (Maybe ScopeValue)
lookupUnsolved (Unknown u) = gets $ foldr ((<|>) . IM.lookup u . tsUnsolved) Nothing . ctxScope

lookupVar :: MonadState Context m => Var -> m (Maybe ScopeValue)
lookupVar v = gets (foldr ((<|>) . M.lookup v . tsVars) Nothing . ctxScope)

unknown :: MonadState Context m => m Unknown
unknown = state $ \ctx ->
  ( Unknown (ctxFresh ctx)
  , ctx { ctxFresh = ctxFresh ctx + 1 }
  )

extendType :: MonadState Context m => Name -> Type -> m ()
extendType n ty = modify $ \ctx -> do
  let
    next = ctxLevel ctx
    value = ScopeValue (LvlAt next) ty (unknowns ty)
  ctx
    { ctxLevel = next + 1
    , ctxTypes = M.insert n value $ ctxTypes ctx
    }

extendUnsolved :: MonadState Context m => Maybe Level -> Unknown -> Type -> m ()
extendUnsolved lvl (Unknown i) ty = modify $ \ctx -> do
  let
    next = ctxLevel ctx
    lvl' = mkLevel next lvl
    value = ScopeValue lvl' ty (unknowns ty)
  ctx
    { ctxLevel = next + 1
    , ctxScope = modifyScope (insertUnsolved i value) lvl' $ ctxScope ctx
    }

extendVar :: MonadState Context m => Var -> Type -> m ()
extendVar var ty = modify $ \ctx -> do
  let
    next = ctxLevel ctx
    lvl = LvlAt next
    value = ScopeValue lvl ty (unknowns ty)
  ctx
    { ctxLevel = next + 1
    , ctxScope = modifyScope (insertVar var value) lvl $ ctxScope ctx
    }

extendTerm :: MonadState Context m => Name -> Type -> m ()
extendTerm n ty = modify $ \ctx ->
  ctx { ctxValues = M.insert n ty (ctxValues ctx) }

solve :: MonadState Context m => Unknown -> Type -> Type -> m ()
solve (Unknown i) knd ty = modify $ \ctx ->
  ctx { ctxSolutions = IM.insert i (Solution knd ty (unknowns ty)) $ ctxSolutions ctx }

newScope :: MonadState Context m => m Int
newScope = state $ \ctx -> do
  let
    scope = TypeScope (ctxLevel ctx) mempty mempty
    ctx' = ctx { ctxScope = scope `NE.cons` ctxScope ctx }
  (ctxLevel ctx, ctx')

dropScope :: MonadState Context m => m (IM.IntMap ScopeValue)
dropScope = state $ \ctx -> do
  let
    TypeScope _ uns _ :| scope' = ctxScope ctx
    uns' = IM.filterWithKey (\i _ -> IM.notMember i (ctxSolutions ctx)) uns
    (uns'', solved) = applyUnknowns (ctxSolutions ctx) uns'
    ctx' = ctx { ctxScope = NE.fromList scope', ctxSolutions = solved }
  (uns'', ctx')

scopedWithUnsolved :: MonadState Context m => m a -> m (a, IM.IntMap ScopeValue)
scopedWithUnsolved act = do
  _ <- newScope
  res <- act
  (res,) <$> dropScope

scoped :: MonadState Context m => m a -> m a
scoped = fmap fst . scopedWithUnsolved

apply :: MonadState Context m => Type -> m Type
apply ty = state $ \ctx -> do
  let
    (res, solved) = applySolutionsToType (ctxSolutions ctx) ty
    ctx' = ctx { ctxSolutions = solved }
  (res, ctx')

data SolutionState = SolutionState
  { ssSeen :: !IS.IntSet
  , ssUnsolved :: !IS.IntSet
  , ssSolutions :: !(IM.IntMap Solution)
  }

applyScopeValue :: IM.IntMap Solution -> ScopeValue -> (ScopeValue, IM.IntMap Solution)
applyScopeValue initialSolved sv@(ScopeValue lvl ty uns)
  | any (flip IM.member initialSolved) $ IS.toList uns = do
      let
        (ty', (SolutionState _ uns' solved)) =
          flip runState (SolutionState mempty mempty initialSolved)
            $ applySolutionsToType' ty
      (ScopeValue lvl ty' uns', solved)
  | otherwise =
      (sv, initialSolved)

applyUnknowns :: IM.IntMap Solution -> IM.IntMap ScopeValue -> (IM.IntMap ScopeValue, IM.IntMap Solution)
applyUnknowns initialSolved =
  fmap ssSolutions . flip runState (SolutionState mempty mempty initialSolved) . applyUnknowns'

applyUnknowns' :: IM.IntMap ScopeValue -> State SolutionState (IM.IntMap ScopeValue)
applyUnknowns' = traverse go
  where
  go (ScopeValue lvl ty _) = do
    modify $ \(SolutionState _ _ solved) ->
      SolutionState mempty mempty solved
    ty' <- applySolutionsToType' ty
    uns <- gets ssUnsolved
    pure $ ScopeValue lvl ty' uns

applySolutionsToType :: IM.IntMap Solution -> Type -> (Type, IM.IntMap Solution)
applySolutionsToType initialSolved =
  fmap ssSolutions . flip runState (SolutionState mempty mempty initialSolved) . applySolutionsToType'

applySolutionsToType' :: Type -> State SolutionState Type
applySolutionsToType' = go
  where
  go = rewriteM $ \ty -> case ty of
    TypeUnknown (Unknown i) -> do
      SolutionState seen unks solved <- get
      case IM.lookup i solved of
        Just (Solution knd ty' unks')
          | any (flip IM.member solved) $ IS.toList unks' -> do
              put $ SolutionState (IS.insert i seen) mempty solved
              ty'' <- go ty'
              state $ \(SolutionState _ unks'' solved') ->
                (ty'' , SolutionState seen unks (IM.insert i (Solution knd ty'' unks'') solved'))
          | otherwise ->
              pure ty'
        _ -> do
          put $ SolutionState seen (IS.insert i unks) solved
          pure ty
    _ ->
      pure ty
