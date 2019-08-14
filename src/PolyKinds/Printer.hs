{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module PolyKinds.Printer where

import Data.List (intercalate, sortBy)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Data.Ord (comparing)
import PolyKinds.Type
import PolyKinds.Context
import PolyKinds.Check

printType :: Type -> String
printType = go
  where
  go = \case
    Star -> "*"
    Lit -> "N"
    Arrow -> "(->)"
    TypeUnknown (Unknown unk) -> "?" <> show unk
    TypeVar (Var var) -> var
    TypeName (Name name) -> name
    TypeApp (TypeApp Arrow ty1@(TypeApp (TypeApp Arrow _) _)) ty2 -> "(" <> go ty1 <> ") -> " <> go ty2
    TypeApp (TypeApp Arrow ty1) ty2 -> go ty1 <> " -> " <> go ty2
    TypeApp ty1 ty2@(TypeApp _ _) -> go ty1 <> " (" <> go ty2 <> ")"
    TypeApp ty1 ty2 -> go ty1 <> " " <> go ty2
    KindApp ty1 ty2@(KindApp _ _) -> go ty1 <> " @(" <> go ty2 <> ")"
    KindApp ty1 ty2 -> go ty1 <> " @" <> go ty2
    Forall bs ty ->
      "forall "
        <> goBinders bs
        <> ". "
        <> go ty

  goBinders =
    intercalate " " . fmap goBinder

  goBinder = \case
    (Var var, Nothing) -> var
    (Var var, Just ty) -> "(" <> var <> " :: " <> go ty <> ")"

data ContextValue
  = CtxType !Name
  | CtxVar !Var
  | CtxUnsolved !Int
  | CtxSolution !Int Type Type

printContext :: Context -> String
printContext ctx=
  intercalate "\n  " ("Types:" : printContextValues ctx) <> "\n\n" <>
  intercalate "\n  " ("Terms:" : printTerms ctx)

printContextValues :: Context -> [String]
printContextValues (Context {..}) =
  fmap (go . snd) . sortBy (comparing fst) $ types <> scopes
  where
  types  = fmap (\(a, (ScopeValue {..})) -> (scLevel, (CtxType a, scType))) . M.toList $ ctxTypes
  scopes =
    foldMap
      (\(TypeScope {..}) -> do
        let
          vars = fmap (\(a, (ScopeValue {..})) -> (scLevel, (CtxVar a, scType))) . M.toList $ tsVars
          unks = fmap (\(a, (ScopeValue {..})) -> (scLevel, (CtxUnsolved a, scType))) . IM.toList $ tsUnsolved
        vars <> unks)
      ctxScope

  go = \case
    (CtxType (Name n), ty) ->
      n <> " :: " <> printType ty
    (CtxVar (Var v), ty) ->
      v <> " :: " <> printType ty
    (CtxUnsolved i, ty)
      | Just (Solution {..}) <- IM.lookup i ctxSolutions ->
          "?" <> show i <> " :: " <> printType solKind <> " = " <> printType solType
      | otherwise ->
          "?" <> show i <> " :: " <> printType ty

printTerms :: Context -> [String]
printTerms (Context {..}) = fmap (uncurry go) . M.toList $ ctxValues
  where
  go (Name n) ty = n <> " :: " <> printType ty

printLog :: Log -> String
printLog (Log lbl ctx1 ins ch outs ctx2) =
  intercalate "\n" $ [ lbl ] <> header <> inputs <> children <> outputs <> footer

  where
  ctx1' = printContextValues ctx1
  ctx2' = printContextValues ctx2
  header
    | null ctx1' = []
    | otherwise =
        [ indent "  - " . intercalate "\n" $ printContextValues ctx1
        ]

  inputs
    | null ins = []
    | otherwise =
        [ indent "  > " . intercalate "\n" $ fmap printType ins
        ]

  children
    | null ch = []
    | otherwise =
        [ indent "    " . intercalate "\n" . fmap printLog $ reverse ch
        ]

  outputs
    | null outs = []
    | otherwise =
        [ indent "  < " . intercalate "\n" $ fmap printType outs
        ]

  footer
    | null ctx2' = []
    | otherwise =
        [ indent "  - " . intercalate "\n" $ printContextValues ctx2
        ]

indent :: String -> String -> String
indent ind = intercalate "\n" . fmap (ind <>) . lines
