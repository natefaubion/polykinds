module Main where

import Data.List (intercalate)

import PolyKinds.Type
import PolyKinds.Context
import PolyKinds.Check
import PolyKinds.Printer

(%->) a b = Arrow %a %b
infixr 4 %->

(%) a b = TypeApp a b
infixl 5 %

var = TypeVar . Var
typ = TypeName . Name

testDecls =
  -- [ Sig (Name "T")
  --     (Forall
  --       [(Var "k", Nothing)]
  --       (var "k" %-> Star)
  --     )
  -- ]

  -- [ Sig (Name "String") Star
  -- , Data (Name "T") [Var "x"]
  --     [ Ctr [(Var "a", Nothing)] (Name "S")
  --         [ var "a"
  --         , var "a" %-> typ "String"
  --         , var "x" %-> typ "String"
  --         ]
  --     ]
  -- ]

  [ Sig (Name "Proxy")
      (Forall [(Var "k", Nothing)]
        (var "k" %-> Star))

  , Sig (Name "Relate")
      (Forall [(Var "a", Nothing), (Var "b", Just (var "a"))]
        (var "a" %-> typ "Proxy" %(var "b") %-> Star))

  , Sig (Name "T")
      (Forall
        [ (Var "a", Just Star)
        , (Var "b", Just (var "a"))
        , (Var "c", Just (var "a"))
        , (Var "d", Nothing)
        ]
        (typ "Relate" %(var "b") %(var "d") %-> Star))
  ]

  {-

  data Proxy :: forall k. k -> *
  data Relate :: forall (a :: *) (b :: a). a -> Proxy b -> *
  data T :: forall (a :: *) (b :: a) (c :: a) d. Relate b d -> *

  Relate @a _ (b)

  -}

main :: IO ()
main =
  case runCheckM (checkProgram testDecls) of
    (res, CheckState lg ctx) -> do
      -- putStrLn . intercalate "\n" . fmap printLog $ reverse lg
      putStrLn $ printContext ctx
      case res of
        Left err ->
          putStrLn $ show err
        _ ->
          pure ()
