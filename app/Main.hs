module Main where

import Data.List (intercalate)

import PolyKinds.Type
import PolyKinds.Check
import PolyKinds.Printer

(%->) :: Type -> Type -> Type
(%->) a b = Arrow %a %b
infixr 4 %->

(%=>) :: Type -> Type -> Type
(%=>) a b = ConstraintArrow %a %b
infixr 4 %=>

(%) :: Type -> Type -> Type
(%) a b = TypeApp a b
infixl 5 %

var :: String -> Type
var = TypeVar . Var

typ :: String -> Type
typ = TypeName . Name

testDecls :: [Decl]
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

  -- [ Sig (Name "Proxy")
  --     (Forall [(Var "k", Nothing)]
  --       (var "k" %-> Star))

  -- , Sig (Name "Relate")
  --     (Forall [(Var "a", Nothing), (Var "b", Just (var "a"))]
  --       (var "a" %-> typ "Proxy" %(var "b") %-> Star))

  -- , Sig (Name "T")
  --     (Forall
  --       [ (Var "a", Just Star)
  --       , (Var "b", Just (var "a"))
  --       , (Var "c", Just (var "a"))
  --       , (Var "d", Nothing)
  --       ]
  --       (typ "Relate" %(var "b") %(var "d") %-> Star))
  -- ]

  -- [ Sig (Name "String") Star
  -- , Data (Name "Proxy") [Var "k"]
  --     [ Ctr [] (Name "Proxy") []]
  -- , Data (Name "Maybe") [Var "a"]
  --     [ Ctr [] (Name "Just") [var "a"]
  --     , Ctr [] (Name "Nothing") []
  --     ]
  -- , Sig (Name "T") (Forall [(Var "a", Nothing)] (typ "Maybe" %(var "a") %-> Star))
  -- , Data (Name "K") []
  --     [ Ctr [] (Name "K")
  --         [ typ "T" %(typ "'Nothing")
  --         ]
  --     ]
  -- ]

  -- [ Data (Name "F") [Var "f"]
  --     [ Ctr [] (Name "MkF")
  --         [ var "f" %(typ "F")
  --         ]
  --     ]
  -- ]

  [ Sig (Name "Boolean") Star
  , Class (Name "Eq") [Var "a"]
      [ ClassMember (Name "eq") (var "a" %-> var "a" %-> typ "Boolean")
      ]
  , Class (Name "Functor") [Var "f"]
      [ ClassMember (Name "map")
          (Forall
            [ (Var "a", Nothing)
            , (Var "b", Nothing)
            ]
            ((var "a" %-> var "b")
              %-> var "f" %(var "a")
              %-> var "f" %(var "b")))
      ]
  , Data (Name "Dict") [Var "c"]
      [ Ctr [] [var "c"] (Name "Dict") []
      ]
  , Data (Name "FBox") [Var "f", Var "a"]
      [ Ctr [(Var "x", Nothing)] [typ "Functor" %(var "f")] (Name "FBox") [var "f" %(var "x"), var "x" %-> var "a"]
      ]
  ]

testTy :: Type
testTy =
  (typ "Dict" %(typ "Boolean"))
  -- Forall [(Var "k", Nothing)]
  --   (typ "Proxy" %(var "k") %-> typ "String")

  {-

  data Proxy :: forall k. k -> *
  data Relate :: forall (a :: *) (b :: a). a -> Proxy b -> *
  data T :: forall (a :: *) (b :: a) (c :: a) d. Relate b d -> *

  Relate @a _ (b)

  -}

main :: IO ()
main =
  case runCheckM (checkProgram testDecls testTy) of
    (res, CheckState lg ctx) -> do
      putStrLn . intercalate "\n" . fst $ printLogs [] lg
      putStrLn $ printContext ctx
      putStrLn $ replicate 64 '-'
      case res of
        Left err ->
          putStrLn $ show err
        Right ty ->
          putStrLn $ printType ty
      putStrLn $ replicate 64 '-'
