{-# LANGUAGE TemplateHaskell, UnicodeSyntax #-}
module Main where

import Test.Hspec
import Test.QuickCheck
import Test.QuickCheck.All

type Id = String
type FieldName = Id
type TyVar = Id

data Ty =
    Nil
  | App TyCon [Ty]
  | Var TyVar
  | Poly [TyVar] Ty
  deriving (Show, Eq)

-- We represent all types as applications
-- of type constructors (even built-in types).
-- For example, the type 'Int' is represented as
-- App (TyCon Int [])
data TyCon =
    Int
  | String
  | Unit
  | Arrow
  | Array
  | Record [FieldName]
  | TyFun [TyVar] Ty      -- A user-defined polymorphic type constructor
  | Unique TyCon
  deriving (Show, Eq)

type Env = [(Id, Ty)]

mtEnv :: Env
mtEnv = []


subst :: Ty -> Env -> Ty
subst (Var α) [] = Var α
subst var@(Var α) ((β, t):bts) =
  if β == α then t
  else subst var bts

subst Nil _ = Nil
subst (App (TyFun tyVars ty) tys) env = Var "wrong"


substSpecs = do
  describe "subst" $ do
    it "substitutes types for type vars" $ do
      subst (Var "foo") mtEnv `shouldBe` Var "foo"
      subst (Var "T") [("T", App Int [])] `shouldBe` App Int []

-- prop_len xs = len xs == len $ reverse xs

return [] -- need this for GHC 7.8
-- quickCheckAll generates test cases for all 'prop_*' properties
-- main = $(quickCheckAll)
main = hspec substSpecs
