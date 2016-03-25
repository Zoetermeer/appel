module Semant where

import Test.Hspec
import qualified Syntax
import Types

type AlphaId = (Int, Syntax.Id)
type Env = [(Syntax.Id, Types.Ty)]

mtEnv :: Env
mtEnv = []

subst :: Ty -> Env -> Ty
subst (TyVar alpha) [] = TyVar alpha
subst var@(TyVar alpha) ((beta, t):betas) =
  if beta == alpha then t
  else subst var betas

subst TyNil _ = TyNil
subst (TyApp (TyFun tyVars ty) tys) env = TyVar "wrong"


substSpecs = do
  describe "subst" $ do
    it "subs nil" $ do
      subst TyNil mtEnv `shouldBe` TyNil

    it "subs types for type vars" $ do
      subst (TyVar "foo") mtEnv `shouldBe` TyVar "foo"
      subst (TyVar "T") [("T", TyApp Int [])] `shouldBe` TyApp Int []

    it "subs polymorphic record types" $ do
      subst (TyApp (TyFun ["T", "K"] (TyApp (Record ["fst", "snd"]) [TyVar "T", TyVar "K"]))
              [TyApp Int [], TyApp String []])
            mtEnv
        `shouldBe`
        (TyApp (Record ["fst", "snd"]) [TyApp Int [], TyApp String []])
