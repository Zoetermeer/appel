module Semant where

import Test.Hspec
import Syntax
import Types

type Env = [(Syntax.Id, Types.Ty)]

mtEnv :: Env
mtEnv = []

subst :: Types.Ty -> Env -> Types.Ty
subst (TyVar alpha) [] = TyVar alpha
subst var@(TyVar alpha) ((beta, t):betas) =
  if beta == alpha then t
  else subst var betas

subst TyNil _ = TyNil
subst (TyApp (TyFun tyVars ty) tys) env = TyVar $ mkId "wrong"


substSpecs = do
  describe "subst" $ do
    it "subs nil" $ do
      subst TyNil mtEnv `shouldBe` TyNil

    it "subs types for type vars" $ do
      subst (TyVar (mkId "foo")) mtEnv `shouldBe` TyVar (mkId "foo")
      subst (TyVar (mkId "T")) [((mkId "T"), TyApp Int [])] `shouldBe` TyApp Int []

    it "subs polymorphic record types" $ do
      subst (TyApp (TyFun [mkId "T", mkId "K"] (TyApp (Record [mkId "fst", mkId "snd"]) [TyVar (mkId "T"), TyVar (mkId "K")]))
              [TyApp Int [], TyApp String []])
            mtEnv
        `shouldBe`
        (TyApp (Record [mkId "fst", mkId "snd"]) [TyApp Int [], TyApp String []])
