{-# LANGUAGE UnicodeSyntax #-}
module Main where

type Id = String
type FieldName = Id
type TyVar = Id

data Ty =
    Nil
  | App TyCon [Ty]
  | Var TyVar
  | Poly [TyVar] Ty
  deriving (Show, Eq)

data TyCon =
    Int
  | String
  | Unit
  | Arrow
  | Array
  | Record [FieldName]
  | TyFun [TyVar] Ty
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


main :: IO ()
main = do
  print $ subst (Var "foo") mtEnv
  print $ subst (Var "bar") mtEnv
  print $ subst (Var "T") [("T", App Int [])]

  -- type pair<A, B> = { fst : A, snd : B }
  -- need an App here, not a TyCon
  print $ subst (TyFun ["A", "B"] (App (Record ["fst", "snd"]) [Var("A"), Var("B")]))
  print $ subst Nil mtEnv
