module Syntax where

import Control.Monad
import Data.Foldable
import Test.Hspec
import Text.Printf

data Id = UserId String | UniqId Int String
  deriving (Eq, Show)

mkId :: String -> Id
mkId sym = UserId sym

type TyVar = Id
type TyField = (Id, Ty)

data Ty =
    TypeIdTy Id                             -- "type identifier"
  | FunTy [Ty] Ty                           -- "function type" (any arity)
  | PolyTy [TyVar] Ty                       -- "polymorphic type"
  | TyConTy Ty [Ty]                         -- "type construction"
  deriving (Eq, Show)

data Exp =
    App Exp [Ty] [Exp]                      -- exp<ty ...>(exp ...)
  | Rec Id [Ty] [(Id, Exp)]                 -- id<ty ...>{ id = exp ... }
  | Let [Dec] Exp                           -- LET dec ... IN exp
  | Num Int
  | Ref Id
  deriving (Eq, Show)

data Dec =
    VarDec Id Ty Exp                        -- VAR id : ty := exp
  | TyConDec Id [TyVar] Ty                  -- TYPE id tyvars = ty
  | ArrayTyDec Id [TyVar] Ty                -- TYPE id tyvars = ARRAY OF ty
  | RecTyDec Id [TyVar] [TyField]           -- TYPE id tyvars = { tyfields }
  | FunDec Id [TyVar] [TyField] Id Exp      -- FUNCTION id tyvars (tyfields) : id = exp
  | ProcDec Id [TyVar] [TyField] Exp        -- FUNCTION id tyvars (tyfields) = exp
  deriving (Eq, Show)


type FailMessage = String
type CanFail a = Either FailMessage a


-- Alpha conversion
-- We rewrite the syntax tree such that each binding
-- occurrence introduces a new, unique identifier and
-- substitute each bound occurrence refers back to the
-- new one.
-- We also get the nice side effect that we can detect
-- any free identifiers and return an error.

data AlphaEnv = AlphaEnv Int [(String, Id)]
  deriving (Eq, Show)

mkAlphaEnv :: AlphaEnv
mkAlphaEnv =
    env''
  where
    mtEnv = AlphaEnv 1 []
    env' = snd $ fresh (UserId "int") mtEnv
    env'' = snd $ fresh (UserId "string") env'

fresh :: Id -> AlphaEnv -> (Id, AlphaEnv)
fresh id@(UniqId _ _) env = (id, env)
fresh (UserId sym) (AlphaEnv counter tbl) =
    (newId, AlphaEnv (counter + 1) ((sym, newId):tbl))
  where
    newId = UniqId counter sym

lookupAlpha :: AlphaEnv -> Id -> CanFail Id
lookupAlpha (AlphaEnv _ table) (UserId sym) =
  let result = find (\(symKey, uid) -> sym == symKey) table
  in
    case result of
      Nothing -> Left $ printf "Unbound identifier '%s'" sym
      Just id -> Right $ snd id

lookupAlpha _ id = return id


_alphaConvertDecs :: AlphaEnv -> [Dec] -> CanFail ([Dec], AlphaEnv)
_alphaConvertDecs env [] = return ([], env)
_alphaConvertDecs env (d:decs) = do
  (d', env') <- _alphaConvertDec env d
  (decs', env'') <- _alphaConvertDecs env' decs
  return (d':decs', env'')


_alphaConvertTy :: AlphaEnv -> Ty -> CanFail (Ty, AlphaEnv)
_alphaConvertTy env (TypeIdTy id) = do
  id' <- lookupAlpha env id
  return (TypeIdTy id', env)


_alphaConvertDec :: AlphaEnv -> Dec -> CanFail (Dec, AlphaEnv)
_alphaConvertDec env (VarDec id ty e) = do
  let (id', env') = fresh id env
  (ty', _) <- _alphaConvertTy env ty
  (e', _) <- _alphaConvert env e
  return (VarDec id' ty' e', env')


_alphaConvert :: AlphaEnv -> Exp -> CanFail (Exp, AlphaEnv)
_alphaConvert env (Ref id) = do
  id' <- lookupAlpha env id
  return (Ref id', env)

_alphaConvert env (Let decs e) = do
  (decs', env') <- _alphaConvertDecs env decs
  (e', _) <- _alphaConvert env' e
  return (Let decs' e', env)

-- TODO: Still need cases for App, Rec
_alphaConvert env id = return (id, env)


alphaConvert :: Exp -> CanFail Exp
alphaConvert e = do { liftM fst $ _alphaConvert mkAlphaEnv e }


specs = do
  describe "fresh" $ do
    it "bumps the counter and gives back a 'unique' id" $ do
      fresh (UniqId 42 "foo") mkAlphaEnv `shouldBe` (UniqId 42 "foo", mkAlphaEnv)
      let env@(AlphaEnv initCounter initTable) = mkAlphaEnv
          (id1, env') = fresh (UserId "bar") env
          (id2, env'') = fresh (UserId "bar") env'
          (id3, env''') = fresh (UserId "foo") env''
      id1 `shouldBe` UniqId 3 "bar"
      id2 `shouldBe` UniqId 4 "bar"
      id3 `shouldBe` UniqId 5 "foo"

      env' `shouldBe` AlphaEnv 2 ([("bar", UniqId 1 "bar")] ++ initTable)
      env'' `shouldBe` AlphaEnv 3 [("bar", UniqId 2 "bar"), ("bar", UniqId 1 "bar")]
      env''' `shouldBe` AlphaEnv 4 [("foo", UniqId 3 "foo"), ("bar", UniqId 2 "bar"), ("bar", UniqId 1 "bar")]

  describe "alphaConvert" $ do
    it "replaces let bindings and occurrences with unique id's" $ do
      alphaConvert
        (Let [VarDec (mkId "foo") (TypeIdTy (mkId "int")) (Num 4)] (Num 3))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4)]
            (Num 3)))
