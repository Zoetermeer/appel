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
  | Add Exp Exp
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
-- We avoid variable capture by rewriting the syntax tree such that each binding
-- occurrence introduces a new, unique identifier and
-- substituting each bound occurrence such that it refers back to the
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
      Just id -> return $ snd id

lookupAlpha _ id = return id


_alphaConvertIds :: AlphaEnv -> [Id] -> CanFail ([Id], AlphaEnv)
_alphaConvertIds env [] = return ([], env)
_alphaConvertIds env (id:ids) = do
  (id', env') <- return $ fresh id env
  (ids', env'') <- _alphaConvertIds env' ids
  return (id':ids', env'')

_alphaConvertDecs :: AlphaEnv -> [Dec] -> CanFail ([Dec], AlphaEnv)
_alphaConvertDecs env [] = return ([], env)
_alphaConvertDecs env (d:decs) = do
  (d', env') <- _alphaConvertDec env d
  (decs', env'') <- _alphaConvertDecs env' decs
  return (d':decs', env'')

_alphaConvertTyFields :: AlphaEnv -> [TyField] -> CanFail ([TyField], AlphaEnv)
_alphaConvertTyFields env [] = return ([], env)
_alphaConvertTyFields env ((id, ty):tyfs) = do
  (id', env') <- return $ fresh id env
  ty' <- _alphaConvertTy env' ty
  (tyfs', env'') <- _alphaConvertTyFields env' tyfs
  return ((id', ty'):tyfs', env'')


_alphaConvertTy :: AlphaEnv -> Ty -> CanFail Ty
_alphaConvertTy env (TypeIdTy id) = do
  id' <- lookupAlpha env id
  return $ TypeIdTy id'


_alphaConvertDec :: AlphaEnv -> Dec -> CanFail (Dec, AlphaEnv)
_alphaConvertDec env (VarDec id ty e) = do
  let (id', env') = fresh id env
  ty' <- _alphaConvertTy env ty
  e' <- _alphaConvert env e
  return (VarDec id' ty' e', env')

_alphaConvertDec env (FunDec funId tyVars tyFields retTyId body) = do
  (funId', env') <- return $ fresh funId env
  (tyVars', env'') <- _alphaConvertIds env' tyVars
  (tyFields', env''') <- _alphaConvertTyFields env'' tyFields
  retTyId' <- lookupAlpha env''' retTyId
  body' <- _alphaConvert env''' body
  return (FunDec funId' tyVars' tyFields' retTyId' body', env')


_alphaConvert :: AlphaEnv -> Exp -> CanFail Exp
_alphaConvert env (Ref id) = do
  id' <- lookupAlpha env id
  return $ Ref id'

_alphaConvert env (Let decs e) = do
  (decs', env') <- _alphaConvertDecs env decs
  e' <- _alphaConvert env' e
  return $ Let decs' e'

_alphaConvert env (Add lhs rhs) = do
  lhs' <- _alphaConvert env lhs
  rhs' <- _alphaConvert env rhs
  return $ Add lhs' rhs'

_alphaConvert env (App funE tyArgs argEs) = do
  funE' <- _alphaConvert env funE
  tyArgs' <- mapM (_alphaConvertTy env) tyArgs
  argEs' <- mapM (_alphaConvert env) argEs
  return $ App funE' tyArgs' argEs'

-- TODO: Still need cases for App, Rec
_alphaConvert env e = return e


alphaConvert :: Exp -> CanFail Exp
alphaConvert e = _alphaConvert mkAlphaEnv e


specs = do
  describe "fresh" $ do
    it "bumps the counter and gives back a 'unique' id" $ do
      fresh (UniqId 42 "foo") mkAlphaEnv `shouldBe` (UniqId 42 "foo", mkAlphaEnv)
      let env@(AlphaEnv initCounter initTable) = mkAlphaEnv
          (id1, env') = fresh (UserId "bar") env
          (id2, env'') = fresh (UserId "bar") env'
          id3 = fst $ fresh (UserId "foo") env''
      id1 `shouldBe` UniqId 3 "bar"
      id2 `shouldBe` UniqId 4 "bar"
      id3 `shouldBe` UniqId 5 "foo"

  describe "alphaConvert" $ do
    it "replaces let bindings and occurrences with unique id's" $ do
      alphaConvert
        (Let [VarDec (mkId "foo") (TypeIdTy (mkId "int")) (Num 4)] (Num 3))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4)]
            (Num 3)))

    it "returns an error for free identifiers" $ do
      alphaConvert (Ref (mkId "foo")) `shouldBe` Left "Unbound identifier 'foo'"

    it "replaces refs with uniq-id pointers" $ do
      alphaConvert
        (Let [VarDec (mkId "foo") (TypeIdTy (mkId "int")) (Num 4)] (Ref (mkId "foo")))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4)]
            (Ref (UniqId 3 "foo"))))

    it "preserves lexical scoping" $ do
      alphaConvert
        (Let [VarDec (mkId "foo") (TypeIdTy (mkId "int")) (Num 4),
              VarDec (mkId "foo") (TypeIdTy (mkId "int")) (Num 5)]
          (Ref (mkId "foo")))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4),
                VarDec (UniqId 4 "foo") (TypeIdTy (UniqId 1 "int")) (Num 5)]
            (Ref (UniqId 4 "foo"))))

    it "preserves lexical scoping in nested lets" $ do
      alphaConvert
        (Let [VarDec (mkId "foo") (TypeIdTy (mkId "int")) (Num 4)]
          (Let [VarDec (mkId "foo") (TypeIdTy (mkId "int")) (Num 5)]
            (Ref (mkId "foo"))))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4)]
            (Let [VarDec (UniqId 4 "foo") (TypeIdTy (UniqId 1 "int")) (Num 5)]
              (Ref (UniqId 4 "foo")))))

    it "rewrites bound occurrences for id's in enclosing scopes" $ do
      alphaConvert
        (Let [VarDec (mkId "foo") (TypeIdTy (mkId "int")) (Num 4)]
          (Let [VarDec (mkId "bar") (TypeIdTy (mkId "int")) (Num 5)]
            (Add (Ref (mkId "foo")) (Ref (mkId "bar")))))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4)]
            (Let [VarDec (UniqId 4 "bar") (TypeIdTy (UniqId 1 "int")) (Num 5)]
              (Add (Ref (UniqId 3 "foo")) (Ref (UniqId 4 "bar"))))))

    it "rewrites polymorphic fun defs" $ do
      alphaConvert
        (Let [FunDec (mkId "identity") [mkId "T"]
                     [(mkId "x", TypeIdTy (mkId "T"))]
                     (mkId "T")
                     (Ref (mkId "x"))]
          (App (Ref (mkId "identity")) [TypeIdTy (mkId "int")] [Num 42]))
        `shouldBe`
        (Right
          (Let [FunDec (UniqId 3 "identity") [UniqId 4 "T"]
                       [(UniqId 5 "x", TypeIdTy (UniqId 4 "T"))]
                       (UniqId 4 "T")
                       (Ref (UniqId 5 "x"))]
            (App (Ref (UniqId 3 "identity")) [TypeIdTy (UniqId 1 "int")] [Num 42])))

