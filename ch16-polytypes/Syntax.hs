module Syntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Test.Hspec
import Text.Printf (printf)

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
  | Nil
  deriving (Eq, Show)

data Dec =
    VarDec Id Ty Exp                        -- VAR id : ty := exp
  | TyConDec Id [TyVar] Ty                  -- TYPE id tyvars = ty
  | ArrayTyDec Id [TyVar] Ty                -- TYPE id tyvars = ARRAY OF ty
  | RecTyDec Id [TyVar] [TyField]           -- TYPE id tyvars = { tyfields }
  | FunDec Id [TyVar] [TyField] Id Exp      -- FUNCTION id tyvars (tyfields) : id = exp
  | ProcDec Id [TyVar] [TyField] Exp        -- FUNCTION id tyvars (tyfields) = exp
  deriving (Eq, Show)



-- Alpha conversion
-- We avoid variable capture by rewriting the syntax tree such that each binding
-- occurrence introduces a new, unique identifier and
-- substituting each bound occurrence such that it refers back to the
-- new one.
-- We also get the nice side effect that we can detect
-- any free identifiers and return an error.

data AlphaEnv = AlphaEnv Int [(String, Id)]
  deriving (Eq, Show)

type FailMessage = String
type AlphaConverted a = ExceptT FailMessage (State AlphaEnv) a

mkAlphaEnv :: AlphaEnv
mkAlphaEnv =
  AlphaEnv 3 [("int", UniqId 1 "int"), ("string", UniqId 2 "string")]


pushEnv :: AlphaConverted AlphaEnv
pushEnv = lift get

popEnv :: AlphaEnv -> AlphaConverted ()
popEnv (AlphaEnv _ table) = do
  (AlphaEnv counter' _) <- lift get
  put $ AlphaEnv counter' table


fresh :: Id -> AlphaConverted Id
fresh id@(UniqId _ _) = return id
fresh (UserId sym) = do
  (AlphaEnv counter table) <- lift $ get
  let newId = UniqId counter sym
  lift $ put $ AlphaEnv (counter + 1) ((sym, newId):table)
  return newId


lookupAlpha :: Id -> AlphaConverted Id
lookupAlpha (UserId sym) = do
  (AlphaEnv _ table) <- lift $ get
  let result = find (\(symKey, uid) -> sym == symKey) table
  case result of
    Nothing -> throwError $ printf "Unbound identifier '%s'" sym
    Just id -> return $ snd id

lookupAlpha id = return id


_alphaConvertTyField :: TyField -> AlphaConverted TyField
_alphaConvertTyField (id, ty) = do
  id' <- fresh id
  ty' <- _alphaConvertTy ty
  return (id', ty')


_alphaConvertTy :: Ty -> AlphaConverted Ty
_alphaConvertTy (TypeIdTy id) = do
  id' <- lookupAlpha id
  return $ TypeIdTy id'

_alphaConvertTy (FunTy argTys retTy) = do
  argTys' <- mapM _alphaConvertTy argTys
  retTy' <- _alphaConvertTy retTy
  return $ FunTy argTys' retTy'

_alphaConvertTy (TyConTy ty tyArgs) = do
  ty' <- _alphaConvertTy ty
  tyArgs' <- mapM _alphaConvertTy tyArgs
  return $ TyConTy ty' tyArgs'

_alphaConvertTy (PolyTy tyVars ty) = do
  tyVars' <- mapM fresh tyVars
  ty' <- _alphaConvertTy ty
  return $ PolyTy tyVars' ty'


_alphaConvertDec :: Dec -> AlphaConverted Dec
_alphaConvertDec (VarDec id ty e) = do
  id' <- fresh id
  ty' <- _alphaConvertTy ty
  e' <- _alphaConvert e
  return (VarDec id' ty' e')

_alphaConvertDec (FunDec funId tyVars tyFields retTyId body) = do
  funId' <- fresh funId
  tyVars' <- mapM fresh tyVars
  tyFields' <- mapM _alphaConvertTyField tyFields
  retTyId' <- lookupAlpha retTyId
  body' <- _alphaConvert body
  return (FunDec funId' tyVars' tyFields' retTyId' body')

_alphaConvertDec (RecTyDec id tyVars tyFields) = do
  id' <- fresh id
  env <- pushEnv
  tyVars' <- mapM fresh tyVars
  tyFields' <- mapM (\(fid, fty) -> do { fty' <- _alphaConvertTy fty; return (fid, fty') }) tyFields
  popEnv env
  return $ RecTyDec id' tyVars' tyFields'


_alphaConvert :: Exp -> AlphaConverted Exp
_alphaConvert (Ref id) = do
  id' <- lookupAlpha id
  return $ Ref id'

_alphaConvert (Let decs e) = do
  env <- pushEnv
  decs' <- mapM _alphaConvertDec decs
  e' <- _alphaConvert e
  popEnv env
  return $ Let decs' e'

_alphaConvert (Add lhs rhs) = do
  lhs' <- _alphaConvert lhs
  rhs' <- _alphaConvert rhs
  return $ Add lhs' rhs'

_alphaConvert (App funE tyArgs argEs) = do
  funE' <- _alphaConvert funE
  tyArgs' <- mapM _alphaConvertTy tyArgs
  argEs' <- mapM _alphaConvert argEs
  return $ App funE' tyArgs' argEs'

_alphaConvert (Rec id tyArgs fields) = do
  id' <- lookupAlpha id
  tyArgs' <- mapM _alphaConvertTy tyArgs
  fields' <- mapM (\(fid, e) -> do { e' <- _alphaConvert e; return (fid, e) }) fields
  return $ Rec id' tyArgs' fields'

_alphaConvert (Num x) = return $ Num x
_alphaConvert Nil = return Nil


alphaConvert :: Exp -> Either FailMessage Exp
alphaConvert e = evalState (runExceptT $ _alphaConvert e) mkAlphaEnv


specs = do
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

    -- let type foo<T> = { x : T }
    --     var T : int = 42
    -- in
    --   ref T
    it "preserves lexical scoping for ty vars" $ do
      alphaConvert
        (Let [RecTyDec (mkId "foo") [mkId "T"] [(mkId "x", TypeIdTy (mkId "T"))],
              VarDec (mkId "T") (TypeIdTy (mkId "int")) (Num 42)]
          (Ref (mkId "T")))
        `shouldBe`
        (Right
          (Let [RecTyDec (UniqId 3 "foo") [UniqId 4 "T"] [(mkId "x", TypeIdTy (UniqId 4 "T"))],
                VarDec (UniqId 5 "T") (TypeIdTy (UniqId 1 "int")) (Num 42)]
            (Ref (UniqId 5 "T"))))

    -- let type foo<T> = { x : T }
    -- in
    --   ref T
    it "does not preserve local ty vars in outer scopes" $ do
      alphaConvert
        (Let [RecTyDec (mkId "foo") [mkId "T"] [(mkId "x", TypeIdTy (mkId "T"))]]
          (Ref (mkId "T")))
        `shouldBe`
        (Left "Unbound identifier 'T'")

    it "does not preserve bindings from nested lets in outer scopes" $ do
      alphaConvert
        (Let [VarDec (mkId "foo")
                     (TypeIdTy (mkId "int"))
                     (Let [VarDec (mkId "bar") (TypeIdTy (mkId "int")) (Num 43)] (Ref (mkId "bar")))]
          (Ref (mkId "bar")))
        `shouldBe`
        (Left "Unbound identifier 'bar'")

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

    it "does not alpha-convert record field identifiers" $ do
      alphaConvert
        (Let [RecTyDec (mkId "list") [mkId "T"]
                       [(mkId "hd", TypeIdTy (mkId "T")),
                        (mkId "tl", TyConTy (TypeIdTy (mkId "list")) [TypeIdTy (mkId "T")])]]
          (Num 42))
        `shouldBe`
        (Right
          (Let [RecTyDec (UniqId 3 "list")
                         [UniqId 4 "T"]
                         [(mkId "hd", TypeIdTy (UniqId 4 "T")),
                          (mkId "tl", TyConTy (TypeIdTy (UniqId 3 "list")) [TypeIdTy (UniqId 4 "T")])]]
            (Num 42)))

    -- let type list<T> = { hd : T, tl : list<T> }
    --     var ls : list<int> = list<int>{ hd = 42, tl = nil }
    -- in
    --   ls
    -- TODO: this needs to be fixed, the type declaration
    -- should be a poly<T>
    -- RecTyDec should probably go away altogether
    it "rewrites record instantiations" $ do
      alphaConvert
        (Let [(RecTyDec (mkId "list") [mkId "T"]
                       [(mkId "hd", TypeIdTy (mkId "T")),
                        (mkId "tl", TyConTy (TypeIdTy (mkId "list")) [TypeIdTy (mkId "T")])]),
              (VarDec (mkId "ls")
                      (TyConTy (TypeIdTy (mkId "list")) [TypeIdTy (mkId "int")])
                      (Rec (mkId "list") [TypeIdTy (mkId "int")] [(mkId "hd", Num 42), (mkId "tl", Nil)]))]
          (Ref (mkId "ls")))
        `shouldBe`
        (Right
          (Let [(RecTyDec (UniqId 3 "list") [UniqId 4 "T"]
                         [(mkId "hd", TypeIdTy (UniqId 4 "T")),
                          (mkId "tl", TyConTy (TypeIdTy (UniqId 3 "list")) [TypeIdTy (UniqId 4 "T")])]),
                (VarDec (UniqId 5 "ls")
                        (TyConTy (TypeIdTy (UniqId 3 "list")) [TypeIdTy (UniqId 1 "int")])
                        (Rec (UniqId 3 "list") [TypeIdTy (UniqId 1 "int")] [(mkId "hd", Num 42), (mkId "tl", Nil)]))]
            (Ref (UniqId 5 "ls"))))
