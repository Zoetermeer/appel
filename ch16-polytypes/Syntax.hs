module Syntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Test.Hspec
import Text.Printf (printf)

type RawId = String
data Id = UserId String | UniqId Int String
  deriving (Eq, Show)

mkId :: String -> Id
mkId sym = UserId sym

type TyVar id = id
type TyField id = (id, Ty id)

data Ty id =
    TypeIdTy id                                     -- "type identifier"
  | FunTy [Ty id] (Ty id)                           -- "function type" (any arity)
  | PolyTy [TyVar id] (Ty id)                       -- "polymorphic type"
  | TyConTy (Ty id) [Ty id]                         -- "type construction"
  deriving (Eq, Show)

data Exp id =
    App (Exp id) [Ty id] [Exp id]                   -- exp<ty ...>(exp ...)
  | Rec id [Ty id] [(id, Exp id)]                   -- id<ty ...>{ id = exp ... }
  | Let [Dec id] (Exp id)                           -- LET dec ... IN exp
  | Num Int
  | Ref id
  | Add (Exp id) (Exp id)
  | Nil
  deriving (Eq, Show)

data Dec id =
    VarDec id (Ty id) (Exp id)                      -- VAR id : ty := exp
  | TyConDec id [TyVar id] (Ty id)                  -- TYPE id tyvars = ty
  | ArrayTyDec id [TyVar id] (Ty id)                -- TYPE id tyvars = ARRAY OF ty
  | RecTyDec id [TyVar id] [TyField id]             -- TYPE id tyvars = { tyfields }
  | FunDec id [TyVar id] [TyField id] id (Exp id)   -- FUNCTION id tyvars (tyfields) : id = exp
  | ProcDec id [TyVar id] [TyField id] (Exp id)     -- FUNCTION id tyvars (tyfields) = exp
  deriving (Eq, Show)



-- Alpha conversion
-- We avoid variable capture by rewriting the syntax tree such that each binding
-- occurrence introduces a new, unique identifier and
-- substituting each bound occurrence such that it refers back to the
-- new one.
-- We also get the nice side effect that we can detect
-- any free identifiers and return an error.

data AlphaEnv = AlphaEnv Int [(RawId, Id)]
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


fresh :: RawId -> AlphaConverted Id
fresh sym = do
  (AlphaEnv counter table) <- lift $ get
  let newId = UniqId counter sym
  lift $ put $ AlphaEnv (counter + 1) ((sym, newId):table)
  return newId


lookupAlpha :: RawId -> AlphaConverted Id
lookupAlpha sym = do
  (AlphaEnv _ table) <- lift $ get
  let result = find (\(symKey, uid) -> sym == symKey) table
  case result of
    Nothing -> throwError $ printf "Unbound identifier '%s'" sym
    Just id -> return $ snd id


alphaConvertTyField :: TyField RawId -> AlphaConverted (TyField Id)
alphaConvertTyField (id, ty) = do
  id' <- fresh id
  ty' <- alphaConvertTy ty
  return (id', ty')


alphaConvertTy :: Ty RawId -> AlphaConverted (Ty Id)
alphaConvertTy (TypeIdTy id) = do
  id' <- lookupAlpha id
  return $ TypeIdTy id'

alphaConvertTy (FunTy argTys retTy) = do
  argTys' <- mapM alphaConvertTy argTys
  retTy' <- alphaConvertTy retTy
  return $ FunTy argTys' retTy'

alphaConvertTy (TyConTy ty tyArgs) = do
  ty' <- alphaConvertTy ty
  tyArgs' <- mapM alphaConvertTy tyArgs
  return $ TyConTy ty' tyArgs'

alphaConvertTy (PolyTy tyVars ty) = do
  tyVars' <- mapM fresh tyVars
  ty' <- alphaConvertTy ty
  return $ PolyTy tyVars' ty'


alphaConvertDec :: Dec RawId -> AlphaConverted (Dec Id)
alphaConvertDec (VarDec id ty e) = do
  id' <- fresh id
  ty' <- alphaConvertTy ty
  e' <- alphaConvert e
  return (VarDec id' ty' e')

alphaConvertDec (FunDec funId tyVars tyFields retTyId body) = do
  funId' <- fresh funId
  tyVars' <- mapM fresh tyVars
  tyFields' <- mapM alphaConvertTyField tyFields
  retTyId' <- lookupAlpha retTyId
  body' <- alphaConvert body
  return (FunDec funId' tyVars' tyFields' retTyId' body')

alphaConvertDec (RecTyDec id tyVars tyFields) = do
  id' <- fresh id
  env <- pushEnv
  tyVars' <- mapM fresh tyVars
  tyFields' <- mapM (\(fid, fty) -> do { fty' <- alphaConvertTy fty; return (UserId fid, fty') }) tyFields
  popEnv env
  return $ RecTyDec id' tyVars' tyFields'


alphaConvert :: Exp RawId -> AlphaConverted (Exp Id)
alphaConvert (Ref id) = do
  id' <- lookupAlpha id
  return $ Ref id'

alphaConvert (Let decs e) = do
  env <- pushEnv
  decs' <- mapM alphaConvertDec decs
  e' <- alphaConvert e
  popEnv env
  return $ Let decs' e'

alphaConvert (Add lhs rhs) = do
  lhs' <- alphaConvert lhs
  rhs' <- alphaConvert rhs
  return $ Add lhs' rhs'

alphaConvert (App funE tyArgs argEs) = do
  funE' <- alphaConvert funE
  tyArgs' <- mapM alphaConvertTy tyArgs
  argEs' <- mapM alphaConvert argEs
  return $ App funE' tyArgs' argEs'

alphaConvert (Rec id tyArgs fields) = do
  id' <- lookupAlpha id
  tyArgs' <- mapM alphaConvertTy tyArgs
  fields' <- mapM (\(fid, e) -> do { e' <- alphaConvert e; return (UserId fid, e') }) fields
  return $ Rec id' tyArgs' fields'

alphaConvert (Num x) = return $ Num x
alphaConvert Nil = return Nil


runAlphaConvert :: Exp RawId -> Either FailMessage (Exp Id)
runAlphaConvert e = evalState (runExceptT $ alphaConvert e) mkAlphaEnv


specs = do
  describe "runAlphaConvert" $ do
    it "replaces let bindings and occurrences with unique id's" $ do
      runAlphaConvert
        (Let [VarDec "foo" (TypeIdTy "int") (Num 4)] (Num 3))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4)]
            (Num 3)))

    it "returns an error for free identifiers" $ do
      runAlphaConvert (Ref "foo") `shouldBe` Left "Unbound identifier 'foo'"

    it "replaces refs with uniq-id pointers" $ do
      runAlphaConvert
        (Let [VarDec "foo" (TypeIdTy "int") (Num 4)] (Ref "foo"))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4)]
            (Ref (UniqId 3 "foo"))))

    it "preserves lexical scoping" $ do
      runAlphaConvert
        (Let [VarDec "foo" (TypeIdTy "int") (Num 4),
              VarDec "foo" (TypeIdTy "int") (Num 5)]
          (Ref "foo"))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4),
                VarDec (UniqId 4 "foo") (TypeIdTy (UniqId 1 "int")) (Num 5)]
            (Ref (UniqId 4 "foo"))))

    it "preserves lexical scoping in nested lets" $ do
      runAlphaConvert
        (Let [VarDec "foo" (TypeIdTy "int") (Num 4)]
          (Let [VarDec "foo" (TypeIdTy "int") (Num 5)]
            (Ref "foo")))
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
      runAlphaConvert
        (Let [RecTyDec "foo" ["T"] [("x", TypeIdTy "T")],
              VarDec "T" (TypeIdTy "int") (Num 42)]
          (Ref "T"))
        `shouldBe`
        (Right
          (Let [RecTyDec (UniqId 3 "foo") [UniqId 4 "T"] [(mkId "x", TypeIdTy (UniqId 4 "T"))],
                VarDec (UniqId 5 "T") (TypeIdTy (UniqId 1 "int")) (Num 42)]
            (Ref (UniqId 5 "T"))))

    -- let type foo<T> = { x : T }
    -- in
    --   ref T
    it "does not preserve local ty vars in outer scopes" $ do
      runAlphaConvert
        (Let [RecTyDec "foo" ["T"] [("x", TypeIdTy "T")]]
          (Ref "T"))
        `shouldBe`
        (Left "Unbound identifier 'T'")

    it "does not preserve bindings from nested lets in outer scopes" $ do
      runAlphaConvert
        (Let [VarDec "foo"
                     (TypeIdTy "int")
                     (Let [VarDec "bar" (TypeIdTy "int") (Num 43)] (Ref "bar"))]
          (Ref "bar"))
        `shouldBe`
        (Left "Unbound identifier 'bar'")

    it "rewrites bound occurrences for id's in enclosing scopes" $ do
      runAlphaConvert
        (Let [VarDec "foo" (TypeIdTy "int") (Num 4)]
          (Let [VarDec "bar" (TypeIdTy "int") (Num 5)]
            (Add (Ref "foo") (Ref "bar"))))
        `shouldBe`
        (Right
          (Let [VarDec (UniqId 3 "foo") (TypeIdTy (UniqId 1 "int")) (Num 4)]
            (Let [VarDec (UniqId 4 "bar") (TypeIdTy (UniqId 1 "int")) (Num 5)]
              (Add (Ref (UniqId 3 "foo")) (Ref (UniqId 4 "bar"))))))

    it "rewrites polymorphic fun defs" $ do
      runAlphaConvert
        (Let [FunDec "identity" ["T"]
                     [("x", TypeIdTy "T")]
                     "T"
                     (Ref "x")]
          (App (Ref "identity") [TypeIdTy "int"] [Num 42]))
        `shouldBe`
        (Right
          (Let [FunDec (UniqId 3 "identity") [UniqId 4 "T"]
                       [(UniqId 5 "x", TypeIdTy (UniqId 4 "T"))]
                       (UniqId 4 "T")
                       (Ref (UniqId 5 "x"))]
            (App (Ref (UniqId 3 "identity")) [TypeIdTy (UniqId 1 "int")] [Num 42])))

    it "does not alpha-convert record field identifiers" $ do
      runAlphaConvert
        (Let [RecTyDec "list" ["T"]
                       [("hd", TypeIdTy "T"),
                        ("tl", TyConTy (TypeIdTy "list") [TypeIdTy "T"])]]
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
    it "rewrites record instantiations" $ do
      runAlphaConvert
        (Let [(RecTyDec "list" ["T"]
                       [("hd", TypeIdTy "T"),
                        ("tl", TyConTy (TypeIdTy "list") [TypeIdTy "T"])]),
              (VarDec "ls"
                      (TyConTy (TypeIdTy "list") [TypeIdTy "int"])
                      (Rec "list" [TypeIdTy "int"] [("hd", Num 42), ("tl", Nil)]))]
          (Ref "ls"))
        `shouldBe`
        (Right
          (Let [(RecTyDec (UniqId 3 "list") [UniqId 4 "T"]
                         [(mkId "hd", TypeIdTy (UniqId 4 "T")),
                          (mkId "tl", TyConTy (TypeIdTy (UniqId 3 "list")) [TypeIdTy (UniqId 4 "T")])]),
                (VarDec (UniqId 5 "ls")
                        (TyConTy (TypeIdTy (UniqId 3 "list")) [TypeIdTy (UniqId 1 "int")])
                        (Rec (UniqId 3 "list") [TypeIdTy (UniqId 1 "int")] [(mkId "hd", Num 42), (mkId "tl", Nil)]))]
            (Ref (UniqId 5 "ls"))))
