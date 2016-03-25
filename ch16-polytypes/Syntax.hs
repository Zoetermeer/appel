module Syntax where

type Id = String
type TyVar = Id
type TyField = (Id, Ty)

data Ty =
    TypeIdTy Id                             -- "type identifier"
  | FunTy [Ty] Ty                           -- "function type" (any arity)
  | PolyTy [TyVar] Ty                       -- "polymorphic type"
  | TyConTy Ty [Ty]                         -- "type construction"
  deriving (Show)

data Exp =
    App Exp [Ty] [Exp]                      -- exp<ty ...>(exp ...)
  | Rec Id [Ty] [(Id, Exp)]                 -- id<ty ...>{ id = exp ... }
  | Let [Dec] Exp                           -- LET dec ... IN exp
  deriving (Show)

data Dec =
    VarDec Id Ty Exp                        -- VAR id : ty := exp
  | TyConDec Id [TyVar] Ty                  -- TYPE id tyvars = ty
  | ArrayTyDec Id [TyVar] Ty                -- TYPE id tyvars = ARRAY OF ty
  | RecTyDec Id [TyVar] [TyField]           -- TYPE id tyvars = { tyfields }
  | FunDec Id [TyVar] [TyField] Id Exp      -- FUNCTION id tyvars (tyfields) : id = exp
  | ProcDec Id [TyVar] [TyField] Exp        -- FUNCTION id tyvars (tyfields) = exp
  deriving (Show)
