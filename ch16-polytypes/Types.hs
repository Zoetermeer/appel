module Types where

import qualified Syntax

type FieldName = Syntax.Id
type Unique = Int

data Ty =
-- Monomorphic
    TyNil
  | TyInt
  | TyString
  | TyUnit
  | TyRecord [(Syntax.Id, Ty)] Unique
  | TyArray Ty Unique
  | TyName Syntax.Id Ty
-- Polymorphic
  | TyApp TyCon [Ty]
  | TyVar Syntax.TyVar
  | TyPoly [Syntax.TyVar] Ty
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
  | TyFun [Syntax.TyVar] Ty      -- A user-defined polymorphic type constructor
  | Unique TyCon
  deriving (Show, Eq)
