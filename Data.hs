module Data
  ( Ident, TVar
  , Prim(..), Exp(..), Stmt(..)
  , BaseType(..), Type(..)
  , TCError (..)
  , Env(..), TEnv(..)
  , Constraints(..), ConstraintEnv(..)
  , Subst(..), idSubst
  , intType, boolType )
  where
import Data.Typeable
import Control.Exception

type Ident = String
type TVar = String

-- Language.
data Prim =
    PNum Int
  | PBool Bool

data Exp =
    EVar Ident
  | ELambda Ident Exp
  | EApp Exp Exp
  | ECond Exp Exp Exp
  | EPlus Exp Exp
  | EPrim Prim
  | ELet Stmt Exp

data Stmt =
    SEmpty
  | SAssign Ident Exp
  | SSeq Stmt Stmt

-- Types.
data BaseType = BTInt | BTBool
  deriving (Eq, Show)
data Type =
    TBase BaseType
  | TVar TVar
  | TArrow Type Type
  deriving (Eq, Show)

-- Errors.
data TCError =
    UnboundVar String
  | TypeCircularity
  | TypeMismatch Type Type
  | Default String
  deriving (Show, Typeable)
instance Exception TCError

-- Environment.
type Env = [(String, Exp)]
type TEnv = [(String, Type)]

{- Constraint environment. -}
type Constraints = [(Type, Type)]
data ConstraintEnv =
  CEnv {
      constraints :: Constraints
    , var :: Int
    , tenv :: TEnv }
type Subst = [(TVar, Type)]
idSubst = []

-- Default types.
intType = TBase BTInt
boolType = TBase BTBool
