module Utils
  ( ToImplement(..)
  , addConstraint, addConstraints
  , newTVar, substVar, substAll, applySubst
  , occursIn )
  where
import Control.Exception
import Data.Typeable
import Data

-- Errors.
data ToImplement = ToImplement deriving (Show, Typeable)
instance Exception ToImplement

addConstraint :: ConstraintEnv -> Type -> Type -> ConstraintEnv
addConstraint cenv expected inferred =
  addConstraints cenv [(expected, inferred)]
addConstraints :: ConstraintEnv -> [(Type, Type)] -> ConstraintEnv
addConstraints cenv new =
  CEnv { constraints = new ++ (constraints cenv)
       , var = var cenv
       , tenv = tenv cenv }

{- Generates a fresh type variable. -}
newTVar :: ConstraintEnv -> (Type, ConstraintEnv)
newTVar cenv =
  let cenv' = CEnv { constraints = constraints cenv
                   , var = var cenv + 1
                   , tenv = tenv cenv }
  in (TVar ("__" ++ show (var cenv)), cenv')

{- Substitution. -}
substVar from to haystack@(TBase _) = haystack
substVar from to var@(TVar _) = if var == from then to else var
substVar from to var@(TArrow t1 t2) =
  TArrow (substVar from to t1) (substVar from to t2)

substAll :: Type -> Type -> Constraints -> Constraints
substAll from to = map substPair
  where substPair (x, y) = (substVar from to x, substVar from to y)

applySubst :: Type -> Subst -> Type
applySubst = foldl doSubst
  where doSubst inType (from, to) = substVar (TVar from) to inType

occursIn :: Type -> Type -> Bool
occursIn needle (TBase _) = False
occursIn needle haystack@(TVar _) = needle == haystack
occursIn needle (TArrow t1 t2) = (occursIn needle t1) || (occursIn needle t2)
