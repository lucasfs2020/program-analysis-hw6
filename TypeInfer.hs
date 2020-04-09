{-
  You will be filling in the gaps to implement simple type inference.  Please
  provide an implementation for all functions that raise the "ToImplement"
  exception.

  Feel free to add additional functions as you wish.
 -}
module TypeInfer (inferType) where
import Control.Exception
import Data
import Utils
import Debug.Trace

unify :: Constraints -> Subst
unify [(t1, t2)] = case (t1, t2) of
  (t1, TVar var2) -> if (not (occursIn (t1) (TVar var2))) then [(var2, t1)] else throw TypeCircularity
  (TVar var1, t2) -> if (not (occursIn (t2) (TVar var1))) then [(var1, t2)] else throw TypeCircularity
  (TBase b1, TBase b2) -> if (b1 == b2) then [] else throw (TypeMismatch (TBase b1) (TBase b2))
  (TArrow t11 t12, TArrow t21 t22) -> let s1 = (unify [(t11, t21)])
                                          s2 = (unify [((applySubst t12 s1), (applySubst t22 s1))])
                                      in s1 ++ s2
  (t1, t2) -> throw (TypeMismatch t1 t2)
                                        
{- Performs type inference. -}
inferTypes :: ConstraintEnv -> Exp -> (ConstraintEnv, Type)
inferTypes cenv (EVar var) = throw ToImplement
inferTypes cenv (ELambda v body) = throw ToImplement
inferTypes cenv (EApp fn arg) = throw ToImplement
inferTypes cenv (ECond pred tbody fbody) = throw ToImplement
inferTypes cenv (EPlus op1 op2) = throw ToImplement
inferTypes cenv (EPrim (PNum _)) = throw ToImplement
inferTypes cenv (EPrim (PBool _)) = throw ToImplement
inferTypes cenv (ELet s body) = throw ToImplement

{- Top-level type inference function. I will be calling it on Submitty. -}
inferType :: Exp -> Type
inferType exp = throw ToImplement

