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

getType :: TEnv -> String -> Type
getType [] name = throw (UnboundVar name)
getType env name = let val = (head env) in
                    if (fst val) == name then (snd val) else getType (tail env) name

{- Performs type inference. -}
inferTypes :: ConstraintEnv -> Exp -> (ConstraintEnv, Type)
inferTypes cenv (EVar var) = let this_type = (getType (tenv cenv) var) in
  (cenv, this_type)
inferTypes cenv (ELambda v body) = 
  let newEnv = (newTVar cenv)
      nextVal = (inferTypes ((snd newEnv) {tenv = (tenv (snd newEnv)) ++ [(v, TVar v)] }) body)
  in
    (CEnv {
      constraints = (constraints (fst nextVal)) ++ [((fst newEnv), (TArrow (TVar v) (snd nextVal)))]
      , var = var cenv
      , tenv = tenv cenv
    }, fst newEnv)
inferTypes cenv (EApp fn arg) = 
  let e = (newTVar cenv)
      e1 = (inferTypes ((snd e)) fn)
      e2 = (inferTypes ((snd e)) arg)
  in
    (CEnv {
      constraints = (constraints (fst e1)) ++ (constraints (fst e2) ++ [((snd e1), (TArrow (snd e2) (fst e)))])
      , var = var cenv
      , tenv = tenv cenv
    }, (fst e))
inferTypes cenv (ECond pred tbody fbody) =
  let e = (newTVar cenv)
      epred = (inferTypes (snd e) pred)
      etbody = (inferTypes (snd e) tbody)
      efbody = (inferTypes (snd e) fbody)
  in
    if (snd epred) == boolType then
      (CEnv {
        constraints = (constraints (fst epred)) ++ (constraints (fst etbody)) ++ (constraints (fst efbody)) ++ [((snd etbody), (snd efbody))]
        , var = var cenv
        , tenv = tenv cenv
      }, (snd etbody))
    else throw (TypeMismatch (snd epred) boolType)
inferTypes cenv (EPlus op1 op2) =
  let e = (newTVar cenv)
      e1 = (inferTypes (snd e) op1)
      e2 = (inferTypes (snd e) op2) in
  (CEnv {
    constraints = (constraints (fst e1)) ++ (constraints (fst e2)) ++ [((snd e1), (intType))] ++ [((snd e2), (intType))] ++ [((fst e), (intType))]
    , var = var cenv
    , tenv = tenv cenv
  }, intType)
inferTypes cenv (EPrim (PNum _)) = (cenv, intType)
inferTypes cenv (EPrim (PBool _)) = (cenv, boolType)
inferTypes cenv (ELet s body) = throw ToImplement

{- Top-level type inference function. I will be calling it on Submitty. -}
inferType :: Exp -> Type
inferType exp = throw ToImplement

