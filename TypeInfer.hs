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
inferTypes cenv (ELambda v body) = let newEnv = (newTVar cenv)
                                       nextVal = (inferTypes ((snd newEnv) {tenv = (tenv (snd newEnv)) ++ [(v, TVar v)] }) body) in
    (CEnv {
      constraints = (constraints (fst nextVal)) ++ [((fst newEnv), (TArrow (TVar v) (snd nextVal)))]
      , var = var cenv
      , tenv = tenv cenv
    }, fst newEnv)
inferTypes cenv (EApp fn arg) = let e = (newTVar cenv)
                                    e1 = (inferTypes ((snd e)) fn)
                                    e2 = (inferTypes ((snd e)) arg) in
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
inferTypes cenv (EPlus op1 op2) = let e = (newTVar cenv)
                                      e1 = (inferTypes (snd e) op1)
                                      e2 = (inferTypes (snd e) op2) in
  (CEnv {
    constraints = (constraints (fst e1)) ++ (constraints (fst e2)) ++ [((snd e1), (intType))] ++ [((snd e2), (intType))] ++ [((fst e), (intType))]
    , var = var cenv
    , tenv = tenv cenv
  }, intType)
inferTypes cenv (EPrim (PNum _)) = (cenv, intType)
inferTypes cenv (EPrim (PBool _)) = (cenv, boolType)
inferTypes cenv (ELet s body) = let e = (newTVar cenv) in case s of 
  SEmpty -> (inferTypes cenv body)
  SAssign id exp -> let e1 = (inferTypes ((snd e) {tenv = (tenv (snd e)) ++ [(id, TVar id)]}) exp) in
    if (getType (tenv cenv) id) == (snd e1) then (inferTypes cenv body) else throw (TypeMismatch (snd e1) (getType (tenv cenv) id))
  SSeq s1 s2 -> let e1 = (inferTypes (snd e) (ELet s1 body))
                    e2 = (inferTypes (snd e) (ELet s2 body)) in
    (CEnv {
      constraints = (constraints (fst e1)) ++ (constraints (fst e2))
      , var = var cenv
      , tenv = (tenv (fst e1)) ++ (tenv (fst e2))
    }, snd (inferTypes cenv body))
  
unifySet :: Constraints -> Subst
unifySet [] = []
unifySet const = let first_val = (head const)
                     second_val = (tail const) in
  (unify [first_val]) ++ (unifySet second_val)

{- Top-level type inference function. I will be calling it on Submitty. -}
inferType :: Exp -> Type
inferType exp = let full = (inferTypes (CEnv {constraints = [], var = 0, tenv = []}) exp) in
  applySubst (snd full) (unifySet (constraints (fst full)))