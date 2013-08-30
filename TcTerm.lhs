\begin{code}
module TcTerm where

import BasicTypes
import Data.IORef
import TcMonad
import Data.List( (\\) )
import Text.PrettyPrint.HughesPJ

------------------------------------------
--      The top-level wrapper           --
------------------------------------------

typecheck :: (Term Name) -> Tc (Sigma, Term Id)
typecheck e = do { (ty, e') <- inferSigma e
                 ; ty' <- zonkType ty 
                 ; e'' <- zonkTerm e'
                 ; return (ty', e'') }

-----------------------------------
--      The expected type       -- 
-----------------------------------

data Expected a = Infer (IORef a) | Check a


------------------------------------------
--      tcRho, and its variants         --
------------------------------------------

checkRho :: (Term Name) -> Rho -> Tc (Term Id)
-- Invariant: the Rho is always in weak-prenex form
checkRho expr ty = tcRho expr (Check ty)

inferRho :: (Term Name) -> Tc (Rho, Term Id)
inferRho expr 
  = do { ref <- newTcRef (error "inferRho: empty result")
       ; expr' <- tcRho expr (Infer ref)
       ; rho <- readTcRef ref
       ; return (rho, expr') }

tcRho :: (Term Name) -> Expected Rho -> Tc (Term Id)
-- Invariant: if the second argument is (Check rho),
-- 	      then rho is in weak-prenex form
tcRho (Lit i) exp_ty
  = do { instSigma intType exp_ty
       ; return (Lit i) }

tcRho (Var v) exp_ty 
  = do { v_sigma <- lookupVar v 
       ; v_sigma' <- instSigma v_sigma exp_ty 
       ; return (Var (Id v v_sigma')) }

tcRho (App fun arg) exp_ty
  = do { (fun_ty, fun') <- inferRho fun
       ; (arg_ty, res_ty) <- unifyFun fun_ty
       ; arg' <- checkSigma arg arg_ty
       ; instSigma res_ty exp_ty
       ; return (App fun' arg') }

tcRho (Lam var body) (Check exp_ty)
  = do { (var_ty, body_ty) <- unifyFun exp_ty 
       ; body' <- extendVarEnv var var_ty (checkRho body body_ty)
       ; return (Lam (Id var var_ty) body') }

tcRho (Lam var body) (Infer ref)
  = do { var_ty  <- newTyVarTy
       ; (body_ty, body') <- extendVarEnv var var_ty (inferRho body)
       ; writeTcRef ref (var_ty --> body_ty) 
       ; return (Lam (Id var var_ty) body') }

tcRho (ALam var var_ty body) (Check exp_ty)
  = do { (arg_ty, body_ty) <- unifyFun exp_ty 
       ; subsCheck arg_ty var_ty
       ; body' <- extendVarEnv var var_ty (checkRho body body_ty)
       ; return (ALam (Id var var_ty) var_ty body') }

tcRho (ALam var var_ty body) (Infer ref)
  = do { (body_ty, body') <- extendVarEnv var var_ty (inferRho body)
       ; writeTcRef ref (var_ty --> body_ty) 
       ; return (ALam (Id var var_ty) var_ty body') }

tcRho (Let var rhs body) exp_ty
  = do { (var_ty, rhs') <- inferSigma rhs
       ; body' <- extendVarEnv var var_ty (tcRho body exp_ty)
       ; return (Let (Id var var_ty) rhs' body') }

tcRho (Ann body ann_ty) exp_ty
   = do { body' <- checkSigma body ann_ty
        ; instSigma ann_ty exp_ty
        ; return (Ann body' ann_ty) }


------------------------------------------
--      inferSigma and checkSigma
------------------------------------------

inferSigma :: (Term Name) -> Tc (Qual Sigma, Term Id)
inferSigma e
   = do { (exp_ty, e') <- inferRho e
        ; env_tys <- getEnvTypes
	; env_tvs <- getMetaTyVars env_tys
        ; res_tvs <- getMetaTyVars [exp_ty]
        ; let forall_tvs = res_tvs \\ env_tvs
        ; sigma <- quantify forall_tvs exp_ty
        ; return (Qual [] sigma, e') }

checkSigma :: (Term Name) -> Qual Sigma -> Tc (Term Id)
checkSigma expr qsigma@(Qual _ sigma)
  = do { (_, skol_tvs, rho) <- skolemise qsigma
       ; expr' <- checkRho expr rho
       ; env_tys <- getEnvTypes
       ; esc_tvs <- getFreeTyVars (sigma : env_tys)
       ; let bad_tvs = filter (`elem` esc_tvs) skol_tvs
       ; check (null bad_tvs)
               (text "Type not polymorphic enough")
       ; return expr' }

------------------------------------------
--      Subsumption checking            --
------------------------------------------

subsCheck :: Sigma -> Sigma -> Tc ()
-- (subsCheck args off exp) checks that 
--     'off' is at least as polymorphic as 'args -> exp'

subsCheck sigma1 sigma2        -- Rule DEEP-SKOL
  = do { (_, skol_tvs, rho2) <- skolemise sigma2
       ; subsCheckRho sigma1 rho2
       ; esc_tvs <- getFreeTyVars [sigma1,sigma2]
       ; let bad_tvs = filter (`elem` esc_tvs) skol_tvs
       ; check (null bad_tvs)
               (vcat [text "Subsumption check failed:",
                      nest 2 (ppr sigma1),
                      text "is not as polymorphic as",
                      nest 2 (ppr sigma2)])
    }

subsCheckRho :: Sigma -> Rho -> Tc ()
-- Invariant: the second argument is in weak-prenex form

subsCheckRho sigma1@(ForAll _ _) rho2	 -- Rule SPEC
  = do { rho1 <- instantiate sigma1
       ; subsCheckRho rho1 rho2 }

subsCheckRho rho1 (TAp (TAp (TyCon FnT) a2) r2) -- Rule FUN
  = do { (a1,r1) <- unifyFun rho1; subsCheckFun a1 r1 a2 r2 }

subsCheckRho (TAp (TAp (TyCon FnT) a1) r1) rho2 -- Rule FUN
  = do { (a2,r2) <- unifyFun rho2; subsCheckFun a1 r1 a2 r2 }

subsCheckRho tau1 tau2                   -- Rule MONO
  = unify tau1 tau2    -- Revert to ordinary unification

subsCheckFun :: Sigma -> Rho -> Sigma -> Rho -> Tc ()
subsCheckFun a1 r1 a2 r2 
  = do { subsCheck a2 a1 ; subsCheckRho r1 r2 }

instSigma :: Sigma -> Expected Rho -> Tc Sigma
-- Invariant: if the second argument is (Check rho),
-- 	      then rho is in weak-prenex form
instSigma t1 (Check t2) = do { subsCheckRho t1 t2
                             ; return t2 }
instSigma t1 (Infer r)  = do { t1' <- instantiate t1
                             ; writeTcRef r t1'
                             ; return t1' }
\end{code}
