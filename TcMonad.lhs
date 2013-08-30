\begin{code}
module TcMonad(
        Tc,     -- The monad type constructor
        runTc, ErrMsg, lift, check,

        -- Environment manipulation
        extendVarEnv, lookupVar, 
        getEnvTypes, getFreeTyVars, getMetaTyVars,

        -- Types and unification
        newTyVarTy, 
        instantiate, skolemise, zonkType, quantify,
        unify, unifyFun,

        -- Ref cells
        newTcRef, readTcRef, writeTcRef,
        
        -- Substitutions
        Subst,
        getSubst,
        
        zonkTerm
        
    ) where

import BasicTypes
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ
import Data.IORef
import Data.List( nub, (\\) )

------------------------------------------
--      The monad itself                --
------------------------------------------

type Subst = Map.Map MetaTv Tau

data TcEnv 
  = TcEnv { uniqs   :: IORef Uniq,          -- Unique supply
            var_env :: Map.Map Name (Qual Sigma),  -- Type environment for term variables
            substs  :: IORef Subst }        -- Substitutions

newtype Tc a = Tc (TcEnv -> IO (Either ErrMsg a))
unTc :: Tc a ->   (TcEnv -> IO (Either ErrMsg a))
unTc (Tc a)  = a

type ErrMsg = Doc

instance Monad Tc where
   return x = Tc (\_env -> return (Right x))
   fail err = Tc (\_env -> return (Left (text err)))
   m >>= k  = Tc (\env -> do { r1 <- unTc m env
                              ; case r1 of
                                  Left err -> return (Left err)
                                  Right v  -> unTc (k v) env })

failTc :: Doc -> Tc a   -- Fail unconditionally
failTc d = fail (docToString d)

check :: Bool -> Doc -> Tc ()
check True  _ = return ()
check False d = failTc d

runTc :: [(Name, Qual Sigma)] -> Tc a -> IO (Either ErrMsg a)
-- Run type-check, given an initial environment
runTc binds (Tc tc)
  = do { uref <- newIORef 0
       ; sref <- newIORef Map.empty
       ; let { env = TcEnv { uniqs = uref, 
                             var_env = Map.fromList binds,
                             substs = sref } }
       ; tc env }
    
lift :: IO a -> Tc a
-- Lift a state transformer action into the typechecker monad
-- ignores the environment and always succeeds
lift st = Tc (\_env -> do { r <- st; return (Right r) })

newTcRef :: a -> Tc (IORef a)
newTcRef v = lift (newIORef v)

readTcRef :: IORef a -> Tc a
readTcRef r = lift (readIORef r)

writeTcRef :: IORef a -> a -> Tc ()
writeTcRef r v = lift (writeIORef r v)


--------------------------------------------------
--      Dealing with the type environment       --
--------------------------------------------------

extendVarEnv :: Name -> Qual Sigma -> Tc a -> Tc a
extendVarEnv var ty (Tc m) 
  = Tc (\env -> m (extend env))
  where
    extend env = env { var_env = Map.insert var ty (var_env env) }

getEnv :: Tc (Map.Map Name (Qual Sigma))
getEnv = Tc (\ env -> return (Right (var_env env)))

lookupVar :: Name -> Tc (Qual Sigma)    -- May fail
lookupVar n = do { env <- getEnv
                 ; case Map.lookup n env of
                     Just ty -> return ty
                     Nothing -> failTc (text "Not in scope:" <+> quotes (pprName n)) }
                     
------------------------------------------
--      Substitutions                   --
------------------------------------------

getSubst :: Tc Subst
getSubst = Tc (\ (TcEnv {substs = ref}) ->
           do { s <- readIORef ref
              ; return (Right s) })
              
applySubst :: Subst -> Tau -> Tau     
applySubst s (MetaTv m) = 
  case (Map.lookup m s) of
    Just t -> t
    Nothing -> MetaTv m
applySubst s t = t

--------------------------------------------------
--      Creating, reading, writing MetaTvs        --
--------------------------------------------------

newTyVarTy :: Tc Tau
newTyVarTy = do { tv <- newMetaTyVar
                ; return (MetaTv tv) }

newMetaTyVar :: Tc MetaTv
newMetaTyVar = do { uniq <- newUnique 
                  ; return (Meta uniq) }

newSkolemTyVar :: TyVar -> Tc TyVar
newSkolemTyVar tv = do { uniq <- newUnique 
                       ; return (SkolemTv (tyVarName tv) uniq) }


readTv  :: MetaTv -> Tc (Maybe Tau)
readTv  m = do { s <- getSubst
               ; return (Map.lookup m s) }
     
writeTv :: MetaTv -> Tau -> Tc ()
writeTv m ty = Tc (\ (TcEnv {substs = ref}) ->
               do { s <- readIORef ref
                  ; let s1 = Map.map (applySubst s) s
                  ; writeIORef ref (Map.insert m ty s1)
                  ; return (Right ()) })

newUnique :: Tc Uniq
newUnique = Tc (\ (TcEnv {uniqs = ref}) ->
            do { uniq <- readIORef ref ;
               ; writeIORef ref (uniq + 1)
               ; return (Right uniq) })


------------------------------------------
--      Instantiation                   --
------------------------------------------

instantiate :: Sigma -> Tc Rho
-- Instantiate the topmost for-alls of the argument type
-- with flexible type variables
instantiate (ForAll tvs ty) 
  = do { tvs' <- mapM (\_ -> newMetaTyVar) tvs
       ; return (substTy tvs (map MetaTv tvs') ty) }
instantiate ty
  = return ty

  
class Skolemise t where
  skolemise :: t -> Tc ([TyVar], [TyVar], t)
  
instance Skolemise Type where
  skolemise (ForAll tvs1 ty)	-- Rule PRPOLY
    = do { sks1 <- mapM newSkolemTyVar tvs1
         ; (tvs2, sks2, ty') <- skolemise (substTy tvs1 (map TyVar sks1) ty)
         ; return (tvs1 ++ tvs2, sks1 ++ sks2, ty') }
  skolemise (TAp (TAp (TyCon FnT) arg_ty) res_ty)	-- Rule PRFUN
    = do { (tvs, sks, res_ty') <- skolemise res_ty
         ; return (tvs, sks, arg_ty --> res_ty') }
  skolemise ty 			-- Rule PRMONO
    = return ([], [], ty)
    
instance (Skolemise t) => Skolemise (Qual t) where
  skolemise (Qual ps t)
    = do { (tvs, sks, t') <- skolemise t
         ; let ps' = substPred tvs (map TyVar sks) `map` ps
         ; return (tvs, sks, Qual ps' t') }

------------------------------------------
--      Quantification                  --
------------------------------------------

quantify :: [MetaTv] -> Rho -> Tc Sigma
-- Quantify over the specified type variables (all flexible)
quantify tvs ty
  = do { mapM_ bind (tvs `zip` new_bndrs)   -- 'bind' is just a cunning way 
       ; ty' <- zonkType ty                 -- of doing the substitution
       ; return (ForAll new_bndrs ty') }
  where
    used_bndrs = tyVarBndrs ty  -- Avoid quantified type variables in use
    new_bndrs  = take (length tvs) (allBinders \\ used_bndrs)
    bind (tv, name) = writeTv tv (TyVar name)

allBinders :: [TyVar]    -- a,b,..z, a1, b1,... z1, a2, b2,... 
allBinders = [ BoundTv [x]          | x <- ['a'..'z'] ] ++
             [ BoundTv (x : show i) | i <- [1 :: Integer ..], x <- ['a'..'z']]

------------------------------------------
--      Getting the free tyvars         --
------------------------------------------

getEnvTypes :: Tc [Qual Type]
  -- Get the types mentioned in the environment
getEnvTypes = do { env <- getEnv; 
	         ; return (Map.elems env) }

getMetaTyVars :: [Type] -> Tc [MetaTv]
-- This function takes account of zonking, and returns a set
-- (no duplicates) of unbound meta-type variables
getMetaTyVars tys = do { tys' <- mapM zonkType tys
		    ; return (metaTvs tys') }

getFreeTyVars :: [Type] -> Tc [TyVar]
-- This function takes account of zonking, and returns a set
-- (no duplicates) of free type variables
getFreeTyVars tys = do { tys' <- mapM zonkType tys
		       ; return (freeTyVars tys') }

------------------------------------------
--      Zonking                         --
-- Eliminate any substitutions in the type
------------------------------------------

zonkType :: Type -> Tc Type
zonkType (ForAll ns ty) = do { ty' <- zonkType ty 
                             ; return (ForAll ns ty') }
zonkType (TAp arg res)  = do { arg' <- zonkType arg 
                             ; res' <- zonkType res
                             ; return (TAp arg' res') }
zonkType (TyCon tc)     = return (TyCon tc)
zonkType (TyVar n)      = return (TyVar n)
zonkType (MetaTv tv)    -- A mutable type variable
  = do { mb_ty <- readTv tv
       ; case mb_ty of
           Nothing -> return (MetaTv tv)
           Just ty -> do { ty' <- zonkType ty
                         ; writeTv tv ty'       -- "Short out" multiple hops
                         ; return ty' } }
                         
zonkTerm :: Term Id -> Tc (Term Id)

zonkTerm (Var (Id i t))
  = do { t' <- zonkType t
       ; return (Var (Id i t')) }
       
zonkTerm (Lit i) = return (Lit i)
       
zonkTerm (App x y)
  = do { x' <- zonkTerm x
       ; y' <- zonkTerm y
       ; return (App x' y') }
       
zonkTerm (Lam (Id i t) expr)
  = do { t' <- zonkType t
       ; expr' <- zonkTerm expr
       ; return (Lam (Id i t') expr') }
       
zonkTerm (ALam (Id i t1) t2 expr)
  = do { t1' <- zonkType t1
       ; expr' <- zonkTerm expr
       ; return (ALam (Id i t1') t2 expr') }
       
zonkTerm (Let (Id i t) expr1 expr2)
  = do { t' <- zonkType t
       ; expr1' <- zonkTerm expr1
       ; expr2' <- zonkTerm expr2
       ; return (Let (Id i t') expr1' expr2') }
       
zonkTerm (Ann expr t)
  = do { expr' <- zonkTerm expr
       ; return (Ann expr' t) }

------------------------------------------
--      Unification                     --
------------------------------------------

unify :: Tau -> Tau -> Tc ()

unify ty1 ty2 
  | badType ty1 || badType ty2  -- Compiler error
  = failTc (text "Panic! Unexpected types in unification:" <+> 
            vcat [ppr ty1, ppr ty2])

unify (TyVar tv1)  (TyVar tv2)  | tv1 == tv2 = return ()
unify (MetaTv tv1) (MetaTv tv2) | tv1 == tv2 = return ()

unify (MetaTv tv) ty = unifyVar tv ty
unify ty (MetaTv tv) = unifyVar tv ty

unify (TAp arg1 res1)
      (TAp arg2 res2)
  = do { unify arg1 arg2; unify res1 res2 }

unify (TyCon tc1) (TyCon tc2) 
  | tc1 == tc2 
  = return ()

unify ty1 ty2 = failTc (text "Cannot unify types:" <+> vcat [ppr ty1, ppr ty2])

-----------------------------------------
unifyVar :: MetaTv -> Tau -> Tc ()
-- Invariant: tv1 is a flexible type variable
unifyVar tv1 ty2        -- Check whether tv1 is bound
  = do { mb_ty1 <- readTv tv1   
       ; case mb_ty1 of
           Just ty1 -> unify ty1 ty2
           Nothing  -> unifyUnboundVar tv1 ty2 }

unifyUnboundVar :: MetaTv -> Tau -> Tc ()
-- Invariant: the flexible type variable tv1 is not bound
unifyUnboundVar tv1 ty2@(MetaTv tv2)
  = do { -- We know that tv1 /= tv2 (else the 
         -- top case in unify would catch it)
         mb_ty2 <- readTv tv2
       ; case mb_ty2 of
           Just ty2' -> unify (MetaTv tv1) ty2'
           Nothing  -> writeTv tv1 ty2 } 

unifyUnboundVar tv1 ty2
  = do { tvs2 <- getMetaTyVars [ty2]
       ; if tv1 `elem` tvs2 then
            occursCheckErr tv1 ty2
         else
            writeTv tv1 ty2 }

-----------------------------------------
unifyFun :: Rho -> Tc (Sigma, Rho)
--      (arg,res) <- unifyFunTy fun
-- unifies 'fun' with '(arg -> res)'
unifyFun (TAp (TAp (TyCon FnT) arg) res) = return (arg,res)
unifyFun tau           = do { arg_ty <- newTyVarTy
                            ; res_ty <- newTyVarTy
                            ; unify tau (arg_ty --> res_ty)
                            ; return (arg_ty, res_ty) }

-----------------------------------------
occursCheckErr :: MetaTv -> Tau -> Tc ()
-- Raise an occurs-check error
occursCheckErr tv ty
  = failTc (text "Occurs check for" <+> quotes (ppr tv) <+> 
            text "in:" <+> ppr ty)

badType :: Tau -> Bool
-- Tells which types should never be encountered during unification
badType (TyVar (BoundTv _)) = True
badType _         	    = False
\end{code}
