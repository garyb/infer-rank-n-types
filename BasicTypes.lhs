\begin{code}
module BasicTypes where

-- This module defines the basic types used by the type checker
-- Everything defined in here is exported

import Text.PrettyPrint.HughesPJ
import Data.IORef
import Data.List( nub )
import Data.Maybe( fromMaybe )

infixr 4 -->     -- The arrow type constructor
infixl 4 `App`   -- Application

-----------------------------------
--      Ubiquitous types        -- 
-----------------------------------

type Name = String
data Id = Id Name Type

-----------------------------------
--      Expressions             -- 
-----------------------------------

data Term a = Var a                     -- x
            | Lit Int                   -- 3
            | App (Term a) (Term a)     -- f x
            | Lam a (Term a)            -- \ x -> x
            | ALam a Sigma (Term a)     -- \ x -> x
            | Let a (Term a) (Term a)   -- let x = f y in x+1
            | Ann (Term a) Sigma        -- (f x) :: Int

atomicTerm :: Term a -> Bool
atomicTerm (Var _) = True
atomicTerm (Lit _) = True
atomicTerm _       = False

-----------------------------------
--      Types                   -- 
-----------------------------------

type Sigma = Type
type Rho   = Type	-- No top-level ForAll
type Tau   = Type	-- No ForAlls anywhere

data Type = ForAll [TyVar] Rho	  -- Forall type
	  | TAp    Type Type      -- Type function application
	  | TyCon  TyCon      	  -- Type constants
	  | TyVar  TyVar      	  -- Always bound by a ForAll
	  | MetaTv MetaTv     	  -- A meta type variable
          
data TyVar
  = BoundTv String		-- A type variable bound by a ForAll

  | SkolemTv String Uniq	-- A skolem constant; the String is 
				-- just to improve error messages

data MetaTv = Meta Uniq  -- Can unify with any tau-type
            deriving( Ord, Eq, Show )

instance Eq TyVar where
  (BoundTv s1)    == (BoundTv s2)    = s1 == s2
  (SkolemTv _ u1) == (SkolemTv _ u2) = u1 == u2

type Uniq = Int

data TyCon = IntT | BoolT | FnT | OptionT | PairT
           deriving( Eq )

---------------------------------
--      Constructors

(-->) :: Sigma -> Sigma -> Sigma
arg --> res = TAp (TAp fnType arg) res

pair :: Sigma -> Sigma -> Sigma
pair x y = TAp (TAp pairType x) y

intType, boolType, fnType, optType :: Tau
intType  = TyCon IntT
boolType = TyCon BoolT
fnType   = TyCon FnT
optType  = TyCon OptionT
pairType = TyCon PairT

---------------------------------
--	Free and bound variables

metaTvs :: [Type] -> [MetaTv]
-- Get the MetaTvs from a type; no duplicates in result
metaTvs tys = foldr go [] tys
  where
    go (MetaTv tv)    acc
	| tv `elem` acc   = acc
	| otherwise	  = tv : acc
    go (TyVar _)      acc = acc
    go (TyCon _)      acc = acc
    go (TAp arg res)  acc = go arg (go res acc)
    go (ForAll _ ty)  acc = go ty acc	-- ForAll binds TyVars only

freeTyVars :: [Type] -> [TyVar]
-- Get the free TyVars from a type; no duplicates in result
freeTyVars tys = foldr (go []) [] tys
  where 
    go :: [TyVar]	-- Ignore occurrences of bound type variables
       -> Type		-- Type to look at
       -> [TyVar]	-- Accumulates result
       -> [TyVar]
    go bound (TyVar tv)      acc 
	| tv `elem` bound        = acc
	| tv `elem` acc		 = acc
	| otherwise		 = tv : acc
    go bound (MetaTv _)      acc = acc
    go bound (TyCon _)       acc = acc
    go bound (TAp arg res)   acc = go bound arg (go bound res acc)
    go bound (ForAll tvs ty) acc = go (tvs ++ bound) ty acc

tyVarBndrs :: Rho -> [TyVar]
-- Get all the binders used in ForAlls in the type, so that
-- when quantifying an outer for-all we can avoid these inner ones
tyVarBndrs ty = nub (bndrs ty)
  where
    bndrs (ForAll tvs body) = tvs ++ bndrs body
    bndrs (TAp arg res)     = bndrs arg ++ bndrs res
    bndrs _                 = []

tyVarName :: TyVar -> String
tyVarName (BoundTv n)    = n
tyVarName (SkolemTv n _) = n


---------------------------------
--      Substitution

type Env = [(TyVar, Tau)]

substTy :: [TyVar] -> [Type] -> Type -> Type
-- Replace the specified quantified type variables by
-- given meta type variables
-- No worries about capture, because the two kinds of type
-- variable are distinct
substTy tvs tys ty = subst_ty (tvs `zip` tys) ty

subst_ty :: Env -> Type -> Type
subst_ty env (TAp arg res)   = TAp (subst_ty env arg) (subst_ty env res)
subst_ty env (TyVar n)       = fromMaybe (TyVar n) (lookup n env)
subst_ty env (MetaTv tv)     = MetaTv tv
subst_ty env (TyCon tc)      = TyCon tc
subst_ty env (ForAll ns rho) = ForAll ns (subst_ty env' rho)
  where
    env' = [(n,ty') | (n,ty') <- env, not (n `elem` ns)]


-----------------------------------
--      Pretty printing class   -- 
-----------------------------------

class Outputable a where
  ppr :: a -> Doc
  
class OutputableName a where
  pprName :: a -> Doc

docToString :: Doc -> String
docToString = render

dcolon, dot :: Doc
dcolon = text "::"
dot    = char '.'

-------------- Pretty-printing terms ---------------------

instance (OutputableName a) => Outputable (Term a) where
   ppr (Var n)       = pprName n
   ppr (Lit i)       = int i
   ppr (App e1 e2)   = pprApp (App e1 e2)
   ppr (Lam v e)     = sep [char '\\' <> pprName v <> text ".", ppr e]
   ppr (ALam v t e)  = sep [char '\\' <> parens (pprName v <> dcolon <> ppr t)
                                      <> text ".", ppr e]
   ppr (Let v rhs b) = sep [text "let {", 
                            nest 2 (pprName v <+> equals <+> ppr rhs <+> char '}') ,
                            text "in",
                            ppr b]
   ppr (Ann e ty)    = pprParendTerm e <+> dcolon <+> pprParendType ty

instance (OutputableName a) => Show (Term a) where
   show t = docToString (ppr t)
   
instance (OutputableName a) => OutputableName [a] where
   pprName xs = hcat (map pprName xs)
   
instance OutputableName Char where
   pprName c = char c
   
instance OutputableName Id where
   pprName (Id s t) = parens $ pprName s <+> dcolon <+> ppr t

pprParendTerm :: (OutputableName a) => Term a -> Doc
pprParendTerm e | atomicTerm e = ppr e
                | otherwise    = parens (ppr e)

pprApp :: (OutputableName a) => Term a -> Doc
pprApp e = go e []
  where
    go (App e1 e2) es = go e1 (e2:es)
    go e' es           = pprParendTerm e' <+> sep (map pprParendTerm es)

-------------- Pretty-printing types ---------------------

instance Outputable Type where
   ppr ty = pprType topPrec ty

instance Outputable MetaTv where
   ppr (Meta u) = text "$" <> int u

instance Outputable TyVar where
   ppr (BoundTv n)    = text n
   ppr (SkolemTv n u) = text n <+> int u

instance Show Type where
   show t = docToString (ppr t)

type Precedence = Int
topPrec, arrPrec, tcPrec, atomicPrec :: Precedence
topPrec    = 0  -- Top-level precedence
arrPrec    = 1  -- Precedence of (a->b)
tcPrec     = 2  -- Precedence of (T a b)
atomicPrec = 3  -- Precedence of t

precType :: Type -> Precedence
precType (ForAll _ _) = topPrec
precType (TAp _ _)    = arrPrec
precType _            = atomicPrec   
        -- All the types are be atomic

pprParendType :: Type -> Doc
pprParendType ty = pprType tcPrec ty


pprType :: Precedence -> Type -> Doc
-- Print with parens if precedence arg > precedence of type itself
pprType p ty | p >= precType ty = parens (ppr_type ty)
             | otherwise        = ppr_type ty

ppr_type :: Type -> Doc         -- No parens
ppr_type (ForAll ns ty) = sep [text "forall" <+> 
                                  hsep (map ppr ns) <> dot, 
                               ppr ty]
ppr_type (TAp (TAp (TyCon FnT) arg) res) = pprType arrPrec arg <+> text "->" <+> pprType (arrPrec-1) res
ppr_type (TAp arg res)  = pprType (arrPrec-1) arg <+> pprType arrPrec res
ppr_type (TyCon tc)     = ppr_tc tc
ppr_type (TyVar n)      = ppr n
ppr_type (MetaTv tv)    = ppr tv

ppr_tc :: TyCon -> Doc
ppr_tc IntT    = text "Int"
ppr_tc BoolT   = text "Bool"
ppr_tc FnT     = text "->"
ppr_tc OptionT = text "Option"
ppr_tc PairT   = text "Pair"
\end{code}
