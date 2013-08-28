The Main module provides a small test harness for the type inference
engine.   You say

	ghci Main.lhs

Then, to the prompt you can type

	tcs "\\x . x"

to type-check a string, or 

	tcf "foo.test"

to type-check the contents of a file (which should be an expression)



\begin{code}
module Main where

import TcTerm
import TcMonad
import BasicTypes
import Parser
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec

import System.IO (hPutStrLn, stderr)
import System.Environment (getArgs)
import System.Exit (exitWith, ExitCode(..))

main :: IO ()
main = do args <- getArgs
          case args of
              [] -> getContents >>= tcs
              [f] -> tcf f
              _ -> do hPutStrLn stderr "Usage: foo [ FILE ]"
                      exitWith (ExitFailure 1)

-------------------------------------
--	tcs type-checks an expression passed directly as a string
--	ghci> tcs "\\x. x"

tcs :: String -> IO ()	-- Strings
tcs s = tc_help (parseString s)

s1, s2, s3, s4, s5, s6, s7 :: String

s1 = "\\x. \\y. x"	-- A tiny example

s2 = "let add = (\\x. \\y. x) :: forall a. a -> a -> a in \
    \ let id  = (\\x. x) :: forall a. a -> a in \
    \ add id id"
     
s3 = "\\x. if x (Some 0) None"

s4 = "let add = (\\x. \\y. x)  :: forall a b. a -> b -> a in \
    \ let id  = (\\x. x) in \
    \ let f = (add id id) in \
    \ f 1"
     
s5 = "let id  = (\\x. x) in \
    \ id 1"
     
s6 = "let f = (\\x. \\y. x) :: forall a b. a -> a -> a in \
    \ let g = (\\x. \\z. x z z) :: forall c. (forall p q. p -> q -> p) -> c -> c in \
    \ g f"
    
s7 = "let id  = (\\x. x) :: forall a. a -> a in \
    \ Pair (id True) (id 0)"
    
s8 = "let thing = \\x. \\y. Pair (check x) (check y) in \
    \ thing 0"
    
    -- should be Plus Int a => or similar
s9 = "let thing = \\x. \\y. plus 0 y in \
    \ thing"

-------------------------------------
--	tcf type-checks an expression in a file
--	ghci> tcs "foo.test"

tcf :: String -> IO ()	-- Files
tcf f = tc_help (parseFile f)



-------------------------------------
--	The initial type environment. 
--	You can extend this as you like

tyvarA, tyvarB :: TyVar
tyvarA = BoundTv "a"
tyvarB = BoundTv "B"

initTypeEnv :: [(Name,Sigma)]
initTypeEnv
      = [ ("+",    intType --> intType --> intType)
	, ("if",    ForAll [tyvarA] (boolType --> TyVar tyvarA --> TyVar tyvarA --> TyVar tyvarA))
	, ("check", ForAll [tyvarA] (PredTy ["Checkable"] (TyVar tyvarA) --> boolType))
	, ("plus",  ForAll [tyvarA, tyvarB] (PredTy ["Plus"] (TyVar tyvarA) --> PredTy ["Plus"] (TyVar tyvarB) --> PredTy ["Plus"] (TyVar tyvarA)))
	, ("True",  boolType)
	, ("False", boolType)
        , ("Some",  ForAll [tyvarA] (TyVar tyvarA --> TAp optType (TyVar tyvarA)))
        , ("Pair",  ForAll [tyvarA, tyvarB] (TyVar tyvarA --> TyVar tyvarB --> pair (TyVar tyvarA) (TyVar tyvarB)))
        , ("None",  ForAll [tyvarA] (TAp optType (TyVar tyvarA)))
	]

-------------------------------------
--	From here down is helper stuff

debugSubst :: Tc a -> Tc (Subst, a)
debugSubst tc = do { x <- tc
                   ; s <- getSubst
                   ; return (s, x) }

tc_help :: IO (Maybe (Term Name)) -> IO ()
tc_help get_term
  = do  { mb_e <- get_term
	; case mb_e of {
	    Nothing -> return () ;
	    Just e  -> do {
	  res <- runTc initTypeEnv (debugSubst (typecheck e))
	; case res of
		Left err -> putStrLn (docToString err)
		Right (s, (ty, e')) -> putStrLn $ 
                        (show e') ++ "\n\n------\n\n" ++
                        (show s) ++ "\n\n" ++ 
                        (docToString (sep [pprParendTerm e, nest 2 (dcolon <+> ppr ty)]))
   }}}


parseFile :: String -> IO (Maybe (Term Name))
parseFile filename
  = do { r <- parseFromFile parseTerm filename
       ; case r of
	   Left err -> do { putStrLn ("Parse error: " ++ show err) 
			  ; return Nothing }
	   Right ans -> return (Just ans) }

parseString :: String -> IO (Maybe (Term Name))
parseString str
  = do { let r = parse parseTerm "<interactive>" str
       ; case r of
	   Left err -> do { putStrLn ("Parse error: " ++ show err) 
			  ; return Nothing }
	   Right ans -> return (Just ans) }
\end{code}
