module Main where

import Prelude hiding (print)
import Control.Monad.Error
import Data.List
import Data.Char
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import System.Console.Readline
import System.IO hiding (print)
import System.IO.Error

import LPH
import Parser
import ParserLP
import Printer
import PrinterLP
import TypingLP

readevalprint :: Interpreter i c v t tinf inf -> State v inf -> IO ()
readevalprint int state@(inter, out, ve, te) =
  let rec int state =
        do
          x <- catchIOError
                 (if inter
                  then readline (iprompt int) 
                  else fmap Just getLine)
                 (\_ -> return Nothing)
          case x of
            Nothing   ->  return ()
            Just ""   ->  rec int state
            Just x    ->
              do
                when inter (addHistory x)
                c  <- interpretCommand x
                state' <- handleCommand int state c
                maybe (return ()) (rec int) state'
  in
    do
      --  welcome
      when inter $ putStrLn ("Interpreter for " ++ iname int ++ ".\n" ++
                             "Type :? for help.")
      --  enter loop
      rec int state
data Command = TypeOf String
             | Compile CompileForm
             | Browse
             | Quit
             | Help
             | Noop
 
data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

--type NameEnv v = [(Name, v)]
type Ctx inf = [(Name, inf)]
type State v inf = (Bool, String, NameEnv v, Ctx inf)

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":type"]        "<expr>"  TypeOf         "print type of expression",
       Cmd [":browse"]      ""        (const Browse) "browse names in scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "load program from file",
       Cmd [":quit"]        ""        (const Quit)   "exit interpreter",
       Cmd [":help",":?"]   ""        (const Help)   "display this list of commands" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "List of commands:  Any command may be abbreviated to :c where\n" ++
     "c is the first character in the full name.\n\n" ++
     "<expr>                  evaluate expression\n" ++
     "let <var> = <expr>      define variable\n" ++
     "assume <var> :: <expr>  assume variable\n\n"
     ++
     unlines (map (\ (Cmd cs a _ d) -> let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) cs))
                                       in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)


interpretCommand :: String -> IO Command
interpretCommand x
  =  if isPrefixOf ":" x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             x   ->  do  putStrLn ("Ambiguous command, could be " ++ concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop
     else
       return (Compile (CompileInteractive x))

handleCommand :: Interpreter i c v t tinf inf -> State v inf -> Command -> IO (Maybe (State v inf))
handleCommand int state@(inter, out, ve, te) cmd
  =  case cmd of
       Quit   ->  when (not inter) (putStrLn "!@#$^&*") >> return Nothing
       Noop   ->  return (Just state)
       Help   ->  putStr (helpTxt commands) >> return (Just state)
       TypeOf x ->
                  do  x <- parseIO "<interactive>" (iiparse int) x
                      t <- maybe (return Nothing) (iinfer int ve te) x
                      maybe (return ()) (\u -> putStrLn (render (itprint int u))) t
                      return (Just state)
       Browse ->  do  putStr (unlines [ s | Global s <- reverse (nub (map fst te)) ])
                      return (Just state)
       Compile c ->
                  do  state <- case c of
                                 CompileInteractive s -> compilePhrase int state s
                                 CompileFile f        -> compileFile int state f
                      return (Just state)
 
compileFile :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
compileFile int state@(inter, out, ve, te) f =
  do
    x <- readFile f
    stmts <- parseIO f (many (isparse int)) x
    maybe (return state) (foldM (handleStmt int) state) stmts

compilePhrase :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
compilePhrase int state@(inter, out, ve, te) x =
  do
    x <- parseIO "<interactive>" (isparse int) x
    maybe (return state) (handleStmt int state) x

data Interpreter i c v t tinf inf =
  I { iname :: String,
      iprompt :: String,
      iitype :: NameEnv v -> Ctx inf -> i -> Result t,
      iquote :: v -> c,
      ieval  :: NameEnv v -> i -> v,
      ihastype :: t -> inf,
      icprint :: c -> Doc,
      itprint :: t -> Doc,
      iiparse :: CharParser () i,
      isparse :: CharParser () (Stmt i tinf),
      iassume :: State v inf -> (String, tinf) -> IO (State v inf) }
 
st :: Interpreter ITerm CTerm Value Type Info Info
st = I { iname = "the simply typed lambda calculus",
         iprompt = "ST> ",
         iitype = \ v c -> iType 0 c,
         iquote = quote0,
         ieval  = \ e x -> iEval x (e, []),
         ihastype = HasType,
         icprint = cPrint 0 0,
         itprint = tPrint 0,
         iiparse = parseITerm 0 [],
         isparse = parseStmt [],
         iassume = \ s (x, t) -> stassume s x t }
 
lp :: Interpreter ITerm_ CTerm_ Value_ Value_ CTerm_ Value_
lp = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = \ v c -> iType_ 0 (v, c),
         iquote = quote0_,
         ieval = \ e x -> iEval_ x (e, []),
         ihastype = id,
         icprint = cPrint_ 0 0,
         itprint = cPrint_ 0 0 . quote0_,
         iiparse = parseITerm_ 0 [],
         isparse = parseStmt_ [],
         iassume = \ s (x, t) -> lpassume s x t }
 
lpte :: Ctx Value_
lpte =      [(Global "Zero", VNat_),
             (Global "Succ", VPi_ VNat_ (\ _ -> VNat_)),
             (Global "Nat", VStar_),
             (Global "natElim", VPi_ (VPi_ VNat_ (\ _ -> VStar_)) (\ m ->
                               VPi_ (m `vapp_` VZero_) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ k -> VPi_ (m `vapp_` k) (\ _ -> (m `vapp_` (VSucc_ k))))) ( \ _ ->
                               VPi_ VNat_ (\ n -> m `vapp_` n))))),
             (Global "Nil", VPi_ VStar_ (\ a -> VVec_ a VZero_)),
             (Global "Cons", VPi_ VStar_ (\ a ->
                            VPi_ VNat_ (\ n ->
                            VPi_ a (\ _ -> VPi_ (VVec_ a n) (\ _ -> VVec_ a (VSucc_ n)))))),
             (Global "Vec", VPi_ VStar_ (\ _ -> VPi_ VNat_ (\ _ -> VStar_))),
             (Global "vecElim", VPi_ VStar_ (\ a ->
                               VPi_ (VPi_ VNat_ (\ n -> VPi_ (VVec_ a n) (\ _ -> VStar_))) (\ m ->
                               VPi_ (m `vapp_` VZero_ `vapp_` (VNil_ a)) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ n ->
                                     VPi_ a (\ x ->
                                     VPi_ (VVec_ a n) (\ xs ->
                                     VPi_ (m `vapp_` n `vapp_` xs) (\ _ ->
                                     m `vapp_` VSucc_ n `vapp_` VCons_ a n x xs))))) (\ _ ->
                               VPi_ VNat_ (\ n ->
                               VPi_ (VVec_ a n) (\ xs -> m `vapp_` n `vapp_` xs))))))),
             (Global "Refl", VPi_ VStar_ (\ a -> VPi_ a (\ x ->
                            VEq_ a x x))),
             (Global "Eq", VPi_ VStar_ (\ a -> VPi_ a (\ x -> VPi_ a (\ y -> VStar_)))),
             (Global "eqElim", VPi_ VStar_ (\ a ->
                              VPi_ (VPi_ a (\ x -> VPi_ a (\ y -> VPi_ (VEq_ a x y) (\ _ -> VStar_)))) (\ m ->
                              VPi_ (VPi_ a (\ x -> m `vapp_` x `vapp_` x `vapp_` VRefl_ a x)) (\ _ ->
                              VPi_ a (\ x -> VPi_ a (\ y ->
                              VPi_ (VEq_ a x y) (\ eq ->
                              m `vapp_` x `vapp_` y `vapp_` eq))))))),
             (Global "FZero", VPi_ VNat_ (\ n -> VFin_ (VSucc_ n))),
             (Global "FSucc", VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f ->
                             VFin_ (VSucc_ n)))),
             (Global "Fin", VPi_ VNat_ (\ n -> VStar_)),
             (Global "finElim", VPi_ (VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ _ -> VStar_))) (\ m ->
                               VPi_ (VPi_ VNat_ (\ n -> m `vapp_` (VSucc_ n) `vapp_` (VFZero_ n))) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f -> VPi_ (m `vapp_` n `vapp_` f) (\ _ -> m `vapp_` (VSucc_ n) `vapp_` (VFSucc_ n f))))) (\ _ ->
                               VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f ->
                               m `vapp_` n `vapp_` f))))))]
 
lpve :: Ctx Value_
lpve =      [(Global "Zero", VZero_),
             (Global "Succ", VLam_ (\ n -> VSucc_ n)),
             (Global "Nat", VNat_),
             (Global "natElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (NatElim_ (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))) ([], [])),
             (Global "Nil", VLam_ (\ a -> VNil_ a)),
             (Global "Cons", VLam_ (\ a -> VLam_ (\ n -> VLam_ (\ x -> VLam_ (\ xs ->
                            VCons_ a n x xs))))),
             (Global "Vec", VLam_ (\ a -> VLam_ (\ n -> VVec_ a n))),
             (Global "vecElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (VecElim_ (Inf_ (Bound_ 5)) (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))))) ([],[])),
             (Global "Refl", VLam_ (\ a -> VLam_ (\ x -> VRefl_ a x))),
             (Global "Eq", VLam_ (\ a -> VLam_ (\ x -> VLam_ (\ y -> VEq_ a x y)))),
             (Global "eqElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (EqElim_ (Inf_ (Bound_ 5)) (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))))) ([],[])),
             (Global "FZero", VLam_ (\ n -> VFZero_ n)),
             (Global "FSucc", VLam_ (\ n -> VLam_ (\ f -> VFSucc_ n f))),
             (Global "Fin", VLam_ (\ n -> VFin_ n)),
             (Global "finElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (FinElim_ (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0))))))))) ([],[]))]
repLP :: Bool -> IO ()
repLP b = readevalprint lp (b, [], lpve, lpte)
 
repST :: Bool -> IO ()
repST b = readevalprint st (b, [], [], [])
 
iinfer int d g t =
  case iitype int d g t of
    Left e -> putStrLn e >> return Nothing
    Right v -> return (Just v)
 
handleStmt :: Interpreter i c v t tinf inf
              -> State v inf -> Stmt i tinf -> IO (State v inf)
handleStmt int state@(inter, out, ve, te) stmt =
  do
    case stmt of
        Assume ass -> foldM (iassume int) state ass 
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> putStrLn x >> return state
        Out f      -> return (inter, f, ve, te)
  where
    --  checkEval :: String -> i -> IO (State v inf)
    checkEval i t =
      check int state i t
        (\ (y, v) -> do
                       --  ugly, but we have limited space in the paper
                       --  usually, you'd want to have the bound identifier *and*
                       --  the result of evaluation
                       let outtext = if i == it then render (icprint int (iquote int v) <> text " :: " <> itprint int y)
                                                else render (text i <> text " :: " <> itprint int y)
                       putStrLn outtext
                       unless (null out) (writeFile out (process outtext)))
        (\ (y, v) -> (inter, "", (Global i, v) : ve, (Global i, ihastype int y) : te))
 
check :: Interpreter i c v t tinf inf -> State v inf -> String -> i
         -> ((t, v) -> IO ()) -> ((t, v) -> State v inf) -> IO (State v inf)
check int state@(inter, out, ve, te) i t kp k =
                do
                  --  typecheck and evaluate
                  x <- iinfer int ve te t
                  case x of
                    Nothing  ->
                      do
                        --  putStrLn "type error"
                        return state
                    Just y   ->
                      do
                        let v = ieval int ve t
                        kp (y, v)
                        return (k (y, v))
 
stassume state@(inter, out, ve, te) x t = return (inter, out, ve, (Global x, t) : te)
lpassume state@(inter, out, ve, te) x t =
  check lp state x (Ann_ t (Inf_ Star_))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
        (\ (y, v) -> (inter, out, ve, (Global x, v) : te))


it = "it"
process :: String -> String
process = unlines . map (\ x -> "< " ++ x) . lines
main :: IO ()
main = repLP True
