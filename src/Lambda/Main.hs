module Lambda.Main where

import Common
import REPL

import Lambda.AST
import Lambda.Eval
import Lambda.Check
import Lambda.Quote
import Lambda.Parser
import Lambda.Printer

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

stassume state@(inter, out, ve, te) x t = return (inter, out, ve, (Global x, t) : te)

repST :: Bool -> IO ()
repST b = readevalprint st (b, [], [], [])

main :: IO ()
main = repST True
