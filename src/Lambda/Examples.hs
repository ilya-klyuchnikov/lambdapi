module Lambda.Examples where

import Common
import Lambda.AST
import Lambda.Eval
import Lambda.Check
import Lambda.Quote

id'      =  Lam (Inf (Bound 0))
const'   =  Lam (Lam (Inf (Bound 1)))

tfree a  =  TFree (Global a)
free x   =  Inf (Free (Global x))
 
term1    =  Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y" 
term2    =  (Ann const' (Fun  (Fun (tfree "b") (tfree "b"))
                             (Fun  (tfree "a")
                                   (Fun (tfree "b") (tfree "b"))))
            :@: id') :@: (free "y")
 
env1     =  [  (Global "y", HasType (tfree "a")),
               (Global "a", HasKind Star)]
env2     =  [(Global "b", HasKind Star)] ++ env1

test_eval1 =  quote0 (iEval term1 ([],[]))
 
test_eval2 =  quote0 (iEval term2 ([],[]))
test_type1 =  iType0 env1 term1
test_type2 =  iType0 env2 term2