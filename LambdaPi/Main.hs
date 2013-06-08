module LambdaPi.Main where

import Common
import REPL

import LambdaPi.AST
import LambdaPi.Eval
import LambdaPi.Check
import LambdaPi.Quote
import LambdaPi.Parser
import LambdaPi.Printer

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
                              VPi_ (VPi_ a (\ x -> ((m `vapp_` x) `vapp_` x) `vapp_` VRefl_ a x)) (\ _ ->
                              VPi_ a (\ x -> VPi_ a (\ y ->
                              VPi_ (VEq_ a x y) (\ eq ->
                              ((m `vapp_` x) `vapp_` y) `vapp_` eq))))))),
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

lpassume state@(inter, out, ve, te) x t =
  -- x: String, t: CTerm
  check lp state x (Ann_ t (Inf_ Star_))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
        (\ (y, v) -> (inter, out, ve, (Global x, v) : te))

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

repLP :: Bool -> IO ()
repLP b = readevalprint lp (b, [], lpve, lpte)

main :: IO ()
main = repLP True
