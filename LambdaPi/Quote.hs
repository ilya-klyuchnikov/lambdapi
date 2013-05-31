module LambdaPi.Quote where

import Common
import LambdaPi.AST

instance Show Value_ where
  show = show . quote0_

quote0_ :: Value_ -> CTerm_
quote0_ = quote_ 0

quote_ :: Int -> Value_ -> CTerm_
quote_ ii (VLam_ t)
  =     Lam_ (quote_ (ii + 1) (t (vfree_ (Quote ii))))

quote_ ii VStar_ = Inf_ Star_ 
quote_ ii (VPi_ v f)                                       
    =  Inf_ (Pi_ (quote_ ii v) (quote_ (ii + 1) (f (vfree_ (Quote ii)))))  
quote_ ii (VNeutral_ n)
  =     Inf_ (neutralQuote_ ii n)
quote_ ii VNat_       =  Inf_ Nat_
quote_ ii VZero_      =  Zero_
quote_ ii (VSucc_ n)  =  Succ_ (quote_ ii n)
quote_ ii (VVec_ a n)         =  Inf_ (Vec_ (quote_ ii a) (quote_ ii n))
quote_ ii (VNil_ a)           =  Nil_ (quote_ ii a)
quote_ ii (VCons_ a n x xs)   =  Cons_  (quote_ ii a) (quote_ ii n)
                                        (quote_ ii x) (quote_ ii xs)
quote_ ii (VEq_ a x y)  =  Inf_ (Eq_ (quote_ ii a) (quote_ ii x) (quote_ ii y))
quote_ ii (VRefl_ a x)  =  Refl_ (quote_ ii a) (quote_ ii x)
quote_ ii (VFin_ n)           =  Inf_ (Fin_ (quote_ ii n))
quote_ ii (VFZero_ n)         =  FZero_ (quote_ ii n)
quote_ ii (VFSucc_ n f)       =  FSucc_  (quote_ ii n) (quote_ ii f)
neutralQuote_ :: Int -> Neutral_ -> ITerm_
neutralQuote_ ii (NFree_ v)
   =  boundfree_ ii v
neutralQuote_ ii (NApp_ n v)
   =  neutralQuote_ ii n :$: quote_ ii v
neutralQuote_ ii (NNatElim_ m z s n)
   =  NatElim_ (quote_ ii m) (quote_ ii z) (quote_ ii s) (Inf_ (neutralQuote_ ii n))
neutralQuote_ ii (NVecElim_ a m mn mc n xs)
   =  VecElim_ (quote_ ii a) (quote_ ii m)
               (quote_ ii mn) (quote_ ii mc)
               (quote_ ii n) (Inf_ (neutralQuote_ ii xs))
neutralQuote_ ii (NEqElim_ a m mr x y eq)
   =  EqElim_  (quote_ ii a) (quote_ ii m) (quote_ ii mr)
               (quote_ ii x) (quote_ ii y)
               (Inf_ (neutralQuote_ ii eq))
neutralQuote_ ii (NFinElim_ m mz ms n f)
   =  FinElim_ (quote_ ii m)
               (quote_ ii mz) (quote_ ii ms)
               (quote_ ii n) (Inf_ (neutralQuote_ ii f))

boundfree_ :: Int -> Name -> ITerm_
boundfree_ ii (Quote k)     =  Bound_ ((ii - k - 1) `max` 0)
boundfree_ ii x             =  Free_ x