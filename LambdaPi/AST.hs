module LambdaPi.AST where

import Common

data CTerm_
   =  Inf_  ITerm_
   |  Lam_  CTerm_
   |  Zero_
   |  Succ_ CTerm_
   |  Nil_ CTerm_
   |  Cons_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Refl_ CTerm_ CTerm_
   |  FZero_ CTerm_
   |  FSucc_ CTerm_ CTerm_
  deriving (Show, Eq)
data ITerm_
   =  Ann_ CTerm_ CTerm_
   |  Star_
   |  Pi_ CTerm_ CTerm_
   |  Bound_  Int
   |  Free_  Name
   |  ITerm_ :$: CTerm_
   |  Nat_
   |  NatElim_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Vec_ CTerm_ CTerm_
   |  VecElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Eq_ CTerm_ CTerm_ CTerm_
   |  EqElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
   |  Fin_ CTerm_
   |  FinElim_ CTerm_ CTerm_ CTerm_ CTerm_ CTerm_
  deriving (Show, Eq)

data Value_
   =  VLam_  (Value_ -> Value_)
   |  VStar_
   |  VPi_ Value_ (Value_ -> Value_)
   |  VNeutral_ Neutral_
   |  VNat_
   |  VZero_
   |  VSucc_ Value_
   |  VNil_ Value_
   |  VCons_ Value_ Value_ Value_ Value_
   |  VVec_ Value_ Value_
   |  VEq_ Value_ Value_ Value_
   |  VRefl_ Value_ Value_
   |  VFZero_ Value_
   |  VFSucc_ Value_ Value_
   |  VFin_ Value_
data Neutral_
   =  NFree_  Name
   |  NApp_  Neutral_ Value_
   |  NNatElim_ Value_ Value_ Value_ Neutral_
   |  NVecElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
   |  NEqElim_ Value_ Value_ Value_ Value_ Value_ Neutral_
   |  NFinElim_ Value_ Value_ Value_ Value_ Neutral_
type Env_ = [Value_]
type Type_     =  Value_  
type Context_    =  [(Name, Type_)] 


vapp_ :: Value_ -> Value_ -> Value_
vapp_ (VLam_ f)      v  =  f v
vapp_ (VNeutral_ n)  v  =  VNeutral_ (NApp_ n v)
 
vfree_ :: Name -> Value_
vfree_ n = VNeutral_ (NFree_ n)