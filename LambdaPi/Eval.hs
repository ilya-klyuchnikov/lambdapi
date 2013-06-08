module LambdaPi.Eval where

import Common
import LambdaPi.AST

cEval_ :: CTerm_ -> (NameEnv Value_,Env_) -> Value_
cEval_ (Inf_  ii)    d  =  iEval_ ii d
cEval_ (Lam_  c)     d  =  VLam_ (\ x -> cEval_ c (((\(e, d) -> (e,  (x : d))) d)))
cEval_ Zero_      d  = VZero_
cEval_ (Succ_ k)  d  = VSucc_ (cEval_ k d)
cEval_ (Nil_ a)          d  =  VNil_ (cEval_ a d)
cEval_ (Cons_ a n x xs)  d  =  VCons_  (cEval_ a d) (cEval_ n d)
                                       (cEval_ x d) (cEval_ xs d)
cEval_ (Refl_ a x)       d  =  VRefl_ (cEval_ a d) (cEval_ x d)
cEval_ (FZero_ n)    d  =  VFZero_ (cEval_ n d)
cEval_ (FSucc_ n f)  d  =  VFSucc_ (cEval_ n d) (cEval_ f d)

iEval_ :: ITerm_ -> (NameEnv Value_,Env_) -> Value_
iEval_ (Ann_  c _)     d  =  cEval_ c d
iEval_ Star_           d  =  VStar_   
iEval_ (Pi_ ty ty1)    d  =  VPi_ (cEval_ ty d) (\ x -> cEval_ ty1 (((\(e, d) -> (e,  (x : d))) d)))
iEval_ (Free_  x)      d  =  case lookup x (fst d) of Nothing ->  (vfree_ x); Just v -> v 
iEval_ (Bound_  ii)    d  =  (snd d) !! ii
iEval_ (i :$: c)       d  =  vapp_ (iEval_ i d) (cEval_ c d)
iEval_ Nat_                  d  =  VNat_
iEval_ (NatElim_ m mz ms n)  d 
  =  let  mzVal = cEval_ mz d
          msVal = cEval_ ms d
          rec nVal =
            case nVal of
              VZero_       ->  mzVal
              VSucc_ k     ->  (msVal `vapp_` k) `vapp_` rec k
              VNeutral_ n  ->  VNeutral_
                               (NNatElim_ (cEval_ m d) mzVal msVal n)
              _            ->  error "internal: eval natElim"
     in   rec (cEval_ n d)
iEval_ (Vec_ a n)                 d  =  VVec_ (cEval_ a d) (cEval_ n d)
iEval_ (VecElim_ a m mn mc n xs)  d  =
  let  mnVal  =  cEval_ mn d
       mcVal  =  cEval_ mc d
       rec nVal xsVal =
         case xsVal of
           VNil_ _          ->  mnVal
           VCons_ _ k x xs  ->  foldl vapp_ mcVal [k, x, xs, rec k xs]
           VNeutral_ n      ->  VNeutral_
                                (NVecElim_  (cEval_ a d) (cEval_ m d)
                                            mnVal mcVal nVal n)
           _                ->  error "internal: eval vecElim"
  in   rec (cEval_ n d) (cEval_ xs d)
iEval_ (Eq_ a x y)                d  =  VEq_ (cEval_ a d) (cEval_ x d) (cEval_ y d)
iEval_ (EqElim_ a m mr x y eq)    d  =
  let  mrVal  =  cEval_ mr d
       rec eqVal =
         case eqVal of
           VRefl_ _ z -> mrVal `vapp_` z
           VNeutral_ n ->  
             VNeutral_ (NEqElim_  (cEval_ a d) (cEval_ m d) mrVal
                                  (cEval_ x d) (cEval_ y d) n)
           _ -> error "internal: eval eqElim"
  in   rec (cEval_ eq d)
iEval_ (Fin_ n)                d  =  VFin_ (cEval_ n d)
iEval_ (FinElim_ m mz ms n f)  d  =
  let  mzVal  =  cEval_ mz d
       msVal  =  cEval_ ms d
       rec fVal =
         case fVal of
           VFZero_ k        ->  mzVal `vapp_` k
           VFSucc_ k g      ->  foldl vapp_ msVal [k, g, rec g]
           VNeutral_ n'     ->  VNeutral_
                                (NFinElim_  (cEval_ m d) (cEval_ mz d)
                                            (cEval_ ms d) (cEval_ n d) n')
           _                ->  error "internal: eval finElim"
  in   rec (cEval_ f d)
