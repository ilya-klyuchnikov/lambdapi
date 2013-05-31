module TypingLP where

import Prelude hiding (print)
import Control.Monad.Error
import Data.List
import Data.Char

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

import LPH
import PrinterLP

iType0_ :: (NameEnv Value_,Context_) -> ITerm_ -> Result Type_
iType0_ = iType_ 0
iType_ :: Int -> (NameEnv Value_,Context_) -> ITerm_ -> Result Type_
iType_ ii g (Ann_ e tyt )
  =     do  cType_  ii g tyt VStar_
            let ty = cEval_ tyt (fst g, [])  
            cType_ ii g e ty
            return ty
iType_ ii g Star_   
   =  return VStar_   
iType_ ii g (Pi_ tyt tyt')  
   =  do  cType_ ii g tyt VStar_    
          let ty = cEval_ tyt (fst g, [])  
          cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)  
                    (cSubst_ 0 (Free_ (Local ii)) tyt') VStar_  
          return VStar_   
iType_ ii g (Free_ x)
  =     case lookup x (snd g) of
          Just ty        ->  return ty
          Nothing        ->  throwError ("unknown identifier: " ++ render (iPrint_ 0 0 (Free_ x)))
iType_ ii g (e1 :$: e2)
  =     do  si <- iType_ ii g e1
            case si of
              VPi_  ty ty'  ->  do  cType_ ii g e2 ty
                                    return ( ty' (cEval_ e2 (fst g, [])))
              _                  ->  throwError "illegal application"
iType_ ii g Nat_                  =  return VStar_
iType_ ii g (NatElim_ m mz ms n)  =
  do  cType_ ii g m (VPi_ VNat_ (const VStar_))
      let mVal  = cEval_ m (fst g, []) 
      cType_ ii g mz (mVal `vapp_` VZero_)
      cType_ ii g ms (VPi_ VNat_ (\ k -> VPi_ (mVal `vapp_` k) (\ _ -> mVal `vapp_` VSucc_ k)))
      cType_ ii g n VNat_
      let nVal = cEval_ n (fst g, [])
      return (mVal `vapp_` nVal)
iType_ ii g (Vec_ a n) =
  do  cType_ ii g a  VStar_
      cType_ ii g n  VNat_
      return VStar_
iType_ ii g (VecElim_ a m mn mc n vs) =
  do  cType_ ii g a VStar_
      let aVal = cEval_ a (fst g, [])
      cType_ ii g m
        (  VPi_ VNat_ (\n -> VPi_ (VVec_ aVal n) (\ _ -> VStar_)))
      let mVal = cEval_ m (fst g, [])
      cType_ ii g mn (foldl vapp_ mVal [VZero_, VNil_ aVal])
      cType_ ii g mc
        (  VPi_ VNat_ (\ n -> 
           VPi_ aVal (\ y -> 
           VPi_ (VVec_ aVal n) (\ ys ->
           VPi_ (foldl vapp_ mVal [n, ys]) (\ _ ->
           (foldl vapp_ mVal [VSucc_ n, VCons_ aVal n y ys]))))))
      cType_ ii g n VNat_
      let nVal = cEval_ n (fst g, [])
      cType_ ii g vs (VVec_ aVal nVal)
      let vsVal = cEval_ vs (fst g, [])
      return (foldl vapp_ mVal [nVal, vsVal])
iType_ i g (Eq_ a x y) =
  do  cType_ i g a VStar_
      let aVal = cEval_ a (fst g, [])
      cType_ i g x aVal
      cType_ i g y aVal
      return VStar_
iType_ i g (EqElim_ a m mr x y eq) =
  do  cType_ i g a VStar_
      let aVal = cEval_ a (fst g, [])
      cType_ i g m
        (VPi_ aVal (\ x ->
         VPi_ aVal (\ y ->
         VPi_ (VEq_ aVal x y) (\ _ -> VStar_)))) 
      let mVal = cEval_ m (fst g, [])
      cType_ i g mr
        (VPi_ aVal (\ x ->
         foldl vapp_ mVal [x, x]))
      cType_ i g x aVal
      let xVal = cEval_ x (fst g, [])
      cType_ i g y aVal
      let yVal = cEval_ y (fst g, [])
      cType_ i g eq (VEq_ aVal xVal yVal)
      let eqVal = cEval_ eq (fst g, [])
      return (foldl vapp_ mVal [xVal, yVal])

cType_ :: Int -> (NameEnv Value_,Context_) -> CTerm_ -> Type_ -> Result ()
cType_ ii g (Inf_ e) v 
  =     do  v' <- iType_ ii g e
            unless ( quote0_ v == quote0_ v') (throwError ("type mismatch:\n" ++ "type inferred:  " ++ render (cPrint_ 0 0 (quote0_ v')) ++ "\n" ++ "type expected:  " ++ render (cPrint_ 0 0 (quote0_ v)) ++ "\n" ++ "for expression: " ++ render (iPrint_ 0 0 e)))
cType_ ii g (Lam_ e) ( VPi_ ty ty')
  =     cType_  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty ) : g))) g)
                (cSubst_ 0 (Free_ (Local ii)) e) ( ty' (vfree_ (Local ii))) 
cType_ ii g Zero_      VNat_  =  return ()
cType_ ii g (Succ_ k)  VNat_  =  cType_ ii g k VNat_
cType_ ii g (Nil_ a) (VVec_ bVal VZero_) =
  do  cType_ ii g a VStar_
      let aVal = cEval_ a (fst g, []) 
      unless  (quote0_ aVal == quote0_ bVal) 
              (throwError "type mismatch")
cType_ ii g (Cons_ a n x xs) (VVec_ bVal (VSucc_ k)) =
  do  cType_ ii g a VStar_
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal)
              (throwError "type mismatch")
      cType_ ii g n VNat_
      let nVal = cEval_ n (fst g, [])
      unless  (quote0_ nVal == quote0_ k)
              (throwError "number mismatch")
      cType_ ii g x aVal
      cType_ ii g xs (VVec_ bVal k)
cType_ ii g (Refl_ a z) (VEq_ bVal xVal yVal) =
  do  cType_ ii g a VStar_
      let aVal = cEval_ a (fst g, [])
      unless  (quote0_ aVal == quote0_ bVal)
              (throwError "type mismatch")
      cType_ ii g z aVal
      let zVal = cEval_ z (fst g, [])
      unless  (quote0_ zVal == quote0_ xVal && quote0_ zVal == quote0_ yVal)
              (throwError "type mismatch")
cType_ ii g _ _
  =     throwError "type mismatch"