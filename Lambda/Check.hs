module Lambda.Check where

import Control.Monad.Error

import Lambda.AST
import Common

cKind :: Context -> Type -> Kind -> Result ()
cKind g (TFree x) Star
  =  case lookup x g of
       Just (HasKind Star)  ->  return ()
       Nothing              ->  throwError "unknown identifier"
cKind g (Fun kk kk') Star
  =  do  cKind g kk   Star
         cKind g kk'  Star
 
iType0 :: Context -> ITerm -> Result Type
iType0 = iType 0
 
iType :: Int -> Context -> ITerm -> Result Type
iType ii g (Ann e ty)
  =  do  cKind g ty Star
         cType ii g e ty
         return ty
iType ii g (Free x)
  =  case lookup x g of
       Just (HasType ty)  ->  return ty
       Nothing            ->  throwError "unknown identifier"
iType ii g (e1 :@: e2)
  =  do  si <- iType ii g e1
         case si of
           Fun ty ty'  ->  do  cType ii g e2 ty
                               return ty'
           _           ->  throwError "illegal application"
 
cType :: Int -> Context -> CTerm -> Type -> Result ()
cType ii g (Inf e) ty
  =  do  ty' <- iType ii g e
         unless (ty == ty') (throwError "type mismatch")
cType ii g (Lam e) (Fun ty ty')
  =  cType  (ii + 1) ((Local ii, HasType ty) : g)
            (cSubst 0 (Free (Local ii)) e) ty'
cType ii g _ _
  =  throwError "type mismatch"

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii r (Ann e ty)   =  Ann (cSubst ii r e) ty
iSubst ii r (Bound j)    =  if ii == j then r else Bound j
iSubst ii r (Free y)     =  Free y
iSubst ii r (e1 :@: e2)  =  iSubst ii r e1 :@: cSubst ii r e2

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii r (Inf e)      =  Inf (iSubst ii r e)
cSubst ii r (Lam e)      =  Lam (cSubst (ii + 1) r e)
