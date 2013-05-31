module LPH where

import Prelude hiding (print)
import Control.Monad.Error
import Data.List
import Data.Char

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

data Stmt i tinf = Let String i           --  let x = t
                   | Assume [(String,tinf)] --  assume x :: t, assume x :: *
                   | Eval i
                   | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                   | Out String             --  more lhs2TeX hacking, allow to print to files
    deriving (Show)

-- 2.4. Implementation
-- Simply typed LC

-- inferrable
data ITerm
   =  Ann    CTerm Type
   |  Bound  Int
   |  Free   Name
   |  ITerm :@: CTerm
  deriving (Show, Eq)

-- checkable term
data CTerm
   =  Inf  ITerm 
   |  Lam  CTerm
  deriving (Show, Eq)
 
data Name
   =  Global  String
   |  Local   Int
   |  Quote   Int
  deriving (Show, Eq)

data Type
   =  TFree  Name
   |  Fun    Type Type
  deriving (Show, Eq)
data Value
   =  VLam      (Value -> Value)
   |  VNeutral  Neutral
data Neutral
   =  NFree  Name
   |  NApp   Neutral Value
vfree :: Name -> Value
vfree n = VNeutral (NFree n)
data Kind = Star
  deriving (Show)
 
data Info
   =  HasKind  Kind
   |  HasType  Type 
  deriving (Show)
 
type Context = [(Name, Info)]
type Env = [Value]

type NameEnv v = [(Name, v)]
--type Ctx inf = [(Name, inf)]
--type State v inf = (Bool, String, NameEnv v, Ctx inf)

type Result a = Either String a

iEval :: ITerm -> (NameEnv Value,Env) -> Value
iEval (Ann  e _)    d  =  cEval e d
iEval (Free  x)     d  =  case lookup x (fst d) of Nothing ->  (vfree x); Just v -> v
iEval (Bound  ii)   d  =  (snd d) !! ii
iEval (e1 :@: e2)   d  =  vapp (iEval e1 d) (cEval e2 d)
 
vapp :: Value -> Value -> Value
vapp (VLam f)      v  =  f v
vapp (VNeutral n)  v  =  VNeutral (NApp n v)
 
cEval :: CTerm -> (NameEnv Value,Env) -> Value
cEval (Inf  ii)   d  =  iEval ii d
cEval (Lam  e)    d  =  VLam (\ x -> cEval e (((\(e, d) -> (e,  (x : d))) d)))
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
quote0 :: Value -> CTerm
quote0 = quote 0
 
quote :: Int -> Value -> CTerm
quote ii (VLam f)      =  Lam (quote (ii + 1) (f (vfree (Quote ii))))
quote ii (VNeutral n)  =  Inf (neutralQuote ii n)
 
neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree x)   =  boundfree ii x
neutralQuote ii (NApp n v)  =  neutralQuote ii n :@: quote ii v
boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k)     =  Bound (ii - k - 1)
boundfree ii x             =  Free x
id'      =  Lam (Inf (Bound 0))
const'   =  Lam (Lam (Inf (Bound 1)))

tfree a  =  TFree (Global a)
free x   =  Inf (Free (Global x))
 
term1    =  Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y" 
term2    =  Ann const' (Fun  (Fun (tfree "b") (tfree "b"))
                             (Fun  (tfree "a")
                                   (Fun (tfree "b") (tfree "b"))))
            :@: id' :@: free "y" 
 
env1     =  [  (Global "y", HasType (tfree "a")),
               (Global "a", HasKind Star)]
env2     =  [(Global "b", HasKind Star)] ++ env1
test_eval1=  quote0 (iEval term1 ([],[]))
 
test_eval2=  quote0 (iEval term2 ([],[]))
test_type1=  iType0 env1 term1
test_type2=  iType0 env2 term2

------------------------
--- Dependent types 
------------------------

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

vapp_ :: Value_ -> Value_ -> Value_
vapp_ (VLam_ f)      v  =  f v
vapp_ (VNeutral_ n)  v  =  VNeutral_ (NApp_ n v)
 
vfree_ :: Name -> Value_
vfree_ n = VNeutral_ (NFree_ n)
 
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
iEval_ (Ann_  c _)       d  =  cEval_ c d
iEval_ Star_           d  =  VStar_   
iEval_ (Pi_ ty ty')    d  =  VPi_ (cEval_ ty d) (\ x -> cEval_ ty' (((\(e, d) -> (e,  (x : d))) d)))   
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
              VSucc_ k     ->  msVal `vapp_` k `vapp_` rec k
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

iSubst_ :: Int -> ITerm_ -> ITerm_ -> ITerm_
iSubst_ ii i'   (Ann_ c c')     =  Ann_ (cSubst_ ii i' c) (cSubst_ ii i' c')

iSubst_ ii r  Star_           =  Star_  
iSubst_ ii r  (Pi_ ty ty')    =  Pi_  (cSubst_ ii r ty) (cSubst_ (ii + 1) r ty')
iSubst_ ii i' (Bound_ j)      =  if ii == j then i' else Bound_ j
iSubst_ ii i' (Free_ y)       =  Free_ y
iSubst_ ii i' (i :$: c)       =  iSubst_ ii i' i :$: cSubst_ ii i' c
iSubst_ ii r  Nat_            =  Nat_
iSubst_ ii r  (NatElim_ m mz ms n)
                              =  NatElim_ (cSubst_ ii r m)
                                          (cSubst_ ii r mz) (cSubst_ ii r ms)
                                          (cSubst_ ii r ms)
iSubst_ ii r  (Vec_ a n)      =  Vec_ (cSubst_ ii r a) (cSubst_ ii r n)
iSubst_ ii r  (VecElim_ a m mn mc n xs)
                              =  VecElim_ (cSubst_ ii r a) (cSubst_ ii r m)
                                          (cSubst_ ii r mn) (cSubst_ ii r mc)
                                          (cSubst_ ii r n) (cSubst_ ii r xs)
iSubst_ ii r  (Eq_ a x y)     =  Eq_ (cSubst_ ii r a)
                                     (cSubst_ ii r x) (cSubst_ ii r y)
iSubst_ ii r  (EqElim_ a m mr x y eq)
                              =  VecElim_ (cSubst_ ii r a) (cSubst_ ii r m)
                                          (cSubst_ ii r mr) (cSubst_ ii r x)
                                          (cSubst_ ii r y) (cSubst_ ii r eq)
iSubst_ ii r  (Fin_ n)        =  Fin_ (cSubst_ ii r n)
iSubst_ ii r  (FinElim_ m mz ms n f)
                              =  FinElim_ (cSubst_ ii r m)
                                          (cSubst_ ii r mz) (cSubst_ ii r ms)
                                          (cSubst_ ii r n) (cSubst_ ii r f)
cSubst_ :: Int -> ITerm_ -> CTerm_ -> CTerm_
cSubst_ ii i' (Inf_ i)      =  Inf_ (iSubst_ ii i' i)
cSubst_ ii i' (Lam_ c)      =  Lam_ (cSubst_ (ii + 1) i' c)
cSubst_ ii r  Zero_         =  Zero_
cSubst_ ii r  (Succ_ n)     =  Succ_ (cSubst_ ii r n)
cSubst_ ii r  (Nil_ a)      =  Nil_ (cSubst_ ii r a)
cSubst_ ii r  (Cons_ a n x xs)
                            =  Cons_ (cSubst_ ii r a) (cSubst_ ii r x)
                                     (cSubst_ ii r x) (cSubst_ ii r xs)
cSubst_ ii r  (Refl_ a x)   =  Refl_ (cSubst_ ii r a) (cSubst_ ii r x)
cSubst_ ii r  (FZero_ n)    =  FZero_ (cSubst_ ii r n)
cSubst_ ii r  (FSucc_ n k)  =  FSucc_ (cSubst_ ii r n) (cSubst_ ii r k)


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

instance Show Value_ where
  show = show . quote0_
type Type_     =  Value_  
type Context_    =  [(Name, Type_)]
quote0_ :: Value_ -> CTerm_
quote0_ = quote_ 0 

----- NEW ----

data Nat = Zero | Succ Nat
plus :: Nat -> Nat -> Nat 
plus Zero n      = n 
plus (Succ k) n  = Succ (plus k n) 

parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id

vars :: [String]
vars = [ c : n | n <- "" : map show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]


