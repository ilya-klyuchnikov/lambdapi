module Lambda.AST where

import Common

-- inferable term
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

data Value
   =  VLam      (Value -> Value)
   |  VNeutral  Neutral
data Neutral
   =  NFree  Name
   |  NApp   Neutral Value

data Kind = Star
  deriving (Show)

data Info
   =  HasKind  Kind
   |  HasType  Type 
  deriving (Show)

type Context = [(Name, Info)]
type Env = [Value]

-- creates the value corresponding to a free variable
vfree :: Name -> Value
vfree n = VNeutral (NFree n)

vapp :: Value -> Value -> Value
vapp (VLam f)      v  =  f v
vapp (VNeutral n)  v  =  VNeutral (NApp n v)
