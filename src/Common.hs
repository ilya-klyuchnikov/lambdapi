module Common where

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP

data Name
   =  Global  String
   |  Local   Int
   |  Quote   Int
  deriving (Show, Eq)

data Type
   =  TFree  Name
   |  Fun    Type Type
  deriving (Show, Eq) 

type Result a = Either String a
type NameEnv v = [(Name, v)]

data Stmt i tinf = Let String i           --  let x = t
                   | Assume [(String,tinf)] --  assume x :: t, assume x :: *
                   | Eval i
                   | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                   | Out String             --  more lhs2TeX hacking, allow to print to files
    deriving (Show)

parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id

vars :: [String]
vars = [ c : n | n <- "" : map show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]


