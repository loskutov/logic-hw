{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

import Data.Map.Strict hiding (map)
import Data.List (intercalate)
import Prelude hiding (readFile, lookup)
import Data.ByteString (readFile)
import Utils
import qualified Lambdas as Λ
import TT5.Unification hiding (main, myshow)
import Debug.Trace

data Type = AtomType String | Type :→: Type deriving (Eq, Ord)

instance Show Type where
  show (AtomType s) = s
  show (t :→: t') = "(" ++ (show t) ++ ")" ++ "→" ++ show t'

instance Show (Term Type) where
  show (Function s xs) = s ++ "(" ++ ((intercalate "," (map show xs))) ++ ")"
  show (Var s) = show s

nameType :: Int → Type
nameType n = AtomType $ "t" ++ (show n)

getType :: (Show (Term Type)) => Λ.Lambda → Int → Map String Type → [Equation Type] → (Type, Int, Map String Type, [Equation Type])
getType _ _ _ x | trace (show x) False = undefined
getType v@(Λ.Var x) n m eqs = (newType, newN, insert x newType m, eqs)
  where (newType, newN) = case lookup x m of
          Nothing → (nameType n, n+1)
          Just s  → (s, n)

getType (Λ.Lambda x λ) n m eqs = (newType, rn+1, delete x rmap, (Function "" [Var ltype, Var rtype], Var newType):reqs)
  where (ltype, ln, lmap, leqs) = getType (Λ.Var x) n m eqs
        (rtype, rn, rmap, reqs) = getType λ ln lmap leqs
        newType = nameType rn -- ltype :→: rtype
getType (Λ.Application lhs rhs) n m eqs = (newType, rn+1, rmap, newEq:reqs)
  where (ltype, ln, lmap, leqs) = getType lhs n  m    eqs
        (rtype, rn, rmap, reqs) = getType rhs ln lmap leqs
        newType = nameType rn
        newEq = (Function "" [Var rtype, Var newType], Var ltype)



myshow :: Term Type → String
myshow (Function _ [lhs, rhs]) = "(" ++ (myshow lhs) ++ "->" ++ (myshow rhs) ++ ")"
myshow (Var (AtomType t)) = t

main :: (Show (Term Type)) => IO ()
main = do
  input ← readFile "task6.in"
  let λ = parseBS Λ.parseLambda input
  let (atype, n, m, eqs) = getType λ 0 empty []
  let unified = unify eqs empty
  let ans = case unified of
        Nothing → "mda"
        Just a → myshow $ a ! (AtomType $ "t" ++ (show (n-1)))
  writeFile "task6.out" $ ans ++ "\n"

