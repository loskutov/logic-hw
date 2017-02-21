{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax     #-}

import           Data.ByteString (readFile)
import           Data.List       (intercalate)
import           Data.Map.Strict hiding (map)
import qualified Data.Set as S
import           Debug.Trace
import qualified Lambdas         as Λ
import           Prelude         hiding (lookup, readFile)
import           TT5.Unification hiding (main, myshow)
import           Utils

data Type = AtomType String | Type :→: Type deriving (Eq, Ord)

arrow = Function ""

instance Show Type where
  show (AtomType s) = s
  show (t :→: t')   = "(" ++ (show t) ++ ")" ++ "→" ++ show t'

instance Show (Term Type) where
  show (Function s xs) = s ++ "(" ++ intercalate "," (show <$> xs) ++ ")"
  show (Var s)         = show s

nameType :: Int → Type
nameType n = AtomType $ "t" ++ (show n)


getType :: (Show (Term Type)) ⇒ Λ.Lambda → Int → Map String Type → [Equation Type] → (Type, Int, Map String Type, [Equation Type])
getType (Λ.Var x) n m eqs = (newType, newN, insert x newType m, eqs)
  where (newType, newN) = case lookup x m of
          Nothing → (nameType n, n + 1)
          Just s  → (s, n)
getType (Λ.Lambda x λ) n m eqs = (newType, rn + 1, delete x rmap, newEq:reqs)
  where (ltype, ln, lmap, leqs) = getType (Λ.Var x) n (delete x m) eqs
        (rtype, rn, rmap, reqs) = getType  λ       ln lmap leqs
        newType = nameType rn -- ltype :→: rtype
        newEq = (Var newType, arrow [Var ltype, Var rtype])
getType (Λ.Application lhs rhs) n m eqs = (newType, ln, rmap, newEq:leqs)
  where newType = nameType n
        (rtype, rn, rmap, reqs) = getType rhs (n + 1) m eqs
        (ltype, ln, lmap, leqs) = getType lhs  rn rmap reqs
        newEq = (Var ltype, arrow [Var rtype, Var newType])


myshow :: Term Type → String
myshow (Function _ [lhs, rhs]) = "(" ++ (myshow lhs) ++ "->" ++ myshow rhs ++ ")"
myshow (Var (AtomType t)) = t

main :: (Show (Term Type)) ⇒ IO ()
main = do
  input ← readFile "task6.in"
  let λ = parseBS Λ.parseLambda input
  print λ
  let (atype, n, m, eqs) = getType λ 0 empty []
  print eqs
  print ("---------------------------------")
  return ()
  let unified = unify S.empty eqs
  print eqs
  print unified
  let ans = case unified of
        Nothing → "Can not infer type"
        -- Just a  | trace (show (n-1)) False -> undefined
        Just a  → myshow $ a ! (AtomType $ "t" ++ (show 0))
  writeFile "task6.out" $ ans ++ "\n"

