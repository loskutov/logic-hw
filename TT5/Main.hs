{-# LANGUAGE UnicodeSyntax #-}
module TT5.Main where

import Control.Applicative hiding (empty)
import Control.Monad
import Data.Map.Strict (Map, empty, insert, assocs)
import Data.Function
import Data.Attoparsec.ByteString.Char8
import Data.Char (isAsciiLower)
import Data.ByteString.Char8 (readFile, lines)
import Prelude.Unicode hiding ((∈))
import Prelude hiding (lookup, readFile, lines)
import Debug.Trace

import Utils (parseBS)

data Term a = Function String [Term a] | Var a
  deriving (Eq, Show)
type Equation a = (Term a, Term a)

emap :: (Term a → Term a) → Equation a → Equation a
emap f (x, y) = ((,) `on` f) x y

(∈) :: (Eq a) => a → Term a → Bool
s ∈ (Var v) = s == v
s ∈ (Function _ xs) = or $ map (s ∈) xs

substitute :: (Eq a, Show a) => a → Term a → Term a → Term a
substitute s t f | trace ("subst " ++ (show s) ++ "→" ++ show t ++ " in " ++ show f) False = undefined
substitute old new (Function f xs) = Function f $ map (substitute old new) xs
substitute old new (Var v) | v == old  = new
                           | otherwise = Var v

rev :: Equation a → Equation a
rev (lhs@(Function _ _), rhs@(Var _)) = (rhs, lhs)
rev eq = eq

differentFun :: Equation a → Bool
differentFun ((Function f fs), (Function g gs)) = (f ≠ g || length fs ≠ length gs)
differentFun _ = False

sameFun :: Equation a → Bool
sameFun ((Function f _), (Function g _)) = (f == g)
sameFun _ = False

addArg :: [Equation a] → [Equation a]
addArg (x@(Function _ l, Function _ r):xs) | sameFun x = (zip l r) ++ addArg xs
addArg (_:xs) = addArg xs
addArg [] = []

substitutable :: Equation a → Bool
substitutable ((Var _), _) = True
substitutable _                         = False

trySubstitute :: (Eq a, Ord a, Show a) => [Equation a] → Map a (Term a) → Maybe ([Equation a], Map a (Term a))
trySubstitute ((eq@(Var x, f)):xs) acc
  | x ∈ f = Nothing
  | otherwise = trySubstitute ((emap (substitute x f)) <$> xs) (insert x f ((substitute x f) <$> acc))
trySubstitute (x:xs) acc = case trySubstitute xs acc of
  Nothing → Nothing
  Just (eqs, newacc) → Just (x:eqs, newacc)
trySubstitute [] acc = Just ([], acc)

unify :: (Eq a, Ord a, Show a) => [Equation a] → Map a (Term a) → Maybe (Map a (Term a))

-- unify (x:_) _ | trace ("unify " ++ show x) False = undefined

unify xs acc | any (\x → rev x ≠ x) xs     = unify (map rev xs) acc
             | any (\(x, y) → (x == y)) xs = unify (filter (\(x, y) → (x ≠ y)) xs) acc
             | any differentFun  xs        = Nothing
             | any      sameFun  xs        = unify (addArg xs) acc
             | any substitutable xs        = (uncurry unify) =<< (trySubstitute xs acc)
             -- | otherwise                   = trace ("OMG: " ++ show xs) Nothing

unify [] acc = Just acc


functionFirst :: Char → Bool
functionFirst c = (isAsciiLower c) && (c < 'i')

varFirst :: Char → Bool
varFirst c = (isAsciiLower c) && (c > 'h')

appropriate :: Char → Bool
appropriate = liftM3 (\x y z → x || y || z) isAsciiLower isDigit (=='\'')

parseTerm :: Parser (Term String)
parseTerm = parseVar <|> do
  fname ← parseFunction
  char '('
  args ← parseTerm `sepBy1` (char ',')
  char ')'
  return $ Function fname args

parseEquation :: Parser (Equation String)
parseEquation = do
  lhs ← parseTerm
  _   ← char '='
  rhs ← parseTerm
  return $ (lhs, rhs)

parseFunction :: Parser String
parseFunction = do
  first ← satisfy functionFirst
  others ← many' $ satisfy appropriate
  return $ first:others

parseVar :: Parser (Term String)
parseVar = do
  first ← satisfy varFirst
  others ← many' $ satisfy appropriate
  return $ Var $ first:others

myshow :: (Show k, Show v) => Maybe (Map k v) → String
myshow (Just m) = concatMap (\(k, a) → (show k) ++ "=" ++ (show a)) (assocs m)
myshow Nothing = "Подстановки не существует"

main :: IO ()
main = do
    input ← readFile "task5.in"
    let eqs = map (parseBS parseEquation) $ lines input
    let ans = unify eqs empty
    writeFile "task5.out" $ myshow ans ++ "\n"

