{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleInstances #-}
module TT5.Unification where
import Control.Applicative hiding (empty)
import Control.Monad
import Data.List (intercalate)
import Data.Map.Strict (Map, insert)
import Data.Function
import Data.Attoparsec.ByteString.Char8
import Data.Char (isAsciiLower)
import Prelude.Unicode hiding ((∈))
import Prelude hiding (lookup, readFile, lines)

data Term a = Function String [Term a] | Var a
  deriving Eq

instance Show (Term String) where
  show (Function s xs) = s ++ "(" ++ ((intercalate "," (map show xs))) ++ ")"
  show (Var s) = s

type Equation a = (Term a, Term a)

emap :: (Term a → Term a) → Equation a → Equation a
emap f = uncurry ((,) `on` f)

(∈) :: (Eq a) => a → Term a → Bool
s ∈ (Var v)         = s == v
s ∈ (Function _ xs) = any (s ∈) xs

substitute :: (Eq a) => a → Term a → Term a → Term a
substitute old new (Function f xs) = Function f $ map (substitute old new) xs
substitute old new (Var v) | v == old  = new
                           | otherwise = Var v

rev :: Equation a → Equation a
rev (lhs@(Function _ _), rhs@(Var _)) = (rhs, lhs)
rev eq = eq

differentFun :: Equation a → Bool
differentFun ((Function f fs), (Function g gs)) = (f ≠ g || length fs ≠ length gs)
differentFun _                                  = False

sameFun :: Equation a → Bool
sameFun ((Function f fs), (Function g gs))      = (f == g && length fs == length gs)
sameFun _                                       = False

addArg :: Equation a → [Equation a]
addArg x@(Function _ l, Function _ r) | sameFun x = zip l r
addArg eq = [eq]

substitutable :: Eq a => [Equation a] -> Equation a → Bool
substitutable xs ((Var a), _) = any (a ∈) ((uncurry (++)) $ unzip xs)
substitutable _ _             = False

trySubstitute :: (Eq a, Ord a) => [Equation a] → Map a (Term a) → Maybe ([Equation a], Map a (Term a))
trySubstitute ((Var x, f):xs) acc
  | x ∈ f = Nothing
  | otherwise = trySubstitute ((emap (substitute x f)) <$> xs) (insert x f ((substitute x f) <$> acc))
trySubstitute (x:xs) acc = case trySubstitute xs acc of
  Nothing → Nothing
  Just (eqs, newacc) → Just (x:eqs, newacc)
trySubstitute [] acc = Just ([], acc)

unify :: (Eq a, Ord a) => [Equation a] → Map a (Term a) → Maybe (Map a (Term a))

unify xs acc | any (\x → rev x ≠ x)   xs = unify (map rev xs) acc               -- f(...) = x => x = f(...)
             | any (uncurry (==))     xs = unify (filter (uncurry (≠)) xs) acc  -- equations like `a = a` are useless
             | any differentFun       xs = Nothing                              -- no substitution for `f(...) = g(...)`
             | any      sameFun       xs = unify (concatMap addArg xs) acc      -- f(a1...) = f(a2...) => a1... = a2...
             | any (substitutable xs) xs = (uncurry unify) =<< (trySubstitute xs acc)

unify [] acc = Just acc


functionFirst :: Char → Bool
functionFirst c = (isAsciiLower c) && (c < 'i')

varFirst :: Char → Bool
varFirst c = (isAsciiLower c) && (c >= 'i')

appropriate :: Char → Bool
appropriate = liftM3 (\x y z → x || y || z) isAsciiLower isDigit (=='\'')

parseTerm :: Parser (Term String)
parseTerm = parseVar <|> do
  fname ← parseFunction
  _ ← char '('
  args ← parseTerm `sepBy1` (char ',')
  _ ← char ')'
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


