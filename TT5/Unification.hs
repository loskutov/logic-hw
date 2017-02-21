{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE UnicodeSyntax     #-}
module TT5.Unification where
import           Control.Applicative              hiding (empty)
import           Control.Monad
import           Data.Attoparsec.ByteString.Char8
import           Data.Char                        (isAsciiLower)
import           Data.Function
import           Data.List                        (intercalate)
import           Data.Map.Strict                  (Map, insert, fromList)
import           Data.Set                         (Set, insert, member)
import           Debug.Trace
import           Prelude                          hiding (lines, lookup,
                                                   readFile)
import           Prelude.Unicode                  hiding ((∈))

data Term a = Function String [Term a] | Var a
  deriving Eq

instance Show (Term String) where
  show (Function s xs) = s ++ "[" ++ intercalate "," (map show xs) ++ "]"
  show (Var s)         = s

type Equation a = (Term a, Term a)

emap :: (Term a → Term a) → Equation a → Equation a
emap f = uncurry ((,) `on` f)

(∈) :: (Eq a) => a → Term a → Bool
s ∈ (Var v)         = s == v
s ∈ (Function _ xs) = any (s ∈) xs

substitute :: (Eq a) ⇒ a → Term a → Term a → Term a
substitute old new (Function f xs) = Function f $ map (substitute old new) xs
substitute old new v@(Var name) | name == old = new
                                | otherwise = v

rev :: Equation a → Equation a
rev (lhs@(Function _ _), rhs@(Var _)) = (rhs, lhs)
rev eq                                = eq

differentFun :: Equation a → Bool
differentFun (Function f fs, Function g gs) = f ≠ g || length fs ≠ length gs
differentFun _                              = False

sameFun :: Equation a → Bool
sameFun (Function f fs, Function g gs)      = f == g && length fs == length gs
sameFun _                                   = False

addArg :: Equation a → [Equation a]
addArg x@(Function _ l, Function _ r) | sameFun x = zip l r
addArg eq                                         = [eq]

substitutable :: (Ord a) => Set a -> Equation a -> Bool
substitutable ws (Var x, _) = not (member x ws)
substitutable _ _ = False

trySubstitute :: (Ord a, Show a, Show (Term a)) ⇒ Set a -> [Equation a] → Maybe (Set a, [Equation a])
trySubstitute ws (t@(Function _ _, _):xs) = Just (ws, xs ++ [t])
trySubstitute ws ((Var x, f):xs) 
  | x ∈ f && Var x /= f = trace ("cant substitute " ++ show x ++ " in " ++ show f) Nothing
  | member x ws       = trySubstitute ws (xs ++ [(Var x, f)])
  | otherwise           = Just ((Data.Set.insert x ws), (emap (substitute x f) <$> xs) ++ [(Var x, f)])
trySubstitute ws []     = Just (ws, [])

unify :: (Ord a, Show a, Show (Term a)) => Set a -> [Equation a] -> Maybe (Map a (Term a))
unify ws xs | any (\x → rev x ≠ x)   xs = trace ("1" ++ show xs) $ unify ws (map rev xs)                               -- f(...) = x => x = f(...)  
            | any (uncurry (==))     xs = trace ("2" ++ show xs) $ unify ws (filter (uncurry (≠)) xs)                  -- equations like `a = a` are useless
            | any differentFun       xs = Nothing                                             -- no substitution for `f(...) = g(...)`
            | any      sameFun       xs = trace ("3" ++ show xs) $ unify ws (addArg =<< xs)                            -- f(a1...) = f(a2...) => a1... = a2...
            | any (substitutable ws) xs = let tmp = uncurry unify =<< trySubstitute ws xs in trace ("4: " ++ show tmp) tmp              -- x = f(...), h(..., x, ...) = g(...) => h(..., f(...)) = g(...)
            | otherwise                 = trace ("otherwise : ") $ pure $ fromList $ (\(Var a, x) -> (a, x)) <$> xs    -- pereherachivaet list to map
-- unify [] acc = Just acc
-- unify xs acc = trace (show xs ++ ", acc=" ++ show acc) $ Just acc


functionFirst :: Char → Bool
functionFirst c = isAsciiLower c && (c < 'i')

varFirst :: Char → Bool
varFirst c = isAsciiLower c && (c >= 'i')

appropriate :: Char → Bool
appropriate = liftM3 (\x y z → x || y || z) isAsciiLower isDigit (=='\'')

parseTerm :: Parser (Term String)
parseTerm = parseVar <|> do
  fname ← parseFunction
  _ ← char '('
  args ← parseTerm `sepBy1` char ','
  _ ← char ')'
  pure $ Function fname args

parseEquation :: Parser (Equation String)
parseEquation = do
  lhs ← parseTerm
  _   ← char '='
  rhs ← parseTerm
  return (lhs, rhs)

parseFunction :: Parser String
parseFunction = do
  first  ← satisfy functionFirst
  others ← many' $ satisfy appropriate
  pure $ first:others

parseVar :: Parser (Term String)
parseVar = do
  first ← satisfy varFirst
  others ← many' $ satisfy appropriate
  pure $ Var $ first:others
