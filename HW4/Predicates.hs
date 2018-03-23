{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE UnicodeSyntax     #-}
{-# LANGUAGE ViewPatterns      #-}
module Predicates where

import           Control.Applicative
import           Control.Monad                  (join)
import           Control.Monad.State            (StateT, evalStateT, get, lift,
                                                 modify)
import           Data.Attoparsec.Internal.Types (Parser)
import           Data.Attoparsec.Text           (char, option, satisfy, sepBy,
                                                 string)
import           Data.Char                      (isAsciiLower, isAsciiUpper,
                                                 isDigit)
import           Data.Function                  (on)
import           Data.Functor                   (($>))
import           Data.List                      (foldl1', intercalate)
import           Data.Monoid                    ((<>))
import qualified Data.Set                       as S
import qualified Data.SetMap                    as SM
import           Data.Text                      (Text)

import           Utils


data Nat = Zero
         | Succ Nat
         | Nat :+: Nat
         | Nat :*: Nat
         | Function String [Nat]
         | Var String
  deriving (Eq, Ord)

data SubstStatus = SubstWith Nat
                 | Original
                 | Different
                 deriving (Eq, Show)

instance Monoid SubstStatus where
  mempty = Original
  Original `mappend` a = a
  a `mappend` Original = a
  SubstWith a `mappend` SubstWith b | a == b    = SubstWith a
                                    | otherwise = Different
  Different `mappend` _ = Different
  _ `mappend` Different = Different

instance Show Nat where
  show Zero = "0"
  show (Succ n) = case n of
    Succ _ → show n ++ "'"
    _      → "(" ++ show n ++ ")'"
  show (a :+: b) = show a ++ "+" ++ show b
  show (a :*: b) = "(" ++ show a ++ ")*(" ++ show b ++ ")"
  show (Function name a) = name ++ if null a then "" else "(" ++ intercalate "," (show <$> a) ++ ")"
  show (Var name) = name

infixr 4 :→
infixl 5 :|
infixl 6 :&
data Prop = Prop :→ Prop
          | Prop :| Prop
          | Prop :& Prop
          | Forall String Prop
          | Exists String Prop
          | Nat :=: Nat
          | Predicate String [Nat]
          | Neg Prop
          deriving (Eq, Ord)

priority :: Prop → Int
priority (_ :→ _) = 1
priority (_ :| _) = 2
priority (_ :& _) = 3
priority (Neg _)  = 4
-- priority (Var _)  = 4
priority _        = 5 -- no eto ne tochno

showBrackets :: Prop → Prop → String
showBrackets x _ = show x
-- showBrackets x φ | priority x <= priority φ = '(' : show x ++ ")"
                 -- | otherwise               = show x

instance Show Prop where
    show (x@(_ :→ _) :→ y)  = "(" ++ show x ++ "->" ++ show y ++ ")"
    show (x :→ y)           = "(" ++ show x ++ "->" ++ show y ++ ")"
    show φ@(x :| y)         = "(" ++ showBrackets x φ ++ "|" ++ showBrackets y φ ++ ")"
    show φ@(x :& y)         = "(" ++ showBrackets x φ ++ "&" ++ showBrackets y φ ++ ")"
    show φ@(Neg x)          = '!' : showBrackets x φ
    show (Predicate name a) = name ++ if null a then "" else "(" ++ intercalate ", " (show <$> a) ++ ")"
    show (a :=: b)          = "(" ++ show a ++ "=" ++ show b ++ ")"
    show (Forall x expr)    = "@" ++ x ++ "(" ++ show expr ++ ")"
    show (Exists x expr)    = "?" ++ x ++ "(" ++ show expr ++ ")"

subst :: String → Nat → Nat → Nat
subst old new v@(Var x) | x == old = new
                        | otherwise = v
subst old new (x :+: y) = ((:+:) `on` subst old new) x y
subst old new (x :*: y) = ((:*:) `on` subst old new) x y
subst old new (Succ x) = Succ $ subst old new x
subst old new (Function f args) = Function f $ subst old new <$> args
subst _ _ Zero = Zero

-- | `substitute old new λ` substitutes `old` with `new` in `λ`
substitute :: String → Nat → Prop → Prop
-- substitute old new l | trace ("mmm substitute " ++ (show old) ++ "->(" ++ (show new) ++ ") in " ++ (show l)) False = undefined
substitute old new (a :→ b) = ((:→) `on` substitute old new) a b
substitute old new (a :| b) = ((:|) `on` substitute old new) a b
substitute old new (a :& b) = ((:&) `on` substitute old new) a b
substitute old new l@(Forall s λ) | s /= old  = l
                                  | otherwise = Forall s $ substitute old new λ
substitute old new l@(Exists s λ) | s /= old  = l
                                  | otherwise = Exists s $ substitute old new λ
substitute old new (a :=: b)          = ((:=:) `on` subst old new) a b
substitute old new (Predicate p args) = Predicate p (subst old new <$> args)
substitute old new (Neg x)            = Neg (substitute old new x)

data Annotation = MP (Int, Prop) (Int, Prop)
                | ForallRule
                | ExistsRule
                | Axiom Int
                | Assumption
                | None
                deriving (Eq)

isAxiom :: Annotation → Bool
isAxiom (Axiom _) = True
isAxiom _         = False

instance Show Annotation where
    show (MP _ _)   = "M.P"
    show (Axiom a)  = "Сх. акс. " ++ show a
    show None       = "Не доказано"
    show Assumption = "Допущение"
    show ForallRule = "Forall Rule"
    show ExistsRule = "Exists Rule"

parseExpr :: Parser Text Prop
parseExpr = do
    disjs ← parseDisj `sepBy` string "->"
    if null disjs then
        fail "no disjuctions, so sad"
    else pure $ foldr1 (:→) disjs
    where
        parseMultiplicand' = (do
            letter ← satisfy isAsciiLower
            numbers ← many $ satisfy isDigit
            args <- option [] (char '(' *> parseTerm `sepBy` char ','<* char ')')
            let name = letter : numbers
            if null args then
                pure $ Var name
            else pure $ Function name args
          ) <|> (
            char '0' $> Zero
          ) <|> (
            char '(' *> parseTerm <* char ')'
          )
        parseMultiplicand = do
            m <- parseMultiplicand'
            primes <- many $ char '\''
            pure $ foldr (const Succ) m primes
        parseSummand = do
            multiplicands ← parseMultiplicand `sepBy` char '*'
            if null multiplicands then
                fail "no multiplicands, so sad"
            else pure $ foldl1 (:*:) multiplicands
        parseTerm = do
            summands ← parseSummand `sepBy` char '+'
            if null summands then
                fail "no summands, so sad"
            else pure $ foldl1 (:+:) summands
        parsePred = (do
            letter ← satisfy isAsciiUpper
            numbers ← many $ satisfy isDigit
            args <- option [] (char '(' *> parseTerm `sepBy` char ','<* char ')')
            pure $ Predicate (letter : numbers) args) <|>
          do
            term1 <- parseTerm
            () <$ char '='
            term2 <- parseTerm
            pure $ term1 :=: term2

        parseExists = do
            () <$ char '?'
            letter ← satisfy isAsciiLower
            numbers ← many $ satisfy isDigit
            Exists (letter : numbers) <$> parseUnary

        parseForall = do
            () <$ char '@'
            letter ← satisfy isAsciiLower
            numbers ← many $ satisfy isDigit
            Forall (letter : numbers) <$> parseUnary

        parseUnary = parsePred <|> Neg <$> (char '!' *> parseUnary)
                  <|> (char '(' *> parseExpr <* char ')') <|> parseExists <|> parseForall

        parseConj = do
            negations ← parseUnary `sepBy` char '&'
            if null negations then
                fail "no negations, so sad"
            else pure $ foldl1' (:&) negations

        parseDisj = do
            conjs ← parseConj `sepBy` char '|'
            if null conjs then
                fail "no conjuctions, so sad"
            else pure $ foldl1' (:|) conjs

parseP :: Text → Prop
parseP = parseText parseExpr

-- whether a'[v:=?] = a
isSubst' :: S.Set String → String → Nat → Nat → SubstStatus
-- isSubst' b v a a' | trace ("\n-----\nisSubst' " ++ show b ++ " "++ v ++ " " ++ show a ++ " " ++ show a' ++ "\n----\n") False = undefined
isSubst' _ _ a       a'  | a == a' = Original
isSubst' b v' a (Var v)  | v == v'  && S.null (freeVarsN a `S.intersection` b)
  = SubstWith a
isSubst' b v (Succ x) (Succ y)     = isSubst' b v x y
isSubst' b v (Function name args) (Function name' args') | name == name' = mconcat (zipWith (isSubst' b v) args args')
isSubst' b v (x :+: y) (x' :+: y') = isSubst' b v x x' <> isSubst' b v y y'
isSubst' _ _ _ _ = Different

isSubst'' = isSubst'
-- isSubst'' b v a a' | True || trace ("\n-----\nisSubst' " ++ show b ++ " "++ v ++ " " ++ show a ++ " " ++ show a' ++ " = " ++ show ans ++ "\n----\n") True = ans
                  -- where ans = isSubst' b v a a'

-- tells whether arg1 is arg2[arg3 := x] for some x
substType :: S.Set String → Prop → Prop → String → SubstStatus
-- substType _ a b c | trace ("substType " ++ show a ++ " " ++ show b ++ " " ++ show c) False = undefined
substType _ a a' _ | a == a' = Original
substType bound (Predicate n args1) (Predicate n' args2) v | n == n' =
  mconcat (zipWith (isSubst'' bound v) args1 args2)
substType bound (a :=: b) (a' :=: b') v =
  isSubst'' bound v a a' <> isSubst'' bound v b b'
substType bound (a :→ b) (a' :→ b') v =
  substType bound a a' v <> substType bound b b' v
substType bound (a :& b) (a' :& b') v =
  substType bound a a' v <> substType bound b b' v
substType bound (a :| b) (a' :| b') v =
  substType bound a a' v <> substType bound b b' v
substType bound (Forall a p1) (Forall a' p2) v | a == a' && a /= v =
  substType (S.insert a bound) p1 p2 v
substType bound (Exists a p1) (Exists a' p2) v | a == a' && a /= v =
  substType (S.insert a bound) p1 p2 v
substType _ _ _ _ = Different

freeVarsN :: Nat → S.Set String
freeVarsN (Var s)           = S.singleton s
freeVarsN (Succ n)          = freeVarsN n
freeVarsN (x :+: y)         = freeVarsN x ∪ freeVarsN y
freeVarsN (x :*: y)         = freeVarsN x ∪ freeVarsN y
freeVarsN (Function _ args) = foldr S.union S.empty (freeVarsN <$> args)
freeVarsN _                 = S.empty

freeVars :: Prop → S.Set String
freeVars (a :→ b)           = (freeVars a) ∪ (freeVars b)
freeVars (a :& b)           = (freeVars a) ∪ (freeVars b)
freeVars (a :| b)           = (freeVars a) ∪ (freeVars b)
freeVars (a :=: b)          = (freeVarsN a) ∪ (freeVarsN b)
freeVars (Forall s λ)       = (freeVars λ)  ∖ (S.singleton s)
freeVars (Exists s λ)       = (freeVars λ)  ∖ (S.singleton s)
freeVars (Predicate _ args) = foldr S.union S.empty (freeVarsN <$> args)
freeVars (Neg p)            = freeVars p

isSubstitution :: Prop → Prop → String → Bool
isSubstitution a b v = case substType S.empty
  a b v of
  SubstWith _ → True
  Original    → True
  _           → False

wtf :: Prop → Annotation
wtf (φ :→ _ :→ φ')
    | φ == φ'                                           = Axiom 1
wtf ((φ'' :→ ψ'') :→ (φ :→ ψ :→ π) :→ (φ' :→ π'))
    | ψ == ψ'' && φ == φ' && φ == φ'' && π == π'        = Axiom 2
wtf (φ :→ ψ :→ (φ' :& ψ'))
    | φ == φ' && ψ == ψ'                                = Axiom 3
wtf (φ :& _ :→ φ')
    | φ == φ'                                           = Axiom 4
wtf (_ :& ψ :→ ψ')
    | ψ == ψ'                                           = Axiom 5
wtf (φ' :→ (φ :| _))
    | φ == φ'                                           = Axiom 6
wtf (ψ' :→ (_ :| ψ))
    | ψ == ψ'                                           = Axiom 7
wtf ((φ :→ π) :→ ((ψ :→ π'') :→ ((φ' :| ψ') :→ π')))
    | φ == φ' && ψ == ψ' && π == π' && π == π''         = Axiom 8
wtf ((φ :→ ψ) :→ ((φ' :→ Neg ψ') :→ Neg φ''))
    | ψ == ψ' && φ == φ' && φ == φ''                    = Axiom 9
wtf (Neg (Neg φ) :→ φ')
    | φ == φ'                                           = Axiom 10
wtf (Forall x ψ :→ ψ') | (ψ' `isSubstitution` ψ) x      = Axiom 11
wtf (ψ' :→ Exists x ψ) | (ψ' `isSubstitution` ψ) x      = Axiom 12
wtf (a :=: b :→ Succ a' :=: Succ b')
    | (a, b) == (a', b')                                = Axiom 0xA1
wtf (a :=: b :→ a' :=: c :→ b' :=: c')
    | (a, b, c) == (a', b', c')                         = Axiom 0xA2
wtf (Succ a' :=: Succ b' :→ a :=: b)
    | (a, b) == (a', b')                                = Axiom 0xA3
wtf (Neg (Succ _ :=: Zero))                             = Axiom 0xA4
wtf (a :+: Succ b :=: Succ (a' :+: b'))
    | (a, b) == (a', b')                                = Axiom 0xA5
wtf (a :+: Zero :=: a') | a == a'                       = Axiom 0xA6
wtf (_ :*: Zero :=: Zero)                               = Axiom 0xA7
wtf ((a :*: Succ b) :=: ((a' :*: b') :+: a''))
    | (a, b) == (a', b') && a == a''                    = Axiom 0xA8
wtf (ψ0 :& Forall x (ψ :→ ψ') :→ φ)
    | ψ0 == substitute x Zero           ψ &&
      ψ' == substitute x (Succ $ Var x) ψ && ψ == φ     = Axiom 0xA9
wtf _ = None

findMP :: S.Set Prop → SM.SetMap Prop Prop → Prop → Maybe (Prop, Prop)
-- findMP l p | trace ("\nfindMP" ++ show l ++ " " ++ show p ++ "\n—-\n") False = undefined
findMP proven r2l prop = let leftParts = r2l SM.! prop
                         in (\x → (x, x :→ prop)) <$> S.lookupMin (S.intersection proven leftParts)

-- annotate assumptions proven (rhs-to-lhs-in-proven) prop
annotate :: [Prop] → S.Set Prop → SM.SetMap Prop Prop → Prop → Annotation
-- annotate ps prvn p | trace ("annotate " ++ show ps ++ " " ++ show prvn ++ " " ++ show p) False = undefined
annotate _      _      _ (wtf → Axiom i)               = Axiom i
annotate assumptions _ _ a | a `elem` assumptions      = Assumption
annotate _      proven r2l (findMP proven r2l → Just (a, b)) = MP (0, a) (0, b)
annotate assumptions _ _ (_ :→ Forall x _) | any (\y -> x `S.member` freeVars y) assumptions = None
annotate assumptions _ _ (Exists x _ :→ _) | any (\y -> x `S.member` freeVars y) assumptions = None
annotate _      proven _ (φ :→ Forall x ψ)
  | (φ :→ ψ) `S.member` proven && not (x `S.member` freeVars φ) = -- trace ("freevars = " ++ show (freeVars φ) ++ "\n")
    ForallRule
annotate _      proven _ (Exists _ φ :→ ψ)
  | (φ :→ ψ) `S.member` proven                         = ExistsRule
annotate _           _ _ _                             = None

annotateList :: [Prop] → [Prop] → Either Int [(Prop, Annotation)]
annotateList = (flip evalStateT (0, S.empty, SM.empty) .) . annotateList'

addProven :: Prop → (Int, S.Set Prop, SM.SetMap Prop Prop) → (Int, S.Set Prop, SM.SetMap Prop Prop)
addProven φ@(α :→ β) (i, proven, r2l) = (i + 1, S.insert φ proven, SM.insert β α r2l)
addProven φ          (i, proven, r2l) = (i + 1, S.insert φ proven, r2l)


annotateList' :: [Prop] → [Prop] → StateT (Int, S.Set Prop, SM.SetMap Prop Prop) (Either Int) [(Prop, Annotation)]
annotateList' _ [] = return []
annotateList' assumptions (φ : xs) = do
  tl <- annotateList' assumptions xs
  (i, proven, r2l) <- get
  let ans = annotate assumptions proven r2l φ
  if (ans /= None) then do
    modify $ addProven φ
    pure $ (φ, ans) : tl
  else
    lift $ Left i

implyItself :: Prop → [Prop]
implyItself α =
  [ (α :→ α :→ α) :→ (α :→ (α :→ α) :→ α) :→ (α :→ α) -- Axiom 2
  , α :→ α :→ α                                       -- Axiom 1
  , (α :→ (α :→ α) :→ α) :→ (α :→ α)                  -- MP
  , α :→ (α :→ α) :→ α                                -- Axiom 1
  , α :→ α                                            -- MP
  ]


implToConj :: Prop → Prop → Prop → [Prop]
implToConj a b c =
  [ ((a :& b) :→ b) :→ (((a :& b) :→ b :→ c) :→ ((a :& b) :→ c))
  , ((a :& b :→ b) :→ (a :& b :→ b :→ c) :→ a :& b :→ c) :→ ((a :→ b :→ c) :→ (a :& b :→ b) :→ (a :& b :→ b :→ c) :→ a :& b :→ c)
  , (a :→ (b :→ c)) :→ (((a :& b) :→ b) :→ (((a :& b) :→ (b :→ c)) :→ ((a :& b) :→ c)))
  , (a :& b) :→ b
  , (a :& b :→ b) :→ ((a :→ b :→ c) :→ ((a :& b) :→ b))
  , (a :→ b :→ c) :→ ((a :& b) :→ b)
  , ((a :→ b :→ c) :→ a :& b :→ b) :→ ((a :→ b :→ c) :→ (a :& b :→ b) :→ (a :& b :→ b :→ c) :→ a :& b :→ c) :→ (a :→ b :→ c) :→ ((a :& b :→ b :→ c) :→ a :& b :→ c)
  , ((a :→ b :→ c) :→ (((a :& b) :→ b) :→ ((a :& b :→ (b :→ c)) :→ ((a :& b) :→ c)))) :→ ((a :→ (b :→ c)) :→ (((a :& b) :→ (b :→ c)) :→ ((a :& b) :→ c)))
  , (a :→ b :→ c) :→ (((a :& b) :→ (b :→ c)) :→ ((a :& b) :→ c))
  , (a :& b :→ a) :→ (((a :& b) :→ (a :→ (b :→ c))) :→ ((a :& b) :→ (b :→ c)))
  , ((a :& b :→ a) :→ (a :& b :→ a :→ b :→ c) :→ a :& b :→ b :→ c) :→ (a :→ b :→ c) :→ ((a :& b :→ a) :→ (a :& b :→ a :→ b :→ c) :→ a :& b :→ b :→ c)
  , (a :→ b :→ c) :→ (((a :& b) :→ a) :→ (((a :& b) :→ (a :→ (b :→ c))) :→ ((a :& b) :→ (b :→ c))))
  , (a :& b) :→ a
  , (a :& b :→ a) :→ ((a :→ (b :→ c)) :→ ((a :& b) :→ a))
  , (a :→ b :→ c) :→ ((a :& b) :→ a)
  , ((a :→ b :→ c) :→ (a :& b :→ a)) :→ (((a :→ b :→ c) :→ ((a :& b :→ a) :→ (a :& b :→ a :→ b :→ c) :→ (a :& b :→ b :→ c))) :→ ((a :→ b :→ c) :→ (a :& b :→ a :→ b :→ c) :→ (a :& b) :→ b :→ c))
  , ((a :→ b :→ c) :→ ((a :& b :→ a) :→ (((a :& b) :→ (a :→ (b :→ c))) :→ ((a :& b) :→ (b :→ c))))) :→ ((a :→ (b :→ c)) :→ (((a :& b) :→ (a :→ (b :→ c))) :→ ((a :& b) :→ (b :→ c))))
  , (a :→ b :→ c) :→ (((a :& b) :→ (a :→ (b :→ c))) :→ ((a :& b) :→ (b :→ c)))
  , (a :→ b :→ c) :→ ((a :& b) :→ (a :→ (b :→ c)))
  , ((a :→ b :→ c) :→ a :& b :→ a :→ b :→ c) :→ ((a :→ b :→ c) :→ (a :& b :→ a :→ b :→ c) :→ a :& b :→ b :→ c) :→ (a :→ b :→ c) :→ (a :& b :→ b :→ c)
  , ((a :→ b :→ c) :→ (((a :& b) :→ (a :→ (b :→ c))) :→ ((a :& b) :→ (b :→ c)))) :→ ((a :→ (b :→ c)) :→ ((a :& b) :→ (b :→ c)))
  , (a :→ b :→ c) :→ ((a :& b) :→ (b :→ c))
  , ((a :→ b :→ c) :→ (a :& b :→ b :→ c)) :→ (((a :→ (b :→ c)) :→ (((a :& b) :→ (b :→ c)) :→ ((a :& b) :→ c))) :→ ((a :→ (b :→ c)) :→ ((a :& b) :→ c)))
  , ((a :→ b :→ c) :→ (((a :& b) :→ (b :→ c)) :→ ((a :& b) :→ c))) :→ ((a :→ (b :→ c)) :→ ((a :& b) :→ c))
  , (a :→ b :→ c) :→ (a :& b :→ c)
  ]

conjToImpl :: Prop → Prop → Prop → [Prop]
conjToImpl a b c =
  [ (a :→ (b :→ ((a :& b) :→ c))) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c)))
  , ((a :→ (b :→ ((a :& b) :→ c))) :→ ((a :→ ((b :→ (a :& b :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c)))) :→ (((a :& b) :→ c) :→ ((a :→ (b :→ ((a :& b) :→ c))) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ b :→ c))))
  , ((a :& b) :→ c) :→ ((a :→ (b :→ ((a :& b) :→ c))) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c))))
  , (a :→ ((a :& b) :→ c)) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c))))
  , ((a :→ ((a :& b) :→ c)) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c))))) :→ (((a :& b) :→ c) :→ ((a :→ ((a :& b) :→ c)) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c))))))
  , ((a :& b) :→ c) :→ ((a :→ ((a :& b) :→ c)) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c)))))
  , ((a :& b) :→ c) :→ (a :→ ((a :& b) :→ c))
  , (((a :& b) :→ c) :→ (a :→ ((a :& b) :→ c))) :→ ((((a :& b) :→ c) :→ ((a :→ ((a :& b) :→ c)) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c)))))) :→ (((a :& b) :→ c) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c))))))
  , (((a :& b) :→ c) :→ ((a :→ ((a :& b) :→ c)) :→ ((a :→ ((a :& b :→ c) :→ (b :→ (a :& b :→ c)))) :→ (a :→ (b :→ (a :& b :→ c)))))) :→ ((a :& b :→ c) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c)))))
  , ((a :& b) :→ c) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c))))
  , (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))))
  , ((((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))))) :→ (((a :& b) :→ c) :→ ((((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))))))
  , ((a :& b) :→ c) :→ ((((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))))
  , ((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))
  , (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))) :→ (((a :& b) :→ c) :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))))
  , ((a :& b) :→ c) :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))
  , (((a :& b) :→ c) :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ ((((a :& b) :→ c) :→ ((((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))))) :→ (((a :& b) :→ c) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))))))
  , (((a :& b) :→ c) :→ ((((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))))) :→ (((a :& b) :→ c) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))))
  , ((a :& b) :→ c) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))))
  , (((a :& b) :→ c) :→ (a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c))))) :→ ((((a :& b) :→ c) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c))))) :→ (((a :& b) :→ c) :→ (a :→ (b :→ ((a :& b) :→ c)))))
  , (((a :& b) :→ c) :→ ((a :→ (((a :& b) :→ c) :→ (b :→ ((a :& b) :→ c)))) :→ (a :→ (b :→ ((a :& b) :→ c))))) :→ (((a :& b) :→ c) :→ (a :→ (b :→ ((a :& b) :→ c))))
  , ((a :& b) :→ c) :→ (a :→ (b :→ ((a :& b) :→ c)))
  , (((a :& b) :→ c) :→ (a :→ (b :→ ((a :& b) :→ c)))) :→ ((((a :& b) :→ c) :→ ((a :→ (b :→ ((a :& b) :→ c))) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c))))) :→ (((a :& b) :→ c) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c)))))
  , (((a :& b) :→ c) :→ ((a :→ (b :→ ((a :& b) :→ c))) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c))))) :→ (((a :& b) :→ c) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c))))
  , ((a :& b) :→ c) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c)))
  , (a :→ (b :→ (a :& b))) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))
  , ((a :→ (b :→ (a :& b))) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))) :→ (((a :& b) :→ c) :→ ((a :→ (b :→ (a :& b))) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))))
  , ((a :& b) :→ c) :→ ((a :→ (b :→ (a :& b))) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))
  , a :→ (b :→ (a :& b))
  , (a :→ (b :→ (a :& b))) :→ (((a :& b) :→ c) :→ (a :→ (b :→ (a :& b))))
  , ((a :& b) :→ c) :→ (a :→ (b :→ (a :& b)))
  , (((a :& b) :→ c) :→ (a :→ (b :→ (a :& b)))) :→ ((((a :& b) :→ c) :→ ((a :→ (b :→ (a :& b))) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))) :→ (((a :& b) :→ c) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))))
  , (((a :& b) :→ c) :→ ((a :→ (b :→ (a :& b))) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))) :→ (((a :& b) :→ c) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))
  , ((a :& b) :→ c) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))
  , ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))
  , (((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))) :→ (((a :& b) :→ c) :→ (((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))))
  , ((a :& b) :→ c) :→ (((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))
  , (b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))
  , ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (((a :& b) :→ c) :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))
  , ((a :& b) :→ c) :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))
  , (((a :& b) :→ c) :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ ((((a :& b) :→ c) :→ (((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))) :→ (((a :& b) :→ c) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))))
  , (((a :& b) :→ c) :→ (((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))) :→ (((a :& b) :→ c) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))
  , ((a :& b) :→ c) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))
  , (((a :& b) :→ c) :→ (a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))) :→ ((((a :& b) :→ c) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))) :→ (((a :& b) :→ c) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))))
  , (((a :& b) :→ c) :→ ((a :→ ((b :→ (a :& b)) :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))) :→ (((a :& b) :→ c) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))))
  , ((a :& b) :→ c) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))
  , (((a :& b) :→ c) :→ (a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c)))) :→ ((((a :& b) :→ c) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c)))) :→ (((a :& b) :→ c) :→ (a :→ (b :→ c))))
  , (((a :& b) :→ c) :→ ((a :→ ((b :→ ((a :& b) :→ c)) :→ (b :→ c))) :→ (a :→ (b :→ c)))) :→ (((a :& b) :→ c) :→ (a :→ (b :→ c)))
  , (a :& b :→ c) :→ (a :→ b :→ c)
  ]

reverseImpl :: Prop → Prop → Prop → [Prop]
reverseImpl a b c =
  [ (b :→ a :→ b :→ c) :→ ((b :→ ((a :→ b :→ c) :→ (a :→ c))) :→ (b :→ a :→ c))
  , ((b :→ (a :→ (b :→ c))) :→ ((b :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ a :→ c))) :→ ((a :→ b :→ c) :→ ((b :→ a :→ b :→ c) :→ ((b :→ ((a :→ b :→ c) :→ (a :→ c))) :→ (b :→ (a :→ c)))))
  , (a :→ (b :→ c)) :→ ((b :→ a :→ b :→ c) :→ ((b :→ (a :→ b :→ c) :→ (a :→ c)) :→ (b :→ a :→ c)))
  , (a :→ (b :→ c)) :→ (b :→ (a :→ (b :→ c)))
  , ((a :→ (b :→ c)) :→ (b :→ (a :→ (b :→ c)))) :→ (((a :→ (b :→ c)) :→ ((b :→ (a :→ (b :→ c))) :→ ((b :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ (a :→ c))))) :→ ((a :→ (b :→ c)) :→ ((b :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ (a :→ c)))))
  , ((a :→ (b :→ c)) :→ ((b :→ (a :→ (b :→ c))) :→ ((b :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ (a :→ c))))) :→ ((a :→ (b :→ c)) :→ ((b :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ (a :→ c))))
  , (a :→ b :→ c) :→ ((b :→ ((a :→ b :→ c) :→ a :→ c)) :→ (b :→ a :→ c))
  , (b :→ a :→ b) :→ ((b :→ ((a :→ b) :→ ((a :→ b :→ c) :→ a :→ c))) :→ (b :→ (a :→ b :→ c) :→ a :→ c))
  , ((b :→ (a :→ b)) :→ ((b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c))))) :→ ((a :→ (b :→ c)) :→ ((b :→ (a :→ b)) :→ ((b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c))))))
  , (a :→ b :→ c) :→ ((b :→ a :→ b) :→ ((b :→ ((a :→ b) :→ ((a :→ b :→ c) :→ a :→ c))) :→ (b :→ ((a :→ b :→ c) :→ (a :→ c)))))
  , b :→ a :→ b
  , (b :→ a :→ b) :→ (a :→ b :→ c) :→ (b :→ a :→ b)
  , (a :→ b :→ c) :→ (b :→ a :→ b)
  , ((a :→ b :→ c) :→ (b :→ a :→ b)) :→ (((a :→ b :→ c) :→ ((b :→ a :→ b) :→ ((b :→ ((a :→ b) :→ ((a :→ b :→ c) :→ a :→ c))) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c)))))) :→ ((a :→ b :→ c) :→ ((b :→ (a :→ b) :→ (a :→ b :→ c) :→ a :→ c) :→ b :→ (a :→ b :→ c) :→ a :→ c)))
  , ((a :→ (b :→ c)) :→ ((b :→ (a :→ b)) :→ ((b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c)))))) :→ ((a :→ (b :→ c)) :→ ((b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c)))))
  , (a :→ (b :→ c)) :→ ((b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c))))
  , ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))))
  , (((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))))) :→ ((a :→ (b :→ c)) :→ (((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))))))
  , (a :→ (b :→ c)) :→ (((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))))
  , (a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))
  , ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ ((a :→ (b :→ c)) :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))))
  , (a :→ (b :→ c)) :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))
  , ((a :→ (b :→ c)) :→ ((a :→ b) :→ ((a :→ b :→ c) :→ a :→ c))) :→ (((a :→ b :→ c) :→ (((a :→ b) :→ ((a :→ b :→ c) :→ a :→ c)) :→ (b :→ ((a :→ b) :→ ((a :→ b :→ c) :→ a :→ c))))) :→ ((a :→ b :→ c) :→ (b :→ ((a :→ b) :→ ((a :→ b :→ c) :→ a :→ c)))))
  , ((a :→ (b :→ c)) :→ (((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ a :→ c))))) :→ ((a :→ b :→ c) :→ (b :→ ((a :→ b) :→ ((a :→ b :→ c) :→ a :→ c))))
  , (a :→ (b :→ c)) :→ (b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))))
  , ((a :→ (b :→ c)) :→ (b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c))))) :→ (((a :→ (b :→ c)) :→ ((b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c))))) :→ ((a :→ (b :→ c)) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c)))))
  , ((a :→ (b :→ c)) :→ ((b :→ ((a :→ b) :→ ((a :→ (b :→ c)) :→ (a :→ c)))) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c))))) :→ ((a :→ (b :→ c)) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c))))
  , (a :→ (b :→ c)) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c)))
  , ((a :→ (b :→ c)) :→ (b :→ ((a :→ (b :→ c)) :→ (a :→ c)))) :→ (((a :→ (b :→ c)) :→ ((b :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ (a :→ c)))) :→ ((a :→ (b :→ c)) :→ (b :→ (a :→ c))))
  , ((a :→ (b :→ c)) :→ ((b :→ ((a :→ (b :→ c)) :→ (a :→ c))) :→ (b :→ (a :→ c)))) :→ ((a :→ (b :→ c)) :→ (b :→ (a :→ c)))
  , (a :→ (b :→ c)) :→ (b :→ (a :→ c))
  ]

  -- imply (α:Γ) (prop, a) produces `Γ ⊢ α → prop` given `α:Γ ⊢ prop`
imply :: [Prop] → (Prop, Annotation) → [Prop]
imply (α:assumptions) (δ, annotation) | δ `elem` assumptions || isAxiom annotation =
    [
        δ :→ α :→ δ,                                       -- Axiom 1
        δ,                                                 -- Assumption/axiom
        α :→ δ                                             -- MP
    ]
imply (α:_) (δ, _) | δ == α = implyItself α
imply (α:_) (δ, MP (_, φ) _) =
    [
        (α :→ φ) :→ (α :→ φ :→ δ) :→ (α :→ δ),            -- Axiom 2
                                                          -- α → φ has been implied before
        (α :→ φ :→ δ) :→ (α :→ δ),                        -- MP
                                                          -- φ → δ also appeared earlier, so α → φ → δ has also been implied
        α :→ δ                                            -- MP
    ]

imply (w:_) (a :→ Forall x b, ForallRule) = join
  [ implToConj w a b
  , pure $ w :& a :→ b -- MP
  , pure $ w :& a :→ Forall x b -- ForallRule
  , conjToImpl w a $ Forall x b
  , pure $ w :→ a :→ Forall x b
  ]
imply (w:_) (Exists x a :→ b, ExistsRule) = join
  [ reverseImpl w a b
  , pure $ a :→ w :→ b
  , pure $ Exists x a :→ w :→ b
  , reverseImpl (Exists x a) w b
  , pure $ w :→ Exists x a :→ b
  ]
imply [] (prop, _) = pure prop
imply _ p = error $ "wrong statement: " ++ show p

-- | Gets list of assumptions and list of the statements; returns the tail of assumptions and the appropriate implication
deduce :: [Prop] → [Prop] → Either Int [Prop]
deduce assumptions props = (>>= imply assumptions) <$> annotated
    where
        annotated = (fmap reverse . annotateList assumptions . reverse) props

contraposition :: Prop → [Prop]
contraposition (α :→ β) = either undefined id $ deduce [α :→ β] =<< deduce [Neg β, α :→ β] intermediate
  where intermediate =
          [ (α :→ β) :→ (α :→ Neg β) :→ Neg α -- Axiom 9
          , α :→ β                            -- Assumption
          , (α :→ Neg β) :→ Neg α             -- M.P.
          , Neg β :→ (α :→ Neg β)             -- Axiom 1
          , Neg β                             -- Assumption
          , α :→ Neg β                        -- MP
          , Neg α                             -- MP
          ]
contraposition _ = error "contraposition is about implications only!"

-- for given α proves α ∨ ¬α
excludedMiddle :: Prop → [Prop]
excludedMiddle α = join
  [ contraposition $ α :→ α :| Neg α
  , pure           $ α :→ α :| Neg α                                                           -- Axiom 6
  , pure           $ Neg (α :| Neg α) :→ Neg α                                                 -- MP
  , contraposition $ Neg α :→ α :| Neg α
  , pure           $ Neg α :→ α :| Neg α                                                       -- Axiom 7
  , pure           $ Neg (α :| Neg α) :→ Neg (Neg α)                                           -- MP
  ] ++
  [ (Neg (α :| Neg α) :→ Neg α) :→ (Neg (α :| Neg α) :→ Neg (Neg α)) :→ Neg (Neg $ α :| Neg α) -- Axiom 9
  , (Neg (α :| Neg α) :→ Neg (Neg α)) :→ Neg (Neg $ α :| Neg α)                                -- MP
  , Neg (Neg $ α :| Neg α)                                                                     -- MP
  , Neg (Neg $ α :| Neg α) :→ (α :| Neg α)                                                     -- Axiom 10
  , α :| Neg α                                                                                 -- MP
  ]
