{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE UnicodeSyntax     #-}
{-# LANGUAGE ViewPatterns      #-}
module Propositions where

import           Control.Applicative
import           Data.Attoparsec.Internal.Types (Parser)
import           Data.Attoparsec.Text           (char, satisfy, sepBy, string)
import           Data.Char
import           Data.Eq.Unicode
import           Data.List                      (find, foldl1')
import           Data.Maybe                     (fromJust)
import           Data.Text                      (Text)
import Debug.Trace
import           Utils

infixr 4 :→
infixl 5 :|
infixl 6 :&
data Prop = Prop :→ Prop
          | Prop :| Prop
          | Prop :& Prop
          | Neg Prop
          | Var String
          deriving Eq

priority :: Prop → Int
priority (_ :→ _) = 1
priority (_ :| _) = 2
priority (_ :& _) = 3
priority (Neg _)  = 4
priority (Var _)  = 4

showBrackets :: Prop → Prop → String
showBrackets x φ | priority x < priority φ = '(' : show x ++ ")"
                 | otherwise               = show x

instance Show Prop where
    show (x@(_ :→ _) :→ y) = '(' : show x ++ ")->" ++ show y
    show (x :→ y)          = show x ++ "->" ++ show y
    show φ@(x :| y)        = showBrackets x φ ++ "|" ++ showBrackets y φ
    show φ@(x :& y)        = showBrackets x φ ++ "&" ++ showBrackets y φ
    show φ@(Neg x)         = '!' : showBrackets x φ
    show (Var x)           = x

data Annotation = MP (Int, Prop) (Int, Prop)
                | Axiom Int
                | Assumption
                | None
                deriving Eq

isAxiom :: Annotation → Bool
isAxiom (Axiom _) = True
isAxiom _         = False

instance Show Annotation where
    show (MP (a, _) (b, _)) = "M.P " ++ show a ++ ", " ++ show b
    show (Axiom a)          = "Сх. акс. " ++ show a
    show None               = "Не доказано"
    show Assumption         = "Допущение"

parseExpr :: Parser Text Prop
parseExpr = do
    disjs ← parseDisj `sepBy` string "->"
    if null disjs then
        fail "no disjuctions, so sad"
    else pure $ foldr1 (:→) disjs
    where
        parseVar = do
            letter ← satisfy isAsciiUpper
            numbers ← many $ satisfy isDigit
            pure $ Var (letter : numbers)

        parseNeg = parseVar <|> Neg <$> (char '!' *> parseNeg) <|> (char '(' *> parseExpr <* char ')')

        parseConj = do
            negations ← parseNeg `sepBy` char '&'
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

wtf :: Prop → Annotation
wtf (φ :→ _ :→ φ')
    | φ == φ'                                           = Axiom 1
wtf ((φ'' :→ ψ'') :→ (φ :→ ψ :→ π) :→ (φ' :→ π'))
    | ψ == ψ'' && φ == φ' && φ == φ'' && π == π'        = Axiom 2
wtf (φ :→ ψ :→ (φ' :& ψ'))
    | φ == φ' && ψ == ψ'                                = Axiom 3
wtf (φ :& _ :→ φ')
    | φ == φ'                                           = Axiom 4
wtf ((_ :& ψ) :→ ψ')
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
wtf _ = None

findinlist :: [(Int, Prop)] → Prop → Maybe (Int, Prop)
findinlist xs a = find (\x → a == snd x) xs

findMP :: [(Int, Prop)] → Prop → Maybe ((Int, Prop), (Int, Prop))
findMP ((n, φ@(a :→ b)) : xs) b' | b == b', left ≠ Nothing
                = (, (n, φ)) <$> left where left = findinlist xs a
findMP ((n, a) : xs) b | left ≠ Nothing
                = ((n, a), ) <$> left where left = findinlist xs (a :→ b)
findMP (_:xs) p = findMP xs p
findMP [] _ = Nothing

-- annotate assumptions proven prop
annotate :: [Prop] -> [(Int, Prop)] → Prop → Annotation
annotate _ _ (wtf → Axiom i) = Axiom i
annotate _ proven (findMP proven → Just (a, b)) = MP a b
annotate assumptions _ a | a `elem` assumptions = Assumption
annotate _ _ _ = None

annotateList :: [Prop] -> [(Int, Prop)] → [(Int, Prop, Annotation)]
annotateList _ [] = []
annotateList assumptions ((n, φ) : xs)  = (n, φ, annotatedHead) : annotatedTail
                               where annotatedTail = annotateList assumptions xs
                                     annotatedHead = annotate assumptions xs φ

implyItself :: Prop -> [Prop]
implyItself α =
  [ (α :→ α :→ α) :→ (α :→ (α :→ α) :→ α) :→ (α :→ α) -- Axiom 2
  , α :→ α :→ α                                       -- Axiom 1
  , (α :→ (α :→ α) :→ α) :→ (α :→ α)                  -- MP
  , α :→ (α :→ α) :→ α                                -- Axiom 1
  , α :→ α                                            -- MP
  ]

-- imply (α:Γ) (prop, a) produces `Γ ⊢ α → prop` given `α:Γ ⊢ prop`
imply :: [Prop] → (Prop, Annotation) → [Prop]
imply (α:assumptions) (δ, annotation) | δ `elem` assumptions || isAxiom annotation =
    [
        δ :→ α :→ δ,                                       -- Axiom 1
        δ,                                                 -- Assumption
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
imply [] _ = error "assumptions list expected to be non-empty!"
imply a b = trace ("imply " ++ show a ++ " " ++ show b) $ error "wrong statement"

-- | Gets list of assumptions and list of the statements; returns the tail of assumptions and the appropriate implication
deduce :: [Prop] → [Prop] → ([Prop], [Prop])
deduce assumptions props = (tail assumptions, (imply assumptions . \(_, φ, a) → (φ, a)) =<< annotated)
    where
        annotated = (reverse . annotateList assumptions . reverse) (zip [1..] props)

contraposition :: Prop -> [Prop]
contraposition (α :→ β) = snd $ uncurry deduce $ deduce [Neg β, α :→ β] intermediate
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
excludedMiddle :: Prop -> [Prop]
excludedMiddle α = concat
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

-- given Γ, a ⊢ x and Γ, ¬a ⊢ x, implies Γ ⊢ x
hypothesisExclusion :: ([Prop], [Prop]) -> ([Prop], [Prop]) -> [Prop]
hypothesisExclusion (γ1, pos) (γ2, neg) = let α = last pos
                                              ρ = head γ1
                                          in concat
  [ snd  $ deduce γ1 pos
  , snd  $ deduce γ2 neg
  , pure $ (ρ :→ α) :→ (Neg ρ :→ α) :→ (ρ :| Neg ρ) :→ α -- Axiom 8
  , pure $ (Neg ρ :→ α) :→ (ρ :| Neg ρ) :→ α             -- MP
  , pure $ (ρ :| Neg ρ) :→ α                             -- MP
  , excludedMiddle ρ
  , pure α                                               -- MP
  ]
