{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module Propositions where

import Control.Applicative
import Data.Attoparsec.Text (string, char, satisfy, sepBy)
import Data.Attoparsec.Internal.Types (Parser)
import Data.Eq.Unicode
import Data.Text hiding (foldl1, foldr1, find)
import Data.Char
import Data.List (find)
import Utils

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
    show (Axiom a) = "Сх. акс. " ++ show a
    show None = "Не доказано"
    show Assumption = "Допущение"

parseExpr :: Parser Text Prop
parseExpr = do
    disjs ← parseDisj `sepBy` (string "->")
    if disjs == [] then
        fail "no disjuctions, so sad"
    else return $ foldr1 (:→) disjs
    where
        parseVar = do
            letter ← satisfy isAsciiUpper
            numbers ← many $ satisfy isDigit
            return $ Var (letter : numbers)

        parseNeg = parseVar <|> Neg <$> (char '!' *> parseNeg) <|> (char '(' *> parseExpr <* char ')')

        parseConj = do
            negations ← parseNeg `sepBy` (char '&')
            if negations == [] then
                fail "no negations, so sad"
            else return $ foldl1 (:&) negations

        parseDisj = do
            conjs ← parseConj `sepBy` (char '|')
            if conjs == [] then
                fail "no conjuctions, so sad"
            else return $ foldl1 (:|) conjs

parseP :: Text → Prop
parseP = parseText parseExpr

wtf :: Prop → Annotation
wtf (φ :→ _ :→ φ')
    | φ == φ'                                           = Axiom 1
wtf ((φ'' :→ ψ'') :→ (φ :→ ψ :→ π) :→ (φ' :→ π'))
    | ψ == ψ'' && φ == φ' && φ == φ'' && π == π'        = Axiom 2
wtf (φ :→ ψ :→ (φ' :& ψ'))
    | φ == φ' && ψ == ψ'                                = Axiom 3
wtf (φ :& ψ :→ φ')
    | φ == φ'                                           = Axiom 4
wtf ((φ :& ψ) :→ ψ')
    | ψ == ψ'                                           = Axiom 5
wtf (φ' :→ (φ :| ψ))
    | φ == φ'                                           = Axiom 6
wtf (ψ' :→ (φ :| ψ))
    | ψ == ψ'                                           = Axiom 7
wtf ((φ :→ π) :→ ((ψ :→ π'') :→ ((φ' :| ψ') :→ π')))
    | φ == φ' && ψ == ψ' && π == π' && π == π''         = Axiom 8
wtf ((φ :→ ψ) :→ ((φ' :→ (Neg ψ')) :→ (Neg φ'')))
    | ψ == ψ' && φ == φ' && φ == φ''                    = Axiom 9
wtf ((Neg (Neg φ)) :→ φ')
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

annotate :: [(Int, Prop)] → (Int, Prop) → Annotation
annotate _ (_, (wtf → Axiom i)) = Axiom i
annotate xs (_, (findMP xs → Just ((a, ϕ), (b, ψ)))) = MP (a, ϕ) (b, ψ)
annotate _ _ = None

annotateList :: [(Int, Prop)] → Maybe [(Int, Prop, Annotation)]
annotateList [] = Just []
annotateList (x@(n, φ) : xs) | annotatedHead == None = Nothing
                             | otherwise             = ((n, φ, annotatedHead) :) <$> annotatedTail
                               where annotatedTail = annotateList xs
                                     annotatedHead = annotate xs x

