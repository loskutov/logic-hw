{-# LANGUAGE ViewPatterns #-}
module Propositions where

import Parser
import Control.Applicative
import Control.Monad.State
import Data.List

data Prop = Prop :→ Prop
          | Prop :| Prop
          | Prop :& Prop
          | Neg Prop
          | Var String
          deriving Eq

instance Show Prop where
    show (x :→ y) = '(' : show x ++ "->" ++ show y ++ ")"
    show (x :| y) = '(' : show x ++ "|" ++ show y ++ ")"
    show (x :& y) = '(' : show x ++ "&" ++ show y ++ ")"
    show (Neg x) = '!' : show x
    show (Var x) = x

data Annotation = MP Integer Integer
                | Axiom Integer
                | Proven Integer
                | None
                deriving Show

parseVar :: Apar Prop
parseVar = Var <$> parseVarName

parseNot :: Apar Prop
parseNot = parseVar <|> Neg <$> after (lexem $ char '!') parseNot <|> between (lexem (char '(')) parseImpl (lexem (char ')'))

parseImpl :: Apar Prop
parseImpl = (foldr1 (:→)) <$> manySepBy parseDisj (lexem $ twochars '-' '>')

parseDisj :: Apar Prop
parseDisj = (foldl1 (:|)) <$> manySepBy parseConj (lexem $ char '|')

parseConj :: Apar Prop
parseConj = (foldl1 (:&)) <$> manySepBy parseNot (lexem $ char '&')


parseP :: String -> Prop
parseP str = case runStateT parseImpl str of
  Nothing -> Var ("")
  Just (u, i) -> u

wtf :: Prop -> Maybe Annotation
wtf (φ :→ (ψ :→ φ'))
    | φ == φ'                                           = Just $ Axiom 1
wtf ((φ'' :→ ψ'') :→ ((φ :→ (ψ :→ π)) :→ (φ' :→ π')))
    | ψ == ψ'' && φ == φ' && φ == φ'' && π == π'        = Just $ Axiom 2
wtf (φ :→ (ψ :→ (φ' :& ψ')))
    | φ == φ' && ψ == ψ'                                = Just $ Axiom 3
wtf ((φ :& ψ) :→ φ')
    | φ == φ'                                           = Just $ Axiom 4
wtf ((φ :& ψ) :→ ψ')
    | ψ == ψ'                                           = Just $ Axiom 5
wtf (φ' :→ (φ :| ψ))
    | φ == φ'                                           = Just $ Axiom 6
wtf (ψ' :→ (φ :| ψ))
    | ψ == ψ'                                           = Just $ Axiom 7
wtf ((φ :→ π) :→ ((ψ :→ π'') :→ ((φ' :| ψ') :→ π')))
    | φ == φ' && ψ == ψ' && π == π' && π == π''         = Just $ Axiom 8
wtf ((φ :→ ψ) :→ ((φ' :→ (Neg ψ')) :→ (Neg φ'')))
    | ψ == ψ' && φ == φ' && φ == φ''                    = Just $ Axiom 9
wtf ((Neg (Neg φ)) :→ φ')
    | φ == φ'                                           = Just $ Axiom 10
wtf _ = Nothing

findinlist :: [(Int, Prop)] -> Prop -> Maybe Int
findinlist xs a = fst <$> find (\x -> a == snd x) xs

findMP :: [(Int, Prop)] -> Prop -> Maybe (Int, Int)
findMP ((n, (a :→ b)) : xs) b' | b == b', findinlist xs a /= Nothing
                = (\i -> (i, n)) <$> (findinlist xs a)
findMP ((n, a) : xs) b | findinlist xs (a :→ b) /= Nothing
                = (\i -> (n, i)) <$> (findinlist xs (a :→ b))
findMP (x:xs) p = findMP xs p
findMP [] _ = Nothing

annotate :: [(Int, Prop)] -> (Int, Prop) -> String
annotate xs (n, φ@(wtf -> Just (Axiom i))) = "Сх. акс. " ++ show i
annotate xs (n, φ@(findMP xs -> Just (a, b))) = "M.P. " ++ show a ++ ", " ++ show b
annotate xs _ = "Не доказано"

pmap f (n, a) = (n, f a)  -- unfortunately, I can not make a pair an instance of Functor ;(

annotateList :: [(Int, Prop)] -> [(Int, Prop, String)]
annotateList [] = []
annotateList (x:xs) = (fst x, snd x, annotate xs x) : annotateList xs

