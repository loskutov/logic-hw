 {-# LANGUAGE UnicodeSyntax #-}
 {-# LANGUAGE OverloadedStrings #-}
module Lambdas where

import Control.Applicative
import Control.Monad
import Data.Attoparsec.Text (char, skipSpace, space, satisfy, sepBy1, option)
import Data.Attoparsec.Internal.Types (Parser)
import Data.Set
import Data.Text hiding (foldl1, foldr1, find, singleton)
import Data.Char

import Utils

data Lambda = Application Lambda Lambda
            | Var String
            | Lambda String Lambda

instance Show Lambda where
  show (Application λ1 λ2) = "(" ++ (show λ1) ++ " " ++ (show λ2) ++ ")"
  show (Var s) = s
  show (Lambda s λ) = "(\\" ++ s ++ "." ++ (show λ) ++ ")"

parseLambda :: Parser Text Lambda
parseLambda = do
  skipSpace
  app ← option id $ Application <$> parseApplication <* skipSpace
  Var var ← char '\\' *> skipSpace *> parseVar
  skipSpace *> char '.' *> skipSpace
  λ ← parseLambda
  return $ app $ Lambda var λ
  <|> parseApplication

parseApplication :: Parser Text Lambda
parseApplication = do
  atoms ← parseAtom `sepBy1` space
  return $ foldl1 Application atoms

parseAtom :: Parser Text Lambda
parseAtom = skipSpace *> (char '(' *> parseLambda <* skipSpace <* char ')' <|> parseVar)

parseVar :: Parser Text Lambda
parseVar = do
    letter ← satisfy isAsciiLower
    others ← many $ satisfy $ liftM3 (\x y z -> x || y || z) isAsciiLower isDigit (=='\'')
    return $ Var $ letter:others

freeVars :: Lambda → Set String
freeVars (Var s)             = singleton s
freeVars (Application λ1 λ2) = (freeVars λ1) ∪ (freeVars λ2)
freeVars (Lambda s λ)        = (freeVars λ)  ∖ (singleton s)
