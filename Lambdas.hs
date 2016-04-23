 {-# LANGUAGE UnicodeSyntax #-}
 {-# LANGUAGE OverloadedStrings #-}
module Lambdas where

import Control.Applicative
import Control.Monad
-- import Data.Attoparsec.ByteString (satisfy, sepBy1, option)
import Data.Attoparsec.ByteString.Char8
-- import Data.Attoparsec.Internal.Types (Parser)
import Data.Function
import Data.Set hiding (map)
import Data.Char (isAsciiLower)

import Utils

data Lambda = Application Lambda Lambda
            | Var String
            | Lambda String Lambda

instance Show Lambda where
  show (Application λ1 λ2) = "(" ++ (show λ1) ++ " " ++ (show λ2) ++ ")"
  show (Var s) = s
  show (Lambda s λ) = "(\\" ++ s ++ "." ++ (show λ) ++ ")"

parseExpr :: Parser Lambda
parseExpr = skipSpace *> (parseApplication <|> parseHnf) <* skipSpace

parseHnf :: Parser Lambda
parseHnf = skipSpace *> (parseAbstraction <|> parseVar <|> char8 '(' *> parseExpr <* char8 ')')

parseAbstraction :: Parser Lambda
parseAbstraction = do
  Var var ← char8 '\\' *> parseVar
  rhs ← char8 '.' *> parseExpr
  return $ Lambda var rhs

parseLambda :: Parser Lambda
parseLambda = parseExpr

parseApplication :: Parser Lambda
parseApplication = do
  atoms ← parseHnf `sepBy1'` space
  return $ foldl1 Application atoms

parseAtom :: Parser Lambda
parseAtom = skipSpace *> (char '(' *> parseLambda <* skipSpace <* char ')' <|> parseVar)

parseVar :: Parser Lambda
parseVar = do
    letter ← satisfy isAsciiLower
    others ← many' $ satisfy $ liftM3 (\x y z → x || y || z) isAsciiLower isDigit (=='\'')
    return $ Var $ letter:others

freeVars :: Lambda → Set String
freeVars (Var s)             = singleton s
freeVars (Application λ1 λ2) = (freeVars λ1) ∪ (freeVars λ2)
freeVars (Lambda s λ)        = (freeVars λ)  ∖ (singleton s)


rename :: String → String
rename = (++ "$")

-- | `substitute old new λ` substitutes `old` with `new` in `λ`
substitute :: String → Lambda → Lambda → Lambda
substitute old new v@(Var s) | s == old  = new
                             | otherwise = v
substitute old new l@(Lambda s λ) | s == old               = l
                                  | s ∈ free || old ∈ free = Lambda newName $ (substitute old new . substitute s (Var newName)) λ
                                  | otherwise              = Lambda s $ substitute old new λ
                                     where newName = rename s
                                           free = freeVars new
substitute s λ (Application λ1 λ2) = (Application `on` substitute s λ) λ1 λ2
