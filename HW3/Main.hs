{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.List hiding (union)
import Data.Set (Set, union, singleton, toAscList, size)
import Data.Text.IO
import Data.Text (pack)
import Prelude hiding (getLine, putStrLn, readFile)
import Prelude.Unicode
import System.Environment

import Data.Map.Strict (Map, fromAscList, (!))

import Propositions

variables :: Prop → Set String
variables (φ :→ ψ) = union (variables φ) (variables ψ)
variables (φ :| ψ) = union (variables φ) (variables ψ)
variables (φ :& ψ) = union (variables φ) (variables ψ)
variables (Neg φ)  = variables φ
variables (Var α)  = singleton α

evaluate :: Prop → Map String Bool → Bool
evaluate (φ :→ ψ) values = not (evaluate φ values) || (evaluate ψ values)
evaluate (φ :& ψ) values = (evaluate φ values) && (evaluate ψ values)
evaluate (φ :| ψ) values = (evaluate φ values) || (evaluate ψ values)
evaluate (Neg φ)  values = not (evaluate φ values)
evaluate (Var α)  values = values ! α

parseFile :: FilePath → IO Prop
parseFile = (fmap parseP) ∘ readFile


assignments :: Set String → [Map String Bool]
assignments vars = [fromAscList (zip varsList vals) | vals ← sequence $ replicate n [False, True]]
    where
        n = size vars
        varsList = toAscList vars

main :: IO ()
main = do
    expr ← parseFile <$> head <$> getArgs
    vars ← variables <$> expr
    putStrLn $ pack $ show $ assignments vars
