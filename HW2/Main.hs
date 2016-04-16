{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Data.Attoparsec.Text (char, string, sepBy)
import Data.Attoparsec.Internal.Types (Parser)
import Data.List
import Data.Maybe (fromJust)
import Data.Text (Text)
import Prelude.Unicode
import System.Environment

import Propositions
import Utils

parseTitle :: Parser Text ([Prop], Prop)
parseTitle = do
    assumptions ← parseExpr `sepBy` (char ',')
    string "|-"
    toImply ← parseExpr
    return $ (reverse assumptions, toImply)

imply :: [Prop] → (Prop, Annotation) → [Prop]
imply (α:assumptions) (δ, annotation) | (δ `elem` assumptions) || (isAxiom annotation) =
    [
        δ,
        δ :→ α :→ δ,
        α :→ δ
    ]
imply (α:assumptions) (δ, _) | δ == α =
    [
        α :→ α :→ α,                                         -- Axiom 1
        (α :→ (α :→ α)) :→ (α :→ (α :→ α) :→ α) :→ (α :→ α), -- Axiom 2
        (α :→ (α :→ α) :→ α) :→ (α :→ α),                    -- MP
        α :→ (α :→ α) :→ α,                                  -- Axiom 1
        α :→ α                                               -- MP
    ]
imply (α:assumptions) (δ, MP (_, φ) _) =
    [
        (α :→ φ) :→ (α :→ φ :→ δ) :→ (α :→ δ),               -- Axiom 2
        ((α :→ (φ :→ δ)) :→ (α :→ δ)),                       -- MP
        α :→ δ
    ]
imply [] _ = error "assumptions list expected to be non-empty!"
imply _ _ = error "wrong statement"

-- | Returns ([assumptions, propositions])
parseFile :: FilePath → IO (([Prop], Prop), [Prop])
parseFile filename = do
    l:ls ← readLines filename
    return $ (parseText parseTitle l, map parseP ls)

-- | Gets list of assumprions and list of the statements; returns the tail of assumptions and the appropriate implication
deduct :: [Prop] → [Prop] → ([Prop], [Prop])
deduct assumptions props = (tail assumptions, concat $ map (imply assumptions ∘ \(_, φ, a) → (φ, a)) annotated)
    where
        annotated = (reverse . fromJust . annotateList . reverse) (zip [1..] props)

main :: IO ()
main = do
    ((assumptions, toImply), props) ← parseFile =<< head <$> getArgs
    let (_,implies) = deduct assumptions props
    putStrLn $ intercalate "," (reverse $ tail $ map show assumptions) ++ "|-" ++ show (head assumptions :→ toImply)
    putStr $ unlines $ map show implies
