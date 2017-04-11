{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax     #-}
module Main where

import           Data.Attoparsec.Internal.Types (Parser)
import           Data.Attoparsec.Text           (char, sepBy, string)
import           Data.List
import           Data.Text                      (Text)
import           System.Environment

import           Propositions
import           Utils

parseTitle :: Parser Text ([Prop], Prop)
parseTitle = do
    assumptions ← parseExpr `sepBy` char ','
    () <$ string "|-"
    toImply ← parseExpr
    pure (reverse assumptions, toImply)

-- | Returns ([assumptions, propositions])
parseFile :: FilePath → IO (([Prop], Prop), [Prop])
parseFile filename = do
    l:ls ← readLines filename
    pure (parseText parseTitle l, map parseP ls)


main :: IO ()
main = do
    ((assumptions, toImply), props) ← parseFile =<< head <$> getArgs
    let (_, implies) = deduce assumptions props
    putStrLn $ intercalate "," (reverse $ tail $ map show assumptions) ++ "|-" ++ show (head assumptions :→ toImply)
    (putStr . unlines . map show) implies
