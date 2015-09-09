{-# LANGUAGE FlexibleContexts, ViewPatterns, FlexibleInstances #-}
module Main where

import System.IO
import System.Environment
import Parser
import Propositions
import Utils


parseFile :: FilePath -> IO [(Int, Prop)]
parseFile filename = map (pmap $ parseP) <$> zip [1..] <$> readLines filename

annotateFile :: FilePath -> IO [(Int, Prop, String)]
annotateFile filename = (reverse . annotateList . reverse) <$> parseFile filename

formatAnnotation :: (Int, Prop, String) -> String
formatAnnotation (i, p, s) = "(" ++ show i ++ ") " ++ show p ++ " (" ++ s ++ ")"

main :: IO ()
main = mapM_ (putStrLn . formatAnnotation) =<< (annotateFile =<< head <$> getArgs)
