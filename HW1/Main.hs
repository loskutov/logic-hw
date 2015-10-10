{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Prelude.Unicode
import System.Environment
import Propositions
import Utils


parseFile :: FilePath → IO [(Int, Prop)]
parseFile filename = do
    ls ← readLines filename
    return $ map (pmap parseP) (zip [1..] ls)

annotateFile :: FilePath → IO [(Int, Prop, Annotation)]
annotateFile = (fmap $ reverse ∘ annotateList ∘ reverse) ∘ parseFile

formatAnnotation :: (Int, Prop, Annotation) → String
formatAnnotation (i, p, s) = ("(" ++ show i ++ ") " ++ show p ++ " (" ++ show s ++ ")")

main :: IO ()
main = mapM_ (putStrLn ∘ formatAnnotation) =<< annotateFile =<< head <$> getArgs
