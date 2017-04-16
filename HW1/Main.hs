{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns  #-}
module Main where

import           Data.List
import           Prelude.Unicode
import           System.Environment

import           Propositions
import           Utils


parseFile :: FilePath → IO [(Int, Prop)]
parseFile filename = do
    ls ← readLines filename
    return $ map (fmap parseP) (zip [1..] ls)

annotateFile :: FilePath → IO [(Int, Prop, Annotation)]
annotateFile = (fmap $ reverse ∘ annotateList [] ∘ reverse) ∘ parseFile

formatAnnotation :: (Int, Prop, Annotation) → String
formatAnnotation (i, p, s) = ("(" ++ show i ++ ") " ++ show p ++ " (" ++ show s ++ ")")

printAnnotationList :: [(Int, Prop, Annotation)] → IO ()
printAnnotationList (find (\(_,_,a) -> a == None) -> Just _)  = putStrLn "Proof incorrect"
printAnnotationList xs = mapM_ (putStrLn ∘ formatAnnotation) xs

main :: IO ()
main = printAnnotationList =<< annotateFile =<< head <$> getArgs
