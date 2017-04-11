{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Prelude.Unicode
import System.Environment
import Propositions
import Utils


parseFile :: FilePath → IO [(Int, Prop)]
parseFile filename = do
    ls ← readLines filename
    return $ map (fmap parseP) (zip [1..] ls)

annotateFile :: FilePath → IO (Maybe [(Int, Prop, Annotation)])
annotateFile = (fmap $ (reverse <$>) ∘ annotateList [] ∘ reverse) ∘ parseFile

formatAnnotation :: (Int, Prop, Annotation) → String
formatAnnotation (i, p, s) = ("(" ++ show i ++ ") " ++ show p ++ " (" ++ show s ++ ")")

printAnnotationList :: Maybe [(Int, Prop, Annotation)] → IO ()
printAnnotationList  Nothing  = putStrLn "Proof incorrect"
printAnnotationList (Just xs) = mapM_ (putStrLn ∘ formatAnnotation) xs

main :: IO ()
main = printAnnotationList =<< annotateFile =<< head <$> getArgs
