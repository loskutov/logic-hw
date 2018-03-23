{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax     #-}
import           Data.Attoparsec.Internal.Types (Parser)
import           Data.Attoparsec.Text           (char, sepBy, string)
import           Data.List                      (intercalate)
import qualified Data.Set                       as S
import qualified Data.SetMap                    as SM
import           Data.Text                      (Text)
import           System.Environment

import           Predicates
import           Utils

parseTitle :: Parser Text ([Prop], Prop)
parseTitle = do
    assumptions ← parseExpr `sepBy` char ','
    () <$ string "|-"
    toImply ← parseExpr
    pure (reverse assumptions, toImply)

parseFile :: FilePath → IO (([Prop], Prop), [Prop])
parseFile filename = do
    l:ls ← readLines filename
    pure (parseText parseTitle l, map parseP ls)

main :: IO ()
main = do
    ((assumptions, toImply), props) ← parseFile =<< head <$> getArgs
    case 'a' of
      'a' -> case deduce assumptions props of
          Right implies -> do
            putStrLn $ intercalate "," (reverse $ tail $ map show assumptions) ++ "|-" ++ show (head assumptions :→ toImply)
            (putStr . unlines . map show) implies
          Left i -> putStrLn $ "Вывод некорректен начиная с формулы номер " ++ show (i + 1)
      'b' -> do
        let ann = zipWith (\a (b, c) -> (a, b, c)) [1..] $ (reverse . either undefined id . annotateList assumptions . reverse) props
        printAnnotationList ann
      'c' -> do
        let a = parseP "(a+0=a)"
        let t = parseP "(t+0=t)"
        -- print $ substType S.empty t a "a"
        print $ annotate [] S.empty SM.empty (Forall "a" a :→ t)

formatAnnotation :: (Int, Prop, Annotation) → String
formatAnnotation (i, p, s) = "(" ++ show i ++ ") " ++ show p ++ " (" ++ show s ++ ")"

printAnnotationList :: [(Int, Prop, Annotation)] → IO ()
printAnnotationList = mapM_ (putStrLn . formatAnnotation)
