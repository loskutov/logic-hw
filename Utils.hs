{-# LANGUAGE UnicodeSyntax #-}
module Utils where
import Data.Attoparsec.Internal.Types (Parser)
import Data.Attoparsec.Text (parseOnly)
import Data.Text
import Data.Text.IO
import Prelude.Unicode

import Prelude hiding (lines, unlines, readFile, putStr)

parseText :: Parser Text a → Text → a
parseText parser str = case parseOnly parser str of
    Left _ → error $ "Could not parse \'" ++ (unpack str) ++ "\'"
    Right a → a


printList :: [Text] → IO ()
printList = putStr ∘ unlines

readLines :: FilePath → IO [Text]
readLines filename = lines <$> readFile filename
