{-# LANGUAGE UnicodeSyntax #-}
module Utils where
import Data.Text
import Data.Text.IO
import Prelude.Unicode

import Prelude hiding (lines, unlines, readFile, putStr)

printList :: [Text] → IO ()
printList = putStr ∘ unlines

readLines :: FilePath → IO [Text]
readLines filename = lines <$> readFile filename
