{-# LANGUAGE UnicodeSyntax #-}
module Utils where
import           Data.Attoparsec.Internal.Types (Parser)
import           Data.Attoparsec.Text (parseOnly)
import qualified Data.Attoparsec.ByteString.Char8
import qualified Data.ByteString.Char8 
import           Data.ByteString (ByteString)
import           Data.Set
import           Data.Text
import           Data.Text.IO
import           Prelude.Unicode

import Prelude hiding (lines, unlines, readFile, putStr)

parseText :: Parser Text a → Text → a
parseText parser str = case parseOnly parser str of
    Left _ → error $ "Could not parse \'" ++ (unpack str) ++ "\'"
    Right a → a

parseBS :: Data.Attoparsec.ByteString.Char8.Parser a → ByteString → a
parseBS parser str = case Data.Attoparsec.ByteString.Char8.parseOnly parser str of
    Left _ → error $ "Could not parse \'" ++ (Data.ByteString.Char8.unpack str) ++ "\'"
    Right a → a


printList :: [Text] → IO ()
printList = putStr . unlines

readLines :: FilePath → IO [Text]
readLines filename = lines <$> readFile filename

(∪) :: Ord α => Set α -> Set α -> Set α 
(∪) = union

(∖) :: Ord α => Set α -> Set α -> Set α
(∖) = difference

(∉) :: Ord α => α -> Set α -> Bool
(∉) = notMember

(∈) :: Ord α => α -> Set α -> Bool
(∈) = member
