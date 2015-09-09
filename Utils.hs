module Utils where

printList :: [String] -> IO ()
printList = putStr . unlines

readLines :: FilePath -> IO [String]
readLines filename = lines <$> readFile filename
