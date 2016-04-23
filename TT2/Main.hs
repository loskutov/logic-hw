{-# LANGUAGE UnicodeSyntax #-}
import Utils
import Lambdas
import Data.Set
import Prelude hiding (readFile)
import Data.ByteString (readFile)

main :: IO ()
main = do
    input ← readFile "task2.in"
    let λ = parseBS parseLambda input
    let free = freeVars λ
    writeFile "task2.out" $ unlines $ elems free
