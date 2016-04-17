{-# LANGUAGE UnicodeSyntax #-}
import Utils
import Lambdas
import Data.Set
import Data.Text (pack)

main :: IO ()
main = do
    input ← readFile "task2.in"
    let λ = parseText parseLambda $ pack input
    let free = freeVars λ
    writeFile "task2.out" $ unlines $ elems free
