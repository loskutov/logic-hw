{-# LANGUAGE UnicodeSyntax #-}
import Utils
import Lambdas
import Data.Text

main :: IO ()
main = do
    input ← readFile "task1.in"
    let λ = parseText parseLambda $ pack input
    writeFile "task1.out" $ show λ ++ "\n"
