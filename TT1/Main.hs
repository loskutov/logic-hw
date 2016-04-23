{-# LANGUAGE UnicodeSyntax #-}
import Utils
import Lambdas
import Data.ByteString (readFile)
import Prelude hiding (readFile)

main :: IO ()
main = do
    input ← readFile "task1.in"
    let λ = parseBS parseLambda input
    writeFile "task1.out" $ show λ ++ "\n"
