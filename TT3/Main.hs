{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE OverloadedStrings #-}
import Utils
import Lambdas
import Data.Attoparsec.ByteString.Char8 (Parser, char, string)
import Data.Function
import Data.ByteString (readFile)
import Prelude hiding (readFile)

parseTask :: Parser (Lambda, String, Lambda)
parseTask = do
  λ ← parseLambda <* char '['
  (Var var) ← parseVar <* string ":="
  subst ← parseLambda <* char ']'
  return (λ, var, subst)

main :: IO ()
main = do
    input ← readFile "task3.in"
    let (λ, s, r) = parseBS parseTask $ input
    let free = freeVars λ
    let ans = if (s ∉ free) then "Нет свободы для подстановки переменной " ++ s else show (substitute s r λ)
    writeFile "task3.out" $ ans ++ "\n"
