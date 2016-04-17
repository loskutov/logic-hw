{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE OverloadedStrings #-}
import Utils
import Lambdas
import Data.Attoparsec.Text (char, string)
import Data.Attoparsec.Internal.Types (Parser)
import Data.Function
import Data.Text (Text)
import Data.Text.IO (readFile)
import Prelude hiding (readFile)

parseTask :: Parser Text (Lambda, String, Lambda)
parseTask = do
  λ ← parseLambda <* char '['
  (Var var) ← parseVar <* string ":="
  subst ← parseLambda <* char ']'
  return (λ, var, subst)

-- | `substitute λ var` new substitutes `new` instead of `var` to `λ`
substitute :: String → Lambda → Lambda -> Lambda
substitute s' λ v@(Var s) | s == s'   = λ
                          | otherwise = v
substitute s' λ' l@(Lambda s λ) | s == s' = l
                                | otherwise = Lambda s (substitute s' λ' λ)
substitute s λ (Application λ1 λ2) = (Application `on` (substitute s λ)) λ1 λ2

main :: IO ()
main = do
    input ← readFile "task3.in"
    let (λ, s, r) = parseText parseTask $ input
    let free = freeVars λ
    let ans = if (s ∉ free) then "Нет свободы для подстановки переменной " ++ s else show (substitute s r λ)
    writeFile "task3.out" $ ans ++ "\n"
