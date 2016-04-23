{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module TT4 where
import Utils
import Lambdas
import Data.Function
import Data.Function.Memoize
import Data.ByteString.Char8 (readFile)
import Prelude hiding (readFile)
-- import Debug.Trace

reduce :: Lambda → Lambda
-- reduce lam | trace ("reduce " ++ show lam) False = undefined
reduce (Lambda v λ) = Lambda v $ reduce λ
reduce (Application lhs rhs) = case normalLhs of
      Lambda v λ → reduce $ substitute v rhs λ
      _          → (Application `on` reduce) normalLhs rhs
      where normalLhs = innovativeHnf lhs
reduce v = v

instance Memoizable Lambda where
  memoize = $(deriveMemoize ''Lambda)

subst = memoize3 substitute

hnf :: Lambda → Lambda
hnf (Lambda v λ) = Lambda v $ innovativeHnf λ
hnf (Application lhs rhs) = case normalLhs of
      Lambda v λ → hnf $ subst v rhs λ
      _          → Application normalLhs rhs
      where normalLhs = innovativeHnf lhs
hnf v = v

innovativeHnf = hnf


main :: IO ()
main = do
    input ← readFile "task4.in"
    let lam = parseBS parseLambda $ input
    let ans = hnf lam
    writeFile "task4.out" $ show ans ++ "\n"
