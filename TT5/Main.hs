{-# LANGUAGE UnicodeSyntax #-}
-- module TT5.Main where

import Data.Map.Strict (Map, empty, assocs)
import qualified Data.Set as S
import Data.ByteString.Char8 (readFile, lines)
import Prelude hiding (lookup, readFile, lines)
import TT5.Unification

import Utils (parseBS)

myshow :: (Show v) => Maybe (Map String v) → String
myshow (Just m) = concatMap (\(k, a) → k ++ "=" ++ (show a) ++ "\n") (assocs m)
myshow Nothing = "Подстановки не существует"

main :: IO ()
main = do
    input ← readFile "task5.in"
    let eqs = map (parseBS parseEquation) $ lines input
    let ans = unify S.empty eqs
    writeFile "task5.out" $ myshow ans ++ "\n"

