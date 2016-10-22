{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE UnicodeSyntax     #-}
import           Data.ByteString.Char8 (readFile)
import           Data.Function
import qualified Data.Map.Strict       as M
import           Lambdas
import           Prelude               hiding (readFile)
import           Utils

type Cache = M.Map Lambda Lambda

reduce :: Cache → Lambda → (Cache, Lambda)
reduce c (Lambda v λ) = (c', Lambda v reducedLam) where (c', reducedLam) = reduce c λ
reduce c (Application lhs rhs) = case normalLhs of
      Lambda v λ → reduce c' (substitute v rhs λ)
      _          → (c''', Application reducedLhs reducedRhs)
      where (c', normalLhs) = memedHnf c lhs
            (c'', reducedLhs) = reduce c' normalLhs
            (c''', reducedRhs) = reduce c'' rhs
reduce c v = (c, v)

main :: IO ()
main = do
    input ← readFile "task4.in"
    let lam = parseBS parseLambda $ input
    let (_, ans) = reduce M.empty lam
    writeFile "task4.out" $ show ans ++ "\n"



memedHnf :: Cache → Lambda → (Cache, Lambda)
memedHnf oldState λ = case M.lookup λ oldState of
      Just l  → (oldState, l)
      Nothing → memedHnf' oldState λ


memedHnf' :: Cache → Lambda → (Cache, Lambda)
memedHnf' oldState λ = (M.insert λ normalized newState, normalized)
  where (newState, normalized) = case λ of
            Lambda v l → (newState', Lambda v ans) where (newState', ans) = memedHnf oldState l
            Application lhs rhs → case normalLhs of
                Lambda v l → memedHnf midState $ substitute v rhs l
                _          → (midState, Application normalLhs rhs)
                where (midState, normalLhs) = memedHnf oldState lhs
            v → (oldState, v)
