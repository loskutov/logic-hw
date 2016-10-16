{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE UnicodeSyntax     #-}
import           Control.Monad.State
import           Data.ByteString.Char8 (readFile)
import           Data.Function
import qualified Data.Map.Strict       as M
-- import           Data.Function.Memoize
import           Debug.Trace
import           Lambdas
import           Prelude               hiding (readFile)
import           Utils

type Cache = M.Map Lambda Lambda

reduce :: Lambda → Cache → Lambda
reduce l _ | trace ("slowly reducing" ++ (show l) ++ "\n\n\n") False = undefined
reduce (Lambda v λ) c = Lambda v $! reduce λ c
reduce (Application lhs rhs) c = case normalLhs of
      Lambda v λ → reduce (substitute v rhs λ) c'
      _          → Application normalLhs rhs
      where (c', normalLhs) = memedHnf c lhs
reduce v _ = v

-- hnf :: Lambda → Lambda
-- hnf (Lambda v λ) = Lambda v $ hnf λ
-- hnf (Application lhs rhs) = case normalLhs of
--       Lambda v λ → hnf $ substitute v rhs λ
--       _          → Application normalLhs rhs
--       where normalLhs = hnf lhs
-- hnf v = v


main :: IO ()
main = do
    input ← readFile "task4.in"
    let lam = parseBS parseLambda $ input
    let ans = reduce lam (M.empty)
    writeFile "task4.out" $ show ans ++ "\n"



memedHnf :: Cache → Lambda → (Cache, Lambda)
memedHnf _ _ | trace "memes come here" False = undefined
memedHnf oldState λ = case M.lookup λ oldState of
      Just l  → (oldState, l)
      Nothing → memedHnf' oldState λ


memedHnf' :: Cache → Lambda → (Cache, Lambda)
memedHnf' _ _ | trace "here come the memes" False = undefined
memedHnf' oldState λ = (M.insert λ normalized newState, normalized)
  where (newState, normalized) = case λ of
            Lambda v l → (newState', Lambda v ans) where (newState', ans) = memedHnf oldState l
            Application lhs rhs → case normalLhs of
                Lambda v l → memedHnf midState $ substitute v rhs l
                _          → (midState, Application normalLhs rhs)
                where (midState, normalLhs) = memedHnf oldState lhs
            v → (oldState, v)
