{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE UnicodeSyntax     #-}
import           Control.Monad.State
import           Data.ByteString.Char8 (readFile)
import           Data.Function
import qualified Data.Map.Strict       as M
import           Lambdas
import           Prelude               hiding (readFile)
import           Utils

type Cache = M.Map Lambda Lambda

reduce :: Lambda → State Cache Lambda
reduce (Lambda v λ) = Lambda v <$> reduce λ
reduce (Application lhs rhs) = do
  normalLhs <- memedHnf lhs
  case normalLhs of
      Lambda v λ → reduce $ substitute v rhs λ
      _          → do reducedLhs <- reduce normalLhs
                      reducedRhs <- reduce rhs
                      pure $ Application reducedLhs reducedRhs
reduce v = pure v

memedHnf :: Lambda → State Cache Lambda
memedHnf λ = do
  cache <- get
  case M.lookup λ cache of
      Just l  → pure l
      Nothing → do ans <- memedHnf' λ
                   modify $ M.insert λ ans
                   pure ans

memedHnf' :: Lambda -> State Cache Lambda
memedHnf' (Lambda v l) = Lambda v <$> memedHnf l
memedHnf' (Application lhs rhs) = do
  normalLhs <- memedHnf lhs
  case normalLhs of
    Lambda v λ → memedHnf $ substitute v rhs λ
    _          → pure $ Application normalLhs rhs
memedHnf' v = pure v

main :: IO ()
main = do
    input ← readFile "task4.in"
    let lam = parseBS parseLambda $ input
    let ans = evalState (reduce lam) M.empty
    writeFile "task4.out" $ show ans ++ "\n"
