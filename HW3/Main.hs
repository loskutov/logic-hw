{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax     #-}
{-# LANGUAGE ViewPatterns      #-}
module Main where

import           Control.Applicative (pure)
import           Control.Monad       (replicateM, (=<<))
import           Data.Bool           (Bool (..), not, otherwise, (&&), (||))
import           Data.Either
import           Data.Function       (id, ($), (.))
import           Data.Functor        ((<$>))
import           Data.List           (find, head, intercalate, unlines, zip,
                                      (++))
import           Data.Map.Strict     ((!))
import qualified Data.Map.Strict     as M
import qualified Data.Set            as S
import           Data.String         (String)
import           Data.Text.IO        (readFile)
import           Data.Tuple          (snd)
import           Prelude             (Maybe (..), show, undefined)
import           System.Environment  (getArgs)
import           System.IO           (FilePath, IO, putStr)

import           Propositions

variables :: Prop → S.Set String
variables (φ :→ ψ) = variables φ `S.union` variables ψ
variables (φ :| ψ) = variables φ `S.union` variables ψ
variables (φ :& ψ) = variables φ `S.union` variables ψ
variables (Neg φ)  = variables φ
variables (Var α)  = S.singleton α

evaluate :: Prop → M.Map String Bool → Bool
evaluate (φ :→ ψ) values = not (evaluate φ values) || evaluate ψ values
evaluate (φ :& ψ) values = evaluate φ values && evaluate ψ values
evaluate (φ :| ψ) values = evaluate φ values || evaluate ψ values
evaluate (Neg φ)  values = not (evaluate φ values)
evaluate (Var α)  values = values ! α

parseFile :: FilePath → IO Prop
parseFile = (parseP <$>) . readFile

-- a |- !!a
aToNegNegA :: Prop -> [Prop]
aToNegNegA a = implyItself (Neg a) ++
  [ a
  , a :→ Neg a :→ a
  , Neg a :→ a
  , (Neg a :→ a) :→ (Neg a :→ Neg a) :→ Neg (Neg a)
  , (Neg a :→ Neg a) :→ Neg (Neg a)
  , Neg (Neg a)
  ]
-- Proves the given proposition or its negation given the assignments of vars
proveOrDisprove :: M.Map String Bool -> Prop -> Either [Prop] [Prop]
proveOrDisprove vars (a@(proveOrDisprove vars -> Right as) :| b) = Right $ as ++
  [ a :→ a :| b -- Axiom
  , a :| b      -- MP
  ]
proveOrDisprove vars (a :| b@(proveOrDisprove vars -> Right bs)) = Right $ bs ++
  [ b :→ a :| b
  , a :| b
  ]
proveOrDisprove vars (a@(proveOrDisprove vars -> Left as) :| b@(proveOrDisprove vars -> Left bs)) = Left $ as ++ bs ++
  implyItself a ++
  [ (a :| b :→ a) :→ (a :| b :→ Neg a) :→ Neg (a :| b)     -- Axiom
  , Neg a :→ a :| b :→ Neg a                               -- Axiom 1
  , a :| b :→ Neg a                                        -- MP
  ] ++ either undefined id (proveOrDisprove vars (b :→ a)) ++
  [ (a :→ a) :→ (b :→ a) :→ (a :| b :→ a)  -- Axiom
  , (b :→ a) :→ (a :| b :→ a)              -- MP
  , a :| b :→ a                            -- MP
  , (a :| b :→ Neg a) :→ Neg (a :| b)      -- MP
  , Neg (a :| b)
  ]
proveOrDisprove vars (a@(proveOrDisprove vars -> Right as) :& b@(proveOrDisprove vars -> Right bs)) = Right $ as ++ bs ++
  [ a :→ b :→ a :& b
  , b :→ a :& b
  , a :& b
  ]
proveOrDisprove vars (a :& b@(proveOrDisprove vars -> Left bs)) = Left $ bs ++
  [ (a :& b :→ b) :→ (a :& b :→ Neg b) :→ Neg (a :& b)
  , a :& b :→ b
  , (a :& b :→ Neg b) :→ Neg (a :& b)
  , Neg b :→ a :& b :→ Neg b
  , a :& b :→ Neg b                   -- MP
  , Neg (a :& b)
  ]
proveOrDisprove vars (a@(proveOrDisprove vars -> Left as) :& b) = Left $ as ++
  [ (a :& b :→ a) :→ (a :& b :→ Neg a) :→ Neg (a :& b)
  , a :& b :→ a
  , (a :& b :→ Neg a) :→ Neg (a :& b)
  , Neg a :→ a :& b :→ Neg a
  , a :& b :→ Neg a                   -- MP
  , Neg (a :& b)
  ]
proveOrDisprove vars (a :→ b@(proveOrDisprove vars -> Right bs)) = Right $ bs ++
  [ b :→ a :→ b
  , a :→ b
  ]
proveOrDisprove vars (a@(proveOrDisprove vars -> Right as) :→ b@(proveOrDisprove vars -> Left bs)) = Left $ as ++ bs ++
  snd (deduce [a :→ b, a] [a, a :→ b, b]) ++
  [ Neg b :→ (a :→ b) :→ Neg b
  , (a :→ b) :→ Neg b
  , ((a :→ b) :→ b) :→ ((a :→ b) :→ Neg b) :→ Neg (a :→ b)
  , ((a :→ b) :→ Neg b) :→ Neg (a :→ b)
  , Neg (a :→ b)
  ]
proveOrDisprove vars (a@(proveOrDisprove vars -> Left _) :→ b@(proveOrDisprove vars -> Left _)) = Right $
  contraposition (Neg b :→ Neg a) ++
  either undefined id (proveOrDisprove vars (Neg b :→ Neg a)) ++
  snd (deduce [a, Neg (Neg a) :→ Neg (Neg b)] (aToNegNegA a ++
       [ Neg (Neg a) :→ Neg (Neg b)
       , Neg (Neg b)
       , Neg (Neg b) :→ b
       , b
       ])) ++
  [ a :→ b ]
proveOrDisprove vars (Neg (proveOrDisprove vars -> Left as)) = Right as
proveOrDisprove vars (Neg a@(proveOrDisprove vars -> Right as)) = Left $ as ++ aToNegNegA a
proveOrDisprove vars v@(Var a) | vars ! a = Right $ pure v
                               | otherwise = Left $ pure (Neg v)

assignments :: S.Set String → [M.Map String Bool]
assignments vars = [M.fromAscList (zip varsList vals) | vals ← replicateM n [False, True]]
    where
        n = S.size vars
        varsList = S.toAscList vars

assignmentsToAssumptions :: M.Map String Bool -> [Prop]
assignmentsToAssumptions = ((\(s, v) -> if v
                                        then      Var s
                                        else Neg (Var s)) <$>) . M.toAscList

-- Proposition, assignments, and vars left to assign
solve :: Prop -> M.Map String Bool -> [String] -> [Prop]
solve p vars (x:xs) = let f = solve p (M.insert x False vars) xs
                          t = solve p (M.insert x  True vars) xs
                          a = assignmentsToAssumptions vars
                      in hypothesisExclusion (Var x : a, t) (Neg (Var x) : a, f)
solve p vars [] = either undefined id $ proveOrDisprove vars p

main :: IO ()
main = do
  expr ← parseFile . head =<< getArgs
  let vars = variables expr
  let a = assignments vars
  case find (not . evaluate expr) a of
    Nothing -> putStr $ unlines $ (show <$>) $ solve expr M.empty $ S.toAscList vars
    Just x  -> putStr $ "False for " ++ intercalate ", " ((\(k, v) -> k ++ "=" ++ show v) <$> M.toAscList x) ++ "\n"
