module Parser where

import Control.Monad.State
import Control.Applicative

hole = hole

type Apar a = StateT String Maybe a

isempty :: (Eq b) => [] b -> Maybe a -> Maybe a
isempty s foo = if (s == []) then Nothing else foo

parseByPred :: (Char -> Bool) -> Apar Char
parseByPred foo = StateT $ \s -> isempty s $ if (foo $ head s)
                                           then Just (head s, tail s)
                                           else Nothing
char :: Char -> Apar Char
char c = parseByPred (== c)

twochars :: Char -> Char -> Apar Char
twochars c1 c2 = do
    x <- parseByPred(==c1)
    x <- parseByPred(==c2)
    return x

spaces :: Apar String
spaces = many $ char ' '

oneOf :: String -> Apar Char
oneOf str = parseByPred (`elem` str)

lexem :: Apar a -> Apar a
lexem p = do
  x <- p
  spaces
  return x

between :: Apar c -> Apar a -> Apar b -> Apar a
between f p g = do
  f
  x <- p
  g
  return x

after :: Apar c -> Apar a -> Apar a
after f p = do
  f
  x <- p
  return x

exactly :: Int -> Apar a -> Apar [a]
exactly 0 _ = return []
exactly n p = (:) <$> p <*> exactly (n - 1) p

eof :: Apar ()
eof = StateT $ \s -> case s of
  [] -> Just ((), [])
  _ -> Nothing

isend :: Apar Char
isend = parseByPred (/= '\n')

clearend :: Apar ()
clearend = (char '\n' >> return ()) <|> eof

toend :: Apar String
toend = do
  x <- many isend
  clearend
  return x

manySepBy :: Apar a -> Apar b -> Apar [a]
manySepBy p g = (:) <$> p <*> many (g >> p)

parseCharString :: Apar String
parseCharString = (many $ lexem $ oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ") >>= \x -> if x == [] then mzero else return x

parseDigitSeq :: Apar String
parseDigitSeq = many $ oneOf "0123456789"

parseVarName :: Apar String
parseVarName = parseCharString >>= \x -> parseDigitSeq >>= \y -> return $ x ++ y
