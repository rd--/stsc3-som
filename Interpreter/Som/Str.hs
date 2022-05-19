{- | String type.
     Requires efficient substring function.
     Som has no Char type.
-}
module Interpreter.Som.Str where

import Data.Char {- base -}

import Interpreter.Som.Int {- stsc3 -}

type UnicodeString = String

toUnicodeString :: String -> UnicodeString
toUnicodeString = id

fromUnicodeString :: UnicodeString -> String
fromUnicodeString = id

readMaybe :: Read t => String -> Maybe t
readMaybe str =
    case reads str of
      [(answer,[])] -> Just answer
      [(answer,[continues])] -> if isSpace continues then Just answer else Nothing
      _ -> Nothing

unicodeStringReadSmallInteger :: UnicodeString -> Maybe SmallInteger
unicodeStringReadSmallInteger = readMaybe

unicodeStringReadLargeInteger :: UnicodeString -> Maybe LargeInteger
unicodeStringReadLargeInteger = readMaybe

unicodeStringReadDouble :: UnicodeString -> Maybe Double
unicodeStringReadDouble = readMaybe

unicodeStringSubstringFromTo :: UnicodeString -> SmallInteger -> SmallInteger -> UnicodeString
unicodeStringSubstringFromTo x i j = drop (i - 1) (take j x)

unicodeStringAll :: (Char -> Bool) -> UnicodeString -> Bool
unicodeStringAll f str = not (null str) && all f str

unicodeStringAppend :: UnicodeString -> UnicodeString -> UnicodeString
unicodeStringAppend = (++)

unicodeStringLength :: UnicodeString -> SmallInteger
unicodeStringLength = length

-- | One-indexed
unicodeStringAt :: UnicodeString -> SmallInteger -> Maybe Char
unicodeStringAt str ix =
  let size = unicodeStringLength str
  in if ix > 0 && ix <= size
     then Just (str !! (ix - 1))
     else Nothing

unicodeStringWrite :: UnicodeString -> IO ()
unicodeStringWrite = putStr
