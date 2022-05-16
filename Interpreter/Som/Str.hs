{- | String type.
     Requires efficient substring function.
     SOM has no Char type.
-}
module Interpreter.Som.Str where

import Interpreter.Som.Int {- stsc3 -}

type UnicodeString = String

toUnicodeString :: String -> UnicodeString
toUnicodeString = id

fromUnicodeString :: UnicodeString -> String
fromUnicodeString = id

unicodeStringReadSmallInteger :: UnicodeString -> Maybe SmallInteger
unicodeStringReadSmallInteger = read

unicodeStringReadLargeInteger :: UnicodeString -> Maybe LargeInteger
unicodeStringReadLargeInteger = read

unicodeStringReadDouble :: UnicodeString -> Maybe Double
unicodeStringReadDouble = read

unicodeStringSubstringFromTo :: UnicodeString -> SmallInteger -> SmallInteger -> UnicodeString
unicodeStringSubstringFromTo x i j = drop (i - 1) (take j x)
