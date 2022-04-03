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

unicodeStringReadInteger :: UnicodeString -> Maybe LargeInteger
unicodeStringReadInteger = read

unicodeStringReadDouble :: UnicodeString -> Maybe Double
unicodeStringReadDouble = read

unicodeStringSubstringFromTo :: UnicodeString -> LargeInteger -> LargeInteger -> UnicodeString
unicodeStringSubstringFromTo x i j = drop (fromLargeInteger i - 1) (take (fromLargeInteger j) x)
