{- | String type.
     Requires efficient substring function.
     SOM has no Char type.
-}
module Interpreter.Som.Str.Text where

import qualified Data.Text as Text {- text -}
import qualified Data.Text.Read as Text.Read {- text -}

import Interpreter.Som.Int {- stsc3 -}

type UnicodeString = Text.Text

toUnicodeString :: String -> UnicodeString
toUnicodeString = Text.pack

fromUnicodeString :: UnicodeString -> String
fromUnicodeString = Text.unpack

unicodeStringReadSmallInteger :: UnicodeString -> Maybe SmallInteger
unicodeStringReadSmallInteger = either (const Nothing) (Just . fst) . Text.Read.signed Text.Read.decimal

unicodeStringReadLargeInteger :: UnicodeString -> Maybe LargeInteger
unicodeStringReadLargeInteger = either (const Nothing) (Just . fst) . Text.Read.signed Text.Read.decimal

unicodeStringReadDouble :: UnicodeString -> Maybe Double
unicodeStringReadDouble = either (const Nothing) (Just . fst) . Text.Read.double

unicodeStringSubstringFromTo :: UnicodeString -> SmallInteger -> SmallInteger -> UnicodeString
unicodeStringSubstringFromTo x i j = Text.drop (i - 1) (Text.take j x)
