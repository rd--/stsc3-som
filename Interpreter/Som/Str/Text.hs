-- | String type implemented as Text.
module Interpreter.Som.Str.Text where

import qualified Data.Text as Text {- text -}
import qualified Data.Text.IO as Text.IO {- text -}
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

unicodeStringAll :: (Char -> Bool) -> UnicodeString -> Bool
unicodeStringAll f str = not (Text.null str) && Text.all f str

unicodeStringAppend :: UnicodeString -> UnicodeString -> UnicodeString
unicodeStringAppend = Text.append

unicodeStringLength :: UnicodeString -> Int
unicodeStringLength = Text.length

-- | One-indexed
unicodeStringAt :: UnicodeString -> SmallInteger -> Maybe Char
unicodeStringAt str ix =
  let size = unicodeStringLength str
  in if ix > 0 && ix <= size
     then Just (Text.index str (fromIntegral ix - 1))
     else Nothing

unicodeStringWrite :: UnicodeString -> IO ()
unicodeStringWrite = Text.IO.putStr
