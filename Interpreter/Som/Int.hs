{- | Type for Smalltalk integers.
     The Som testsuite requires >64bit.
-}
module Interpreter.Som.Int where

import Data.Bits {- base -}
import Data.Int {- base -}
import Data.Word {- base -}

type SmallInteger = Int
type LargeInteger = Integer

fromLargeInteger :: LargeInteger -> SmallInteger
fromLargeInteger = fromIntegral

toLargeInteger :: SmallInteger -> LargeInteger
toLargeInteger = fromIntegral

largeIntegerShiftLeft ::  LargeInteger -> LargeInteger ->  LargeInteger
largeIntegerShiftLeft x by = Data.Bits.shiftL x (fromLargeInteger by)

largeIntegerShiftRight ::  LargeInteger -> LargeInteger ->  LargeInteger
largeIntegerShiftRight x by = Data.Bits.shiftR x (fromLargeInteger by)

as32BitUnsignedValue :: LargeInteger -> LargeInteger
as32BitUnsignedValue x =
  let uint32 = (fromIntegral x) :: Word32
  in fromIntegral uint32

as32BitSignedValue :: LargeInteger -> LargeInteger
as32BitSignedValue x =
  let int32 = (fromIntegral x) :: Int32
  in fromIntegral int32
