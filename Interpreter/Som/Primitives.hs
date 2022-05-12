-- | Primitives that do not require access to interpreter state.
module Interpreter.Som.Primitives where

import Control.Monad.IO.Class {- base -}
import Data.Bits {- base -}
import qualified Data.Char {- base -}
import Data.Fixed {- base -}
import Data.List {- base -}
import System.Directory {- directory -}
import System.Mem {- base -}
import System.Random {- random -}
import Text.Printf {- random -}

import qualified Data.Text as Text {- text -}
import qualified Data.Text.IO as Text.IO {- text -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}

import Interpreter.Som.Int
import Interpreter.Som.Primitives.Util
import Interpreter.Som.Ref
import Interpreter.Som.Str.Text
import Interpreter.Som.Sym
import Interpreter.Som.Tbl
import Interpreter.Som.Types
import Interpreter.Som.Vec

prArrayAt :: Ref (Vec Object) -> LargeInteger -> VM Object
prArrayAt ref ix = do
  v <- deRef ref
  if ix <= vecLength v
    then return (vecAt v (ix - 1))
    else prError "Array>>at: index out of range"

prIntegerFromString :: UnicodeString -> VM Object
prIntegerFromString x = maybe (prError "Integer class>>fromString:") (return . integerObject) (unicodeStringReadInteger x)

prObjectEqual :: Object -> Object -> VM Object
prObjectEqual rcv arg = do
  hash1 <- objectIntHash rcv
  hash2 <- objectIntHash arg
  return (booleanObject (hash1 == hash2))

prStringEqual :: (Bool, UnicodeString) -> ObjectData -> VM Object
prStringEqual (typ1, str1) rhs =
  case rhs of
    DataString typ2 str2 -> return (booleanObject ((not typ1 || typ1 == typ2) && str1 == str2))
    _ -> return falseObject

-- | Basis for isLetters and isDigits and isWhiteSpace.  Null strings are false.
prStringAll :: (Char -> Bool) -> UnicodeString -> VM Object
prStringAll f str = return (booleanObject (not (Text.null str) && Text.all f str))

{- | C.f. DoubleTest, c.f. Js

(doubleMod (-3) 2, mod' (-3) 2) == (-1, 1)
(doubleMod 3 (-2), mod' 3 (-2)) == (1, -1)
-}
doubleMod :: Real t => t -> t -> t
doubleMod p q =
  let r = mod' p q
  in case (p < 0, q < 0) of
       (True, False) -> -r
       (False, True) -> -r
       _ -> r

readFileMaybe :: FilePath -> IO (Maybe String)
readFileMaybe fn = do
  exists <- doesFileExist fn
  if exists then fmap Just (readFile fn) else return Nothing

prSystemLoadFile :: UnicodeString -> VM Object
prSystemLoadFile aString = do
    let fn = Text.unpack aString
        onFailure = return nilObject
    maybeText <- liftIO (readFileMaybe fn)
    maybe onFailure (return . stringObject) maybeText

{- | Primitive

Notes:
Block>>restart is not implemented, for now the single use in the class library (Block>>whileTrue:) should be modified to call itself.
String>>= has the rule (in the Som tests) is 'x' = #x but #x ~= 'x'
System>>loadFile: if the file does not exist returns nil, i.e. does not error.
System>>ticks is elapsed time in microseconds.
System>>time is elapsed time in milliseconds.
-}
nonCorePrimitive :: Symbol -> Symbol -> Object  -> [Object] -> VM Object
nonCorePrimitive prClass prMethod receiver@(Object receiverName receiverObj) arguments =
  case (prClass, prMethod, receiverObj, arguments) of
    ("Array class", "new:", DataClass {},[Object _ (DataInteger size)]) -> arrayFromList (genericReplicate size nilObject)
    ("Array", "at:", DataArray ref, [Object _ (DataInteger ix)]) -> prArrayAt ref ix
    ("Array", "at:put:", DataArray ref, [Object _ (DataInteger ix), value]) -> vecRefWrite ref (ix - 1) value
    ("Array", "length", DataArray ref, []) -> deRef ref >>= \v -> return (integerObject (vecLength v))
    ("Block", "restart", DataBlock {}, []) -> prError "Block>>restart not implemented"
    ("Block", "value", DataBlock {}, []) -> prError "Block>>value not implemented"
    ("Class", "methods", _, []) -> maybe (prError "Class>>methods") arrayFromVec (classMethodsVec receiver)
    ("Class", "name", DataClass (cd, isMeta) _ _, []) -> return (symbolObject ((if isMeta then St.metaclassName else id) (St.className cd)))
    ("Double class", "PositiveInfinity", DataClass {}, []) -> return (doubleObject (read "Infinity"))
    ("Double class", "fromString:", DataClass {}, [Object _ (DataString _ x)]) -> return (maybe nanObject doubleObject (unicodeStringReadDouble x))
    ("Double", "%", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive doubleMod lhs rhs
    ("Double", "*", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (*) lhs rhs
    ("Double", "+", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (+) lhs rhs
    ("Double", "-", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (-) lhs rhs
    ("Double", "//", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (/) lhs rhs -- Som?
    ("Double", "<", DataDouble lhs, [Object _ rhs]) -> doubleNumBoolPrimitive (<) lhs rhs
    ("Double", "=", DataDouble lhs, [Object _ rhs]) -> doubleNumBoolPrimitive (==) lhs rhs
    ("Double", "asInteger", DataDouble x, []) -> return (integerObject (truncate x)) -- Som?
    ("Double", "asString", DataDouble x, []) -> return (stringObject (show x))
    ("Double", "cos", DataDouble x, []) -> return (doubleObject (cos x))
    ("Double", "round", DataDouble x, []) -> return (integerObject (round x)) -- Som (roundTowardPositive in IEEE 754-2008)
    ("Double", "sin", DataDouble x, []) -> return (doubleObject (sin x))
    ("Double", "sqrt", DataDouble x, []) -> return (doubleObject (sqrt x))
    ("Integer class", "fromString:", DataClass {}, [Object _ (DataString _ x)]) -> prIntegerFromString x
    ("Integer", "+", DataInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (+) (+) lhs rhs
    ("Integer", "-", DataInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (-) (-) lhs rhs
    ("Integer", "*", DataInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (*) (*) lhs rhs
    ("Integer", "/", DataInteger lhs, [Object _ rhs]) -> intNumNumPrimitive div (/) lhs rhs -- ? Som 1/2=0
    ("Integer", "%", DataInteger lhs, [Object _ rhs]) -> intNumNumPrimitive mod mod' lhs rhs
    ("Integer", "rem:", DataInteger lhs, [Object _ rhs]) -> intNumNumPrimitive rem undefined lhs rhs
    ("Integer", "//", lhs, [Object _ rhs]) -> numNumNumPrimitive (/) lhs rhs
    ("Integer", "=", DataInteger lhs, [Object _ rhs]) -> intNumBoolPrimitive (return falseObject) (==) (==) lhs rhs
    ("Integer", "<", DataInteger lhs, [Object _ rhs]) -> intNumBoolPrimitive (prError "Integer>><") (<) (<) lhs rhs
    ("Integer", "&", DataInteger lhs, [Object _ (DataInteger rhs)]) -> return (integerObject (lhs Data.Bits..&. rhs))
    ("Integer", "<<", DataInteger lhs, [Object _ (DataInteger rhs)]) -> return (integerObject (shiftLeft lhs rhs))
    ("Integer", ">>>", DataInteger lhs, [Object _ (DataInteger rhs)]) -> return (integerObject (shiftRight lhs rhs))
    ("Integer", "bitXor:", DataInteger lhs, [Object _ (DataInteger rhs)]) -> return (integerObject (Data.Bits.xor lhs rhs))
    ("Integer", "asString", DataInteger x, []) -> return (stringObject (show x))
    ("Integer", "asDouble", DataInteger x, []) -> return (doubleObject (fromIntegral x))
    ("Integer", "as32BitUnsignedValue", DataInteger x, []) -> return (integerObject (as32BitUnsignedValue x))
    ("Integer", "as32BitSignedValue", DataInteger x, []) -> return (integerObject (as32BitSignedValue x))
    ("Integer", "atRandom", DataInteger x, []) -> fmap integerObject (liftIO (getStdRandom (randomR (0, x - 1))))
    ("Integer", "sqrt", rcv, []) -> numNumPrimitive sqrt rcv
    ("Method", "signature", DataMethod _ mth _, []) -> return (symbolObject (St.selectorIdentifier (St.methodSelector mth)))
    ("Object", "==", _, [arg]) -> prObjectEqual receiver arg
    ("Object", "hashcode", _, []) -> fmap integerObject (objectIntHash receiver)
    ("Object", "instVarAt:", DataUser _ tbl, [Object _ (DataInteger ix)]) -> tblAtDefault tbl (fromLargeInteger ix - 1) (prError "Object>>instVarAt:")
    ("Object", "instVarAt:put:", DataUser _ tbl, [Object _ (DataInteger ix), newObject]) -> tblAtPutDefault tbl (fromLargeInteger ix - 1) newObject (prError "Object>>instVarAt:put")
    ("Object", "instVarNamed:", DataUser _ tbl, [Object _ (DataString True key)]) -> tblAtKeyDefault tbl (fromUnicodeString key) (prError "Object>>instVarNamed:")
    ("Primitive", "holder", DataPrimitive x _, []) -> return (symbolObject x)
    ("Primitive", "signature", DataPrimitive _ x, []) -> return (symbolObject x)
    ("String", "=", DataString typ str, [Object _ arg]) -> prStringEqual (typ, str) arg
    ("String", "asSymbol", DataString _ x, []) -> return (unicodeSymbolObject x)
    ("String", "concatenate:", DataString _ x, [Object _ (DataString _ y)]) -> return (unicodeStringObject (Text.append x y))
    ("String", "hashcode", _, []) -> fmap integerObject (objectIntHash receiver)
    ("String", "isDigits", DataString _ str, []) -> prStringAll Data.Char.isDigit str
    ("String", "isLetters", DataString _ str, []) -> prStringAll Data.Char.isLetter str
    ("String", "isWhiteSpace", DataString _ str, []) -> prStringAll Data.Char.isSpace str
    ("String", "length", DataString _ str, []) -> return (integerObject (toLargeInteger (Text.length str)))
    ("String", "primSubstringFrom:to:", DataString _ str, [Object _ (DataInteger int1), Object _ (DataInteger int2)]) -> return (unicodeStringObject (unicodeStringSubstringFromTo str int1 int2))
    ("Symbol", "asString", DataString True x, []) -> return (unicodeStringObject x)
    ("System", "errorPrintln:", DataSystem, [Object _ (DataString _ x)]) -> liftIO (Text.IO.putStr x >> putChar '\n') >> error "System>>error"
    ("System", "exit:", DataSystem, [Object _ (DataInteger x)]) -> prError ("System>>exit: " ++ show x)
    ("System", "fullGC", DataSystem, []) -> liftIO System.Mem.performMajorGC >> return trueObject
    ("System", "global:", DataSystem, [Object _ (DataString True x)]) -> vmGlobalLookupOrNil (Text.unpack x)
    ("System", "global:put:", DataSystem, [Object _ (DataString True x), e]) -> vmGlobalAssign (Text.unpack x) e
    ("System", "hasGlobal:", DataSystem, [Object _ (DataString True x)]) -> fmap booleanObject (vmHasGlobal (Text.unpack x))
    ("System", "loadFile:", DataSystem, [Object _ (DataString False x)]) -> prSystemLoadFile x
    ("System", "printNewline", DataSystem, []) -> liftIO (putChar '\n') >> return nilObject
    ("System", "printString:", DataSystem, [Object _ (DataString _ x)]) -> liftIO (Text.IO.putStr x) >> return nilObject
    ("System", "ticks", DataSystem, []) -> fmap (integerObject . toLargeInteger) vmSystemTicksInt
    ("System", "time", DataSystem, []) -> fmap (integerObject . toLargeInteger . (`div` 1000)) vmSystemTicksInt
    _ -> prError (printf "%s>>%s (%s)" prClass prMethod (fromSymbol receiverName))

{-
import System.Exit {- base -}
-- | System>>exit: (exit process)
systemExitProcess :: Primitive
systemExitProcess (Object nm obj) arg = case (obj,arg) of
  (DataSystem,[Object _ (DataInteger x)]) ->
    liftIO (if x == 0 then exitSuccess else exitWith (ExitFailure x))
  _ -> prError ("System>>exit: " ++ fromSymbol nm)
-}

{-
> fromIntegral (maxBound::Int) >= ((2::Integer) ^ 62) -- True
> (((maxBound::Int) `div` (10^6)) `div` (60 * 60 * 24 * 365)) == 292471
> (((2^64) `div` (10^6)) `div` (60 * 60 * 24 * 365)) == 584942
-}
