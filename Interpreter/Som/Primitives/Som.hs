{-# Language FlexibleContexts #-}

-- | Som primitives either succeed or raise an error.
module Interpreter.Som.Primitives.Som where

import Control.Monad.IO.Class {- base -}
import Data.Bits {- base -}
import qualified Data.Char {- base -}
import Data.Fixed {- base -}
import Data.List {- base -}
import System.Exit {- base -}
import System.Mem {- base -}
import Text.Printf {- base -}

import System.Random {- random -}

import qualified Data.Text as Text {- text -}
import qualified Data.Text.IO as Text.IO {- text -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Som as Som {- stsc3 -}

import Interpreter.Som.Core
import Interpreter.Som.Error
import Interpreter.Som.Int
import Interpreter.Som.Ref
import Interpreter.Som.Str.Text
import Interpreter.Som.Sym
import Interpreter.Som.Sys
import Interpreter.Som.Tbl
import Interpreter.Som.Types
import Interpreter.Som.Vec

-- Types

type Uop t = t -> t
type Binop t = t -> t -> t
type Cmp t = t -> t -> Bool

type SomPrimitiveOf t = (Symbol, Symbol) -> Object -> [Object] -> t
type SomPrimitiveM m = (Symbol, Symbol) -> Object -> [Object] -> m Object
type SomPrimitiveDispatcher = SomPrimitiveOf (Vm Object)

-- * Util

intObject :: LargeInteger -> Object
intObject x = Object (toSymbol "Integer") (DataLargeInteger x)

strObject :: String -> Object
strObject = unicodeStringObject . toUnicodeString . Som.somEscapedString

numNumPrimitive :: Uop Double -> ObjectData -> Maybe Object
numNumPrimitive f = fmap (doubleAsFractional intObject . f) . objectDataAsDouble

numNumNumPrimitive :: Binop Double -> ObjectData -> ObjectData -> Maybe Object
numNumNumPrimitive f rcv arg = do
  lhs <- objectDataAsDouble rcv
  rhs <- objectDataAsDouble arg
  return (doubleAsFractional intObject (f lhs rhs))

intNumNumPrimitive :: Binop LargeInteger -> Binop Double -> LargeInteger -> ObjectData -> Maybe Object
intNumNumPrimitive f1 f2 lhs rhs =
  case rhs of
    DataLargeInteger rhs' -> return (intObject (f1 lhs rhs'))
    DataDouble rhs' -> return (doubleObject (f2 (fromIntegral lhs) rhs'))
    _ -> Nothing

intNumBoolPrimitive :: Maybe Object -> Cmp LargeInteger -> Cmp Double -> LargeInteger -> ObjectData -> Maybe Object
intNumBoolPrimitive def f1 f2 lhs rhs =
  case rhs of
    DataLargeInteger rhs' -> Just (booleanObject (f1 lhs rhs'))
    DataDouble rhs' -> Just (booleanObject (f2 (fromIntegral lhs) rhs'))
    _ -> def

doubleNumDoublePrimitive :: Binop Double -> Double -> ObjectData -> Maybe Object
doubleNumDoublePrimitive f lhs rhs = fmap (doubleObject . f lhs) (objectDataAsDouble rhs)

doubleNumBoolPrimitive :: Cmp Double -> Double -> ObjectData -> Maybe Object
doubleNumBoolPrimitive f lhs rhs = fmap (booleanObject . f lhs) (objectDataAsDouble rhs)

-- * Primtives

prArrayAt :: (StError m, MonadIO m) => Ref (Vec Object) -> LargeInteger -> m Object
prArrayAt ref ix = arrayAt ref (fromInteger ix) >>= maybe (prError "Array>>at: index out of range") return

prObjectEqual :: (StError m, MonadIO m) => Object -> Object -> m Object
prObjectEqual rcv arg = do
  hash1 <- objectIntHash rcv
  hash2 <- objectIntHash arg
  return (booleanObject (hash1 == hash2))

prStringEqual :: (Bool, UnicodeString) -> ObjectData -> Object
prStringEqual (typ1, str1) rhs =
  case rhs of
    DataString typ2 str2 -> booleanObject ((not typ1 || typ1 == typ2) && str1 == str2)
    _ -> falseObject

-- | Basis for isLetters and isDigits and isWhiteSpace.  Null strings are false.
prStringAll :: (Char -> Bool) -> UnicodeString -> Object
prStringAll f str = booleanObject (not (Text.null str) && Text.all f str)

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

prSystemLoadFile :: (StError m, MonadIO m) => UnicodeString -> m Object
prSystemLoadFile aString = do
    let fn = Text.unpack aString
        onFailure = return nilObject
    maybeText <- liftIO (readFileMaybe fn)
    maybe onFailure (return . strObject) maybeText

prSystemExit :: MonadIO m => LargeInteger -> m t
prSystemExit exitCode = liftIO (if exitCode == 0 then exitSuccess else exitWith (ExitFailure (fromInteger exitCode)))

-- | Primitives with no requirements that, given types have matched, do not fail.
somPrimitivesO :: SomPrimitiveOf (Maybe Object)
somPrimitivesO (prClass, prMethod) (Object _receiverName receiverObj) arguments =
  case (prClass, prMethod, receiverObj, arguments) of
    ("Double class", "PositiveInfinity", DataClass {}, []) -> Just (doubleObject (read "Infinity"))
    ("Double class", "fromString:", DataClass {}, [Object _ (DataString _ x)]) -> Just (maybe nanObject doubleObject (unicodeStringReadDouble x))
    ("Double", "asInteger", DataDouble x, []) -> Just (intObject (truncate x)) -- Som?
    ("Double", "asString", DataDouble x, []) -> Just (strObject (show x))
    ("Double", "cos", DataDouble x, []) -> Just (doubleObject (cos x))
    ("Double", "round", DataDouble x, []) -> Just (intObject (round x)) -- Som (roundTowardPositive in IEEE 754-2008)
    ("Double", "sin", DataDouble x, []) -> Just (doubleObject (sin x))
    ("Double", "sqrt", DataDouble x, []) -> Just (doubleObject (sqrt x))
    ("Integer", "<", DataLargeInteger lhs, [Object _ rhs]) -> intNumBoolPrimitive Nothing (<) (<) lhs rhs
    ("Integer", "&", DataLargeInteger lhs, [Object _ (DataLargeInteger rhs)]) -> Just (intObject (lhs Data.Bits..&. rhs))
    ("Integer", "<<", DataLargeInteger lhs, [Object _ (DataLargeInteger rhs)]) -> Just (intObject (shiftLeft lhs rhs))
    ("Integer", "=", DataLargeInteger lhs, [Object _ rhs]) -> intNumBoolPrimitive (Just falseObject) (==) (==) lhs rhs
    ("Integer", ">>>", DataLargeInteger lhs, [Object _ (DataLargeInteger rhs)]) -> Just (intObject (shiftRight lhs rhs))
    ("Integer", "as32BitSignedValue", DataLargeInteger x, []) -> Just (intObject (as32BitSignedValue x))
    ("Integer", "as32BitUnsignedValue", DataLargeInteger x, []) -> Just (intObject (as32BitUnsignedValue x))
    ("Integer", "asDouble", DataLargeInteger x, []) -> Just (doubleObject (fromIntegral x))
    ("Integer", "asString", DataLargeInteger x, []) -> Just (strObject (show x))
    ("Integer", "bitXor:", DataLargeInteger lhs, [Object _ (DataLargeInteger rhs)]) -> Just (intObject (Data.Bits.xor lhs rhs))
    ("Method", "signature", DataMethod _ mth _, []) -> Just (symbolObject (St.selectorIdentifier (St.methodSelector mth)))
    ("Primitive", "holder", DataPrimitive x _, []) -> Just (symbolObject x)
    ("Primitive", "signature", DataPrimitive _ x, []) -> Just (symbolObject x)
    ("String", "=", DataString typ str, [Object _ arg]) -> Just (prStringEqual (typ, str) arg)
    ("String", "asSymbol", DataString _ x, []) -> Just (unicodeSymbolObject x)
    ("String", "concatenate:", DataString _ x, [Object _ (DataString _ y)]) -> Just (unicodeStringObject (Text.append x y))
    ("String", "isDigits", DataString _ str, []) -> Just (prStringAll Data.Char.isDigit str)
    ("String", "isLetters", DataString _ str, []) -> Just (prStringAll Data.Char.isLetter str)
    ("String", "isWhiteSpace", DataString _ str, []) -> Just (prStringAll Data.Char.isSpace str)
    ("String", "length", DataString _ str, []) -> Just (intObject (toLargeInteger (Text.length str)))
    ("String", "primSubstringFrom:to:", DataString _ str, [Object _ (DataLargeInteger int1), Object _ (DataLargeInteger int2)]) -> Just (unicodeStringObject (unicodeStringSubstringFromTo str (fromLargeInteger int1) (fromLargeInteger int2)))
    ("Symbol", "asString", DataString True x, []) -> Just (unicodeStringObject x)
    _ -> Nothing

-- | Primitives with no requirements that may fail.
somPrimitivesM :: SomPrimitiveOf (Maybe Object)
somPrimitivesM (prClass, prMethod) receiver@(Object _receiverName receiverObj) arguments =
  case (prClass, prMethod, receiverObj, arguments) of
    ("Block", "restart", DataBlock {}, []) -> Nothing -- not implemented
    ("Block", "value", DataBlock {}, []) -> Nothing -- not implemented
    ("Double", "%", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive doubleMod lhs rhs
    ("Double", "*", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (*) lhs rhs
    ("Double", "+", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (+) lhs rhs
    ("Double", "-", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (-) lhs rhs
    ("Double", "//", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (/) lhs rhs -- Som?
    ("Double", "<", DataDouble lhs, [Object _ rhs]) -> doubleNumBoolPrimitive (<) lhs rhs
    ("Double", "=", DataDouble lhs, [Object _ rhs]) -> doubleNumBoolPrimitive (==) lhs rhs
    ("Integer class", "fromString:", DataClass {}, [Object _ (DataString _ x)]) -> fmap intObject (unicodeStringReadLargeInteger x)
    ("Integer", "%", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive mod mod' lhs rhs
    ("Integer", "*", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (*) (*) lhs rhs
    ("Integer", "+", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (+) (+) lhs rhs
    ("Integer", "-", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (-) (-) lhs rhs
    ("Integer", "/", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive div (/) lhs rhs -- ? Som 1/2=0
    ("Integer", "//", lhs, [Object _ rhs]) -> numNumNumPrimitive (/) lhs rhs
    ("Integer", "rem:", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive rem undefined lhs rhs
    ("Integer", "sqrt", rcv, []) -> numNumPrimitive sqrt rcv
    _ -> somPrimitivesO (prClass, prMethod) receiver arguments

{- | Primitives that require Io but not Vm state.

Notes:
Block>>restart is not implemented, for now the single use in the class library (Block>>whileTrue:) should be modified to call itself.
String>>= has the rule (in the Som tests) is 'x' = #x but #x ~= 'x'
System>>loadFile: if the file does not exist returns nil, i.e. does not error.
-}
somPrimitivesI :: (StError m, MonadIO m) => SomPrimitiveM m
somPrimitivesI (prClass, prMethod) receiver@(Object receiverName receiverObj) arguments =
  case (prClass, prMethod, receiverObj, arguments) of
    ("Array class", "new:", DataClass {},[Object _ (DataLargeInteger size)]) -> arrayFromList (genericReplicate size nilObject)
    ("Array", "at:", DataArray ref, [Object _ (DataLargeInteger ix)]) -> prArrayAt ref ix
    ("Array", "at:put:", DataArray ref, [Object _ (DataLargeInteger ix), value]) -> vecRefWrite ref (fromInteger ix - 1) value
    ("Array", "length", DataArray ref, []) -> deRef ref >>= \v -> return (intObject (fromIntegral (vecLength v)))
    ("Class", "methods", _, []) -> maybe (prError "Class>>methods") arrayFromVec (classMethodsVec receiver)
    ("Class", "name", DataClass (cd, isMeta) _ _, []) -> return (symbolObject ((if isMeta then St.metaclassName else id) (St.className cd)))
    ("Integer", "atRandom", DataLargeInteger x, []) -> fmap intObject (liftIO (getStdRandom (randomR (0, x - 1))))
    ("Object", "==", _, [arg]) -> prObjectEqual receiver arg
    ("Object", "hashcode", _, []) -> fmap (intObject . fromIntegral) (objectIntHash receiver)
    ("Object", "instVarAt:", DataUser _ tbl, [Object _ (DataLargeInteger ix)]) -> tblAtDefault tbl (fromLargeInteger ix - 1) (prError "Object>>instVarAt:")
    ("Object", "instVarAt:put:", DataUser _ tbl, [Object _ (DataLargeInteger ix), newObject]) -> tblAtPutDefault tbl (fromLargeInteger ix - 1) newObject (prError "Object>>instVarAt:put")
    ("Object", "instVarNamed:", DataUser _ tbl, [Object _ (DataString True key)]) -> tblAtKeyDefault tbl (fromUnicodeString key) (prError "Object>>instVarNamed:")
    ("String", "hashcode", _, []) -> fmap (intObject . fromIntegral) (objectIntHash receiver)
    ("System", "errorPrintln:", DataSystem, [Object _ (DataString _ x)]) -> liftIO (Text.IO.putStr x >> putChar '\n') >> error "System>>error"
    ("System", "exit:", DataSystem, [Object _ (DataLargeInteger x)]) -> prSystemExit x
    ("System", "fullGC", DataSystem, []) -> liftIO System.Mem.performMajorGC >> return trueObject
    ("System", "loadFile:", DataSystem, [Object _ (DataString False x)]) -> prSystemLoadFile x
    ("System", "printNewline", DataSystem, []) -> liftIO (putChar '\n') >> return nilObject
    ("System", "printString:", DataSystem, [Object _ (DataString _ x)]) -> liftIO (Text.IO.putStr x) >> return nilObject
    _ -> case somPrimitivesM (prClass, prMethod) receiver arguments of
           Nothing -> prError (printf "%s>>%s (%s)" prClass prMethod (fromSymbol receiverName))
           Just answer -> return answer

{- | Primitives that require access to Vm state.

Notes:
System>>ticks is elapsed time in microseconds.
System>>time is elapsed time in milliseconds.
-}
somPrimitivesV :: SomPrimitiveDispatcher
somPrimitivesV (prClass, prMethod) receiver@(Object _receiverName receiverObj) arguments =
  case (prClass, prMethod, receiverObj, arguments) of
    ("System", "global:", DataSystem, [Object _ (DataString True x)]) -> vmGlobalLookupOrNil (Text.unpack x)
    ("System", "global:put:", DataSystem, [Object _ (DataString True x), e]) -> vmGlobalAssign (Text.unpack x) e
    ("System", "hasGlobal:", DataSystem, [Object _ (DataString True x)]) -> fmap booleanObject (vmHasGlobal (Text.unpack x))
    ("System", "ticks", DataSystem, []) -> fmap (intObject . toLargeInteger) vmSystemTicksInt
    ("System", "time", DataSystem, []) -> fmap (intObject . toLargeInteger . (`div` 1000)) vmSystemTicksInt
    _ -> somPrimitivesI (prClass, prMethod) receiver arguments

{- | Class>>fields => Array[Symbol]

This is Behaviour>>allInstVarNames and Class>>allClassVarNames in Smalltalk, which are not primitive.
-}
prClassFields :: St.ClassDefinition -> Bool -> Vm Object
prClassFields cd isMeta =
  case isMeta of
    False -> do
      fld <- classAllVariableNames St.classInstanceVariableNames cd
      arrayFromList (map symbolObject fld)
    True -> do
      fld <- classAllVariableNames St.classVariableNames cd
      arrayFromList (map symbolObject fld)

prMethodInvokeOnWith :: CoreOpt -> ObjectData -> Object -> Object -> Vm Object
prMethodInvokeOnWith opt obj receiver argumentsArray = do
  arguments <- arrayElements argumentsArray
  evalMethodOrPrimitive opt obj receiver arguments

-- | Primitives that require functions from Core.
somPrimitivesC :: SomPrimitiveDispatcher
somPrimitivesC (prClass, prMethod) receiver@(Object _ receiverObj) arguments =
  case (prClass, prMethod, receiverObj, arguments) of
    ("Block1", "value", DataBlock {}, []) -> evalBlock somCoreOpt receiver []
    ("Block2", "value:", DataBlock {}, [arg]) -> evalBlock somCoreOpt receiver [arg]
    ("Block3", "value:with:", DataBlock {}, [arg1, arg2]) -> evalBlock somCoreOpt receiver [arg1, arg2]
    ("Class", "fields", DataClass (cd,isMeta) _ _, []) -> prClassFields cd isMeta
    ("Class", "new", DataClass (cd,_) _ _,[]) -> classNew cd
    ("Class", "superclass", DataClass (cd,isMeta) _ _,[]) -> classSuperclass cd isMeta
    ("Method", "holder", DataMethod holder _ _,[]) -> vmGlobalResolveOrError holder
    ("Method", "invokeOn:with:", rcv, [arg1, arg2]) -> prMethodInvokeOnWith somCoreOpt rcv arg1 arg2
    ("Object","class", _, []) -> objectClass receiver
    ("Object", "inspect", _, []) -> objectInspect receiver
    ("Object", "perform:", _, [Object "Symbol" (DataString True sel)]) -> objectPerform somCoreOpt receiver sel
    ("Object", "perform:inSuperclass:", _, [Object "Symbol" (DataString True sel), cl]) -> objectPerformInSuperclass somCoreOpt receiver sel cl
    ("Object", "perform:withArguments:", _, [Object "Symbol" (DataString True sel), arg]) -> objectPerformWithArguments somCoreOpt receiver sel arg
    ("Object", "perform:withArguments:inSuperclass:", _, [Object "Symbol" (DataString True sel), arg, cl]) -> objectPerformWithArgumentsInSuperclass somCoreOpt receiver sel arg cl
    ("Primitive", "invokeOn:with:", DataPrimitive {}, [_,_]) -> vmError "Primitive>>invokeOn:with: not implemented"
    ("System", "load:", DataSystem, [Object "Symbol" (DataString True x)]) -> systemLoadClassOrNil (Text.unpack x)
    _ -> somPrimitivesV (prClass, prMethod) receiver arguments

somPrimitives :: PrimitiveDispatcher
somPrimitives hs _cd rcv arg = do
  answer <- somPrimitivesC hs rcv arg
  return (Just answer)

somCoreOpt :: CoreOpt
somCoreOpt = CoreOpt SomSystem (intObject, strObject) somPrimitives

{-
> fromIntegral (maxBound::Int) >= ((2::Integer) ^ 62) -- True
> (((maxBound::Int) `div` (10^6)) `div` (60 * 60 * 24 * 365)) == 292471
> (((2^64) `div` (10^6)) `div` (60 * 60 * 24 * 365)) == 584942
-}
