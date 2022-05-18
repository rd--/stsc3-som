{-# Language FlexibleContexts #-}

{- | Smalltalk primitives indicate success by returning (Just answer) and failure by returning Nothing.
Error handling and delegation is in the standard library.
-}
module Interpreter.Som.Primitives.Smalltalk where

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

-- * Util

intObject :: SmallInteger -> Object
intObject x = Object (toSymbol "SmallInteger") (DataSmallInteger x)

strObject :: String -> Object
strObject = unicodeStringObject . toUnicodeString

{-
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
    DataSmallInteger rhs' -> return (intObject (f1 lhs rhs'))
    DataDouble rhs' -> return (doubleObject (f2 (fromIntegral lhs) rhs'))
    _ -> Nothing

intNumBoolPrimitive :: Maybe Object -> Cmp LargeInteger -> Cmp Double -> LargeInteger -> ObjectData -> Maybe Object
intNumBoolPrimitive def f1 f2 lhs rhs =
  case rhs of
    DataSmallInteger rhs' -> Just (booleanObject (f1 lhs rhs'))
    DataDouble rhs' -> Just (booleanObject (f2 (fromIntegral lhs) rhs'))
    _ -> def

doubleNumDoublePrimitive :: Binop Double -> Double -> ObjectData -> Maybe Object
doubleNumDoublePrimitive f lhs rhs = fmap (doubleObject . f lhs) (objectDataAsDouble rhs)

doubleNumBoolPrimitive :: Cmp Double -> Double -> ObjectData -> Maybe Object
doubleNumBoolPrimitive f lhs rhs = fmap (booleanObject . f lhs) (objectDataAsDouble rhs)

-- * Primtives

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

-- | Primitives with no requirements that, given types have matched, do not fail.
stPrimitivesO :: PrimitiveDispatcherTo (Maybe Object)
stPrimitivesO (prClass, prMethod) _prCode (Object _receiverName receiverObj) arguments =
  case (prClass, prMethod, receiverObj, arguments) of
    ("Double", "cos", DataDouble x, []) -> Just (doubleObject (cos x))
    ("SmallInteger", "as32BitSignedValue", DataSmallInteger x, []) -> Just (intObject (as32BitSignedValue x))
    ("SmallInteger", "as32BitUnsignedValue", DataSmallInteger x, []) -> Just (intObject (as32BitUnsignedValue x))
    _ -> Nothing

-- | Primitives with no requirements that may fail.
stPrimitivesM :: StPrimitiveDispatcherTo (Maybe Object)
stPrimitivesM (prClass, prMethod) prCode receiver@(Object _receiverName receiverObj) arguments =
  case (prClass, prMethod, receiverObj, arguments) of
    ("Double", "%", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive doubleMod lhs rhs
    ("Double", "//", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (/) lhs rhs -- St?
    ("SmallInteger", "%", DataSmallInteger lhs, [Object _ rhs]) -> intNumNumPrimitive mod mod' lhs rhs
    ("SmallInteger", "//", lhs, [Object _ rhs]) -> numNumNumPrimitive (/) lhs rhs
    ("SmallInteger", "rem:", DataSmallInteger lhs, [Object _ rhs]) -> intNumNumPrimitive rem undefined lhs rhs
    ("SmallInteger", "sqrt", rcv, []) -> numNumPrimitive sqrt rcv
    _ -> stPrimitivesO (prClass, prMethod) prCode receiver arguments
-}


-- | Basis for isLetters and isDigits and isWhiteSpace.  Null strings are false.
prStringAll :: (Char -> Bool) -> UnicodeString -> Object
prStringAll f str = booleanObject (not (Text.null str) && Text.all f str)

prObjectEqual :: (StError m, MonadIO m) => Object -> Object -> m Object
prObjectEqual rcv arg = do
  hash1 <- objectIntHash rcv
  hash2 <- objectIntHash arg
  return (booleanObject (hash1 == hash2))

prStringEqual :: (Bool, UnicodeString) -> ObjectData -> Object
prStringEqual (typ1, str1) rhs =
  case rhs of
    DataImmutableString typ2 str2 -> booleanObject ((not typ1 || typ1 == typ2) && str1 == str2)
    _ -> falseObject

prSystemLoadFile :: (StError m, MonadIO m) => UnicodeString -> m Object
prSystemLoadFile aString = do
    let fn = Text.unpack aString
        onFailure = return nilObject
    maybeText <- liftIO (readFileMaybe fn)
    maybe onFailure (return . strObject) maybeText

prSystemExit :: MonadIO m => SmallInteger -> m t
prSystemExit exitCode = liftIO (if exitCode == 0 then exitSuccess else exitWith (ExitFailure exitCode))

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

stPrimitivesC :: PrimitiveDispatcher
stPrimitivesC (prClass, prMethod) _prCode receiver@(Object _ receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("=", DataImmutableString typ str, [Object _ arg]) -> return (Just (prStringEqual (typ, str) arg))
    ("PositiveInfinity", DataClass {}, []) -> return (Just (doubleObject (read "Infinity")))
    ("asString", DataDouble x, []) -> return (Just (strObject (show x)))
    ("asString", DataImmutableString True x, []) -> return (Just (unicodeStringObject x))
    ("asString", DataSmallInteger x, []) -> return (Just (strObject (show x)))
    ("asSymbol", DataImmutableString _ x, []) -> return (Just (unicodeSymbolObject x))
    ("atRandom", DataSmallInteger x, []) -> fmap (Just . intObject) (liftIO (getStdRandom (randomR (0, x - 1))))
    ("concatenate:", DataImmutableString _ x, [Object _ (DataImmutableString _ y)]) -> return (Just (unicodeStringObject (Text.append x y)))
    ("errorPrintln:", DataSystem, [Object _ (DataImmutableString _ x)]) -> fmap Just (liftIO (Text.IO.putStr x >> putChar '\n') >> error "System>>error")
    ("fields", DataClass (cd,isMeta) _ _, []) -> fmap Just (prClassFields cd isMeta)
    ("fromString:", DataClass {}, [Object _ (DataImmutableString _ x)]) ->
      case prClass of
        "Double class" -> return (Just (maybe nanObject doubleObject (unicodeStringReadDouble x)))
        "SmallInteger class" -> return (fmap intObject (unicodeStringReadSmallInteger x))
        _ -> return Nothing
    ("fullGC", DataSystem, []) -> liftIO System.Mem.performMajorGC >> return (Just trueObject)
    ("global:", DataSystem, [Object _ (DataImmutableString True x)]) -> fmap Just (vmGlobalLookupOrNil (Text.unpack x))
    ("global:put:", DataSystem, [Object _ (DataImmutableString True x), e]) -> fmap Just (vmGlobalAssign (Text.unpack x) e)
    ("hasGlobal:", DataSystem, [Object _ (DataImmutableString True x)]) -> fmap (Just . booleanObject) (vmHasGlobal (Text.unpack x))
    ("hashcode", _, []) -> fmap (Just . intObject) (objectIntHash receiver)
    ("holder", DataMethod holder _ _,[]) -> fmap Just (vmGlobalResolveOrError holder)
    ("holder", DataPrimitive x _, []) -> return (Just (symbolObject x))
    ("inspect", _, []) -> fmap Just (objectInspect receiver)
    ("instVarAt:", DataNonIndexable _ tbl, [Object _ (DataSmallInteger ix)]) -> fmap Just (tblAtDefault tbl (ix - 1) (prError "Object>>instVarAt:"))
    ("instVarAt:put:", DataNonIndexable _ tbl, [Object _ (DataSmallInteger ix), newObject]) -> fmap Just (tblAtPutDefault tbl (ix - 1) newObject (prError "Object>>instVarAt:put"))
    ("instVarNamed:", DataNonIndexable _ tbl, [Object _ (DataImmutableString True key)]) -> fmap Just (tblAtKeyDefault tbl (fromUnicodeString key) (prError "Object>>instVarNamed:"))
    ("invokeOn:with:", DataMethod {}, [arg1, arg2]) -> fmap Just (prMethodInvokeOnWith stCoreOpt receiverObj arg1 arg2)
    ("invokeOn:with:", DataPrimitive {}, [_,_]) -> fmap Just (vmError "Primitive>>invokeOn:with: not implemented")
    ("isDigits", DataImmutableString _ str, []) -> return (Just (prStringAll Data.Char.isDigit str))
    ("isLetters", DataImmutableString _ str, []) -> return (Just (prStringAll Data.Char.isLetter str))
    ("isWhiteSpace", DataImmutableString _ str, []) -> return (Just (prStringAll Data.Char.isSpace str))
    ("load:", DataSystem, [Object "Symbol" (DataImmutableString True x)]) -> fmap Just (systemLoadClassOrNil (Text.unpack x))
    ("loadFile:", DataSystem, [Object _ (DataImmutableString False x)]) -> fmap Just (prSystemLoadFile x)
    ("methods", DataClass {}, []) -> fmap Just (maybe (prError "Class>>methods") arrayFromVec (classMethodsVec receiver))
    ("name", DataClass (cd, isMeta) _ _, []) -> return (Just (symbolObject ((if isMeta then St.metaclassName else id) (St.className cd))))
    ("perform:inSuperclass:", _, [Object "Symbol" (DataImmutableString True sel), cl]) -> fmap Just (objectPerformInSuperclass stCoreOpt receiver sel cl)
    ("primSubstringFrom:to:", DataImmutableString _ str, [Object _ (DataSmallInteger int1), Object _ (DataSmallInteger int2)]) -> return (Just (unicodeStringObject (unicodeStringSubstringFromTo str int1 int2)))
    ("printNewline", DataSystem, []) -> liftIO (putChar '\n') >> return (Just nilObject)
    ("printString:", DataSystem, [Object _ (DataImmutableString _ x)]) -> liftIO (Text.IO.putStr x) >> return (Just nilObject)
    ("signature", DataMethod _ mth _, []) -> return (Just (symbolObject (St.selectorIdentifier (St.methodSelector mth))))
    ("signature", DataPrimitive _ x, []) -> return (Just (symbolObject x))
    ("superclass", DataClass (cd,isMeta) _ _,[]) -> fmap Just (classSuperclass cd isMeta)
    ("ticks", DataSystem, []) -> fmap (Just . intObject) vmSystemTicksInt
    ("time", DataSystem, []) -> fmap (Just . intObject . (`div` 1000)) vmSystemTicksInt
    ("value", DataBlock {}, []) -> fmap Just (evalBlock stCoreOpt receiver [])
    ("value:", DataBlock {}, [arg]) -> fmap Just (evalBlock stCoreOpt receiver [arg])
    ("value:with:", DataBlock {}, [arg1, arg2]) -> fmap Just (evalBlock stCoreOpt receiver [arg1, arg2])
    _ -> return Nothing

prIntegerDivisionExact :: SmallInteger -> SmallInteger -> Maybe Object
prIntegerDivisionExact lhs rhs =
  case divMod lhs rhs of
    (answer, 0) -> Just (intObject answer)
    _ -> Nothing

prBitShift :: SmallInteger -> SmallInteger -> Object
prBitShift lhs rhs =
  intObject
  (if rhs >= 0
   then Data.Bits.shiftL lhs rhs
   else Data.Bits.shiftL lhs (negate rhs))

stPrimitives :: PrimitiveDispatcher
stPrimitives (prClass, prMethod) prCode receiver@(Object _ receiverObj) arguments = do
  case (prCode, receiverObj, arguments) of
    (1, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (lhs + rhs)))
    (2, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (lhs - rhs)))
    (3, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (booleanObject (lhs < rhs)))
    (4, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (booleanObject (lhs > rhs)))
    (5, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (booleanObject (lhs <= rhs)))
    (6, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (booleanObject (lhs >= rhs)))
    (7, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (booleanObject (lhs == rhs)))
    (8, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (booleanObject (lhs /= rhs)))
    (9, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (lhs * rhs)))
    (10, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (prIntegerDivisionExact lhs rhs)
    (11, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (lhs `mod` rhs)))
    (12, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (lhs `div` rhs)))
    (14, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (lhs Data.Bits..&. rhs)))
    (15, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (lhs Data.Bits..|. rhs)))
    (16, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (Data.Bits.xor lhs rhs)))
    (17, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (prBitShift lhs rhs))
    (40, DataSmallInteger x, []) -> return (Just (doubleObject (fromIntegral x)))
    (41, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (doubleObject (lhs + rhs)))
    (42, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (doubleObject (lhs - rhs)))
    (43, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (booleanObject (lhs < rhs)))
    (44, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (booleanObject (lhs > rhs)))
    (45, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (booleanObject (lhs <= rhs)))
    (46, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (booleanObject (lhs >= rhs)))
    (47, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (booleanObject (lhs == rhs)))
    (48, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (booleanObject (lhs /= rhs)))
    (49, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (doubleObject (lhs * rhs)))
    (50, DataDouble lhs, [Object _ (DataDouble rhs)]) -> return (Just (doubleObject (lhs / rhs)))
    (51, DataDouble x, []) -> return (Just (intObject (truncate x)))
    (52, DataDouble x, []) -> return (Just (doubleObject (x - fromInteger (truncate x))))
    (55, DataDouble x, []) -> return (Just (doubleObject (sqrt x)))
    (56, DataDouble x, []) -> return (Just (doubleObject (sin x)))
    (58, DataDouble x, []) -> return (Just (doubleObject (log x)))
    (59, DataDouble x, []) -> return (Just (doubleObject (exp x)))
    (60, DataArrayLiteral vec, [Object _ (DataSmallInteger ix)]) -> return (vecAtMaybe vec ix)
    (60, DataIndexable _ ref, [Object _ (DataSmallInteger ix)]) -> vecRefAt ref ix
    (61, DataIndexable _ ref, [Object _ (DataSmallInteger ix), value]) -> fmap Just (vecRefWrite ref (ix - 1) value)
    (62, DataArrayLiteral vec, []) -> return (Just (intObject (vecLength vec)))
    (62, DataIndexable _ ref, []) -> deRef ref >>= \vec -> return (Just (intObject (vecLength vec)))
    (62, DataImmutableString _ str, []) -> return (Just (intObject (Text.length str)))
    (70, DataClass (cd,_) _ _,[]) -> fmap Just (classNew cd)
    (71, DataClass {},[Object _ (DataSmallInteger size)]) -> fmap Just (arrayFromList (genericReplicate size nilObject)) -- !!
    --(71, DataClass (cd,_) _ _,[Object _ (DataSmallInteger size)]) -> fmap Just (classNewWithArg cd size)
    (75, _, []) -> fmap (Just . intObject) (objectIntHash receiver)
    (83, _, [Object "Symbol" (DataImmutableString True sel)]) -> fmap Just (objectPerform stCoreOpt receiver sel)
    (84, _, [Object "Symbol" (DataImmutableString True sel), arg]) -> fmap Just (objectPerformWithArguments stCoreOpt receiver sel arg)
    (100, _, [Object "Symbol" (DataImmutableString True sel), arg, cl]) -> fmap Just (objectPerformWithArgumentsInSuperclass stCoreOpt receiver sel arg cl)
    (110, _, [arg]) -> fmap Just (prObjectEqual receiver arg)
    (111, _, []) -> fmap Just (objectClass receiver)
    (113, DataSystem, [Object _ (DataSmallInteger x)]) -> fmap Just (prSystemExit x)
    (148, _, []) -> fmap Just (objectShallowCopy receiver)
    (170, DataClass {}, [Object _ (DataSmallInteger ix)]) -> return (Just (characterObject (toEnum ix)))
    (171, DataCharacter char, []) -> return (Just (intObject (fromEnum char)))
    _ -> stPrimitivesC (prClass, prMethod) prCode receiver arguments

stCoreOpt :: CoreOpt
stCoreOpt = CoreOpt SmalltalkSystem (intObject . fromInteger, strObject) stPrimitives
