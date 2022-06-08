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

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Som as Som {- stsc3 -}

import Interpreter.Som.Eval
import Interpreter.Som.Int
import Interpreter.Som.Ref
import Interpreter.Som.Str
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
type SomPrimitiveDispatcher = SomPrimitiveOf (Vm Object)

-- * Util

intObject :: LargeInteger -> Object
intObject x = Object (toSymbol "Integer") (DataLargeInteger x)

strObject :: String -> Object
strObject = immutableStringObject . Som.somEscapedString

symObject :: String -> Object
symObject = immutableSymbolObject

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

prArrayAt :: (StError m, MonadIO m) => VecRef Object -> LargeInteger -> m Object
prArrayAt ref ix = vecRefAtMaybe ref (fromInteger ix - 1) >>= maybe (prError "Array>>at: index out of range") return

-- | Basis for isLetters and isDigits and isWhiteSpace.  Null strings are false.
prStringAll :: (Char -> Bool) -> UnicodeString -> Object
prStringAll f = booleanObject . unicodeStringAll f

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
    let fn = fromUnicodeString aString
        onFailure = return nilObject
    maybeText <- liftIO (readFileMaybe fn)
    maybe onFailure (return . strObject) maybeText

prSystemExit :: MonadIO m => LargeInteger -> m Object
prSystemExit exitCode =
  let actuallyExit = False
  in if actuallyExit
     then liftIO (if exitCode == 0 then exitSuccess else exitWith (ExitFailure (fromInteger exitCode)))
     else liftIO (putStrLn (printf "exit: %d" exitCode)) >> return nilObject

prStringEqual :: (String, String) -> Object -> Object
prStringEqual (lhsClass, lhs) obj =
  case obj of
    Object rhsClass (DataImmutableString rhs) ->
      booleanObject ((lhsClass == rhsClass || (lhsClass == "String" && rhsClass == "Symbol")) && lhs == rhs)
    _ -> booleanObject False

-- | Primitives with no requirements that, given types have matched, do not fail.
somPrimitivesO :: SomPrimitiveOf (Maybe Object)
somPrimitivesO (prClass, prMethod) (Object receiverName receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("&", DataLargeInteger lhs, [Object _ (DataLargeInteger rhs)]) -> Just (intObject (lhs Data.Bits..&. rhs))
    ("<", DataLargeInteger lhs, [Object _ rhs]) -> intNumBoolPrimitive Nothing (<) (<) lhs rhs
    ("<<", DataLargeInteger lhs, [Object _ (DataLargeInteger rhs)]) -> Just (intObject (largeIntegerShiftLeft lhs rhs))
    ("=", DataImmutableString lhs, [rhs]) -> Just (prStringEqual (receiverName, lhs) rhs)
    ("=", DataLargeInteger lhs, [Object _ rhs]) -> intNumBoolPrimitive (Just falseObject) (==) (==) lhs rhs
    (">>>", DataLargeInteger lhs, [Object _ (DataLargeInteger rhs)]) -> Just (intObject (largeIntegerShiftRight lhs rhs))
    ("PositiveInfinity", DataClass {}, []) -> Just (doubleObject (read "Infinity"))
    ("as32BitSignedValue", DataLargeInteger x, []) -> Just (intObject (as32BitSignedValue x))
    ("as32BitUnsignedValue", DataLargeInteger x, []) -> Just (intObject (as32BitUnsignedValue x))
    ("asDouble", DataLargeInteger x, []) -> Just (doubleObject (fromIntegral x))
    ("asInteger", DataDouble x, []) -> Just (intObject (truncate x)) -- Som?
    ("asString", DataDouble x, []) -> Just (strObject (show x))
    ("asString", DataImmutableString x, []) -> Just (strObject x)
    ("asString", DataLargeInteger x, []) -> Just (strObject (show x))
    ("asSymbol", DataImmutableString x, []) -> Just (symObject x)
    ("bitXor:", DataLargeInteger lhs, [Object _ (DataLargeInteger rhs)]) -> Just (intObject (Data.Bits.xor lhs rhs))
    ("concatenate:", DataImmutableString x, [Object _ (DataImmutableString y)]) -> Just (strObject (unicodeStringAppend x y))
    ("cos", DataDouble x, []) -> Just (doubleObject (cos x))
    ("fromString:", DataClass {}, [Object _ (DataImmutableString x)]) ->
      case prClass of
        "Integer class" -> fmap intObject (unicodeStringReadLargeInteger x)
        "Double class" -> Just (maybe nanObject doubleObject (unicodeStringReadDouble x))
        _ -> Nothing
    ("holder", DataPrimitive x _, []) -> Just (symObject x)
    ("isDigits", DataImmutableString str, []) -> Just (prStringAll Data.Char.isDigit str)
    ("isLetters", DataImmutableString str, []) -> Just (prStringAll Data.Char.isLetter str)
    ("isWhiteSpace", DataImmutableString str, []) -> Just (prStringAll Data.Char.isSpace str)
    ("length", DataImmutableString str, []) -> Just (intObject (toLargeInteger (unicodeStringLength str)))
    ("primSubstringFrom:to:", DataImmutableString str, [Object _ (DataLargeInteger int1), Object _ (DataLargeInteger int2)]) -> Just (strObject (unicodeStringSubstringFromTo str (fromLargeInteger int1) (fromLargeInteger int2)))
    ("round", DataDouble x, []) -> Just (intObject (round x)) -- Som (roundTowardPositive in IEEE 754-2008)
    ("signature", DataMethod _ mth _, []) -> Just (symObject (St.selectorIdentifier (St.methodSelector mth)))
    ("signature", DataPrimitive _ x, []) -> Just (symObject x)
    ("sin", DataDouble x, []) -> Just (doubleObject (sin x))
    ("sqrt", DataDouble x, []) -> Just (doubleObject (sqrt x))
    _ -> Nothing

-- | Primitives with no requirements that may fail.
somPrimitivesM :: SomPrimitiveOf (Maybe Object)
somPrimitivesM (prClass, prMethod) receiver@(Object _receiverName receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("%", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive doubleMod lhs rhs
    ("%", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive mod mod' lhs rhs
    ("*", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (*) lhs rhs
    ("*", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (*) (*) lhs rhs
    ("+", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (+) lhs rhs
    ("+", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (+) (+) lhs rhs
    ("-", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (-) lhs rhs
    ("-", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive (-) (-) lhs rhs
    ("/", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive div (/) lhs rhs -- ? Som 1/2=0
    ("//", DataDouble lhs, [Object _ rhs]) -> doubleNumDoublePrimitive (/) lhs rhs -- Som?
    ("//", lhs, [Object _ rhs]) -> numNumNumPrimitive (/) lhs rhs
    ("<", DataDouble lhs, [Object _ rhs]) -> doubleNumBoolPrimitive (<) lhs rhs
    ("=", DataDouble lhs, [Object _ rhs]) -> doubleNumBoolPrimitive (==) lhs rhs
    ("rem:", DataLargeInteger lhs, [Object _ rhs]) -> intNumNumPrimitive rem undefined lhs rhs
    ("restart", DataBlockClosure {}, []) -> Nothing -- not implemented
    ("sqrt", _, []) -> numNumPrimitive sqrt receiverObj
    _ -> somPrimitivesO (prClass, prMethod) receiver arguments

prAtPut :: (MonadIO m, StError m) => VecRef t -> Int -> t -> m t
prAtPut ref ix value = do
  answer <- vecRefAtPutMaybe ref (ix - 1) value
  case answer of
    Nothing -> prError "at:put:"
    Just sent -> return sent

{- | Primitives that require Io but not Vm state.

Notes:
Block>>restart is not implemented, for now the single use in the class library (Block>>whileTrue:) should be modified to call itself.
String>>= has the rule (in the Som tests) is 'x' = #x but #x ~= 'x'
System>>loadFile: if the file does not exist returns nil, i.e. does not error.
-}
somPrimitivesI :: (StError m, MonadIO m) => SomPrimitiveOf (m Object)
somPrimitivesI (prClass, prMethod) receiver@(Object receiverName receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("==", _, [arg]) -> fmap booleanObject (objectHashEqual receiver arg)
    ("at:", DataIndexable _ ref, [Object _ (DataLargeInteger ix)]) -> prArrayAt ref ix
    ("at:put:", DataIndexable _ ref, [Object _ (DataLargeInteger ix), value]) -> prAtPut ref (fromInteger ix) value
    ("atRandom", DataLargeInteger x, []) -> fmap intObject (liftIO (getStdRandom (randomR (0, x - 1))))
    ("errorPrintln:", DataSystem, [Object _ (DataImmutableString x)]) -> liftIO (unicodeStringWrite x >> putChar '\n') >> error "System>>error"
    ("exit:", DataSystem, [Object _ (DataLargeInteger x)]) -> prSystemExit x
    ("fullGC", DataSystem, []) -> liftIO System.Mem.performMajorGC >> return trueObject
    ("hashcode", _, []) -> fmap (intObject . fromIntegral) (objectHash receiver)
    ("instVarAt:", DataNonIndexable _ tbl, [Object _ (DataLargeInteger ix)]) -> tblAtDefault tbl (fromLargeInteger ix - 1) (prError "Object>>instVarAt:")
    ("instVarAt:put:", DataNonIndexable _ tbl, [Object _ (DataLargeInteger ix), newObject]) -> tblAtPutDefault tbl (fromLargeInteger ix - 1) newObject (prError "Object>>instVarAt:put")
    ("instVarNamed:", DataNonIndexable _ tbl, [Object "Symbol" (DataImmutableString key)]) -> tblAtKeyDefault tbl (fromUnicodeString key) (prError "Object>>instVarNamed:")
    ("length", DataIndexable _ ref, []) -> deRef ref >>= \v -> return (intObject (fromIntegral (vecLength v)))
    ("loadFile:", DataSystem, [Object "String" (DataImmutableString x)]) -> prSystemLoadFile x
    ("name", DataClass (cd, isMeta) _ _, []) -> return (symObject ((if isMeta then St.metaclassName else id) (St.className cd)))
    ("printNewline", DataSystem, []) -> liftIO (putChar '\n') >> return nilObject
    ("printString:", DataSystem, [Object _ (DataImmutableString x)]) -> liftIO (unicodeStringWrite x) >> return nilObject
    _ ->
      case somPrimitivesM (prClass, prMethod) receiver arguments of
        Just answer -> return answer
        Nothing -> prError (printf "%s>>%s (rcv: '%s', arity: %d, types: '%s')"
                             prClass
                             prMethod
                             (fromSymbol receiverName)
                             (length arguments)
                             (unwords (map objectClassName arguments)))

{- | Primitives that require access to Vm state.

Notes:
System>>ticks is elapsed time in microseconds.
System>>time is elapsed time in milliseconds.
-}
somPrimitivesV :: SomPrimitiveDispatcher
somPrimitivesV (prClass, prMethod) receiver@(Object _receiverName receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("global:", DataSystem, [Object "Symbol" (DataImmutableString x)]) -> vmGlobalLookupOrNil (fromUnicodeString x)
    ("global:put:", DataSystem, [Object "Symbol" (DataImmutableString x), e]) -> vmGlobalAssignOrCreate (fromUnicodeString x) e
    ("hasGlobal:", DataSystem, [Object "Symbol" (DataImmutableString x)]) -> fmap booleanObject (vmHasGlobal (fromUnicodeString x))
    ("methods", _, []) -> maybe (prError "Class>>methods") arrayFromIndexedMap (classCachedMethods receiver)
    ("new:", DataClass {},[Object _ (DataLargeInteger size)]) -> arrayFromList (genericReplicate size nilObject)
    ("ticks", DataSystem, []) -> fmap (intObject . toLargeInteger) vmElapsedTimeInMicroseconds
    ("time", DataSystem, []) -> fmap (intObject . toLargeInteger . (`div` 1000)) vmElapsedTimeInMicroseconds
    _ -> somPrimitivesI (prClass, prMethod) receiver arguments

{- | Class>>fields => Array[Symbol]

This is Behaviour>>allInstVarNames and Class>>allClassVarNames in Smalltalk, which are not primitive.
-}
prClassFields :: St.ClassDefinition -> Bool -> Vm Object
prClassFields cd isMeta = arrayFromList . map symObject =<< classAllVariableNamesFor cd isMeta

prMethodInvokeOnWith :: EvalOpt -> ObjectData -> Object -> Object -> Vm Object
prMethodInvokeOnWith opt obj receiver argumentsArray = do
  arguments <- arrayElements argumentsArray
  evalMethodOrPrimitive opt obj receiver arguments

-- | Primitives that require functions from Core.
somPrimitivesC :: SomPrimitiveDispatcher
somPrimitivesC (prClass, prMethod) receiver@(Object _ receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("class", _, []) -> objectClass receiver
    ("fields", DataClass (cd,isMeta) _ _, []) -> prClassFields cd isMeta
    ("holder", DataMethod holder _ _,[]) -> vmGlobalResolveOrError holder
    ("inspect", _, []) -> objectInspectAndPrint receiver
    ("invokeOn:with:", DataPrimitive {}, [_,_]) -> vmError "Primitive>>invokeOn:with: not implemented"
    ("invokeOn:with:", rcv, [arg1, arg2]) -> prMethodInvokeOnWith somEvalOpt rcv arg1 arg2
    ("load:", DataSystem, [Object "Symbol" (DataImmutableString x)]) -> systemLoadClassOrNil (fromUnicodeString x)
    ("new", DataClass (cd,_) _ _,[]) -> classNew cd
    ("perform:", _, [Object "Symbol" (DataImmutableString sel)]) -> objectPerform somEvalOpt receiver sel
    ("perform:inSuperclass:", _, [Object "Symbol" (DataImmutableString sel), cl]) -> objectPerformInSuperclass somEvalOpt receiver sel cl
    ("perform:withArguments:", _, [Object "Symbol" (DataImmutableString sel), arg]) -> objectPerformWithArguments somEvalOpt receiver sel arg
    ("perform:withArguments:inSuperclass:", _, [Object "Symbol" (DataImmutableString sel), arg, cl]) -> objectPerformWithArgumentsInSuperclass somEvalOpt receiver sel arg cl
    ("superclass", DataClass (cd,isMeta) _ _,[]) -> classSuperclass cd isMeta
    _ -> somPrimitivesV (prClass, prMethod) receiver arguments

somPrimitives :: PrimitiveDispatcher
somPrimitives hs@(_prClass, prMethod) _cd receiver@(Object _ receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("value", DataBlockClosure {}, []) -> evalBlock somEvalOpt receiver []
    ("value:", DataBlockClosure {}, [arg]) -> evalBlock somEvalOpt receiver [arg]
    ("value:with:", DataBlockClosure {}, [arg1, arg2]) -> evalBlock somEvalOpt receiver [arg1, arg2]
    _ -> fmap Just (somPrimitivesC hs receiver arguments)

somEvalOpt :: EvalOpt
somEvalOpt = EvalOpt SomSystem (intObject, strObject, symObject . Som.somEscapedString) somPrimitives

{-
> fromIntegral (maxBound::Int) >= ((2::Integer) ^ 62) -- True
> (((maxBound::Int) `div` (10^6)) `div` (60 * 60 * 24 * 365)) == 292471
> (((2^64) `div` (10^6)) `div` (60 * 60 * 24 * 365)) == 584942
-}
