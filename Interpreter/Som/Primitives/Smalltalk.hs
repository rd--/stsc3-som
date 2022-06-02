{-# Language FlexibleContexts #-}

{- | Smalltalk primitives indicate success by returning (Just answer) and failure by returning Nothing.
Error handling and delegation is in the standard library.
-}
module Interpreter.Som.Primitives.Smalltalk where

import Control.Monad.IO.Class {- base -}
import Data.Bits {- base -}
import System.Exit {- base -}
import System.Mem {- base -}

import System.Random {- random -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Ansi.Expr as St {- stsc3 -}

import Interpreter.Som.Core
import Interpreter.Som.Error
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

-- * Util

intObject :: SmallInteger -> Object
intObject x = Object (toSymbol "SmallInteger") (DataSmallInteger x)

strObject :: String -> Object
strObject = immutableStringObject

symObject :: String -> Object
symObject = immutableSymbolObject

-- | Basis for isLetters and isDigits and isWhiteSpace.  Null strings are false.
prStringAll :: (Char -> Bool) -> UnicodeString -> Object
prStringAll f = booleanObject . unicodeStringAll f

prSystemLoadFile :: (StError m, MonadIO m) => UnicodeString -> m Object
prSystemLoadFile aString = do
    let fn = fromUnicodeString aString
        onFailure = return nilObject
    maybeText <- liftIO (readFileMaybe fn)
    maybe onFailure (return . strObject) maybeText

prQuit :: MonadIO m => SmallInteger -> m t
prQuit exitCode = liftIO (if exitCode == 0 then exitSuccess else exitWith (ExitFailure exitCode))

{- | Class>>fields => Array[Symbol]

This is Behaviour>>allInstVarNames and Class>>allClassVarNames in Smalltalk, which are not primitive.
-}
prClassFields :: St.ClassDefinition -> Bool -> Vm Object
prClassFields cd isMeta =
  case isMeta of
    False -> do
      fld <- classAllVariableNames St.classInstanceVariableNames cd
      arrayFromList (map symObject fld)
    True -> do
      fld <- classAllVariableNames St.classVariableNames cd
      arrayFromList (map symObject fld)

prMethodInvokeOnWith :: CoreOpt -> ObjectData -> Object -> Object -> Vm Object
prMethodInvokeOnWith opt obj receiver argumentsArray = do
  arguments <- arrayElements argumentsArray
  evalMethodOrPrimitive opt obj receiver arguments

prMethodArray :: Object -> Vm (Maybe Object)
prMethodArray rcv =
  case classCachedMethods rcv of
    Nothing -> return Nothing
    Just mth  -> fmap Just (arrayFromIndexedMap mth)

fmapMaybeM :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
fmapMaybeM f = maybe (return Nothing) (fmap Just . f)

mapMM :: Monad m => (a -> m b) -> m (Maybe a) -> m (Maybe b)
mapMM f x = fmapMaybeM f =<< x

mapMMM :: Monad m => (a -> m (Maybe b)) -> m (Maybe a) -> m (Maybe b)
mapMMM f x = maybe (return Nothing) f =<< x

prPrintString :: Object -> Vm (Maybe Object)
prPrintString (Object _ obj) = do
  let wr str = liftIO (unicodeStringWrite str) >> return nilObject
  mapMM wr (objectDataAsString obj)

prAllInstVarNames :: St.ClassDefinition -> Vm (Maybe Object)
prAllInstVarNames cd = do
  nm <- classAllVariableNamesFor cd False
  fmap Just (arrayFromList (map symObject nm))

prAllClassVarNames :: St.ClassDefinition -> Vm (Maybe Object)
prAllClassVarNames cd = do
  nm <- classAllVariableNamesFor cd True
  fmap Just (arrayFromList (map symObject nm))

stPrimitivesC :: PrimitiveDispatcher
stPrimitivesC (prClass, prMethod) _prCode receiver@(Object _ receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("allInstVarNames", DataClass (cd, False) _ _, []) -> prAllInstVarNames cd
    ("allClassVarNames", DataClass (cd, False) _ _, []) -> prAllClassVarNames cd
    ("asString", DataDouble x, []) -> fmap Just (mutableStringObject False (show x))
    ("asSymbol", _, []) -> if prClass == "Symbol" then return (Just receiver) else fmap (fmap symObject) (objectDataAsString receiverObj)
    ("atRandom", DataSmallInteger x, []) -> fmap (Just . intObject) (liftIO (getStdRandom (randomR (1, x))))
    ("atRandom", DataDouble x, []) -> fmap (Just . doubleObject) (liftIO (getStdRandom (randomR (0, x))))
    ("evaluate:", DataSystem, [Object "String" str]) -> mapMMM (evalString stCoreOpt) (objectDataAsString str)
    ("fields", DataClass (cd,isMeta) _ _, []) -> fmap Just (prClassFields cd isMeta)
    ("fromString:", DataClass {}, [Object _ (DataImmutableString x)]) ->
      case prClass of
        "Double class" -> return (Just (maybe nanObject doubleObject (unicodeStringReadDouble x)))
        "SmallInteger class" -> return (fmap intObject (unicodeStringReadSmallInteger x))
        _ -> return Nothing
    ("garbageCollect", DataSystem, []) -> liftIO System.Mem.performMajorGC >> return (Just nilObject)
    ("global:", DataSystem, [Object "Symbol" str]) -> mapMMM vmGlobalLookupMaybe (objectDataAsString str)
    ("global:put:", DataSystem, [Object "Symbol" str, e]) -> mapMM (\sym -> vmGlobalAssign sym e) (objectDataAsString str)
    ("hasGlobal:", DataSystem, [Object "Symbol" str]) -> mapMM (fmap booleanObject . vmHasGlobal) (objectDataAsString str)
    ("inspect", _, []) -> fmap Just (objectInspectAndPrint receiver)
    ("invokeOn:with:", DataMethod {}, [arg1, arg2]) -> fmap Just (prMethodInvokeOnWith stCoreOpt receiverObj arg1 arg2)
    ("load:", DataSystem, [Object "Symbol" str]) -> mapMM systemLoadClassOrNil (objectDataAsString str)
    ("loadFile:", DataSystem, [Object "String" str]) -> mapMM prSystemLoadFile (objectDataAsString str)
    ("methodArray", DataClass {}, []) -> prMethodArray receiver
    ("methodClass", DataMethod methodClass _ _,[]) -> fmap Just (vmGlobalResolveOrError methodClass)
    ("name", DataClass (cd, isMeta) _ _, []) -> return (Just (symObject ((if isMeta then St.metaclassName else id) (St.className cd))))
    ("numArgs", DataBlockClosure _ _ (St.Lambda _ args _ _), []) -> return (Just (intObject (length args)))
    ("on:do:", DataBlockClosure {}, [exception, handler]) -> evalBlockWithMaybeExceptionHandler stCoreOpt receiver [] (Just (exception, handler))
    ("perform:inSuperclass:", _, [Object "Symbol" str, cl]) -> mapMM (\sym -> objectPerformInSuperclass stCoreOpt receiver sym cl) (objectDataAsString str)
    ("primitive", DataMethod _ mth _, []) -> return (fmap (literalObject stLiteralConstructors) (St.methodDefinitionPrimitiveLabel mth))
    ("primSubstringFrom:to:", _, [Object _ (DataSmallInteger int1), Object _ (DataSmallInteger int2)]) -> mapMM (\str -> return (strObject (unicodeStringSubstringFromTo str int1 int2))) (objectDataAsString receiverObj)
    ("printCharacter:", DataSystem, [Object _ (DataCharacter ch)]) -> liftIO (putChar ch) >> return (Just nilObject)
    ("printContext", DataSystem, []) -> vmContext >>= vmContextPrint >> return (Just nilObject)
    ("printString:", DataSystem, [str]) -> prPrintString str
    ("sender", DataContext ctx, []) -> return (fmap (Object "Context" . DataContext) (contextSender ctx))
    ("signal", _, []) -> return (Just (exceptionObject receiver))
    ("selector", DataContext ctx, []) -> return (fmap (symObject . contextSelector) (contextNearestMethod ctx))
    ("selector", DataMethod _ mth _, []) -> return (Just (symObject (St.selectorIdentifier (St.methodSelector mth))))
    ("superclass", DataClass (cd,isMeta) _ _,[]) -> fmap Just (classSuperclass cd isMeta)
    ("utcOffset", DataSystem, []) -> fmap (Just . intObject) getSystemTimezoneInSeconds
    ("utcTime", DataSystem, []) -> fmap (Just . intObject . secondsToMicroseconds) getSystemTimeInSeconds
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
   else Data.Bits.shiftR lhs (negate rhs))

prValueWithArguments :: Object -> Object -> Vm (Maybe Object)
prValueWithArguments receiver (Object _ argumentsArray) = do
  maybeList <- objectDataAsArray argumentsArray
  case maybeList of
    Just lst -> evalBlock stCoreOpt receiver lst
    Nothing -> return Nothing

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
    (13, DataSmallInteger lhs, [Object _ (DataSmallInteger rhs)]) -> return (Just (intObject (lhs `quot` rhs)))
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
    (57, DataDouble x, []) -> return (Just (doubleObject (atan x)))
    (58, DataDouble x, []) -> return (Just (doubleObject (log x)))
    (59, DataDouble x, []) -> return (Just (doubleObject (exp x)))
    (60, DataArrayLiteral vec, [Object _ (DataSmallInteger ix)]) -> return (vecAtMaybe vec (ix - 1))
    (60, DataIndexable _ ref, [Object _ (DataSmallInteger ix)]) -> vecRefAtMaybe ref (ix - 1) -- basicAt: at:
    (61, DataIndexable _ ref, [Object _ (DataSmallInteger ix), value]) -> vecRefAtPutMaybe ref (ix - 1) value -- basicAt:put: at:put:
    (62, DataArrayLiteral vec, []) -> return (Just (intObject (vecLength vec))) -- basicSize size
    (62, DataIndexable _ ref, []) -> deRef ref >>= \vec -> return (Just (intObject (vecLength vec)))
    (62, DataCharacterArray _ ref, []) -> deRef ref >>= \vec -> return (Just (intObject (vecLength vec)))
    (62, DataImmutableString str, []) -> return (Just (intObject (unicodeStringLength str)))
    (63, DataImmutableString str, [Object _ (DataSmallInteger ix)]) -> return (fmap characterObject (unicodeStringAt str ix))
    (63, DataCharacterArray _ ref, [Object _ (DataSmallInteger ix)]) -> fmap (fmap characterObject) (vecRefAtMaybe ref (ix - 1))
    (64, DataCharacterArray _ ref, [Object _ (DataSmallInteger ix), Object _ (DataCharacter ch)]) -> fmap (fmap characterObject) (vecRefAtPutMaybe ref (ix - 1) ch)
    -- 65 next
    (70, DataClass (cd,_) _ _,[]) -> fmap Just (classNew cd) -- basicNew
    (71, DataClass (cd,_) _ _,[Object _ (DataSmallInteger size)]) -> classNewWithArg cd size -- basicNew:
    (73, DataNonIndexable _ tbl, [Object _ (DataSmallInteger ix)]) -> tblAtMaybe tbl (ix - 1) -- instVarAt:
    (74, DataNonIndexable _ tbl, [Object _ (DataSmallInteger ix), newObject]) -> tblAtPutMaybe tbl (ix - 1) newObject -- instVarAt:put:
    (75, _, []) -> fmap (Just . intObject) (objectHash receiver) -- identityHash
    (81, DataBlockClosure {}, []) -> evalBlock stCoreOpt receiver [] -- value value: &etc.
    (81, DataBlockClosure {}, [arg1]) -> evalBlock stCoreOpt receiver [arg1]
    (81, DataBlockClosure {}, [arg1, arg2]) -> evalBlock stCoreOpt receiver [arg1, arg2]
    (81, DataBlockClosure {}, [arg1, arg2, arg3]) -> evalBlock stCoreOpt receiver [arg1, arg2, arg3]
    (81, DataBlockClosure {}, [arg1, arg2, arg3, arg4]) -> evalBlock stCoreOpt receiver [arg1, arg2, arg3, arg4]
    (81, DataBlockClosure {}, [arg1, arg2, arg3, arg4, arg5]) -> evalBlock stCoreOpt receiver [arg1, arg2, arg3, arg4, arg5]
    (82, DataBlockClosure {}, [argumentsArray]) -> prValueWithArguments receiver argumentsArray -- value:withArguments:
    (83, _, [Object "Symbol" (DataImmutableString sel)]) -> fmap Just (objectPerform stCoreOpt receiver sel) -- perform: perform:with:
    (84, _, [Object "Symbol" (DataImmutableString sel), arg]) -> fmap Just (objectPerformWithArguments stCoreOpt receiver sel arg) -- perform:withArguments:
    (100, _, [Object "Symbol" (DataImmutableString sel), arg, cl]) -> fmap Just (objectPerformWithArgumentsInSuperclass stCoreOpt receiver sel arg cl) -- perform:withArguments:inSuperclass:
    (110, _, [arg]) -> fmap (Just . booleanObject) (objectIdentical receiver arg) -- ==
    (111, _, []) -> fmap Just (objectClass receiver) -- class species
    (113, DataSystem, [Object _ (DataSmallInteger x)]) -> fmap Just (prQuit x)
    (114, _, []) -> vmErrorWithBacktrace "halt" [receiver] -- ExitToDebugger
    (130, DataSystem, []) -> liftIO System.Mem.performMajorGC >> return (Just (intObject 0))
    (148, _, []) -> fmap Just (objectShallowCopy receiver) -- shallowCopy
    (170, DataClass {}, [Object _ (DataSmallInteger ix)]) -> return (Just (characterObject (toEnum ix)))
    (171, DataCharacter char, []) -> return (Just (intObject (fromEnum char)))
    _ -> stPrimitivesC (prClass, prMethod) prCode receiver arguments

stLiteralConstructors :: LiteralConstructors
stLiteralConstructors = (intObject . fromInteger, strObject, symObject)

stCoreOpt :: CoreOpt
stCoreOpt = CoreOpt SmalltalkSystem stLiteralConstructors stPrimitives
