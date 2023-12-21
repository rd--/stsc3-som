{-# LANGUAGE FlexibleContexts #-}

{- | Smalltalk primitives indicate success by returning (Just answer) and failure by returning Nothing.
Error handling and delegation is in the standard library.
-}
module Interpreter.Som.Primitives.Smalltalk where

import Control.Concurrent {- base -}
import qualified Control.Concurrent.MVar as MVar {- base -}
import Control.Monad.IO.Class {- base -}
import Data.Bits {- base -}
import Data.Word {- base -}
import System.Exit {- base -}
import System.Mem {- base -}

import qualified Data.ByteString {- bytestring -}
import qualified Network.Socket {- network -}
import qualified Network.Socket.ByteString {- network -}
import qualified System.Process {- process -}
import qualified System.Random {- random -}

import qualified Music.Theory.Byte {- hmt-base -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Ansi.Expr as St {- stsc3 -}

import Interpreter.Som.Eval
import Interpreter.Som.Int
import Interpreter.Som.Ref
import Interpreter.Som.Str
import Interpreter.Som.Sym
import Interpreter.Som.Sys
import Interpreter.Som.Tbl
import Interpreter.Som.Time
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

prMethodInvokeOnWith :: EvalOpt -> ObjectData -> Object -> Object -> Vm Object
prMethodInvokeOnWith opt obj receiver argumentsArray = do
  arguments <- arrayElements argumentsArray
  evalMethodOrPrimitive opt obj receiver arguments

prMethodArray :: Object -> Vm (Maybe Object)
prMethodArray rcv =
  case classCachedMethods rcv of
    Nothing -> return Nothing
    Just mth -> fmap Just (arrayFromIndexedMap mth)

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

prReadTextFile :: ObjectData -> Vm (Maybe Object)
prReadTextFile aFileName = do
  maybeFileName <- objectDataAsString aFileName
  case maybeFileName of
    Just fileName -> liftIO (readFile fileName) >>= return . Just . strObject
    _ -> return Nothing

prWriteStringToTextFile :: ObjectData -> ObjectData -> Vm (Maybe Object)
prWriteStringToTextFile aString aFileName = do
  maybeString <- objectDataAsString aString
  maybeFileName <- objectDataAsString aFileName
  case (maybeString, maybeFileName) of
    (Just string, Just fileName) -> liftIO (writeFile fileName string) >> return (Just nilObject)
    _ -> return Nothing

prWriteByteArrayToBinaryFile :: VecRef Word8 -> ObjectData -> Vm (Maybe Object)
prWriteByteArrayToBinaryFile aVecRef aFileName = do
  bytes <- vecRefToList aVecRef
  maybeFileName <- objectDataAsString aFileName
  case maybeFileName of
    Just fileName -> liftIO (Data.ByteString.writeFile fileName (Data.ByteString.pack bytes)) >> return (Just nilObject)
    _ -> return Nothing

prSystemCommand :: ObjectData -> Vm (Maybe Object)
prSystemCommand aString = do
  maybeString <- objectDataAsString aString
  case maybeString of
    Just string -> liftIO (System.Process.callCommand string) >> return (Just nilObject)
    _ -> return Nothing

sendUdpPacket :: String -> Int -> Data.ByteString.ByteString -> IO ()
sendUdpPacket host port bytes = do
  fd <- Network.Socket.socket Network.Socket.AF_INET Network.Socket.Datagram 0
  let hints = Network.Socket.defaultHints {Network.Socket.addrFamily = Network.Socket.AF_INET} -- localhost=ipv4
  i : _ <- Network.Socket.getAddrInfo (Just hints) (Just host) (Just (show port))
  let sa = Network.Socket.addrAddress i
  Network.Socket.connect fd sa
  Network.Socket.ByteString.sendAllTo fd bytes sa
  Network.Socket.close fd

prSendUdp :: VecRef Word8 -> ObjectData -> Int -> Vm (Maybe Object)
prSendUdp bytes hostString port = do
  bytes' <- fmap Data.ByteString.pack (vecRefToList bytes)
  maybeHost <- objectDataAsString hostString
  case maybeHost of
    Nothing -> return Nothing
    Just host -> liftIO (sendUdpPacket host port bytes') >> return (Just nilObject)

stPrimitivesC :: PrimitiveDispatcher
stPrimitivesC (prClass, prMethod) _prCode receiver@(Object _ receiverObj) arguments =
  case (prMethod, receiverObj, arguments) of
    ("allInstVarNames", DataClass (cd, False) _ _, []) -> prAllInstVarNames cd
    ("allClassVarNames", DataClass (cd, False) _ _, []) -> prAllClassVarNames cd
    ("asIEEE32BitWord", DataDouble x, []) -> return (Just (intObject (fromIntegral (Music.Theory.Byte.castFloatToWord32 (realToFrac x)))))
    ("asString", DataDouble x, []) -> fmap Just (mutableStringObject False (show x))
    ("asSymbol", _, []) -> if prClass == "Symbol" then return (Just receiver) else fmap (fmap symObject) (objectDataAsString receiverObj)
    ("atRandom", DataSmallInteger x, []) -> fmap (Just . intObject) (liftIO (System.Random.getStdRandom (System.Random.randomR (1, x))))
    ("atRandom", DataDouble x, []) -> fmap (Just . doubleObject) (liftIO (System.Random.getStdRandom (System.Random.randomR (0, x))))
    ("evaluate:", DataSystem, [Object "String" str]) -> mapMMM (evalString stEvalOpt) (objectDataAsString str)
    ("fields", DataClass (cd, isMeta) _ _, []) -> fmap Just (prClassFields cd isMeta)
    ("fork", DataBlockClosure {}, []) -> fmap Just (threadObject stEvalOpt receiver)
    ("fromIEEE32Bit:", DataClass {}, [Object _ (DataSmallInteger x)]) -> return (Just (doubleObject (realToFrac (Music.Theory.Byte.castWord32ToFloat (fromIntegral x)))))
    ("fromString:", DataClass {}, [Object _ (DataImmutableString x)]) ->
      case prClass of
        "Double class" -> return (Just (maybe nanObject doubleObject (unicodeStringReadDouble x)))
        "SmallInteger class" -> return (fmap intObject (unicodeStringReadSmallInteger x))
        _ -> return Nothing
    ("garbageCollect", DataSystem, []) -> liftIO System.Mem.performMajorGC >> return (Just nilObject)
    ("global:", DataSystem, [Object "Symbol" str]) -> mapMMM vmGlobalLookupMaybe (objectDataAsString str)
    ("global:put:", DataSystem, [Object "Symbol" str, e]) -> mapMM (\sym -> vmGlobalAssignOrCreate sym e) (objectDataAsString str)
    ("globalKeys", DataSystem, []) -> fmap Just (arrayFromList . map symObject =<< vmGlobalDictAllKeys)
    ("hasGlobal:", DataSystem, [Object "Symbol" str]) -> mapMM (fmap booleanObject . vmHasGlobal) (objectDataAsString str)
    ("inspect", _, []) -> fmap Just (objectInspectAndPrint receiver)
    ("invokeOn:with:", DataMethod {}, [arg1, arg2]) -> fmap Just (prMethodInvokeOnWith stEvalOpt receiverObj arg1 arg2)
    ("kill", DataThread threadId, []) -> liftIO (killThread threadId) >> return (Just nilObject)
    ("load:", DataSystem, [Object "Symbol" str]) -> mapMM systemLoadClassOrNil (objectDataAsString str)
    ("loadFile:", DataSystem, [Object "String" str]) -> mapMM prSystemLoadFile (objectDataAsString str)
    ("log2", DataDouble x, []) -> return (Just (doubleObject (logBase 2 x)))
    ("methodArray", DataClass {}, []) -> prMethodArray receiver
    ("methodClass", DataMethod methodClass _ _, []) -> fmap Just (vmGlobalResolveOrError methodClass)
    ("name", DataClass (cd, isMeta) _ _, []) -> return (Just (symObject ((if isMeta then St.metaclassName else id) (St.className cd))))
    ("next", DataRandomGenerator _ rng, []) -> fmap (Just . doubleObject) (randomGeneratorNext rng)
    ("nextInt:", DataRandomGenerator _ rng, [Object _ (DataSmallInteger x)]) -> fmap (Just . intObject) (randomGeneratorNextInt rng x)
    ("numArgs", DataBlockClosure _ _ (St.Lambda _ args _ _), []) -> return (Just (intObject (length args)))
    ("on:do:", DataBlockClosure {}, [exception, handler]) -> evalBlockWithMaybeExceptionHandler stEvalOpt receiver [] (Just (exception, handler))
    ("sendUdpData:toHost:port:", DataSystem, [Object _ (DataByteArray _ aByteArray), Object _ hostAddress, Object _ (DataSmallInteger portNumber)]) -> prSendUdp aByteArray hostAddress portNumber
    ("threadDelayMicroseconds", DataSmallInteger x, []) -> liftIO (threadDelay x) >> return (Just receiver)
    ("perform:inSuperclass:", _, [Object "Symbol" str, cl]) -> mapMM (\sym -> objectPerformInSuperclass stEvalOpt receiver sym cl) (objectDataAsString str)
    ("primitive", DataMethod _ mth _, []) -> return (fmap (literalObject stLiteralConstructors) (St.methodDefinitionPrimitiveLabel mth))
    ("primSubstringFrom:to:", _, [Object _ (DataSmallInteger int1), Object _ (DataSmallInteger int2)]) -> mapMM (\str -> return (strObject (unicodeStringSubstringFromTo str int1 int2))) (objectDataAsString receiverObj)
    ("printCharacter:", DataSystem, [Object _ (DataCharacter ch)]) -> liftIO (if ch == carriageReturn then putChar lineFeed else putChar ch) >> return (Just nilObject)
    ("printContext", DataSystem, []) -> vmGetContext >>= contextPrint >> return (Just nilObject)
    ("printString:", DataSystem, [str]) -> prPrintString str
    ("randomGenerator", DataSmallInteger x, []) -> fmap Just (randomGeneratorObject x)
    ("readTextFile:", DataSystem, [Object "String" aFileName]) -> prReadTextFile aFileName
    ("sender", DataContext ctx, []) -> return (fmap contextObject (contextSender ctx))
    ("signal", _, []) -> signalException receiver
    ("selector", DataContext ctx, []) -> return (fmap (symObject . contextSelectorOrError) (contextNearestMethod ctx))
    ("selector", DataMethod _ mth _, []) -> return (Just (symObject (St.selectorIdentifier (St.methodSelector mth))))
    ("superclass", DataClass (cd, isMeta) _ _, []) -> fmap Just (classSuperclass cd isMeta)
    ("systemCommand:", DataSystem, [Object "String" aString]) -> prSystemCommand aString
    ("utcOffset", DataSystem, []) -> fmap (Just . intObject) getSystemTimezoneInSeconds
    ("utcTime", DataSystem, []) -> fmap (Just . intObject . secondsToMicroseconds) getSystemTimeInSeconds
    ("writeByteArray:toBinaryFile:", DataSystem, [Object "ByteArray" (DataByteArray _ aVecRef), Object "String" aFileName]) -> prWriteByteArrayToBinaryFile aVecRef aFileName
    ("writeString:toTextFile:", DataSystem, [Object "String" aString, Object "String" aFileName]) -> prWriteStringToTextFile aString aFileName
    _ -> return Nothing

prIntegerDivisionExact :: SmallInteger -> SmallInteger -> Maybe Object
prIntegerDivisionExact lhs rhs =
  if rhs == 0
    then Nothing
    else case divMod lhs rhs of
      (answer, 0) -> Just (intObject answer)
      _ -> Nothing

prBitShift :: SmallInteger -> SmallInteger -> Object
prBitShift lhs rhs =
  intObject
    ( if rhs >= 0
        then Data.Bits.shiftL lhs rhs
        else Data.Bits.shiftR lhs (negate rhs)
    )

prValueWithArguments :: Object -> Object -> Vm (Maybe Object)
prValueWithArguments receiver (Object _ argumentsArray) = do
  maybeList <- objectDataAsArray argumentsArray
  case maybeList of
    Just lst -> evalBlock stEvalOpt receiver lst
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
    (60, DataArrayLiteral vec, [Object _ (DataSmallInteger ix)]) -> return (vecAtMaybe vec (ix - 1)) -- basicAt: at:
    (60, DataIndexable _ ref, [Object _ (DataSmallInteger ix)]) -> vecRefAtMaybe ref (ix - 1)
    (60, DataByteArray _ ref, [Object _ (DataSmallInteger ix)]) -> fmap (fmap (intObject . fromIntegral)) (vecRefAtMaybe ref (ix - 1))
    (61, DataIndexable _ ref, [Object _ (DataSmallInteger ix), value]) -> vecRefAtPutMaybe ref (ix - 1) value -- basicAt:put: at:put:
    (61, DataByteArray _ ref, [Object _ (DataSmallInteger ix), Object _ (DataSmallInteger byte)]) -> fmap (fmap (intObject . fromIntegral)) (vecRefAtPutMaybe ref (ix - 1) (fromIntegral byte))
    (62, DataArrayLiteral vec, []) -> return (Just (intObject (vecLength vec))) -- basicSize size
    (62, DataIndexable _ ref, []) -> deRef ref >>= \vec -> return (Just (intObject (vecLength vec)))
    (62, DataCharacterArray _ ref, []) -> deRef ref >>= \vec -> return (Just (intObject (vecLength vec)))
    (62, DataByteArray _ ref, []) -> deRef ref >>= \vec -> return (Just (intObject (vecLength vec)))
    (62, DataImmutableString str, []) -> return (Just (intObject (unicodeStringLength str)))
    (63, DataImmutableString str, [Object _ (DataSmallInteger ix)]) -> return (fmap characterObject (unicodeStringAt str ix))
    (63, DataCharacterArray _ ref, [Object _ (DataSmallInteger ix)]) -> fmap (fmap characterObject) (vecRefAtMaybe ref (ix - 1))
    (64, DataCharacterArray _ ref, [Object _ (DataSmallInteger ix), Object _ (DataCharacter ch)]) -> fmap (fmap characterObject) (vecRefAtPutMaybe ref (ix - 1) ch)
    (65, DataMVar mvar, []) -> fmap Just (liftIO (MVar.takeMVar mvar)) -- next
    (66, DataMVar mvar, [obj]) -> liftIO (MVar.putMVar mvar obj) >> return (Just obj) -- nextPut:
    (70, DataClass (cd, _) _ _, []) -> fmap Just (classNew cd) -- basicNew
    (71, DataClass (cd, _) _ _, [Object _ (DataSmallInteger size)]) -> classNewWithArg cd size -- basicNew:
    (73, DataNonIndexable _ tbl, [Object _ (DataSmallInteger ix)]) -> tblAtMaybe tbl (ix - 1) -- instVarAt:
    (74, DataNonIndexable _ tbl, [Object _ (DataSmallInteger ix), newObject]) -> tblAtPutMaybe tbl (ix - 1) newObject -- instVarAt:put:
    (75, _, []) -> fmap (Just . intObject) (objectHash receiver) -- identityHash
    (81, DataBlockClosure {}, []) -> evalBlock stEvalOpt receiver [] -- value value: &etc.
    (81, DataBlockClosure {}, [arg1]) -> evalBlock stEvalOpt receiver [arg1]
    (81, DataBlockClosure {}, [arg1, arg2]) -> evalBlock stEvalOpt receiver [arg1, arg2]
    (81, DataBlockClosure {}, [arg1, arg2, arg3]) -> evalBlock stEvalOpt receiver [arg1, arg2, arg3]
    (81, DataBlockClosure {}, [arg1, arg2, arg3, arg4]) -> evalBlock stEvalOpt receiver [arg1, arg2, arg3, arg4]
    (81, DataBlockClosure {}, [arg1, arg2, arg3, arg4, arg5]) -> evalBlock stEvalOpt receiver [arg1, arg2, arg3, arg4, arg5]
    (82, DataBlockClosure {}, [argumentsArray]) -> prValueWithArguments receiver argumentsArray -- value:withArguments:
    (83, _, [Object "Symbol" (DataImmutableString sel)]) -> fmap Just (objectPerform stEvalOpt receiver sel) -- perform: perform:with:
    (84, _, [Object "Symbol" (DataImmutableString sel), arg]) -> fmap Just (objectPerformWithArguments stEvalOpt receiver sel arg) -- perform:withArguments:
    (100, _, [Object "Symbol" (DataImmutableString sel), arg, cl]) -> fmap Just (objectPerformWithArgumentsInSuperclass stEvalOpt receiver sel arg cl) -- perform:withArguments:inSuperclass:
    (110, _, [arg]) -> fmap (Just . booleanObject) (objectIdentical receiver arg) -- ==
    (111, _, []) -> fmap Just (objectClass receiver) -- class species
    (113, DataSystem, []) -> fmap Just (prQuit 0)
    (113, DataSystem, [Object _ (DataSmallInteger x)]) -> fmap Just (prQuit x)
    (114, _, []) -> vmErrorWithBacktrace "halt" [receiver] -- ExitToDebugger
    (130, DataSystem, []) -> liftIO System.Mem.performMajorGC >> return (Just (intObject 0))
    (148, _, []) -> fmap Just (objectShallowCopy receiver) -- shallowCopy
    (170, DataClass {}, [Object _ (DataSmallInteger ix)]) -> return (Just (characterObject (toEnum ix)))
    (171, DataCharacter char, []) -> return (Just (intObject (fromEnum char)))
    _ -> stPrimitivesC (prClass, prMethod) prCode receiver arguments

stLiteralConstructors :: LiteralConstructors
stLiteralConstructors = (intObject . fromInteger, strObject, symObject)

stEvalOpt :: EvalOpt
stEvalOpt = EvalOpt SmalltalkSystem stLiteralConstructors stPrimitives
