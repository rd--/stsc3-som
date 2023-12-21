{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{- | Type definitions and functions over these.

Some constructors are parameterized so that the types can be used both for a correct Som interpreter,
and for a more traditional Smalltalk interpreter.
-}
module Interpreter.Som.Types where

import Control.Concurrent {- base -}
import qualified Control.Concurrent.MVar as MVar {- base -}
import Control.Monad {- base -}
import Control.Monad.IO.Class {- base -}
import qualified Data.Char {- base -}
import Data.List {- base -}
import Data.Maybe {- base -}
import Data.Word {- base -}
import Text.Printf {- base -}

import qualified Data.Hashable as Hashable {- hashable -}
import qualified Data.Map as Map {- containers -}
import qualified System.Random as Random {- containers -}

import qualified Control.Monad.Except as Except {- mtl -}
import qualified Control.Monad.State as State {- mtl -}

import qualified Music.Theory.Byte {- hmt-base -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Ansi.Expr as Expr {- stsc3 -}
import qualified Language.Smalltalk.Som as St {- stsc3 -}

import Interpreter.Som.DictRef
import Interpreter.Som.Int
import Interpreter.Som.Ref
import Interpreter.Som.Str
import Interpreter.Som.Sym
import Interpreter.Som.Tbl
import Interpreter.Som.Time
import Interpreter.Som.Vec

-- | Smalltalk expression
type StExpr = Expr.Expr

-- | Support both Som and St-80 rules.
data SystemType = SomSystem | SmalltalkSystem

-- | Identifier.
type Id = Int

-- * Context Frame

-- | (exception:anException, handler:aBlockClosure)
type ExceptionHandler = (Object, Object)

{- | Method contexts store:
       1. a context identifier to receive non-local returns
       2. the class the method was defined in (for super message send)
       3. the method selector (signature) for back traces
       4. the receiver
     Block contexts store:
       1. a context identifier (not strictly required, for tracing)
       2. the Block object to report cases of escaped blocks.
       3. maybe an (exception, handler) pair
     In addition both store local variables (arguments and temporaries) as an ObjectDictionary.
-}
data ContextFrame
  = MethodFrame Id ((Symbol, Bool), Symbol) Object ObjectDictionary
  | BlockFrame Id Object (Maybe ExceptionHandler) ObjectDictionary
  deriving (Eq)

contextFrameTypeCharacter :: ContextFrame -> Char
contextFrameTypeCharacter frm =
  case frm of
    MethodFrame {} -> 'm'
    BlockFrame {} -> 'b'

contextFrameIsMethod :: ContextFrame -> Bool
contextFrameIsMethod = (== 'm') . contextFrameTypeCharacter

contextFrameId :: ContextFrame -> Id
contextFrameId frm =
  case frm of
    MethodFrame k _ _ _ -> k
    BlockFrame k _ _ _ -> k

contextFrameSelector :: ContextFrame -> Symbol
contextFrameSelector frm =
  case frm of
    MethodFrame _ (_, sel) _ _ -> sel
    _ -> error "contextFrameSelector"

contextFrameInspect :: MonadIO m => ContextFrame -> m String
contextFrameInspect ctx =
  case ctx of
    MethodFrame ctxId ((cl, _), sel) rcv dict -> do
      let hdr = printf "<pc:%d> '%s.%s'" ctxId cl sel
      rcv' <- objectInspect rcv
      dict' <- objectDictionaryInspect dict
      return (unlines ["MethodFrame:", hdr, rcv', dict'])
    BlockFrame ctxId blk eh dict -> do
      blk' <- objectInspect blk
      dict' <- objectDictionaryInspect dict
      return (unlines [printf "BlockFrame: <pc:%d, exc:%s>" ctxId (show (isJust eh)), blk', dict'])

-- * Context

{- | A Context is the environment a Smalltalk expression is evaluated in.
     The Name lookup rules are:

     For methods:
                  1. temporaries (including arguments),
                  2. receiver instance variables,
                  3. receiver class variables,
                  4. globals.

     For blocks:
                  1. temporaries & arguments,
                  2. parent context chain,
                  3. globals,
                  4. workspace.
-}
type Context = [ContextFrame]

nilContext :: Context
nilContext = []

isNilContext :: Context -> Bool
isNilContext = (==) []

contextFrame :: Context -> Maybe ContextFrame
contextFrame ctx =
  case ctx of
    [] -> Nothing
    frame : _ -> Just frame

contextParent :: Context -> Maybe Context
contextParent ctx =
  case ctx of
    [] -> Nothing
    _ : parent -> Just parent

contextFrameOrError :: Context -> ContextFrame
contextFrameOrError = fromMaybe (error "contextFrame") . contextFrame

contextParentOrError :: Context -> Context
contextParentOrError = fromMaybe (error "contextParent") . contextParent

contextId :: Context -> Maybe Id
contextId = fmap contextFrameId . contextFrame

contextIdOrError :: Context -> Id
contextIdOrError = contextFrameId . contextFrameOrError

contextFrames :: Context -> [ContextFrame]
contextFrames = id

contextIdSequence :: Context -> [Id]
contextIdSequence = map contextFrameId

contextTypeAndIdSequence :: Context -> [(Char, Id)]
contextTypeAndIdSequence = map (\frame -> (contextFrameTypeCharacter frame, contextFrameId frame))

contextSelectorOrError :: Context -> Symbol
contextSelectorOrError = contextFrameSelector . contextFrameOrError

contextUnwindTo :: Context -> Id -> Context
contextUnwindTo ctx k =
  case ctx of
    [] -> error ("contextUnwindTo: " ++ show k)
    frame : parent -> if contextFrameId frame == k then ctx else contextUnwindTo parent k

contextNearestMethod :: Context -> Maybe Context
contextNearestMethod ctx =
  case ctx of
    [] -> Nothing
    frame : parent -> if contextFrameIsMethod frame then Just ctx else contextNearestMethod parent

contextNearestMethodFrame :: Context -> Maybe ContextFrame
contextNearestMethodFrame = fmap head . contextNearestMethod

contextSender :: Context -> Maybe Context
contextSender = maybe (error "contextSender?") contextNearestMethod . contextNearestMethod

contextSenderOrError :: Context -> Context
contextSenderOrError = fromMaybe (error "contextSenderOrError?") . contextSender

contextReceiver :: Context -> Maybe Object
contextReceiver ctx =
  case contextNearestMethod ctx of
    Just (MethodFrame _ _ rcv _ : _) -> Just rcv
    _ -> Nothing

contextHasMethodWithId :: Context -> Id -> Bool
contextHasMethodWithId ctx k =
  case ctx of
    [] -> False
    BlockFrame {} : p -> contextHasMethodWithId p k
    MethodFrame pc _ _ _ : p -> pc == k || contextHasMethodWithId p k

contextCurrentBlock :: Context -> Maybe Object
contextCurrentBlock ctx =
  case ctx of
    BlockFrame _ blockObject _ _ : _ -> Just blockObject
    _ -> Nothing

contextExceptionHandler :: Context -> Maybe ExceptionHandler
contextExceptionHandler ctx =
  case ctx of
    BlockFrame _ _ (Just eh) _ : _ -> Just eh
    _ -> Nothing

contextAddFrame :: ContextFrame -> Context -> Context
contextAddFrame frm ctx = frm : ctx

contextDeleteFrame :: StError m => Context -> m Context
contextDeleteFrame ctx =
  case ctx of
    [] -> vmError "contextDeleteFrame: empty context"
    _ : p -> return p

contextPrint :: MonadIO m => Context -> m ()
contextPrint ctx =
  case ctx of
    [] -> return ()
    frame : parent -> do
      str <- contextFrameInspect frame
      liftIO (putStr (unlines ["Context: ", str]))
      contextPrint parent

-- * ObjectData

{- | Data associated with an object.

     Som:
       Som has no Character class
       Som strings are primitive and immutable, St strings are mutable.
       Symbol is a subclass of String
-}
data ObjectData
  = -- | nil
    DataUndefinedObject
  | DataBoolean
  | -- | Not in Som
    DataSmallInteger SmallInteger
  | -- | Som Integer
    DataLargeInteger LargeInteger
  | DataDouble Double
  | -- | Not in Som
    DataCharacter Char
  | DataImmutableString UnicodeString
  | -- | Class definition and level, class variables, method caches
    DataClass (St.ClassDefinition, Bool) ObjectTable (MethodCache, MethodCache)
  | DataContext Context
  | -- | Holder, definition, lambda StExpr
    DataMethod Symbol St.MethodDefinition StExpr
  | -- | Holder & Signature
    DataPrimitive Symbol Symbol
  | -- | Identity, blockContext, lambda StExpr
    DataBlockClosure Id Context StExpr
  | -- | Token for system or Smalltalk singleton
    DataSystem
  | -- | Immutable array of literals
    DataArrayLiteral (Vec Object)
  | -- | Objects with a fixed number of integer indexed mutable slots
    DataIndexable Id (VecRef Object)
  | -- | Objects with named and index addressable instance variables
    DataNonIndexable Id ObjectTable
  | -- | Character array
    DataCharacterArray Id (VecRef Char)
  | -- | Byte array
    DataByteArray Id (VecRef Word8)
  | DataThread ThreadId
  | DataMVar (MVar.MVar Object)
  | DataRandomGenerator Id (Ref Random.StdGen)
  deriving (Eq)

objectDataAsDouble :: ObjectData -> Maybe Double
objectDataAsDouble o =
  case o of
    DataSmallInteger x -> Just (fromIntegral x)
    DataLargeInteger x -> Just (fromIntegral x)
    DataDouble x -> Just x
    _ -> Nothing

objectDataAsString :: MonadIO m => ObjectData -> m (Maybe String)
objectDataAsString o =
  case o of
    DataImmutableString str -> return (Just (fromUnicodeString str))
    DataCharacterArray _ ref -> fmap Just (vecRefToList ref)
    DataByteArray _ ref -> fmap (Just . map (toEnum . fromIntegral)) (vecRefToList ref)
    _ -> return Nothing

objectDataAsArray :: MonadIO m => ObjectData -> m (Maybe [Object])
objectDataAsArray o =
  case o of
    DataArrayLiteral vec -> return (Just (vecToList vec))
    DataIndexable _ ref -> fmap Just (vecRefToList ref)
    _ -> return Nothing

-- * Object

-- | Object represented as class name and object data.
data Object = Object {objectClassName :: Symbol, objectData :: ObjectData} deriving (Eq)

-- | Association list of named objects.
type ObjectAssociationList = [(Symbol, Object)]

-- | Extensible mutable dictionary of named objects.
type ObjectDictionary = DictRef Symbol Object

-- | Indexable mutable association list (zero-indexed) of named objects.
type ObjectTable = Vec (Symbol, Ref Object)

objectToConciseString :: Object -> String
objectToConciseString (Object nm obj) =
  case obj of
    DataUndefinedObject -> "nil"
    DataBoolean -> map Data.Char.toLower nm
    DataSmallInteger x -> show x
    DataLargeInteger x -> show x
    DataDouble x -> show x
    DataCharacter x -> ['$', x]
    DataImmutableString x ->
      if nm == toSymbol "Symbol"
        then concat ["#'", fromUnicodeString x, "'"]
        else concat ["'", fromUnicodeString x, "'"]
    DataClass (x, isMeta) _ _ -> (if isMeta then St.metaclassName else id) (St.className x)
    DataMethod holder method _ -> concat [fromSymbol holder, ">>", St.methodSignature method]
    DataPrimitive holder signature -> concat ["Primitive:", fromSymbol holder, ">>", fromSymbol signature]
    DataArrayLiteral vec -> "#(" ++ unwords (map objectToConciseString (vecToList vec)) ++ ")"
    _ -> "instance of " ++ fromSymbol nm

instance Show Object where show = objectToConciseString

objectPrint :: MonadIO m => Object -> m Object
objectPrint o =
  let recursionDepth = 5 :: Int
      f k = if k == 0 then return . objectToConciseString else objectExamine (return "...") (f (k - 1))
  in liftIO (f recursionDepth o >>= putStrLnAllowingCr) >> return nilObject

objectListPrint :: MonadIO m => [Object] -> m Object
objectListPrint o = liftIO (putStrLn (intercalate ", " (map objectToConciseString o))) >> return nilObject

-- * Object Inspect

objectTableExamine :: MonadIO m => (Object -> m String) -> ObjectTable -> m String
objectTableExamine f tbl = do
  (keys, values) <- fmap unzip (tblToList tbl)
  valuesInspected <- mapM f values
  return (show (zip keys valuesInspected))

objectDictionaryExamine :: MonadIO m => (Object -> m String) -> ObjectDictionary -> m String
objectDictionaryExamine f dict = do
  keys <- dictRefKeys dict
  values <- dictRefValues dict
  inspectors <- mapM f values
  return (unlines (zipWith (\k i -> k ++ ": " ++ i) keys inspectors))

objectExamine :: MonadIO m => m String -> (Object -> m String) -> Object -> m String
objectExamine vmPp f (Object nm obj) =
  case obj of
    DataIndexable x ref -> do
      vec <- deRef ref
      lst <- mapM f (vecToList vec)
      return (printf "instance of %s <pc:%d> with: {%s}" nm x (intercalate ". " lst))
    DataCharacterArray x ref -> do
      vec <- deRef ref
      let str = vecToList vec
      return (printf "instance of %s <pc:%d> with: '%s'" nm x str)
    DataByteArray x ref -> do
      vec <- deRef ref
      let bytes = vecToList vec
      return (printf "instance of %s <pc:%d> with: '%s'" nm x (Music.Theory.Byte.byte_seq_hex_pp False bytes))
    DataClass (x, _) tbl _ -> do
      tblStr <- objectTableExamine f tbl
      return (St.className x ++ ": " ++ tblStr)
    DataMethod _ x _ -> return (show x)
    DataBlockClosure x _ (Expr.Lambda ld _ _ _) ->
      return (printf "instance of %s <pc:%d, %s>" nm x (Expr.lambdaDefinitionShow ld))
    DataNonIndexable x tbl -> do
      tblStr <- objectTableExamine f tbl
      return (printf "instance of %s <pc:%d>: %s" nm x tblStr)
    DataSystem -> vmPp
    _ -> return (objectToConciseString (Object nm obj))

objectTableInspect :: MonadIO m => ObjectTable -> m String
objectTableInspect = objectTableExamine objectInspect

objectDictionaryInspect :: MonadIO m => ObjectDictionary -> m String
objectDictionaryInspect = objectDictionaryExamine objectInspect

objectInspect :: MonadIO m => Object -> m String
objectInspect = objectExamine (return "VmState") objectInspect -- todo: recursion depth

objectInspectAndPrint :: MonadIO m => Object -> m Object
objectInspectAndPrint rcv = objectInspect rcv >>= liftIO . putStrLn >> return rcv

blockObjectArity :: Object -> Maybe Int
blockObjectArity obj =
  case obj of
    Object _ (DataBlockClosure _ _ (Expr.Lambda _ blockArguments _ _)) -> Just (length blockArguments)
    _ -> Nothing

-- * VmState

{- | The Vm state holds:
     - class path, the list of directories to search for class files along
     - startTime (required by Som for System>>ticks and System>>time)
     - programCounter, used to identify method contexts and non-immediate objects
     - context, holds the currently executing context
     - globalDictionary, holds global variables
     - workspaceDictionary, holds workspace variables

The name Vm is used instead of Interpreter because it is shorter.
-}
type VmState = ([FilePath], Double, Int, Context, ObjectDictionary, ObjectDictionary)

type WithVmState m = State.StateT VmState m

vmStateInit :: [FilePath] -> ObjectDictionary -> IO VmState
vmStateInit classPath globalDictionary = do
  startTime <- getSystemTimeInSeconds
  let programCounter = 0
  workspace <- dictRefEmpty
  return (classPath, startTime, programCounter, nilContext, globalDictionary, workspace)

vmStateInspect :: MonadIO m => VmState -> m String
vmStateInspect (_cp, _tm, pc, _ctx, glb, wrk) = do
  globalKeys <- dictRefKeys glb
  workspaceKeys <- dictRefKeys wrk
  return (show ("programCounter", pc, "global", globalKeys, "workspace", workspaceKeys))

-- * Exception

{- | Block return is non-local, it returns from the method the block was defined in.
This is implemented using Monad.Except.
St-80 Exception>>signal and BlockClosure>>on:do: are also implemented here.
System generated errors are also implemented here.
The handler for NonLocalReturn is installed at message sends,
the handler for Exception is installed at block evaluations.
-}
data ExceptionOrNonLocalReturn
  = -- | message
    SystemError String
  | -- | exceptionObject signalContext
    Exception Object Context
  | -- | contextId, block returned from, value returned
    NonLocalReturn Id Object Object

type StError m = Except.MonadError ExceptionOrNonLocalReturn m

type WithException m = Except.ExceptT ExceptionOrNonLocalReturn m

exceptionOrNonLocalReturn_pp :: ExceptionOrNonLocalReturn -> String
exceptionOrNonLocalReturn_pp e =
  case e of
    SystemError msg -> "SystemError: " ++ msg
    Exception obj _ctx -> "Exception: " ++ objectToConciseString obj
    NonLocalReturn pc blk obj -> printf "NonLocalReturn: <pc=%d, blk=%s>" pc (objectToConciseString blk) ++ objectToConciseString obj

nonLocalReturn :: StError m => Id -> Object -> Object -> m a
nonLocalReturn pc blk obj = Except.throwError (NonLocalReturn pc blk obj)

signalException :: Object -> Vm t
signalException exceptionObject = do
  ctx <- vmGetContext
  Except.throwError (Exception exceptionObject ctx)

stError :: StError m => String -> m t
stError msg = Except.throwError (SystemError ("Error: " ++ msg))

prError :: StError m => String -> m t
prError txt = stError ("Primitive error: " ++ txt)

vmError :: StError m => String -> m t
vmError txt = stError ("Virtual machine error: " ++ txt)

-- * Vm

type Vm r = WithException (WithVmState IO) r

vmStartTime :: Vm Double
vmStartTime = State.get >>= \(_, startTime, _, _, _, _) -> return startTime

vmClassPath :: Vm [FilePath]
vmClassPath = State.get >>= \(cp, _, _, _, _, _) -> return cp

vmElapsedTimeInSeconds :: Vm Double
vmElapsedTimeInSeconds = do
  startTime <- vmStartTime
  currentTime <- getSystemTimeInSeconds
  return (currentTime - startTime)

vmElapsedTimeInMicroseconds :: Vm Int
vmElapsedTimeInMicroseconds = fmap secondsToMicroseconds vmElapsedTimeInSeconds

vmGetProgramCounter :: Vm Int
vmGetProgramCounter = State.get >>= \(_, _, programCounter, _, _, _) -> return programCounter

vmIncrementProgramCounter :: Vm Int
vmIncrementProgramCounter = State.get >>= \(cp, tm, pc, ctx, glb, usr) -> State.put (cp, tm, pc + 1, ctx, glb, usr) >> return pc

vmGetContext :: Vm Context
vmGetContext = State.get >>= \(_, _, _, ctx, _, _) -> return ctx

vmThisContextObject :: Vm Object
vmThisContextObject = do
  ctx <- vmGetContext
  return (Object "Context" (DataContext ctx))

vmCurrentBlock :: Vm (Maybe Object)
vmCurrentBlock = fmap contextCurrentBlock vmGetContext

vmNearestMethodFrame :: Vm Context
vmNearestMethodFrame = maybe (vmErrorWithBacktrace "vmNearestMethodFrame" []) return . contextNearestMethod =<< vmGetContext

vmModifyContext :: (Context -> Vm Context) -> Vm Context
vmModifyContext f = do
  (cp, tm, pc, ctx, glb, usr) <- State.get
  modifiedCtx <- f ctx
  State.put (cp, tm, pc, modifiedCtx, glb, usr)
  return ctx

vmAddContextFrame :: ContextFrame -> Vm Context
vmAddContextFrame frm = vmModifyContext (return . contextAddFrame frm)

vmDeleteContextFrame :: Vm Context
vmDeleteContextFrame = vmModifyContext contextDeleteFrame

vmReplaceContext :: Context -> Vm Context
vmReplaceContext ctx = do
  (cp, tm, pc, previousCtx, glb, usr) <- State.get
  State.put (cp, tm, pc, ctx, glb, usr)
  return previousCtx

vmPutContext :: Context -> Vm ()
vmPutContext ctx = vmReplaceContext ctx >> return ()

vmUnwindTo :: Id -> Vm Context
vmUnwindTo k = do
  ctx <- vmGetContext
  when (not (contextHasMethodWithId ctx k)) (vmBacktrace >> error "vmUnwindTo: context does not exist")
  vmReplaceContext (contextUnwindTo (contextParentOrError ctx) k)

vmGetGlobalDict :: Vm ObjectDictionary
vmGetGlobalDict = State.get >>= \(_, _, _, _, dict, _) -> return dict

vmGlobalDictAllKeys :: Vm [Symbol]
vmGlobalDictAllKeys = vmGetGlobalDict >>= dictRefKeys

vmGlobalLookupMaybe :: Symbol -> Vm (Maybe Object)
vmGlobalLookupMaybe key = vmGetGlobalDict >>= \dict -> dictRefLookup dict key

vmGlobalLookupOrNil :: Symbol -> Vm Object
vmGlobalLookupOrNil key = vmGlobalLookupMaybe key >>= return . fromMaybe nilObject

vmGlobalLookupOrSymbol :: Symbol -> Vm Object
vmGlobalLookupOrSymbol key = vmGlobalLookupMaybe key >>= return . fromMaybe (immutableSymbolObject key)

vmGlobalLookupOrError :: Symbol -> Vm Object
vmGlobalLookupOrError key = vmGlobalLookupMaybe key >>= maybe (vmError ("vmGlobalLookup: " ++ fromSymbol key)) return

vmHasGlobal :: Symbol -> Vm Bool
vmHasGlobal = fmap (maybe False (const True)) . vmGlobalLookupMaybe

vmGlobalAssign :: Symbol -> Object -> Vm (Maybe Object)
vmGlobalAssign key value = do
  d <- vmGetGlobalDict
  dictRefAssignMaybe d key value

vmGlobalAssignOrCreate :: Symbol -> Object -> Vm Object
vmGlobalAssignOrCreate key value = vmGetGlobalDict >>= \d -> dictRefInsert d key value >> return value

vmGetWorkspaceDict :: Vm ObjectDictionary
vmGetWorkspaceDict = State.get >>= \(_, _, _, _, _, d) -> return d

vmWorkspaceLookupMaybe :: Symbol -> Vm (Maybe Object)
vmWorkspaceLookupMaybe key = vmGetWorkspaceDict >>= \dict -> dictRefLookup dict key

vmWorkspaceAssign :: Symbol -> Object -> Vm (Maybe Object)
vmWorkspaceAssign key value = do
  d <- vmGetWorkspaceDict
  dictRefAssignMaybe d key value

vmWorkspaceAssignOrCreate :: Symbol -> Object -> Vm Object
vmWorkspaceAssignOrCreate key value = do
  d <- vmGetWorkspaceDict
  dictRefInsert d key value
  return value

vmInspect :: Vm String
vmInspect = do
  (_, _tm, pc, _ctx, glb, wrk) <- State.get
  globalKeys <- dictRefKeys glb
  workspaceKeys <- dictRefKeys wrk
  return (show ("programCounter", pc, "global", globalKeys, "workspace", workspaceKeys))

objectVmInspect :: Object -> Vm String
objectVmInspect = objectExamine vmInspect objectVmInspect -- todo: recursion depth

vmBacktrace :: Vm ()
vmBacktrace = do
  ctx <- vmGetContext
  liftIO (putStrLn "Vm: Backtrace")
  contextPrint ctx

-- * Object Error

objectError :: Object -> String -> Vm t
objectError o msg = objectPrint o >> vmError msg

objectListError :: [Object] -> String -> Vm t
objectListError o msg = objectListPrint o >> vmError (printf "%s: arity=%d" msg (length o))

vmErrorWithBacktrace :: String -> [Object] -> Vm t
vmErrorWithBacktrace msg obj = vmBacktrace >> objectListError obj msg

-- * Object Accessors

classCachedMethods :: Object -> Maybe MethodCache
classCachedMethods (Object _ obj) =
  case obj of
    DataClass (_, False) _ (instanceMethodsCache, _) -> Just instanceMethodsCache
    DataClass (_, True) _ (_, classMethodsCache) -> Just classMethodsCache
    _ -> Nothing

classCachedMethodLookup :: Object -> St.Selector -> Vm (Maybe Object)
classCachedMethodLookup o sel =
  case classCachedMethods o of
    Just mth -> return (fmap snd (Map.lookup sel mth))
    _ -> vmError "classCachedMethodLookup?"

indexableObjectElements :: Object -> Vm [Object]
indexableObjectElements o = case o of
  Object _ (DataIndexable _ vectorRef) -> fmap vecToList (deRef vectorRef)
  _ -> vmError ("indexableObjectElements: not indexable")

arrayElements :: Object -> Vm [Object]
arrayElements o = case o of
  Object "Array" (DataArrayLiteral vec) -> return (vecToList vec)
  Object "Array" (DataIndexable _ vecRef) -> fmap vecToList (deRef vecRef)
  _ -> vmError ("arrayElements: not indexable object")

objectLookupInstanceVariable :: Object -> Symbol -> Vm (Maybe Object)
objectLookupInstanceVariable o key =
  case o of
    Object _ (DataNonIndexable _ tbl) -> tblAtKeyMaybe tbl key
    _ -> return Nothing

objectAssignInstanceVariable :: Object -> Symbol -> Object -> Vm (Maybe Object)
objectAssignInstanceVariable object key value =
  case object of
    Object _ (DataNonIndexable _ tbl) -> tblAtKeyPutMaybe tbl key value
    _ -> return Nothing

-- * Object constructors

contextObject :: Context -> Object
contextObject = Object "Context" . DataContext

systemNilClass :: SystemType -> String
systemNilClass sys =
  case sys of
    SomSystem -> "Nil"
    SmalltalkSystem -> "UndefinedObject"

systemReserverIdentifier :: SystemType -> String
systemReserverIdentifier typ =
  case typ of
    SomSystem -> "system"
    SmalltalkSystem -> "Smalltalk"

reservedIdentifierObjectFor :: SystemType -> String -> Object
reservedIdentifierObjectFor sys x =
  case x of
    "true" -> Object (toSymbol "True") DataBoolean
    "false" -> Object (toSymbol "False") DataBoolean
    "nil" -> Object (toSymbol (systemNilClass sys)) DataUndefinedObject
    "system" -> Object (toSymbol "System") DataSystem -- Som
    "Smalltalk" -> Object (toSymbol "SmalltalkImage") DataSystem -- St-80
    _ -> error "reservedObject"

-- | echhh...  don't worry for St.
reservedObject :: String -> Object
reservedObject = reservedIdentifierObjectFor SomSystem

reservedObjectTableFor :: SystemType -> ObjectAssociationList
reservedObjectTableFor typ =
  let f x = (x, reservedObject x)
  in map f (systemReserverIdentifier typ : words "nil true false")

nilObject :: Object
nilObject = reservedObject "nil"

{- | The method cache has indices of the ordering in the class description because Som tests for this.
If methods were compiled then lookup would be by index and the cache would be a vector.
-}
type MethodCache = Map.Map St.Selector (Int, Object)

classMakeMethodCaches :: St.ClassDefinition -> (MethodCache, MethodCache)
classMakeMethodCaches cd =
  let f nm m ix = (St.methodSelector m, (ix, methodObject nm m))
      im = zipWith (f (St.className cd)) (St.instanceMethods cd) [1 ..]
      cm = zipWith (f (St.classMetaclassName cd)) (St.classMethods cd) [1 ..]
  in (Map.fromList im, Map.fromList cm)

makeObjectTable :: MonadIO m => [Symbol] -> m ObjectTable
makeObjectTable variableNames = tblFromList (zip variableNames (repeat nilObject))

{- | Create Class object from ClassDefinition
     The instance and class methods are generated and cached.
     Since at present class objects are created in the interpreter startup sequence, this function should not raise an StError.
-}
classObject :: MonadIO m => St.ClassDefinition -> m Object
classObject cd = do
  let classVarNames = map toSymbol (St.classVariableNames cd)
      mc = toSymbol (St.classMetaclassName cd)
  tbl <- makeObjectTable classVarNames
  return (Object mc (DataClass (cd, False) tbl (classMakeMethodCaches cd)))

{- | Create method Object for named Class.
     This is the point at which the MethodDefinition is translated to Expr form.
-}
methodObject :: Symbol -> St.MethodDefinition -> Object
methodObject holder method = Object (toSymbol "Method") (DataMethod holder method (Expr.methodDefinitionExpr method))

smallIntegerObject :: SmallInteger -> Object
smallIntegerObject x = Object (toSymbol "SmallInteger") (DataSmallInteger x)

largeIntegerObject :: LargeInteger -> Object
largeIntegerObject x = Object (toSymbol "LargeInteger") (DataLargeInteger x)

doubleObject :: Double -> Object
doubleObject x = Object (toSymbol "Double") (DataDouble x)

-- | Integer given by constructor if fractional part is zero, else Double.
doubleAsFractional :: Integral t => (t -> Object) -> Double -> Object
doubleAsFractional cons x =
  case properFraction x of
    (i, 0) -> cons i
    _ -> doubleObject x

nanObject :: Object
nanObject = doubleObject (0 / 0)

characterObject :: Char -> Object
characterObject ch = Object (toSymbol "Character") (DataCharacter ch)

immutableStringObject :: String -> Object
immutableStringObject str = Object (toSymbol "String") (DataImmutableString (toUnicodeString str))

immutableSymbolObject :: String -> Object
immutableSymbolObject str = Object (toSymbol "Symbol") (DataImmutableString (toUnicodeString str))

booleanObject :: Bool -> Object
booleanObject x = if x then reservedObject "true" else reservedObject "false"

falseObject :: Object
falseObject = booleanObject False

trueObject :: Object
trueObject = booleanObject True

arrayLiteralObject :: [Object] -> Object
arrayLiteralObject lst = Object (toSymbol "Array") (DataArrayLiteral (vecFromList lst))

randomGeneratorObject :: Int -> Vm Object
randomGeneratorObject seed = do
  pc <- vmIncrementProgramCounter
  ref <- toRef (Random.mkStdGen seed)
  return (Object "RandomGenerator" (DataRandomGenerator pc ref))

randomGenerator :: (MonadIO m, Random.Random t) => Ref Random.StdGen -> (t, t) -> m t
randomGenerator ref rng = do
  gen <- deRef ref
  let (answer, gen') = Random.randomR rng gen
  wrRef ref gen'
  return answer

randomGeneratorNextInt :: MonadIO m => Ref Random.StdGen -> Int -> m Int
randomGeneratorNextInt rng n = randomGenerator rng (1, n)

randomGeneratorNext :: MonadIO m => Ref Random.StdGen -> m Double
randomGeneratorNext rng = randomGenerator rng (0, 1)

-- | (intObject, strObject, symObject)
type LiteralConstructors = (LargeInteger -> Object, String -> Object, String -> Object)

literalObject :: LiteralConstructors -> St.Literal -> Object
literalObject opt@(integerObject, stringObject, symbolObject) l =
  case l of
    St.NumberLiteral (St.Int x) -> integerObject x
    St.NumberLiteral (St.Float x) -> doubleObject x
    St.StringLiteral x -> stringObject x
    St.CharacterLiteral x -> characterObject x -- Note: Som has no Character object
    St.SymbolLiteral x -> symbolObject x
    St.SelectorLiteral x -> symbolObject (St.selectorIdentifier x)
    St.ArrayLiteral x -> arrayLiteralObject (map (arrayLiteralElemObject opt) x)

arrayLiteralElemObject :: LiteralConstructors -> Either St.Literal String -> Object
arrayLiteralElemObject opt e =
  case e of
    Left x -> literalObject opt x
    Right x -> reservedObject x

-- * Object predicates

isNil :: Object -> Bool
isNil = (==) nilObject

isBlock :: Object -> Bool
isBlock = isJust . blockObjectArity

isBlockOfArity :: Int -> Object -> Bool
isBlockOfArity k = (==) (Just k) . blockObjectArity

-- * Context

{- | Dictionary of arguments and temporaries.
     Temporaries may shadow arguments.
     Dict will discard multiple keys, keeping the last assigned, therefore arguments are set first.
-}
localVariablesDict :: MonadIO m => ObjectAssociationList -> [Symbol] -> m ObjectDictionary
localVariablesDict args tmp = dictRefFromList (args ++ zip tmp (repeat nilObject))

methodContextFrame :: MonadIO m => Id -> ((Symbol, Bool), Symbol) -> Object -> ObjectAssociationList -> [St.Identifier] -> m ContextFrame
methodContextFrame pc cs rcv arg tmp = fmap (MethodFrame pc cs rcv) (localVariablesDict arg (map toSymbol tmp))

-- * Hash

mHash :: (Monad m, Hashable.Hashable t) => t -> m SmallInteger
mHash = return . Hashable.hash

-- | Hash of object.  Used for object equality.
objectHash :: (MonadIO m, StError m) => Object -> m SmallInteger
objectHash (Object nm obj) =
  case obj of
    DataUndefinedObject -> mHash (nm, "nil")
    DataBoolean -> mHash nm
    DataSmallInteger x -> return x -- c.f. Integer>>hashcode
    DataLargeInteger x -> return (fromInteger x) -- c.f. Integer>>hash
    DataDouble x -> mHash x
    DataCharacter x -> mHash x
    DataImmutableString x -> mHash (nm, x) -- c.f. 'x' hash /= #'x' hash
    DataClass (x, _) _ _ -> mHash (nm, St.className x)
    DataContext _ -> vmError ("Object>>hash: Context")
    DataMethod holder method _ -> mHash (nm, holder, St.methodSignature method)
    DataPrimitive holder signature -> mHash (nm, holder, signature)
    DataBlockClosure x _ _ -> mHash ("Block", x)
    DataSystem -> mHash (nm, "system")
    DataArrayLiteral vec -> mapM objectHash (vecToList vec) >>= \lst -> mHash (nm, lst)
    DataIndexable x _ -> mHash (nm, x)
    DataNonIndexable x _ -> mHash (nm, x)
    DataCharacterArray _ ref -> vecRefToList ref >>= \str -> mHash (nm, str) -- strings and copies of strings hash equally
    DataByteArray _ ref -> vecRefToList ref >>= \bytes -> mHash (nm, bytes)
    DataThread _ -> vmError ("Object>>hash: Thread")
    DataMVar _ -> vmError ("Object>>hash: MVar")
    DataRandomGenerator x _ -> mHash (nm, x)

objectHashEqual :: (StError m, MonadIO m) => Object -> Object -> m Bool
objectHashEqual obj1 obj2 = do
  hash1 <- objectHash obj1
  hash2 <- objectHash obj2
  return (hash1 == hash2)

-- * Identical

-- | String literals must hash to the same value.
stringLiteralId :: Id
stringLiteralId = -1

-- | Object identity test (==).  String literals are a special case.
objectIdentical :: (MonadIO m, StError m) => Object -> Object -> m Bool
objectIdentical obj1 obj2 =
  case (obj1, obj2) of
    (Object "String" (DataCharacterArray k1 _), Object "String" (DataCharacterArray k2 _)) ->
      if k1 == stringLiteralId && k2 == stringLiteralId then objectHashEqual obj1 obj2 else return (obj1 == obj2)
    _ -> return (obj1 == obj2)

-- * Constructors

stringToCharacterArray :: Bool -> String -> Vm ObjectData
stringToCharacterArray isLiteral str = do
  pc <- if isLiteral then return stringLiteralId else vmIncrementProgramCounter
  ref <- vecRefFromList (fromUnicodeString str)
  return (DataCharacterArray pc ref)

mutableStringObject :: Bool -> String -> Vm Object
mutableStringObject isLiteral str = fmap (Object (toSymbol "String")) (stringToCharacterArray isLiteral str)

indexableFromVec :: Symbol -> Vec Object -> Vm Object
indexableFromVec cl vec = do
  pc <- vmIncrementProgramCounter
  ref <- liftIO (toRef vec)
  return (Object cl (DataIndexable pc ref))

indexableFromList :: Symbol -> [Object] -> Vm Object
indexableFromList cl e = indexableFromVec cl (vecFromList e)

arrayFromVec :: Vec Object -> Vm Object
arrayFromVec = indexableFromVec "Array"

arrayFromList :: [Object] -> Vm Object
arrayFromList = indexableFromList "Array"

arrayFromMap :: Map.Map t Object -> Vm Object
arrayFromMap = arrayFromList . Map.elems

arrayFromIndexedMap :: Map.Map t (Int, Object) -> Vm Object
arrayFromIndexedMap = arrayFromList . map snd . sortOn fst . Map.elems

mvarObject :: Vm Object
mvarObject = do
  mvar <- liftIO MVar.newEmptyMVar
  return (Object "MVar" (DataMVar mvar))

-- * Copy

{- | Make a shallow copy of an object.

St-80: "Answer a copy of the receiver which shares the receiver's instance variables."

Symbols are unique.
The class library ensures symbols aren't copied, however when copying arrays we need to do the check here.
-}
objectShallowCopy :: Object -> Vm Object
objectShallowCopy object@(Object nm obj) = do
  case nm of
    "Symbol" -> return object
    _ -> do
      cpy <- objectDataShallowCopy obj
      return (Object nm cpy)

objectTableShallowCopy :: ObjectTable -> Vm ObjectTable
objectTableShallowCopy vec = do
  let (keys, refs) = unzip (vecToList vec)
  values <- mapM deRef refs
  copies <- mapM objectShallowCopy values
  newRefs <- mapM toRef copies
  return (vecFromList (zip keys newRefs))

objectDataShallowCopy :: ObjectData -> Vm ObjectData
objectDataShallowCopy od =
  case od of
    DataArrayLiteral vec -> do
      pc <- vmIncrementProgramCounter
      ref <- toRef (vecShallowCopy vec)
      return (DataIndexable pc ref)
    DataCharacterArray _ ref -> do
      pc <- vmIncrementProgramCounter
      cpy <- vecRefShallowCopy ref
      return (DataCharacterArray pc cpy)
    DataByteArray _ ref -> do
      pc <- vmIncrementProgramCounter
      cpy <- vecRefShallowCopy ref
      return (DataByteArray pc cpy)
    DataImmutableString str -> stringToCharacterArray False str
    DataIndexable _ ref -> do
      pc <- vmIncrementProgramCounter
      cpy <- vecRefShallowCopy ref
      return (DataIndexable pc cpy)
    DataNonIndexable _ tbl -> do
      pc <- vmIncrementProgramCounter
      cpy <- objectTableShallowCopy tbl
      return (DataNonIndexable pc cpy)
    _ -> return od

-- * Lookup

-- | Sequence of lookup procedures to be tried in left to right sequence.
mLookupSequence :: Monad m => [k -> m (Maybe v)] -> k -> m (Maybe v)
mLookupSequence l k =
  case l of
    [] -> return Nothing
    f : l' -> do
      r <- f k
      case r of
        Nothing -> mLookupSequence l' k
        _ -> return r

-- | Sequence of assignment procedures to be tried in left to right sequence.
mAssignSequence :: Monad m => [k -> v -> m (Maybe v)] -> k -> v -> m (Maybe v)
mAssignSequence l k v =
  case l of
    [] -> return Nothing
    f : l' -> do
      r <- f k v
      case r of
        Nothing -> mAssignSequence l' k v
        _ -> return r

{- | Lookup class variable from Object. If the object is:
     1. a class then look in it's table, else lookup it's superclass.
     2. nil then stop looking
     3. any other object look in it's class object
-}
objectLookupClassVariable :: Object -> Symbol -> Vm (Maybe Object)
objectLookupClassVariable object key =
  case object of
    Object _ DataUndefinedObject -> return Nothing
    Object _ (DataClass (cd, isMeta) tbl _) ->
      mLookupSequence
        [ tblAtKeyMaybe tbl
        , \k -> classSuperclass cd isMeta >>= \sp -> objectLookupClassVariable sp k
        ]
        key
    _ -> objectClass object >>= \cl -> objectLookupClassVariable cl key

-- * Class

objectClass :: Object -> Vm Object
objectClass rcv@(Object nm obj) =
  case obj of
    DataClass {} -> classMetaclass rcv
    _ -> vmGlobalLookupOrError nm

{- | Class of class (Metaclass).
     If the Class object isMeta then return Metaclass, else set isMeta.
     Metaclass should be an ordinary class, it is looked up in the global dictionary.
-}
classMetaclass :: Object -> Vm Object
classMetaclass receiver@(Object nm obj) =
  case obj of
    DataClass (cd, isMeta) cVar mCache ->
      if isMeta
        then vmGlobalLookupOrError "Metaclass"
        else return (Object "Class" (DataClass (cd, True) cVar mCache))
    _ -> vmErrorWithBacktrace ("classMetaclass: " ++ nm) [receiver]

{- | Class>>superclass => Class|nil

In a ClassDefinition the superclass of the final class (i.e. Object or ProtoObject) is Nothing, and in Smalltalk it is nil.
In Smalltalks the superclass of the meta class of the final class (i.e. Object class or ProtoObject class) is "Class".
This is the only case where a Metaclass has a superclass which is not a Metaclass.
For all other classes "C class superclass = C superclass class".

> Object superclass = nil "=> true"
> Object class superclass = Class "=> true"
> Integer class superclass = Integer superclass class "=> true"
-}
classSuperclass :: St.ClassDefinition -> Bool -> Vm Object
classSuperclass cd isMeta =
  if St.superclassName cd == Nothing
    then if isMeta then vmGlobalLookupOrError "Class" else return nilObject
    else do
      sp <- maybe (return nilObject) vmGlobalLookupOrNil (St.superclassName cd)
      if isMeta then classMetaclass sp else return sp

-- * Class Primitives

{- | Get all variables of the indicated kind for the indicated class.
     This involves traversing the class hierachy to collect instance variables of all parent classes.
     The ordering places each subclasses instance variables after their superclasses.
     This value could be cached to avoid repeated lookups.
-}
classAllVariableNames :: (St.ClassDefinition -> [Symbol]) -> St.ClassDefinition -> Vm [Symbol]
classAllVariableNames fn cd = do
  case St.superclassName cd of
    Just spName ->
      do
        res <- vmGlobalLookupMaybe spName
        case res of
          Just (Object _ (DataClass (spCd, _) _ _)) ->
            do
              spIv <- classAllVariableNames fn spCd
              return (spIv ++ fn cd)
          _ -> vmError "classAllVariableNames"
    Nothing -> return (fn cd)

classAllVariableNamesFor :: St.ClassDefinition -> Bool -> Vm [Symbol]
classAllVariableNamesFor cd isMeta =
  case isMeta of
    False -> classAllVariableNames St.classInstanceVariableNames cd
    True -> classAllVariableNames St.classVariableNames cd

{- | Create instance of a non-indexable non-immediate class.
     Allocate reference for instance variables and initialize to nil.
     The instance variables of an object are:
         - the instance variables of it's class definition
         - all of the instance variables of all of it's superclasses.
-}
classNew :: St.ClassDefinition -> Vm Object
classNew cd =
  case St.className cd of
    "MVar" -> mvarObject
    _ -> do
      instVarNames <- classAllVariableNames St.classInstanceVariableNames cd
      tbl <- makeObjectTable instVarNames
      pc <- vmIncrementProgramCounter
      return (Object (St.className cd) (DataNonIndexable pc tbl))

arrayNewWithArg :: Int -> Vm Object
arrayNewWithArg size = arrayFromList (replicate size nilObject)

stringOrSymbolNewWithArg :: Symbol -> SmallInteger -> Vm Object
stringOrSymbolNewWithArg typ size = do
  pc <- vmIncrementProgramCounter
  let vec = vecFromList (replicate size '\0')
  ref <- liftIO (toRef vec)
  return (Object typ (DataCharacterArray pc ref))

byteArrayNewWithArg :: SmallInteger -> Vm Object
byteArrayNewWithArg size = do
  pc <- vmIncrementProgramCounter
  let vec = vecFromList (replicate size 0)
  ref <- liftIO (toRef vec)
  return (Object "ByteArray" (DataByteArray pc ref))

-- | This isn't correct.  Subclasses should be allowed, Symbol is special cased for now...
classNewWithArg :: St.ClassDefinition -> SmallInteger -> Vm (Maybe Object)
classNewWithArg cd size =
  if size < 0
    then return Nothing
    else case St.className cd of
      "Array" -> fmap Just (arrayNewWithArg size)
      "ByteArray" -> fmap Just (byteArrayNewWithArg size)
      "String" -> fmap Just (stringOrSymbolNewWithArg "String" size)
      "Symbol" -> fmap Just (stringOrSymbolNewWithArg "Symbol" size)
      _ -> return Nothing

classSuperclassOf :: Object -> Vm Object
classSuperclassOf (Object _ obj) =
  case obj of
    DataClass (cd, isMeta) _ _ -> classSuperclass cd isMeta
    _ -> vmError "classSuperclassOf"

-- * Tables

makeClassTable :: MonadIO m => [St.ClassDefinition] -> m ObjectAssociationList
makeClassTable classLibrary = do
  let classNames = map St.className classLibrary
  classObjects <- mapM classObject classLibrary
  return (zip classNames classObjects)

-- * Load

{- | Loads the named class and all of it's superclasses that are not already loaded.
     Assign each class in the global dictionary.
     Returns the last class loaded (ie. not necessarily the initial class requested).
     Halts when arriving at a class that is already loaded.
-}
systemLoadAndAssignClassesAbove :: Symbol -> Vm (Maybe Object)
systemLoadAndAssignClassesAbove x = do
  existing <- vmGlobalLookupMaybe x
  cp <- vmClassPath
  case existing of
    Just _ -> return existing
    Nothing -> do
      maybeCd <- liftIO (St.somLoadClassDefinitionExtMod True cp x) -- todo: this should also read .st and .stc files
      case maybeCd of
        Just cd -> do
          co <- classObject cd
          _ <- case St.superclassName cd of
            Just sp -> systemLoadAndAssignClassesAbove sp
            Nothing -> return (Just co)
          _ <- vmGlobalAssignOrCreate (St.className cd) co
          return (Just co)
        _ -> return Nothing

-- | Load and return class (and required parent classes) if it exists.
systemLoadClassMaybe :: Symbol -> Vm (Maybe Object)
systemLoadClassMaybe x = do
  c <- systemLoadAndAssignClassesAbove x
  case c of
    Nothing -> return Nothing
    Just _ -> vmGlobalLookupMaybe x

-- | Load class or return nil.
systemLoadClassOrNil :: Symbol -> Vm Object
systemLoadClassOrNil = fmap (fromMaybe nilObject) . systemLoadClassMaybe

-- * Som/St-80

-- | Som/St-80.  Som has distinct numbered Block classes.
closureClass :: SystemType -> Int -> String
closureClass typ numArg =
  case typ of
    SomSystem -> "Block" ++ show (numArg + 1)
    SmalltalkSystem -> "BlockClosure"

{- | Som/St-80.
Som array literals are mutable.
St string literals are mutable.  However equal string literals must also be identical.
-}
sysLiteralObject :: SystemType -> Object -> Vm Object
sysLiteralObject typ obj =
  case (typ, obj) of
    (SomSystem, Object "Array" (DataArrayLiteral _)) -> objectShallowCopy obj
    (SmalltalkSystem, Object "String" (DataImmutableString str)) -> mutableStringObject True str
    _ -> return obj

-- * Resolve

-- | If a global does not exist, attempt to resolve it by loading a class file.
vmGlobalResolveMaybe :: Symbol -> Vm (Maybe Object)
vmGlobalResolveMaybe key = do
  maybeResult <- vmGlobalLookupMaybe key
  case maybeResult of
    Just _ -> return maybeResult
    Nothing -> systemLoadClassMaybe key

vmGlobalResolveOrNil :: Symbol -> Vm Object
vmGlobalResolveOrNil = fmap (fromMaybe nilObject) . vmGlobalResolveMaybe

vmGlobalResolveOrError :: Symbol -> Vm Object
vmGlobalResolveOrError key = vmGlobalResolveMaybe key >>= maybe (vmError ("vmGlobalResolve: " ++ key)) return

-- * Context

-- | Lookup a name in a Context.  See Context for description of lookup rules.
contextLookup :: Context -> Symbol -> Vm (Maybe Object)
contextLookup ctx k =
  case ctx of
    [] ->
      mLookupSequence
        [ vmGlobalResolveMaybe
        , vmWorkspaceLookupMaybe
        ]
        k
    MethodFrame _ _ rcv localVariables : _ ->
      if k == "self" || k == "super"
        then return (Just rcv)
        else
          mLookupSequence
            [ dictRefLookup localVariables
            , objectLookupInstanceVariable rcv
            , objectLookupClassVariable rcv
            , vmGlobalResolveMaybe
            ]
            k
    BlockFrame _ _ _ localVariables : p ->
      mLookupSequence
        [ dictRefLookup localVariables
        , contextLookup p
        , vmGlobalResolveMaybe
        , vmWorkspaceLookupMaybe
        ]
        k

-- | Assign to class variable of Object.  For rules see objectLookupClassVariable.
objectAssignClassVariable :: Object -> Symbol -> Object -> Vm (Maybe Object)
objectAssignClassVariable object key value =
  case object of
    Object _ DataUndefinedObject -> return Nothing
    Object _ (DataClass (cd, isMeta) tbl _) ->
      mAssignSequence
        [ tblAtKeyPutMaybe tbl
        , \k v -> classSuperclass cd isMeta >>= \sp -> objectAssignClassVariable sp k v
        ]
        key
        value
    _ -> objectClass object >>= \cl -> objectAssignClassVariable cl key value

{- | Set a name in a Context.
     Assignments at the empty context set variables in the Workspace.
-}
contextDoAssignment :: Context -> Symbol -> Object -> Vm (Maybe Object)
contextDoAssignment ctx k v =
  case ctx of
    [] -> fmap Just (vmWorkspaceAssignOrCreate k v)
    MethodFrame _ _ rcv localVariables : _p ->
      mAssignSequence
        [ dictRefAssignMaybe localVariables
        , objectAssignInstanceVariable rcv
        , objectAssignClassVariable rcv
        , vmGlobalAssign
        ]
        k
        v
    BlockFrame _ _ _ localVariables : p ->
      mAssignSequence
        [ dictRefAssignMaybe localVariables
        , contextDoAssignment p
        , vmGlobalAssign
        , vmWorkspaceAssign
        ]
        k
        v

-- | Add new BlockFrame frame to blockContext at blockObject.
blockContextFrame :: Object -> [Object] -> Maybe ExceptionHandler -> Vm Context
blockContextFrame blockObject arguments maybeExceptionHandler = do
  let Object _ (DataBlockClosure _ blockContext lambda) = blockObject
      Expr.Lambda _ blockArguments blockTemporaries _ = lambda
  localVariables <- localVariablesDict (zip blockArguments arguments) blockTemporaries
  pc <- vmIncrementProgramCounter
  return (contextAddFrame (BlockFrame pc blockObject maybeExceptionHandler localVariables) blockContext)

vmDoAssignment :: Symbol -> Object -> Vm Object
vmDoAssignment key value = do
  ctx <- vmGetContext
  res <- contextDoAssignment ctx key value
  maybe (vmErrorWithBacktrace ("vmDoAssignment: " ++ show key) [value]) return res

vmAssignAllToNil :: [Symbol] -> Vm ()
vmAssignAllToNil = mapM_ (\name -> vmDoAssignment name nilObject)

-- * Method

-- | Look in the methods of the class, then in the superclass.
findMethodMaybe :: Object -> St.Selector -> Vm (Maybe Object)
findMethodMaybe obj sel =
  if isNil obj -- Object superclass = nil
    then return Nothing
    else do
      r <- classCachedMethodLookup obj sel
      case r of
        Just m -> return (Just m)
        Nothing -> classSuperclassOf obj >>= \sc -> findMethodMaybe sc sel
