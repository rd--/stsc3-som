{-# Language FlexibleContexts #-}

{- | Type definitions and functions over these.

Some constructors are parameterized so that the types can be used both for a correct Som interpreter,
and for a more traditional Smalltalk interpreter.
-}
module Interpreter.Som.Types where

import Control.Monad.IO.Class {- base -}
import qualified Data.Char {- base -}
import Data.List {- base -}
import Data.Maybe {- base -}
import Text.Printf {- base -}

import qualified Data.Hashable as Hashable {- hashable -}
import qualified Data.Time.Clock.System as Time {- time -}

import qualified Control.Monad.State as State {- mtl -}
import qualified Control.Monad.Except as Except {- mtl -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Ansi.Expr as Expr {- stsc3 -}

import Interpreter.Som.DictRef
import Interpreter.Som.Error
import Interpreter.Som.Int
import Interpreter.Som.Ref
import Interpreter.Som.Str
import Interpreter.Som.Sym
import Interpreter.Som.Tbl
import Interpreter.Som.Vec

-- | Extensible mutable dictionary of named objects.
type ObjectDictionary = DictRef Symbol Object

-- | Indexable mutable association list (zero-indexed) of named objects.
type ObjectTable = Vec (Symbol, Ref Object)

-- | Identifier.
type Id = Int

-- | String literals must hash to the same value.
stringLiteralId :: Id
stringLiteralId = -1

{- | Method contexts store:
       1. a context identifier to receive non-local returns
       2. the method selector (signature) for back traces
       3. the receiver
     Block contexts store:
       1. the Block object to report cases of escaped blocks.
     In addition both store local variables (arguments and temporaries) as a Dict.
-}
data ContextNode =
    MethodContext Id Symbol Object ObjectDictionary
  | BlockContext Object ObjectDictionary
  | NilContext
  deriving (Eq)

{- | A Context is the environment a Smalltalk expression is evaluated in.
     The Name lookup rules are:

     For methods:
                  1. temporaries & arguments,
                  2. receiver instance variables,
                  3. receiver class variables,
                  4. globals.

     For blocks:
                  1. temporaries & arguments,
                  2. parent context chain,
                  3. globals,
                  4. workspace.
-}
data Context = Context { contextNode :: ContextNode, contextParent :: Maybe Context } deriving (Eq)

contextIdSequence :: Context -> [Id]
contextIdSequence ctx =
  case ctx of
    Context (MethodContext ctxId _ _ _) next -> ctxId : maybe [] contextIdSequence next
    Context _ (Just next) -> contextIdSequence next
    Context _ Nothing -> []

-- | Smalltalk expression
type StExpr = Expr.Expr

-- * Object

-- | (intObject, strObject, symObject)
type LiteralConstructors = (LargeInteger -> Object, String -> Object, String -> Object)

{- | Data associated with an object.

     Som:
       Som has no Character class
       Som strings are primitive and immutable, St strings are mutable.
       Symbol is a subclass of String
-}
data ObjectData
  = DataUndefinedObject -- ^ nil
  | DataBoolean
  | DataSmallInteger SmallInteger -- ^ Not in Som
  | DataLargeInteger LargeInteger -- ^ Som Integer
  | DataDouble Double
  | DataCharacter Char -- ^ Not in Som
  | DataImmutableString UnicodeString
  | DataClass (St.ClassDefinition, Bool) ObjectTable (Vec Object,Vec Object) -- ^ Class definition and level, class variables, method caches
  | DataMethod Symbol St.MethodDefinition StExpr -- ^ Holder, definition, lambda StExpr
  | DataPrimitive Symbol Symbol -- ^ Holder & Signature
  | DataBlock Id Context StExpr -- ^ Identity, context, lambda StExpr
  | DataReturn Id (Maybe Object) Object -- ^ Return contextId, Block returned from & value
  | DataSystem -- ^ Token for system or Smalltalk singleton
  | DataArrayLiteral (Vec Object) -- ^ Immutable array of literals
  | DataIndexable Id (VecRef Object) -- ^ Objects with a fixed number of integer indexed mutable slots
  | DataNonIndexable Id ObjectTable -- ^ Objects with named and index addressable instance variables
  | DataCharacterArray Id (VecRef Char) -- ^ Character array (for String and Symbol)
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
    _ -> return Nothing

objectDataAsArray :: MonadIO m => ObjectData -> m (Maybe [Object])
objectDataAsArray o =
  case o of
    DataArrayLiteral vec -> return (Just (vecToList vec))
    DataIndexable _ ref -> fmap Just (vecRefToList ref)
    _ -> return Nothing

-- | Object represented as class name and object data.
data Object = Object { objectClassName :: Symbol, objectData :: ObjectData } deriving (Eq)

-- | Association list of named objects.
type ObjectAssociationList = [(Symbol, Object)]

{- | The Vm state holds:
     - startTime, required for System>>ticks and System>>time
     - programCounter, used to identify method contexts and non-immediate objects
     - context, holds the currently executing context
     - globalDictionary, holds global variables
     - workspaceDictionary, holds workspace variables
-}
type VmState = (Double, Int, Context, ObjectDictionary, ObjectDictionary)

-- | Vm is an Exception/State monad over VmState
type Vm r = Except.ExceptT String (State.StateT VmState IO) r

-- | Generate Vm state from initial global dictionary.
vmStateInit :: ObjectDictionary -> IO VmState
vmStateInit globalDictionary = do
  startTime <- getSystemTimeInSeconds
  let programCounter = 0
  workspace <- dictRefEmpty
  return (startTime, programCounter, nilContext, globalDictionary, workspace)

-- | Fetch start time.
vmStartTime :: Vm Double
vmStartTime = State.get >>= \(startTime,_,_,_,_) -> return startTime

-- | Get system time in seconds (floating point).
getSystemTimeInSeconds :: MonadIO m => m Double
getSystemTimeInSeconds = do
  tm <- liftIO Time.getSystemTime
  return (fromIntegral (Time.systemSeconds tm) + (fromIntegral (Time.systemNanoseconds tm) * 1.0e-9))

vmElapsedTimeInMicroseconds :: Vm Int
vmElapsedTimeInMicroseconds = do
  startTime <- vmStartTime
  currentTime <- getSystemTimeInSeconds
  return (round ((currentTime - startTime) * 1.0e6))

-- | Fetch program counter.
vmProgramCounter :: Vm Int
vmProgramCounter = State.get >>= \(_,programCounter,_,_,_) -> return programCounter

-- | Increment program counter and return previous (pre-increment) value.
vmProgramCounterIncrement :: Vm Int
vmProgramCounterIncrement = State.get >>= \(tm,pc,ctx,glb,usr) -> State.put (tm,pc + 1,ctx,glb,usr) >> return pc

-- | Fetch current context
vmContext :: Vm Context
vmContext = State.get >>= \(_,_,ctx,_,_) -> return ctx

-- | Fetch Id of Method context, else error.
vmContextId :: Vm Id
vmContextId = vmContext >>= \ctx -> maybe (vmError "vmContextId: lookup failed") return (contextIdMaybe ctx)

vmContextIdSequence :: Vm [Id]
vmContextIdSequence = fmap contextIdSequence vmContext

-- | Fetch current block, else Nothing
vmContextCurrentBlock :: Vm (Maybe Object)
vmContextCurrentBlock = fmap contextCurrentBlock vmContext

-- | Apply /f/ at the context and store the result.
vmContextModify :: (Context -> Vm Context) -> Vm Object
vmContextModify f = do
  (tm,pc,ctx,glb,usr) <- State.get
  modifiedCtx <- f ctx
  State.put (tm,pc,modifiedCtx,glb,usr)
  return nilObject

-- | Add a frame to the context.
vmContextAdd :: ContextNode -> Vm ()
vmContextAdd x = vmContextModify (\ctx -> return (contextAdd ctx x)) >> return ()

-- | Delete a frame from the context
vmContextDelete :: Vm ()
vmContextDelete = vmContextModify contextDelete >> return ()

-- | Replace the context, return the previous context.
vmContextReplace :: Context -> Vm Context
vmContextReplace ctx = do
  (tm,pc,previousCtx,glb,usr) <- State.get
  State.put (tm,pc,ctx,glb,usr)
  return previousCtx

-- | Fetch global dictionary
vmGlobalDict :: Vm ObjectDictionary
vmGlobalDict = State.get >>= \(_,_,_,dict,_) -> return dict

-- | Lookup global, don't attempt to resolve if not found.
vmGlobalLookupMaybe :: Symbol -> Vm (Maybe Object)
vmGlobalLookupMaybe key = vmGlobalDict >>= \dict -> dictRefLookup dict key

-- | Lookup global, don't attempt to resolve if not found, return nil if not found.
vmGlobalLookupOrNil :: Symbol -> Vm Object
vmGlobalLookupOrNil key = vmGlobalLookupMaybe key >>= return . fromMaybe nilObject

-- | Lookup global, don't attempt to resolve if not found, return symbol looked for if not found.
vmGlobalLookupOrSymbol :: Symbol -> Vm Object
vmGlobalLookupOrSymbol key = vmGlobalLookupMaybe key >>= return . fromMaybe (immutableSymbolObject key)

-- | Lookup global, don't attempt to resolve if not found, error if not found.
vmGlobalLookupOrError :: Symbol -> Vm Object
vmGlobalLookupOrError key = vmGlobalLookupMaybe key >>= maybe (vmError ("vmGlobalLookup: " ++ fromSymbol key)) return

-- | Is global assigned, don't attempt to resolve if not.
vmHasGlobal :: Symbol -> Vm Bool
vmHasGlobal = fmap (maybe False (const True)) . vmGlobalLookupMaybe

-- | Assign to existing global variable.
vmGlobalAssignMaybe :: Symbol -> Object -> Vm (Maybe Object)
vmGlobalAssignMaybe key value = do
  d <- vmGlobalDict
  dictRefAssignMaybe d key value

-- | Assign to or create new global variable.
vmGlobalAssign :: Symbol -> Object -> Vm Object
vmGlobalAssign key value = vmGlobalDict >>= \d -> dictRefInsert d key value >> return value

-- | Fetch workspace dictionary
vmWorkspaceDict :: Vm ObjectDictionary
vmWorkspaceDict = State.get >>= \(_,_,_,_,d) -> return d

vmWorkspaceLookupMaybe :: Symbol -> Vm (Maybe Object)
vmWorkspaceLookupMaybe key = vmWorkspaceDict >>= \dict -> dictRefLookup dict key

-- | Assign to existing workspace variable.
vmWorkspaceAssignMaybe :: Symbol -> Object -> Vm (Maybe Object)
vmWorkspaceAssignMaybe key value = do
  d <- vmWorkspaceDict
  dictRefAssignMaybe d key value

-- | Assign to existing workspace variable or allocate new variable.
vmWorkspaceInsert :: Symbol -> Object -> Vm Object
vmWorkspaceInsert key value = do
  d <- vmWorkspaceDict
  dictRefInsert d key value
  return value

vmInspect :: Vm String
vmInspect = do
  (_tm,pc,_ctx,glb,wrk) <- State.get
  globalKeys <- dictRefKeys glb
  workspaceKeys <- dictRefKeys wrk
  return (show ("programCounter",pc,"global",globalKeys,"workspace",workspaceKeys))

-- * Printing

-- | Concise object printer.
objectToString :: Object -> String
objectToString (Object nm obj) =
  case obj of
    DataUndefinedObject -> "nil"
    DataBoolean -> map Data.Char.toLower nm
    DataSmallInteger x -> show x
    DataLargeInteger x -> show x
    DataDouble x -> show x
    DataCharacter x -> ['$',x]
    DataImmutableString x ->
      if nm == toSymbol "Symbol"
      then concat ["#'",fromUnicodeString x,"'"]
      else concat ["'",fromUnicodeString x,"'"]
    DataClass (x,isMeta) _ _ -> (if isMeta then St.metaclassName else id) (St.className x)
    DataMethod holder method _ -> concat [fromSymbol holder,">>",St.methodSignature method]
    DataPrimitive holder signature -> concat ["Primitive:",fromSymbol holder,">>",fromSymbol signature]
    DataBlock {} -> "instance of " ++ fromSymbol nm
    DataReturn _ _ o -> "Return: " ++ objectToString o
    DataSystem -> "instance of " ++ fromSymbol nm
    DataArrayLiteral vec -> "#(" ++ unwords (map objectToString (vecToList vec)) ++ ")"
    DataIndexable {} -> "instance of " ++ fromSymbol nm
    DataNonIndexable {} -> "instance of " ++ fromSymbol nm
    DataCharacterArray {} -> "instance of " ++ fromSymbol nm

instance Show Object where show = objectToString

objectPrint :: MonadIO m => Object -> m Object
objectPrint o =
  let recursionDepth = 5 :: Int
      f k = if k == 0 then return . objectToString else objectExamine (return "Vm") (f (k - 1))
  in liftIO (f recursionDepth o >>= putStrLn) >> return nilObject

objectListPrint :: MonadIO m => [Object] -> m Object
objectListPrint o = liftIO (putStrLn (intercalate ", " (map objectToString o))) >> return nilObject

-- * Inspect

objectTableExamine :: MonadIO m => (Object -> m String) -> ObjectTable -> m String
objectTableExamine f tbl = do
  (keys,values) <- fmap unzip (tblToList tbl)
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
    DataClass (x,_) tbl _ -> do
      tblStr <- objectTableExamine f tbl
      return (St.className x ++ ": " ++ tblStr)
    DataMethod _ x _ -> return (show x)
    DataBlock x _ (Expr.Lambda ld _ _ _) ->
      return (printf "instance of %s <pc:%d, %s>" nm x (Expr.lambdaDefinitionShow ld))
    DataNonIndexable x tbl -> do
      tblStr <- objectTableExamine f tbl
      return (printf "instance of %s <pc:%d>: %s" nm x tblStr)
    DataSystem -> vmPp
    _ -> return (objectToString (Object nm obj))

objectTableInspect :: ObjectTable -> Vm String
objectTableInspect = objectTableExamine objectInspect

objectDictionaryInspect :: ObjectDictionary -> Vm String
objectDictionaryInspect = objectDictionaryExamine objectInspect

objectInspect :: Object -> Vm String
objectInspect = objectExamine vmInspect objectInspect -- todo: recursion depth

contextNodeInspect :: ContextNode -> Vm String
contextNodeInspect ctx =
  case ctx of
    MethodContext ctxId sel rcv dict -> do
      let hdr = printf "<pc:%d> '%s'" ctxId sel
      rcv' <- objectInspect rcv
      dict' <- objectDictionaryInspect dict
      return (unlines ["MethodContext:", hdr, rcv', dict'])
    BlockContext blk dict -> do
      blk' <- objectInspect blk
      dict' <- objectDictionaryInspect dict
      return (unlines ["BlockContext:", blk', dict'])
    NilContext -> return "NilContext\n"

vmContextPrint :: Context -> Vm ()
vmContextPrint (Context node parent) = do
  str <- contextNodeInspect node
  liftIO (putStr (unlines ["Context: ", str]))
  case parent of
    Nothing -> return ()
    Just ctx -> vmContextPrint ctx

-- * Error

objectError :: Object -> String -> Vm t
objectError o msg = objectPrint o >> vmError msg

objectListError :: [Object] -> String -> Vm t
objectListError o msg = objectListPrint o >> vmError (printf "%s: arity=%d" msg (length o))

-- * Accessors

-- | The cache should be a dictionary rather than a vector.
classCachedMethodsVec :: Object -> Maybe (Vec Object)
classCachedMethodsVec (Object _ obj) =
  case obj of
    DataClass (_,False) _ (instanceMethodsCache,_) -> Just instanceMethodsCache
    DataClass (_,True) _ (_,classMethodsCache) -> Just classMethodsCache
    _ -> Nothing

indexableObjectElements :: Object -> Vm [Object]
indexableObjectElements o = case o of
  Object _ (DataIndexable _ vectorRef) -> fmap vecToList (deRef vectorRef)
  _ -> vmError ("indexableObjectElements: not indexable")

{-
arrayLiteralElements :: Object -> [Object]
arrayLiteralElements o = case o of
  Object "Array" (DataArrayLiteral vector) -> return vector
  _ -> vmError ("arrayLiteralElements: not literal array")
-}

arrayElements :: Object -> Vm [Object]
arrayElements o = case o of
  Object "Array" (DataIndexable _ vectorRef) -> fmap vecToList (deRef vectorRef)
  _ -> vmError ("arrayElements: not indexable object")

-- | Lookup instance variable of Object.
objectLookupInstanceVariable :: Object -> Symbol -> Vm (Maybe Object)
objectLookupInstanceVariable o key =
  case o of
    Object _ (DataNonIndexable _ tbl) -> tblAtKeyMaybe tbl key
    _ -> return Nothing

-- | Assign to instance variable of Object.
objectAssignInstanceVariable :: Object -> Symbol -> Object -> Vm (Maybe Object)
objectAssignInstanceVariable object key value =
  case object of
    Object _ (DataNonIndexable _ tbl) -> tblAtKeyPutMaybe tbl key value
    _ -> return Nothing

-- * Object constructors

data SystemType = SomSystem | SmalltalkSystem

-- | In Som the class of nil is Nil and in St-80 it is UndefinedObject.
sysNilClass :: SystemType -> String
sysNilClass sys =
  case sys of
    SomSystem -> "Nil"
    SmalltalkSystem -> "UndefinedObject"

-- | Make reserved identifier object.  These are stored in the global dictionary.
reservedObjectForSystem :: SystemType -> String -> Object
reservedObjectForSystem sys x =
  case x of
    "true" -> Object (toSymbol "True") DataBoolean
    "false" -> Object (toSymbol "False") DataBoolean
    "nil" -> Object (toSymbol (sysNilClass sys)) DataUndefinedObject
    "system" -> Object (toSymbol "System") DataSystem
    "Smalltalk" -> Object (toSymbol "SmalltalkImage") DataSystem
    _ -> error "reservedObject"

-- | echhh...  don't worry for St.
reservedObject :: String -> Object
reservedObject = reservedObjectForSystem SomSystem

systemReserverIdentifier :: SystemType -> String
systemReserverIdentifier typ =
  case typ of
    SomSystem -> "system"
    SmalltalkSystem  -> "Smalltalk"

-- | Table of reserved identifiers: nil, true, false and either system or Smalltalk.
reservedObjectTableFor :: SystemType -> ObjectAssociationList
reservedObjectTableFor typ =
  let f x = (x, reservedObject x)
  in map f (systemReserverIdentifier typ : words "nil true false")

-- | nil
nilObject :: Object
nilObject = reservedObject "nil"

-- | Make class and instance method caches.
classMethodCache :: St.ClassDefinition -> (Vec Object,Vec Object)
classMethodCache cd =
  let im = map (methodObject (toSymbol (St.className cd))) (St.instanceMethods cd)
      cm = map (methodObject (toSymbol (St.classMetaclassName cd))) (St.classMethods cd)
  in (vecFromList im,vecFromList cm)

-- | An ObjectTable with all variables set to nil.
variablesTbl :: MonadIO m => [Symbol] -> m ObjectTable
variablesTbl variableNames = tblFromList (zip variableNames (repeat nilObject))

{- | Create Class object from ClassDefinition
     The instance and class methods are generated and cached.
-}
classObject :: MonadIO m => St.ClassDefinition -> m Object
classObject cd = do
  let classVarNames = map toSymbol (St.classVariableNames cd)
  tbl <- variablesTbl classVarNames
  return (Object
           (toSymbol (St.classMetaclassName cd))
           (DataClass (cd,False) tbl (classMethodCache cd)))

{- | Create method Object for named Class.
     This is the point at which the MethodDefinition is translated to Expr form.
-}
methodObject :: Symbol -> St.MethodDefinition -> Object
methodObject holder method =
  Object (toSymbol "Method") (DataMethod holder method (Expr.methodDefinitionExpr method))

smallIntegerObject :: SmallInteger -> Object
smallIntegerObject x = Object (toSymbol "SmallInteger") (DataSmallInteger x)

largeIntegerObject :: LargeInteger -> Object
largeIntegerObject x = Object (toSymbol "LargeInteger") (DataLargeInteger x)

doubleObject :: Double -> Object
doubleObject x = Object (toSymbol "Double") (DataDouble x)

-- | Integer given by consrtructor if fractional part is zero, else Double.
doubleAsFractional :: Integral t => (t -> Object) -> Double -> Object
doubleAsFractional cons x =
  case properFraction x of
    (i,0) -> cons i
    _ -> doubleObject x

nanObject :: Object
nanObject = doubleObject (0/0)

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

{- | Mark an Object as being a Return Object (from a Block or Method).
     Include the contextId the value is returning to,
     and the Block that is returning (if it is a Block and not a Method).
     It is an error if the object returned is already a Return Object.
-}
returnObject :: StError m => Id -> Maybe Object -> Object -> m Object
returnObject pc blockObject x =
  if isReturnObject x
  then vmError "returnObject: already Return"
  else return (Object (toSymbol "Return") (DataReturn pc blockObject x))

-- * Object predicates

isReturnObject :: Object -> Bool
isReturnObject x =
  case x of
    Object _ (DataReturn _ _ _) -> True
    _ -> False

isNil :: Object -> Bool
isNil = (==) nilObject

-- * Context

{- | Dictionary of arguments and temporaries.
     Temporaries may shadow arguments.
     Dict will discard multiple keys, keeping the last assigned.
     Therefore arguments are set first.
-}
localVariablesDict :: MonadIO m => ObjectAssociationList -> [Symbol] -> m ObjectDictionary
localVariablesDict args tmp = dictRefFromList (args ++ zip tmp (repeat nilObject))

methodContextNode :: MonadIO m => Id -> Symbol -> Object -> ObjectAssociationList -> St.Temporaries -> m ContextNode
methodContextNode pc sel rcv arg (St.Temporaries tmp) =
  fmap (MethodContext pc sel rcv) (localVariablesDict arg (map toSymbol tmp))

-- | The empty context.  It is ordinarily an error to encounter this.
nilContext :: Context
nilContext = Context NilContext Nothing

-- | Traverse context to innermost MethodContext and get receiver.
contextReceiverMaybe :: Context -> Maybe Object
contextReceiverMaybe (Context c p) =
  case c of
    BlockContext _ _ -> maybe Nothing contextReceiverMaybe p
    MethodContext _ _ rcv _ -> Just rcv
    NilContext -> Nothing

-- | Traverse context to innermost MethodContext and get Id.
contextIdMaybe :: Context -> Maybe Id
contextIdMaybe (Context c p) =
  case c of
    BlockContext _ _ -> maybe Nothing contextIdMaybe p
    MethodContext pc _ _ _ -> Just pc
    NilContext -> Nothing

-- | Does Context have a Method with Id?
contextHasId :: Id -> Context -> Bool
contextHasId k (Context c p) =
  case c of
    BlockContext _ _ -> maybe False (contextHasId k) p
    MethodContext pc _ _ _ -> pc == k || maybe False (contextHasId k) p
    NilContext -> False

-- | Get the blockObject from the current frame.
contextCurrentBlock :: Context -> Maybe Object
contextCurrentBlock (Context c _x) =
  case c of
    BlockContext blockObject _ -> Just blockObject
    _ -> Nothing

-- | Add a node to the start of the Context.
contextAdd :: Context -> ContextNode -> Context
contextAdd ctx nd = Context nd (Just ctx)

{- | Deleting a context with no parent is an error.
     (Root contexts ought to have the NilContext as a parent.)
-}
contextDelete :: StError m => Context -> m Context
contextDelete ctx =
  case ctx of
    Context _ (Just p) -> return p
    Context _ Nothing -> vmError "contextDelete: empty context"

-- * Hash

mHash :: (Monad m,Hashable.Hashable t) => t -> m SmallInteger
mHash = return . Hashable.hash

-- | Hash of object.  Used for object equality.
objectIntHash :: (MonadIO m, StError m) => Object -> m SmallInteger
objectIntHash (Object nm obj) =
  case obj of
    DataUndefinedObject -> mHash (nm,"nil")
    DataBoolean -> mHash nm
    DataSmallInteger x -> return x -- c.f. Integer>>hashcode
    DataLargeInteger x -> return (fromInteger x) -- c.f. Integer>>hashcode
    DataDouble x -> mHash x
    DataCharacter x -> mHash x
    DataImmutableString x -> mHash (nm, x) -- c.f. 'x' hashcode /= #'x' hashcode
    DataClass (x,_) _ _ -> mHash (nm,St.className x)
    DataMethod holder method _ -> mHash (nm,holder,St.methodSignature method)
    DataPrimitive holder signature -> mHash (nm,holder,signature)
    DataBlock x _ _ -> mHash ("Block",x)
    DataReturn _ _ _ -> vmError ("Object>>hashcode: Return")
    DataSystem -> mHash (nm,"system")
    DataArrayLiteral vec -> mapM objectIntHash (vecToList vec) >>= \lst -> mHash (nm, lst)
    DataIndexable x _ -> mHash (nm,x)
    DataNonIndexable x _ -> mHash (nm,x)
    DataCharacterArray _ ref -> vecRefToList ref >>= \str -> mHash (nm, str) -- strings and copies of strings hash equally
