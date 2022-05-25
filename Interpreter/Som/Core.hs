{- | Variable lookup and assignment,
     expression evalulation,
     interpreter primitives -}
module Interpreter.Som.Core where

import Control.Monad {- base -}
import Control.Monad.IO.Class {- base -}
import qualified Data.Char {- base -}
import Data.Maybe {- base -}
import Text.Printf {- base -}

import qualified Control.Monad.State as State {- mtl -}
import qualified Control.Monad.Except as Except {- mtl -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Ansi.Expr as Expr {- stsc3 -}

import Interpreter.Som.DictRef
import Interpreter.Som.Dir
import Interpreter.Som.Error
import Interpreter.Som.Int
import Interpreter.Som.Ref
import Interpreter.Som.Str
import Interpreter.Som.Sym
import Interpreter.Som.Tbl
import Interpreter.Som.Types
import Interpreter.Som.Vec

-- * Types

-- | (Holder, selector), code, receiver, arguments, answer.
type PrimitiveDispatcher = (Symbol, Symbol) -> Integer -> Object -> [Object] -> Vm (Maybe Object)

data CoreOpt = CoreOpt { coreOptTyp :: SystemType, coreOptLit :: LiteralConstructors, coreOptPrim :: PrimitiveDispatcher }

-- * Error

vmBacktrace :: Vm ()
vmBacktrace = do
  ctx <- vmContext
  liftIO (putStrLn "Vm: Backtrace")
  vmContextPrint ctx

vmErrorWithBacktrace :: String -> [Object] -> Vm t
vmErrorWithBacktrace msg obj = vmBacktrace >> objectListError obj msg

-- * Copy

stringToCharacterArray :: String -> Vm ObjectData
stringToCharacterArray str = do
  pc <- vmProgramCounterIncrement
  ref <- vecRefFromList (fromUnicodeString str)
  return (DataCharacterArray pc ref)

mutableStringObject :: String -> Vm Object
mutableStringObject str = fmap (Object (toSymbol "String")) (stringToCharacterArray str)

mutableSymbolObject :: String -> Vm Object
mutableSymbolObject str = fmap (Object (toSymbol "Symbol")) (stringToCharacterArray str)

objectDataShallowCopy :: ObjectData -> Vm ObjectData
objectDataShallowCopy od =
  case od of
    DataArrayLiteral vec -> do
      pc <- vmProgramCounterIncrement
      ref <- toRef (vecShallowCopy vec)
      return (DataIndexable pc ref)
    DataCharacterArray _ ref -> do
      pc <- vmProgramCounterIncrement
      cpy <- vecRefShallowCopy ref
      return (DataCharacterArray pc cpy)
    DataImmutableString False str -> stringToCharacterArray str
    DataIndexable _ ref -> do
      pc <- vmProgramCounterIncrement
      cpy <- vecRefShallowCopy ref
      return (DataIndexable pc cpy)
    DataNonIndexable _ tbl -> do
      pc <- vmProgramCounterIncrement
      cpy <- objectTableShallowCopy tbl
      return (DataNonIndexable pc cpy)
    _ -> return od

objectShallowCopy :: Object -> Vm Object
objectShallowCopy (Object nm obj) = do
  cpy <- objectDataShallowCopy obj
  return (Object nm cpy)

objectTableShallowCopy :: ObjectTable -> Vm ObjectTable
objectTableShallowCopy vec = do
  let (keys, refs) = unzip (vecToList vec)
  values <- mapM deRef refs
  copies <- mapM objectShallowCopy values
  newRefs <- mapM toRef copies
  return (vecFromList (zip keys newRefs))

-- * Lookup

-- | Sequence of lookup procedures to be tried in left to right sequence.
mLookupSequence :: Monad m => [k -> m (Maybe v)] -> k -> m (Maybe v)
mLookupSequence l k =
  case l of
    [] -> return Nothing
    f:l' -> do
      r <- f k
      case r of
        Nothing -> mLookupSequence l' k
        _ -> return r

-- | Sequence of assignment procedures to be tried in left to right sequence.
mAssignSequence :: Monad m => [k -> v -> m (Maybe v)] -> k -> v -> m (Maybe v)
mAssignSequence l k v =
  case l of
    [] -> return Nothing
    f:l' -> do
      r <- f k v
      case r of
        Nothing -> mAssignSequence l' k v
        _ -> return r

-- * Context

{- | Lookup class variable from Object. If the object is:
     1. a class then look in it's table, else lookup it's superclass.
     2. nil then stop looking
     3. any other object look in it's class object
-}
objectLookupClassVariable :: Object -> Symbol -> Vm (Maybe Object)
objectLookupClassVariable object key =
  case object of
    Object _ DataUndefinedObject -> return Nothing
    Object _ (DataClass (cd,isMeta) tbl _) ->
      mLookupSequence [tblAtKeyMaybe tbl
                      ,\k -> classSuperclass cd isMeta >>= \sp -> objectLookupClassVariable sp k] key
    _ -> objectClass object >>= \cl -> objectLookupClassVariable cl key

-- | Lookup a name in a Context.  See Context for description of lookup rules.
contextLookup :: Context -> Symbol -> Vm (Maybe Object)
contextLookup (Context c p) k =
  case c of
    MethodContext _ _ rcv localVariables ->
      if k == "self" || k == "super"
      then return (Just rcv)
      else mLookupSequence [dictRefLookup localVariables
                           ,objectLookupInstanceVariable rcv
                           ,objectLookupClassVariable rcv
                           ,vmGlobalResolveMaybe] k
    BlockContext _ localVariables ->
      mLookupSequence [dictRefLookup localVariables
                      ,maybe (\_ -> return Nothing) (\c' -> contextLookup c') p
                      ,vmGlobalResolveMaybe
                      ,vmWorkspaceLookupMaybe] k
    NilContext ->
      mLookupSequence [vmGlobalResolveMaybe
                      ,vmWorkspaceLookupMaybe] k

-- | Assign to class variable of Object.  For rules see objectLookupClassVariable.
objectAssignClassVariable :: Object -> Symbol -> Object -> Vm (Maybe Object)
objectAssignClassVariable object key value =
  case object of
    Object _ DataUndefinedObject -> return Nothing
    Object _ (DataClass (cd,isMeta) tbl _) ->
      mAssignSequence [tblAtKeyPutMaybe tbl
                      ,\k v -> classSuperclass cd isMeta >>= \sp -> objectAssignClassVariable sp k v] key value
    _ -> objectClass object >>= \cl -> objectAssignClassVariable cl key value

{- | Set a name in a Context.
     Assignments at NilContext (the empty context) set variables in the Workspace.
-}
contextAssign :: Context -> Symbol -> Object -> Vm (Maybe Object)
contextAssign (Context c p) k v =
  case c of
    MethodContext _ _ rcv localVariables ->
      mAssignSequence [dictRefAssignMaybe localVariables
                      ,objectAssignInstanceVariable rcv
                      ,objectAssignClassVariable rcv
                      ,vmGlobalAssignMaybe] k v
    BlockContext _ localVariables ->
      mAssignSequence [dictRefAssignMaybe localVariables
                      ,maybe (\_ _ -> return Nothing) (\c' -> contextAssign c') p
                      ,vmGlobalAssignMaybe
                      ,vmWorkspaceAssignMaybe] k v
    NilContext -> fmap Just (vmWorkspaceInsert k v)

{- | Add blockFrame to blockContext.
     For blocks with no arguments and no temporaries and no return statements,
     the context could perhaps be elided.
-}
contextAddBlockContext :: Object -> [Object] -> Vm Context
contextAddBlockContext blockObject arguments = do
  let Object _ (DataBlock _ blockContext lambda) = blockObject
      Expr.Lambda _ blockArguments (St.Temporaries blockTemporaries) _ = lambda
  when
    (length blockArguments /= length arguments)
    (vmErrorWithBacktrace "contextAddBlockContext: arity error" (blockObject : arguments))
  localVariables <- localVariablesDict (zip blockArguments arguments) blockTemporaries
  return (contextAdd blockContext (BlockContext blockObject localVariables))

-- | Lookup value in current context.
vmContextLookup :: CoreOpt -> Symbol -> Vm Object
vmContextLookup opt k = do
  ctx <- vmContext
  res <- contextLookup ctx k
  maybe (vmUnknownGlobal opt ctx k) return res

-- | Assign value in current context
vmContextAssign :: Symbol -> Object -> Vm Object
vmContextAssign k v = do
  ctx <- vmContext
  res <- contextAssign ctx k v
  maybe (vmError ("vmContextAssign: " ++ show k)) return res

-- | Run vmContextAssign to set all temporaries to Nil.
vmContextAssignAllToNil :: [Symbol] -> Vm ()
vmContextAssignAllToNil = mapM_ (\name -> vmContextAssign name nilObject)

-- * Vm

coreSymbolObject :: CoreOpt -> String -> Object
coreSymbolObject opt str = let (_, _, symObject) = coreOptLit opt in symObject str

-- | When a method lookup fails, the doesNotUnderstand:arguments: message is sent to the receiver.
vmDoesNotUnderstand :: CoreOpt -> Object -> String -> Object -> Vm Object
vmDoesNotUnderstand opt receiver k argsArray = do
  let sel = St.KeywordSelector "doesNotUnderstand:arguments:"
  --printTrace ("vmDoesNotUnderstand: " ++ k ++ " <= ") [receiver, argsArray]
  evalMessageSend opt False receiver sel [coreSymbolObject opt k, argsArray]

-- | When a global lookup fails, the unknownGlobal: message is sent to the contextReceiver, if there is one.
vmUnknownGlobal :: CoreOpt -> Context -> String -> Vm Object
vmUnknownGlobal opt ctx k =
  case contextReceiverMaybe ctx of
    Just receiver -> evalMessageSend opt False receiver (St.KeywordSelector "unknownGlobal:") [coreSymbolObject opt k]
    _ -> vmError ("vmUnknownGlobal: no contextReceiver: " ++ show k)

{- | If a Return escapes we send an escapedBlock: message to the Object that the Block that Returned escaped from.
     For this purpose the Return object stores the Block that sent it.
     The Block can access the required Object from it's stored context.
     The Block that sent Return will be the current BlockContext.
     The Object that received the message that created a block will be the current MethodContext.
-}
vmEscapedBlock :: CoreOpt -> Maybe Object -> Vm Object
vmEscapedBlock opt maybeBlock =
  case maybeBlock of
    Just block ->
      case block of
        Object _ (DataBlock _ context _) ->
          case contextReceiverMaybe context of
            Just receiver -> evalMessageSend opt False receiver (St.KeywordSelector "escapedBlock:") [block]
            Nothing -> vmError "escaped context: no receiver"
        _ -> vmError "escaped context: bad block"
    Nothing -> vmError "escaped context?"

-- * Resolve

-- | If a global does not exist, attempt to resolve it by loading a class file.
vmGlobalResolveMaybe :: Symbol -> Vm (Maybe Object)
vmGlobalResolveMaybe key = do
  maybeResult <- vmGlobalLookupMaybe key
  case maybeResult of
    Just _ -> return maybeResult
    Nothing -> systemLoadClassMaybe key

-- | Resolve global, nil if not located.
vmGlobalResolveOrNil :: Symbol -> Vm Object
vmGlobalResolveOrNil = fmap (fromMaybe nilObject) . vmGlobalResolveMaybe

-- | Resolve global, error if not located.
vmGlobalResolveOrError :: Symbol -> Vm Object
vmGlobalResolveOrError key = vmGlobalResolveMaybe key >>= maybe (vmError ("vmGlobalResolve: " ++ key)) return

-- * Eval

{- | Evaluate StExpr in sequence.

If an StExpr evaluates to a Return Object it is returned and no further StExpr are evaluated.
Note that the return value of e0 being a Return object is not the same as e0 being a Return expression.
-}
evalExprSequence :: CoreOpt -> [StExpr] -> Vm Object
evalExprSequence opt st =
  case st of
    [] -> error "evalExprSequence: empty sequence"
    [e] -> evalExpr opt e
    e0:eN -> do
      r <- evalExpr opt e0
      if isReturnObject r then return r else evalExprSequence opt eN

-- | An empty sequence returns nil, otherwise either a Return value or the value of the last StExpr is returned.
evalStatements :: CoreOpt -> [StExpr] -> Vm Object
evalStatements opt st = if null st then return nilObject else evalExprSequence opt st

{- | evalBlock works by:
   1. extending the stored (block) context with a context frame
   2. saving the current (Vm) context and replacing it with the extended stored context
   3. evaluating the block body and saving the result
   4. restoring the saved context
   5. returning the saved result
-}
evalBlock :: CoreOpt -> Object -> [Object] -> Vm Object
evalBlock opt blockObject arguments = do
  let Object _ (DataBlock _ _ (Expr.Lambda _ _ _ blockStatements)) = blockObject
  extendedBlockContext <- contextAddBlockContext blockObject arguments
  currentContext <- vmContextReplace extendedBlockContext
  result <- evalStatements opt blockStatements
  _ <- vmContextReplace currentContext
  case result of
    Object _ (DataReturn pc maybeBlock _) ->
      if contextHasId pc currentContext
      then return result
      else vmEscapedBlock opt maybeBlock
    _ -> return result

{- | evalMethod is similar to evalBlock, except that methods:
   1. have a receiver which is stored and can be referenced as self or super
   2. store a context identifier in order to receive non-local returns
   2. don't have a stored (saved) context (they begin in the current environment, they are not closures)
   4. return self (the receiver) if there is no return statement

Return statements are allowed as the last statement of either a Method or a Block.
Returns in Blocks are non-local, they return to the blocks home context.
The home context is the method the block was defined in.

-}
evalMethod :: CoreOpt -> St.MethodDefinition -> [Symbol] -> St.Temporaries -> [StExpr] -> Object -> [Object] -> Vm Object
evalMethod opt methodDefinition methodArguments methodTemporaries methodStatements receiver arguments = do
  --printTrace ("evalMethod: " ++ St.methodSignature methodDefinition ++ " <= ") [receiver]
  let requiredArguments = length methodArguments
      providedArguments = length arguments
      selector = St.methodSignature methodDefinition
      arityError = printf "evalMethod: wrong number of arguments: %s %d" selector providedArguments
  when (requiredArguments /= providedArguments) (vmError arityError)
  pc <- vmProgramCounterIncrement
  vmContextAdd =<< methodContextNode pc selector receiver (zip methodArguments arguments) methodTemporaries
  result <- evalStatements opt methodStatements
  _ <- vmContextDelete
  case result of
    (Object "Return" (DataReturn ctxId _ x)) ->
      if ctxId == pc
      then --printTrace ("Return: ctxId at pc: " ++ show (ctxId, pc)) [receiver, result] >>
           return x
      else --(vmContextIdSequence >>= \sq -> printTrace ("Return: ctxId not at pc: " ++ show (ctxId, pc, sq)) [receiver, result]) >>
           return result
    _ -> return receiver

-- | Evaluate method, deferring to Primitive if required.
evalMethodOrPrimitive :: CoreOpt -> ObjectData -> Object -> [Object] -> Vm Object
evalMethodOrPrimitive opt dat rcv arg =
  let (DataMethod holder methodDefinition expr) = dat
      (Expr.Lambda _ methodArguments methodTemporaries methodStatements) = expr
  in case St.methodDefinitionPrimitiveCode methodDefinition of
       Just k -> do
         --printTrace "evalMethodOrPrimitive: primitive" (rcv : arg)
         answer <- (coreOptPrim opt) (holder, St.methodSignature methodDefinition) k rcv arg
         case answer of
           Just result -> return result
           Nothing -> evalMethod opt methodDefinition methodArguments methodTemporaries methodStatements rcv arg
       Nothing -> evalMethod opt methodDefinition methodArguments methodTemporaries methodStatements rcv arg

indexableFromVec :: Symbol -> Vec Object -> Vm Object
indexableFromVec cl vec = do
  pc <- vmProgramCounterIncrement
  ref <- liftIO (toRef vec)
  return (Object cl (DataIndexable pc ref))

indexableFromList :: Symbol -> [Object] -> Vm Object
indexableFromList cl e = indexableFromVec cl (vecFromList e)

arrayFromVec :: Vec Object -> Vm Object
arrayFromVec = indexableFromVec "Array"

arrayFromList :: [Object] -> Vm Object
arrayFromList = indexableFromList "Array"

-- | Find method & evaluate, else send doesNotUnderstand message.
findAndEvalMethodOrPrimitive :: CoreOpt -> Object -> Object -> St.Selector -> [Object] -> Vm Object
findAndEvalMethodOrPrimitive opt receiver methodReceiver selector arguments = do
  maybeMethod <- findMethodMaybe methodReceiver selector
  --printTrace ("findAndEvalMethodOrPrimitive: " ++ St.selectorIdentifier selector) (receiver : arguments)
  case maybeMethod of
    Nothing -> do
      argumentsArray <- arrayFromList arguments
      vmDoesNotUnderstand opt receiver (St.selectorIdentifier selector) argumentsArray
    Just (Object "Method" dat) -> evalMethodOrPrimitive opt dat receiver arguments
    _ -> vmError "findAndEvalMethodOrPrimitive"

-- | Look in the methods of the class, then in the superclass.
findMethodMaybe :: Object -> St.Selector -> Vm (Maybe Object)
findMethodMaybe o sel =
  if isNil o
  then return Nothing
  else case classCachedMethodsVec o of
         Just mth ->
          case vecFind (\(Object _ (DataMethod _ m _)) -> sel == St.methodSelector m) mth of
            Just m -> return (Just m)
            Nothing -> classSuperclassOf o >>= \sc -> findMethodMaybe sc sel
         _ -> vmError "findMethodMaybe"

-- | Evaluate message send.
evalMessageSend :: CoreOpt -> Bool -> Object -> St.Selector -> [Object] -> Vm Object
evalMessageSend opt isSuper receiver selector arguments = do
  receiverClass <- objectClass receiver
  methodClass <- if isSuper
                 then classSuperclassOf receiverClass
                 else return receiverClass
  findAndEvalMethodOrPrimitive opt receiver methodClass selector arguments

-- | Som/St.  Som has distinct numbered Block classes.
closureClass :: SystemType -> Int -> String
closureClass typ numArg =
  case typ of
    SomSystem -> "Block" ++ show (numArg + 1)
    SmalltalkSystem -> "BlockClosure"

-- | Som/St.  Som array literals are mutable, St string literals are mutable...
sysLiteralObject :: SystemType -> Object -> Vm Object
sysLiteralObject typ obj =
  case (typ, obj) of
    (SomSystem, Object _ (DataArrayLiteral _)) -> objectShallowCopy obj
    (SmalltalkSystem, Object _ (DataImmutableString False str))  -> mutableStringObject str
    _ -> return obj

{- | Evaluate expression.

The evaluator handles non-local returns by making a "Return" object.
The evaluator runs isReturnObject to see if further work needs to be done, or if the evaluation is unwinding.
-}
evalExpr :: CoreOpt -> StExpr -> Vm Object
evalExpr opt expr =
  case expr of
    Expr.Identifier x -> vmContextLookup opt (if x == "super" then "self" else x)
    Expr.Literal x -> sysLiteralObject (coreOptTyp opt) (literalObject (coreOptLit opt) x)
    Expr.Assignment lhs rhs -> evalExpr opt rhs >>= vmContextAssign lhs
    Expr.Return x -> do
      result <- evalExpr opt x
      if isReturnObject result
      then return result
      else do pc <- vmContextId
              blk <- vmContextCurrentBlock
              returnObject pc blk result
    Expr.Send e (Expr.Message selector exprList) -> do
      receiver <- evalExpr opt e
      if (isReturnObject receiver)
      then return receiver
      else do arguments <- mapM (evalExpr opt) exprList
              evalMessageSend opt (Expr.exprIsSuper e) receiver selector arguments
    Expr.Lambda _ld arg _tmp _stm -> do
      ctx <- vmContext
      pc <- vmProgramCounterIncrement
      return (Object (closureClass (coreOptTyp opt) (length arg)) (DataBlock pc ctx expr))
    Expr.Array exprList -> mapM (evalExpr opt) exprList >>= arrayFromList
    Expr.Begin exprList -> evalExprSequence opt exprList
    Expr.Init _ (St.Temporaries tmp) exprList -> vmContextAssignAllToNil tmp >> evalExprSequence opt exprList

-- | Parse string as a Smalltalk program, convert to Expr form, run evalExpr and return an Object.
evalString :: CoreOpt -> String -> Vm Object
evalString opt txt = evalExpr opt (Expr.smalltalkProgramExpr (St.stParse St.smalltalkProgram txt))

deleteLeadingSpaces :: String -> String
deleteLeadingSpaces = dropWhile Data.Char.isSpace

{- | Run evalString given initial state and input text.
     If the text is empty (or whitespace only) return nil.
-}
vmEval :: CoreOpt -> VmState -> String -> IO (Either String Object, VmState)
vmEval opt vmState str =
  case deleteLeadingSpaces str of
    [] -> return (Right nilObject, vmState)
    txt -> State.runStateT (Except.runExceptT (evalString opt txt)) vmState

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
      do res <- vmGlobalLookupMaybe spName
         case res of
           Just (Object _ (DataClass (spCd,_) _ _)) ->
             do spIv <- classAllVariableNames fn spCd
                return (spIv ++ fn cd)
           _ -> vmError "classAllVariableNames"
    Nothing -> return (fn cd)

{- | Create instance of a non-indexable non-immediate class.
     Allocate reference for instance variables and initialize to nil.
     The instance variables of an object are:
         - the instance variables of it's class definition
         - all of the instance variables of all of it's superclasses.
-}
classNew :: St.ClassDefinition -> Vm Object
classNew cd = do
  instVarNames <- classAllVariableNames St.classInstanceVariableNames cd
  tbl <- variablesTbl instVarNames
  pc <- vmProgramCounterIncrement
  return (Object (St.className cd) (DataNonIndexable pc tbl))

arrayNewWithArg :: Int -> Vm Object
arrayNewWithArg size = arrayFromList (replicate size nilObject)

stringNewWithArg :: SmallInteger -> Vm Object
stringNewWithArg size = do
  pc <- vmProgramCounterIncrement
  let vec = vecFromList (replicate size '\0')
  ref <- liftIO (toRef vec)
  return (Object "String" (DataCharacterArray pc ref))

classNewWithArg :: St.ClassDefinition -> SmallInteger -> Vm Object
classNewWithArg cd size = do
  case St.className cd of
    "Array" -> arrayNewWithArg size
    "String" -> stringNewWithArg size
    _ -> vmError "classNewWithArg"

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
    sp <- maybe (return nilObject) vmGlobalResolveOrNil (St.superclassName cd)
    if isMeta then classMetaclass sp else return sp

classSuperclassOf :: Object -> Vm Object
classSuperclassOf (Object _ obj) =
  case obj of
    DataClass (cd,isMeta) _ _ -> classSuperclass cd isMeta
    _ -> vmError "classSuperclassOf"

-- * Object Primitives

{- | Class of class (Metaclass).
     If the Class object isMeta then return Metaclass, else set isMeta.
     Metaclass should be an ordinary class, it is looked up in the global dictionary.
-}
classMetaclass :: Object -> Vm Object
classMetaclass receiver@(Object _ obj) =
  case obj of
    DataClass (cd,isMeta) cVar mCache ->
      if isMeta
      then vmGlobalResolveOrError "Metaclass"
      else return (Object "Class" (DataClass (cd,True) cVar mCache))
    _ -> vmErrorWithBacktrace "classMetaclass" [receiver]

objectClass :: Object -> Vm Object
objectClass rcv@(Object nm obj) =
  case obj of
    DataClass {} -> classMetaclass rcv
    _ -> vmGlobalLookupOrError nm

objectInspectAndPrint :: Object -> Vm Object
objectInspectAndPrint rcv = objectInspect rcv >>= liftIO . putStrLn >> return rcv

objectPerformWithArgumentsInSuperclass :: CoreOpt -> Object -> UnicodeString -> Object -> Object -> Vm Object
objectPerformWithArgumentsInSuperclass opt rcv sel argumentsArray cl = do
  arguments <- arrayElements argumentsArray
  findAndEvalMethodOrPrimitive opt rcv cl (St.stParse St.quotedSelector ('#' : fromUnicodeString sel)) arguments

objectPerformWithArguments :: CoreOpt -> Object -> UnicodeString -> Object -> Vm Object
objectPerformWithArguments opt rcv sel argArray = objectClass rcv >>= \cl -> objectPerformWithArgumentsInSuperclass opt rcv sel argArray cl

objectPerformInSuperclass :: CoreOpt -> Object -> UnicodeString -> Object -> Vm Object
objectPerformInSuperclass opt rcv sel cl = findAndEvalMethodOrPrimitive opt rcv cl (St.stParse St.quotedSelector ('#' : fromUnicodeString sel)) []

objectPerform :: CoreOpt -> Object -> UnicodeString -> Vm Object
objectPerform opt rcv sel = objectClass rcv >>= \cl -> objectPerformInSuperclass opt rcv sel cl

-- * System Primitives

-- | Load class or return nil.
systemLoadClassOrNil :: Symbol -> Vm Object
systemLoadClassOrNil = fmap (fromMaybe nilObject) . systemLoadClassMaybe

-- | Load and return class (and required parent classes) if it exists.
systemLoadClassMaybe :: Symbol -> Vm (Maybe Object)
systemLoadClassMaybe x = do
  c <- systemLoadAndAssignClassesAbove x
  case c of
    Nothing -> return Nothing
    Just _ -> vmGlobalLookupMaybe x

{- | Loads the named class and all of it's superclasses that are not already loaded.
     Assign each class in the global dictionary.
     Returns the last class loaded (ie. not necessarily the initial class requested).
     Halts when arriving at a class that is already loaded.
-}
systemLoadAndAssignClassesAbove :: Symbol -> Vm (Maybe Object)
systemLoadAndAssignClassesAbove x = do
  existing <- vmGlobalLookupMaybe x
  case existing of
      Just _ -> return existing
      Nothing -> do
        -- printTrace ("systemLoadAndAssignClassesAbove: " ++ x) []
        maybeCd <- liftIO (somLoadClassFile x) -- todo: this should also read .st and .stc files
        case maybeCd of
          Just cd -> do
            co <- classObject cd
            _ <- case St.superclassName cd of
                   Just sp -> systemLoadAndAssignClassesAbove sp
                   Nothing -> return (Just co)
            _ <- vmGlobalAssign (St.className cd) co
            return (Just co)
          _ -> return Nothing

-- * Tables

makeClassTable :: MonadIO m => [St.ClassDefinition] -> m ObjectAssociationList
makeClassTable classLibrary = do
  let classNames = map St.className classLibrary
  classObjects <- mapM classObject classLibrary
  return (zip classNames classObjects)

-- * Trace

printTrace :: MonadIO m => String -> [Object] -> m ()
printTrace msg o = liftIO (putStr (msg ++ " with: ")) >> objectListPrint o >> return ()
