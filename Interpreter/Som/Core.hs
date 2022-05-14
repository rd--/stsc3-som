{- | Variable lookup and assignment,
     expression evalulation,
     interpreter primitives -}
module Interpreter.Som.Core where

import Control.Monad {- base -}
import Control.Monad.IO.Class {- base -}
import qualified Data.Char {- base -}
import Data.Maybe {- base -}
import Text.Printf {- base -}

--import qualified Data.Text as Text {- text -}
import qualified Data.Vector as Vector {- vector -}

import qualified Control.Monad.State as State {- mtl -}
import qualified Control.Monad.Except as Except {- mtl -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Ansi.Expr as Expr {- stsc3 -}
import qualified Language.Smalltalk.Som as Som {- stsc3 -}

import Interpreter.Som.DictRef
--import Interpreter.Som.Primitives
import Interpreter.Som.Str.Text
import Interpreter.Som.Sym
import Interpreter.Som.Tbl
import Interpreter.Som.Types

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
    Object _ DataNil -> return Nothing
    Object _ (DataClass (cd,isMeta) tbl _) ->
      mLookupSequence [tblAtKeyMaybe tbl
                      ,\k -> prClassSuperclass cd isMeta >>= \sp -> objectLookupClassVariable sp k] key
    _ -> prObjectClass object >>= \cl -> objectLookupClassVariable cl key

-- | Lookup a name in a Context.  See Context for description of lookup rules.
contextLookup :: Context -> Symbol -> Vm (Maybe Object)
contextLookup (Context c p) k =
  case c of
    MethodContext _ rcv localVariables ->
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
    Object _ DataNil -> return Nothing
    Object _ (DataClass (cd,isMeta) tbl _) ->
      mAssignSequence [tblAtKeyPutMaybe tbl
                      ,\k v -> prClassSuperclass cd isMeta >>= \sp -> objectAssignClassVariable sp k v] key value
    _ -> prObjectClass object >>= \cl -> objectAssignClassVariable cl key value

{- | Set a name in a Context.
     Assignments at NilContext (the empty context) set variables in the Workspace.
-}
contextAssign :: Context -> Symbol -> Object -> Vm (Maybe Object)
contextAssign (Context c p) k v =
  case c of
    MethodContext _ rcv localVariables ->
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
     the context could be elided.
-}
contextAddBlockContext :: Object -> [Object] -> Vm Context
contextAddBlockContext blockObject arguments = do
  let Object _ (DataBlock _ blockContext lambda) = blockObject
      Expr.Lambda _ blockArguments (St.Temporaries blockTemporaries) _ = lambda
  when (length blockArguments /= length arguments) (vmError "contextAddBlockContext: arity error")
  localVariables <- localVariablesDict (zip blockArguments arguments) blockTemporaries
  return (contextAdd blockContext (BlockContext blockObject localVariables))

-- | Lookup value in current context.
vmContextLookup :: PrimitiveDispatcher -> Symbol -> Vm Object
vmContextLookup pd k = do
  ctx <- vmContext
  res <- contextLookup ctx k
  maybe (vmUnknownGlobal pd ctx k) return res

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

-- | When a method lookup fails, the doesNotUnderstand:arguments: message is sent to the receiver.
vmDoesNotUnderstand :: PrimitiveDispatcher -> Object -> String -> Object -> Vm Object
vmDoesNotUnderstand pd receiver k argsArray = do
  let sel = St.KeywordSelector "doesNotUnderstand:arguments:"
  evalMessageSend pd False receiver sel [symbolObject k, argsArray]

-- | When a global lookup fails, the unknownGlobal: message is sent to the contextReceiver, if there is one.
vmUnknownGlobal :: PrimitiveDispatcher -> Context -> String -> Vm Object
vmUnknownGlobal pd ctx k =
  case contextReceiverMaybe ctx of
    Just receiver -> evalMessageSend pd False receiver (St.KeywordSelector "unknownGlobal:") [symbolObject k]
    _ -> vmError ("vmUnknownGlobal: no contextReceiver: " ++ show k)

{- | If a Return escapes we send an escapedBlock: message to the Object that the Block that Returned escaped from.
     For this purpose the Return object stores the Block that sent it.
     The Block can access the required Object from it's stored context.
     The Block that sent Return will be the current BlockContext.
     The Object that received the message that created a block will be the current MethodContext.
-}
vmEscapedBlock :: PrimitiveDispatcher -> Maybe Object -> Vm Object
vmEscapedBlock pd maybeBlock =
  case maybeBlock of
    Just block ->
      case block of
        Object _ (DataBlock _ context _) ->
          case contextReceiverMaybe context of
            Just receiver -> evalMessageSend pd False receiver (St.KeywordSelector "escapedBlock:") [block]
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

-- | Evaluate StExpr in sequence.  If an StExpr evaluates to a Return Object it is returned and no further StExpr are evaluated.
evalExprSequence :: PrimitiveDispatcher -> [StExpr] -> Vm Object
evalExprSequence pd st =
  case st of
    [] -> error "evalExprSequence: empty sequence"
    [e] -> evalExpr pd e
    e0:eN -> do
      r <- evalExpr pd e0
      if isReturnObject r then return r else evalExprSequence pd eN

-- | An empty sequence returns nil, otherwise either a Return value or the value of the last StExpr is returned.
evalStatements :: PrimitiveDispatcher -> [StExpr] -> Vm Object
evalStatements pd st = if null st then return nilObject else evalExprSequence pd st

{- | evalBlock works by:
   1. extending the stored (block) context with a context frame
   2. saving the current (Vm) context and replacing it with the extended stored context
   3. evaluating the block body and saving the result
   4. restoring the saved context
   5. returning the saved result
-}
evalBlock :: PrimitiveDispatcher -> Object -> [Object] -> Vm Object
evalBlock pd blockObject arguments = do
  let Object _ (DataBlock _ _ (Expr.Lambda _ _ _ blockStatements)) = blockObject
  extendedBlockContext <- contextAddBlockContext blockObject arguments
  currentContext <- vmContextReplace extendedBlockContext
  result <- evalStatements pd blockStatements
  _ <- vmContextReplace currentContext
  case result of
    Object _ (DataReturn pc maybeBlock _) ->
      if contextHasId pc currentContext
      then return result
      else vmEscapedBlock pd maybeBlock
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
evalMethod :: PrimitiveDispatcher -> St.MethodDefinition -> [Symbol] -> St.Temporaries -> [StExpr] -> Object -> [Object] -> Vm Object
evalMethod pd methodDefinition methodArguments methodTemporaries methodStatements receiver arguments = do
  -- printTrace ("evalMethod: " ++ St.methodSignature methodDefinition ++ " <= ") [receiver]
  let requiredArguments = length methodArguments
      providedArguments = length arguments
      arityError = printf "evalMethod: wrong number of arguments: %s %d" (St.methodSignature methodDefinition) providedArguments
  when (requiredArguments /= providedArguments) (vmError arityError)
  pc <- vmProgramCounterIncrement
  vmContextAdd =<< methodContextNode pc receiver (zip methodArguments arguments) methodTemporaries
  result <- evalStatements pd methodStatements
  _ <- vmContextDelete
  case result of
    (Object "Return" (DataReturn ctxId _ x)) -> if ctxId == pc then return x else return result
    _ -> return receiver

type PrimitiveDispatcher = Symbol -> Symbol -> St.Literal -> Object -> [Object] -> Vm Object

-- | Evaluate method, deferring to Primitive if required.
evalMethodOrPrimitive :: PrimitiveDispatcher -> ObjectData -> Object -> [Object] -> Vm Object
evalMethodOrPrimitive pd dat =
  let (DataMethod holder methodDefinition expr) = dat
      (Expr.Lambda _ methodArguments methodTemporaries methodStatements) = expr
  in case St.methodDefinitionPrimitiveLabel methodDefinition of
       Just k -> pd holder (St.methodSignature methodDefinition) k
       Nothing -> evalMethod pd methodDefinition methodArguments methodTemporaries methodStatements

-- | Find method & evaluate, else send doesNotUnderstand message.
findAndEvalMethodOrPrimitive :: PrimitiveDispatcher -> Object -> Object -> St.Selector -> [Object] -> Vm Object
findAndEvalMethodOrPrimitive pd receiver methodReceiver selector arguments = do
  maybeMethod <- findMethodMaybe methodReceiver selector
  -- printTrace ("findAndEvalMethodOrPrimitive: " ++ St.selectorIdentifier selector) arguments
  case maybeMethod of
    Nothing -> do
      argumentsArray <- arrayFromList arguments
      vmDoesNotUnderstand pd receiver (St.selectorIdentifier selector) argumentsArray
    Just (Object "Method" dat) -> evalMethodOrPrimitive pd dat receiver arguments
    _ -> vmError "findAndEvalMethodOrPrimitive"

-- | Look in the methods of the class, then in the superclass.
findMethodMaybe :: Object -> St.Selector -> Vm (Maybe Object)
findMethodMaybe o sel =
  if isNil o
  then return Nothing
  else case classMethodsVec o of
         Just mth ->
          case Vector.find (\(Object _ (DataMethod _ m _)) -> sel == St.methodSelector m) mth of
            Just m -> return (Just m)
            Nothing -> classSuperclassOf o >>= \sc -> findMethodMaybe sc sel
         _ -> vmError "findMethodMaybe"

-- | Evaluate message send.
evalMessageSend :: PrimitiveDispatcher -> Bool -> Object -> St.Selector -> [Object] -> Vm Object
evalMessageSend pd isSuper receiver selector arguments = do
  receiverClass <- prObjectClass receiver
  methodClass <- if isSuper
                 then classSuperclassOf receiverClass
                 else return receiverClass
  findAndEvalMethodOrPrimitive pd receiver methodClass selector arguments

-- | Evaluate expression
evalExpr :: PrimitiveDispatcher -> StExpr -> Vm Object
evalExpr pd expr =
  case expr of
    Expr.Identifier x -> vmContextLookup pd (if x == "super" then "self" else x)
    Expr.Literal x -> literalObject (somIntegerObject, somStringObject) x
    Expr.Assignment lhs rhs -> evalExpr pd rhs >>= vmContextAssign lhs
    Expr.Return x -> do
      result <- evalExpr pd x
      if isReturnObject result
      then return result
      else do pc <- vmContextId
              blk <- vmContextCurrentBlock
              returnObject pc blk result
    Expr.Send e (Expr.Message selector exprList) ->
      do receiver <- evalExpr pd e
         arguments <- mapM (evalExpr pd) exprList
         evalMessageSend pd (Expr.exprIsSuper e) receiver selector arguments
    Expr.Lambda _ld arg _tmp _stm -> do
      ctx <- vmContext
      pc <- vmProgramCounterIncrement
      return (Object ("Block" ++ show (length arg + 1)) (DataBlock pc ctx expr))
    Expr.Array exprList -> mapM (evalExpr pd) exprList >>= arrayFromList
    Expr.Begin exprList -> evalExprSequence pd exprList
    Expr.Init _ (St.Temporaries tmp) exprList -> vmContextAssignAllToNil tmp >> evalExprSequence pd exprList
    Expr.Primitive _ -> error "evalExpr: primitive?"

-- | Parse string as a Smalltalk program, convert to Expr form, run evalExpr and return an Object.
evalString :: PrimitiveDispatcher -> String -> Vm Object
evalString pd txt = evalExpr pd (Expr.smalltalkProgramExpr (St.stParse St.smalltalkProgram txt))

deleteLeadingSpaces :: String -> String
deleteLeadingSpaces = dropWhile Data.Char.isSpace

{- | Run evalString given initial state and input text.
     If the text is empty (or whitespace only) return nil.
-}
vmEval :: PrimitiveDispatcher -> VmState -> String -> IO (Either String Object, VmState)
vmEval pd vmState str =
  case deleteLeadingSpaces str of
    [] -> return (Right nilObject, vmState)
    txt -> State.runStateT (Except.runExceptT (evalString pd txt)) vmState

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

-- | Class>>fields => Array[Symbol]
prClassFields :: St.ClassDefinition -> Bool -> Vm Object
prClassFields cd isMeta =
  case isMeta of
    False -> do
      fld <- classAllVariableNames St.classInstanceVariableNames cd
      arrayFromList (map symbolObject fld)
    True -> do
      fld <- classAllVariableNames St.classVariableNames cd
      arrayFromList (map symbolObject fld)

{- | Create instance of class that is not defined primitively.
     Allocate reference for instance variables and initialize to nil.
     The instance variables of an object are:
         - the instance variables of it's class definition
         - all of the instance variables of all of it's superclasses.
-}
prClassNew :: St.ClassDefinition -> Vm Object
prClassNew cd = do
  instVarNames <- classAllVariableNames St.classInstanceVariableNames cd
  tbl <- variablesTbl instVarNames
  pc <- vmProgramCounterIncrement
  return (Object (St.className cd) (DataUser pc tbl))

{- | Class>>superclass => Class|nil

In Som the superclass of "Object" is "nil".
In Som the superclass of "Object class" is "Class".
This is the only case where a Metaclass has a superclass which is not a Metaclass.
For all other classes "C class superclass = C superclass class".

> Object superclass = nil                         "=> true"
> Object class superclass = Class                 "=> true"
> Nil class superclass = Nil superclass class     "=> true"
-}
prClassSuperclass :: St.ClassDefinition -> Bool -> Vm Object
prClassSuperclass cd isMeta =
  if St.className cd == "Object"
  then if isMeta then vmGlobalLookupOrError "Class" else return nilObject
  else do
    sp <- maybe (return nilObject) vmGlobalResolveOrNil (St.superclassName cd)
    if isMeta then classMetaclass sp else return sp

classSuperclassOf :: Object -> Vm Object
classSuperclassOf (Object _ obj) =
  case obj of
    DataClass (cd,isMeta) _ _ -> prClassSuperclass cd isMeta
    _ -> vmError "classSuperclassOf"

-- * Method Primitives

prMethodInvokeOnWith :: PrimitiveDispatcher -> ObjectData -> Object -> Object -> Vm Object
prMethodInvokeOnWith pd obj receiver argumentsArray = do
  arguments <- arrayElements argumentsArray
  evalMethodOrPrimitive pd obj receiver arguments

-- * Object Primitives

{- | Class of class (Metaclass).
     If the Class object isMeta then return Metaclass, else set isMeta.
     Metaclass is a standard Som class, it is looked up in the global dictionary.
-}
classMetaclass :: Object -> Vm Object
classMetaclass (Object _ obj) =
  case obj of
    DataClass (cd,isMeta) cVar mCache ->
      if isMeta
      then vmGlobalResolveOrError "Metaclass"
      else return (Object "Class" (DataClass (cd,True) cVar mCache))
    _ -> Except.throwError "classMetaclass"

prObjectClass :: Object -> Vm Object
prObjectClass rcv@(Object nm obj) =
  case obj of
    DataClass {} -> classMetaclass rcv
    _ -> vmGlobalLookupOrError nm

prObjectInspect :: Object -> Vm Object
prObjectInspect rcv = objectToInspector rcv >>= liftIO . putStrLn >> return rcv

prObjectPerformInSuperclass :: PrimitiveDispatcher -> Object -> UnicodeString -> Object -> Vm Object
prObjectPerformInSuperclass pd rcv sel cl = findAndEvalMethodOrPrimitive pd rcv cl (St.stParse St.quotedSelector ('#' : fromUnicodeString sel)) []

prObjectPerform :: PrimitiveDispatcher -> Object -> UnicodeString -> Vm Object
prObjectPerform pd rcv sel = prObjectClass rcv >>= \cl -> prObjectPerformInSuperclass pd rcv sel cl

prObjectPerformWithArgumentsInSuperclass :: PrimitiveDispatcher -> Object -> UnicodeString -> Object -> Object -> Vm Object
prObjectPerformWithArgumentsInSuperclass pd rcv sel argumentsArray cl = do
  arguments <- arrayElements argumentsArray
  findAndEvalMethodOrPrimitive pd rcv cl (St.stParse St.quotedSelector ('#' : fromUnicodeString sel)) arguments

prObjectPerformWithArguments :: PrimitiveDispatcher -> Object -> UnicodeString -> Object -> Vm Object
prObjectPerformWithArguments pd rcv sel argArray = prObjectClass rcv >>= \cl -> prObjectPerformWithArgumentsInSuperclass pd rcv sel argArray cl

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
        -- liftIO (putStrLn (show ("systemLoadAndAssignClassesAbove", x)))
        maybeCd <- liftIO (Som.somLoadClassFile x)
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

-- | Load the core Som classes and generate an object Table.
loadClassTable :: MonadIO m => FilePath -> m ObjectAssociationList
loadClassTable somDirectory = do
  classLibrary <- liftIO (Som.somLoadClassList somDirectory Som.somStandardClassList)
  let classNames = map fst classLibrary
  classObjects <- mapM (classObject . snd) classLibrary
  return (zip classNames classObjects)

{- | Table of reserved identifiers: nil, true, false and system.
     These words are defined in System>>global.
-}
reservedIdentifiersTable :: ObjectAssociationList
reservedIdentifiersTable =
  let f x = (x, reservedObject x)
  in map f (words "nil true false system")

-- | The initial global dictionary holds the class table and the reserved identifiers table.
initialGlobalDictionary :: MonadIO m => FilePath -> m ObjectDictionary
initialGlobalDictionary somDirectory = do
  classTable <- loadClassTable somDirectory
  let compositeTable = concat [classTable, reservedIdentifiersTable]
  dictRefFromList compositeTable

-- * Trace

printTrace :: MonadIO m => String -> [Object] -> m ()
printTrace msg o = liftIO (putStr msg) >> objectListPrint o >> return ()
