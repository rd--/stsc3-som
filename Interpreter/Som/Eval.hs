{-# Language FlexibleContexts #-}

{- | Evalulator -}
module Interpreter.Som.Eval where

import Control.Concurrent {- base -}
import Control.Monad {- base -}
import Control.Monad.IO.Class {- base -}
import qualified Data.Char {- base -}
import Data.Maybe {- base -}
import Text.Printf {- base -}

import qualified Control.Monad.State as State {- mtl -}
import qualified Control.Monad.Except as Except {- mtl -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Ansi.Expr as Expr {- stsc3 -}

import Interpreter.Som.Str
import Interpreter.Som.Sym
import Interpreter.Som.Types

-- * Types

-- | (Holder, selector), code, receiver, arguments, answer.
type PrimitiveDispatcher = (Symbol, Symbol) -> Integer -> Object -> [Object] -> Vm (Maybe Object)

data EvalOpt = EvalOpt { evalOptTyp :: SystemType, evalOptLit :: LiteralConstructors, evalOptPrim :: PrimitiveDispatcher }

contextLookupOrUnknown :: EvalOpt -> Symbol -> Context -> Vm Object
contextLookupOrUnknown opt k ctx = do
  res <- contextLookup ctx k
  maybe (vmUnknownGlobal opt ctx k) return res

vmContextLookup :: EvalOpt -> Symbol -> Vm Object
vmContextLookup opt k = vmGetContext >>= contextLookupOrUnknown opt k

coreSymbolObject :: EvalOpt -> String -> Object
coreSymbolObject opt str = let (_, _, symObject) = evalOptLit opt in symObject str

-- | When a method lookup fails, the doesNotUnderstand:arguments: message is sent to the receiver.
vmDoesNotUnderstand :: EvalOpt -> Object -> String -> Object -> Vm Object
vmDoesNotUnderstand opt receiver k argsArray = do
  let sel = St.KeywordSelector "doesNotUnderstand:arguments:"
  --printTrace ("vmDoesNotUnderstand: " ++ k ++ " <= ") [receiver, argsArray]
  evalMessageSend opt False receiver sel [coreSymbolObject opt k, argsArray]

-- | When a global lookup fails, the unknownGlobal: message is sent to the contextReceiver, if there is one.
vmUnknownGlobal :: EvalOpt -> Context -> String -> Vm Object
vmUnknownGlobal opt ctx k =
  case contextReceiver ctx of
    Just receiver -> evalMessageSend opt False receiver (St.KeywordSelector "unknownGlobal:") [coreSymbolObject opt k]
    _ -> vmError ("vmUnknownGlobal: no contextReceiver: " ++ show k)

{- | If a block returns after it's homeContext is deleted send an escapedBlock: message to the Object that the Block escaped from.
     For this purpose NonLocalReturn stores the Block that sent it.
     The Block can access the required Object from it's stored context.
     The Block that sent the non-local return will be the current BlockFrame.
     The Object that received the message that created a block will be the nearest MethodFrame.
-}
vmEscapedBlock :: EvalOpt -> Maybe Object -> Vm Object
vmEscapedBlock opt maybeBlock =
  case maybeBlock of
    Just block ->
      case block of
        Object _ (DataBlockClosure _ blockContext _) ->
          case contextReceiver blockContext of
            Just receiver -> evalMessageSend opt False receiver (St.KeywordSelector "escapedBlock:") [block]
            Nothing -> vmError "escaped context: no receiver"
        _ -> vmError "escaped context: bad block"
    Nothing -> vmError "escaped context?"

-- * Eval

evalExprSequence :: EvalOpt -> [StExpr] -> Vm Object
evalExprSequence opt st =
  case st of
    [] -> return nilObject
    [e] -> evalExpr opt e
    e0:eN -> evalExpr opt e0 >> evalExprSequence opt eN

{- | Result indicates whether it's a "return" or the value of the last expression.
This function doesn't run nonLocalReturn because it is used for both methods and blocks, and return at methods is local.
-}
evalStatements :: EvalOpt -> ([StExpr], Maybe StExpr) -> Vm (Bool, Object)
evalStatements opt (stm, ret) = do
  res <- evalExprSequence opt stm
  case ret of
    Nothing -> return (False, res)
    Just ret' -> evalExpr opt ret' >>= \ret'' -> return (True, ret'')

blockHandler :: EvalOpt -> Bool -> ExceptionHandler -> ExceptionOrNonLocalReturn -> Vm (Bool, Object)
blockHandler opt hasReturn (_exc, hnd) exception = do
  case exception of
    SystemError _msg -> Except.throwError exception
    Exception obj _ -> fmap (\r -> (hasReturn, r)) (evalBlockOfCorrectArity opt hnd [obj] Nothing) -- should match on exception...
    NonLocalReturn _pc _blk _obj -> Except.throwError exception

evalBlockOfCorrectArity :: EvalOpt -> Object -> [Object] -> Maybe (Object, Object) -> Vm Object
evalBlockOfCorrectArity opt blockObject arguments maybeExceptionHandler = do
  currentContext <- vmReplaceContext =<< blockContextFrame blockObject arguments maybeExceptionHandler
  let Object _ (DataBlockClosure _ blockContext (Expr.Lambda _ _ _ blockStatements)) = blockObject
      hasReturn = isJust (snd blockStatements)
      Just homeContext = contextNearestMethod blockContext
      onReturn result = let pc = contextIdOrError homeContext in nonLocalReturn pc blockObject result
      onNoReturn result = return result
  (isReturn, result) <- case maybeExceptionHandler of
            Nothing -> evalStatements opt blockStatements
            Just eh -> evalStatements opt blockStatements `Except.catchError` blockHandler opt hasReturn eh
  --printTrace (printf "evalBlockOfCorrectArity: ret=%s" (show isReturn)) (result : blockObject : arguments)
  _ <- vmReplaceContext currentContext
  if isReturn then onReturn result else onNoReturn result

evalBlockWithMaybeExceptionHandler :: EvalOpt -> Object -> [Object] -> Maybe (Object, Object) -> Vm (Maybe Object)
evalBlockWithMaybeExceptionHandler opt blockObject arguments maybeExceptionHandler =
  if blockObjectArity blockObject /= length arguments
  then return Nothing
  else fmap Just (evalBlockOfCorrectArity opt blockObject arguments maybeExceptionHandler)

{- | evalBlock works by:
   1. extending the stored (block) context with a context frame
   2. saving the current (Vm) context and replacing it with the extended stored context
   3. installing an exception handler if one is provided
   4. evaluating the block body, handling any exceptions, and saving the result
   5. if the block has a non-local return a NonLocalReturn exception is raised
   6. else the saved context is restored and the saved result returned locally

The arity error is reported by returning Nothing rather that raising an error because this is a <primitive> at St-80.
Exception handlers are at Block contexts, see on:do: and ifError:.
If an exception is received, and the block context has a handler for that exception, the handler is evaluated.
The exception stores the context it was signaled (raised) in as well as a message.
-}
evalBlock :: EvalOpt -> Object -> [Object] -> Vm (Maybe Object)
evalBlock opt blockObject arguments = evalBlockWithMaybeExceptionHandler opt blockObject arguments Nothing

sendHandler :: Id -> ExceptionOrNonLocalReturn -> Vm (Bool, Object)
sendHandler ctxId exception = do
  ctx <- vmGetContext
  let frm = contextFrameOrError ctx
  _frm_str <- contextFrameInspect frm
  case exception of
    NonLocalReturn pc _blk obj -> if ctxId == pc then return (True, obj) else  Except.throwError exception
    SystemError _msg -> Except.throwError exception
    Exception {} -> Except.throwError exception

{- | evalMethod is similar to evalBlock, except that methods:
   1. have a receiver which is stored and can be referenced as self or super
   2. store a context identifier and install an exception handler in order to receive non-local returns
   2. don't have a stored (saved) context (they begin in the current environment, they are not closures)
   4. return self (the receiver) if there is no return or exception value

Return statements are allowed as the last statement of either a method or a block.
Returns in blocks are non-local, they return to the blocks home context.
The home context is the method the block was defined in.
When a non-local return arrives at it's home context the answer is unpacked and returned.
When an exception value arrives at a handler (exception handlers are at Block contexts) it is handled.

-}
evalMethod :: EvalOpt -> St.MethodDefinition -> [Symbol] -> St.Temporaries -> ([StExpr], Maybe StExpr) -> Object -> [Object] -> Vm Object
evalMethod opt methodDefinition methodArguments methodTemporaries methodStatements receiver arguments = do
  let requiredArguments = length methodArguments
      providedArguments = length arguments
      className = St.methodClass methodDefinition
      selector = St.methodSignature methodDefinition
      arityError = printf "evalMethod: wrong number of arguments: %s %d" selector providedArguments
  when (requiredArguments /= providedArguments) (vmError arityError)
  pc <- vmIncrementProgramCounter
  currentContext <- vmAddContextFrame =<< methodContextFrame pc (className, selector) receiver (zip methodArguments arguments) methodTemporaries
  --printTrace (printf "evalMethod: <pc=%d> %s -- " pc (St.methodSignature methodDefinition)) (receiver : arguments)
  (isReturn, result) <- evalStatements opt methodStatements `Except.catchError` sendHandler pc
  _ <- vmReplaceContext currentContext
  if isReturn then return result else return receiver

-- | Evaluate method, deferring to Primitive if required.
evalMethodOrPrimitive :: EvalOpt -> ObjectData -> Object -> [Object] -> Vm Object
evalMethodOrPrimitive opt dat rcv arg =
  let (DataMethod holder methodDefinition expr) = dat
      (Expr.Lambda _ methodArguments methodTemporaries methodStatements) = expr
      notPrimitive = evalMethod opt methodDefinition methodArguments methodTemporaries methodStatements rcv arg
  in case St.methodDefinitionPrimitiveCode methodDefinition of
       Just k -> do
         --printTrace (printf "evalMethodOrPrimitive: <primitive: %d>: " k) (rcv : arg)
         answer <- (evalOptPrim opt) (holder, St.methodSignature methodDefinition) k rcv arg
         case answer of
           Just result -> return result
           Nothing -> notPrimitive
       Nothing -> notPrimitive

-- | Find method & evaluate, else send doesNotUnderstand message.
findAndEvalMethodOrPrimitive :: EvalOpt -> Object -> Object -> St.Selector -> [Object] -> Vm Object
findAndEvalMethodOrPrimitive opt receiver methodReceiver selector arguments = do
  maybeMethod <- findMethodMaybe methodReceiver selector
  --printTrace ("findAndEvalMethodOrPrimitive: " ++ St.selectorIdentifier selector) (receiver : arguments)
  case maybeMethod of
    Nothing -> do
      argumentsArray <- arrayFromList arguments
      vmDoesNotUnderstand opt receiver (St.selectorIdentifier selector) argumentsArray
    Just (Object "Method" dat) -> evalMethodOrPrimitive opt dat receiver arguments
    _ -> vmError "findAndEvalMethodOrPrimitive"

lookupClassForSuper :: EvalOpt -> Vm Object
lookupClassForSuper opt = do
  ctx <- vmGetContext
  case contextNearestMethodFrame ctx of
    Just (MethodFrame _ ((className, isMeta), _) _ _) -> do
             obj <- contextLookupOrUnknown opt (if isMeta then St.metaclassNameClassName className else className) ctx
             classSuperclassOf =<< if isMeta then classMetaclass obj else return obj
    _ -> vmError "lookupClassForSuper: no method context?"

{- | Evaluate message send.

Lookup for super message sends begins in the superclass of the class where the method was defined.
-}
evalMessageSend :: EvalOpt -> Bool -> Object -> St.Selector -> [Object] -> Vm Object
evalMessageSend opt isSuper receiver selector arguments = do
  receiverClass <- objectClass receiver
  lookupClass <- if isSuper then lookupClassForSuper opt else return receiverClass
  findAndEvalMethodOrPrimitive opt receiver lookupClass selector arguments

{- | Evaluate expression.

The evaluator handles non-local returns as exceptions.
When a non-local return is caught if it is not for the current method it is re-thrown.
-}
evalExpr :: EvalOpt -> StExpr -> Vm Object
evalExpr opt expr =
  case expr of
    Expr.Identifier x -> if x == "thisContext" then vmThisContextObject else vmContextLookup opt (if x == "super" then "self" else x)
    Expr.Literal x -> sysLiteralObject (evalOptTyp opt) (literalObject (evalOptLit opt) x)
    Expr.Assignment lhs rhs -> evalExpr opt rhs >>= vmDoAssignment lhs
    Expr.Send receiverExpr (Expr.Message selector argumentsExpr) -> do
      --ctx <- vmGetContext
      receiver <- evalExpr opt receiverExpr
      arguments <- mapM (evalExpr opt) argumentsExpr
      evalMessageSend opt (Expr.exprIsSuper receiverExpr) receiver selector arguments
    Expr.Lambda _ld arg _tmp _stm -> do
      blockContext <- vmGetContext
      pc <- vmIncrementProgramCounter
      return (Object (closureClass (evalOptTyp opt) (length arg)) (DataBlockClosure pc blockContext expr))
    Expr.Array exprList -> mapM (evalExpr opt) exprList >>= arrayFromList
    Expr.Init _ (St.Temporaries tmp) exprList -> vmAssignAllToNil tmp >> evalExprSequence opt exprList

evalString :: EvalOpt -> String -> Vm (Maybe Object)
evalString opt txt = do
  case St.stParseMaybe St.programInitializerDefinition txt of
    Nothing -> return Nothing
    Just st -> fmap Just (evalExpr opt (Expr.initializerDefinitionExpr st))

-- | Parse string as a Smalltalk program, convert to Expr form, run evalExpr and return an Object.
evalStringOrError :: EvalOpt -> String -> Vm Object
evalStringOrError opt txt = do
  maybeAnswer <- evalString opt txt
  case maybeAnswer of
    Nothing -> vmError "evalString"
    Just answer -> return answer

{-
case answer of
        Object _ (DataException exc (Object _ (DataContext ctx))) -> objectInspectAndPrint exc >> vmPrintContext ctx >> return answer
-}

vmRun :: VmState -> Vm Object -> IO (Either ExceptionOrNonLocalReturn Object, VmState)
vmRun vmState f = State.runStateT (Except.runExceptT f) vmState

deleteLeadingSpaces :: String -> String
deleteLeadingSpaces = dropWhile Data.Char.isSpace

{- | Run evalStringOrError given initial state and input text.
     If the text is empty (or whitespace only) return nil.
-}
vmEval :: EvalOpt -> VmState -> String -> IO (Either ExceptionOrNonLocalReturn Object, VmState)
vmEval opt vmState str =
  case deleteLeadingSpaces str of
    [] -> return (Right nilObject, vmState)
    txt -> vmRun vmState (evalStringOrError opt txt)

threadObject :: EvalOpt -> Object -> Vm Object
threadObject opt block = do
  st <- State.get
  threadId <- liftIO (forkIO (vmRun st (evalBlock opt block [] >> return nilObject) >> return ()))
  return (Object "Thread" (DataThread threadId))

-- * Object Primitives

objectPerformWithArgumentsInSuperclass :: EvalOpt -> Object -> UnicodeString -> Object -> Object -> Vm Object
objectPerformWithArgumentsInSuperclass opt rcv sel argumentsArray cl = do
  arguments <- arrayElements argumentsArray
  findAndEvalMethodOrPrimitive opt rcv cl (St.stParse St.quotedSelector ('#' : fromUnicodeString sel)) arguments

objectPerformWithArguments :: EvalOpt -> Object -> UnicodeString -> Object -> Vm Object
objectPerformWithArguments opt rcv sel argArray = objectClass rcv >>= \cl -> objectPerformWithArgumentsInSuperclass opt rcv sel argArray cl

objectPerformInSuperclass :: EvalOpt -> Object -> UnicodeString -> Object -> Vm Object
objectPerformInSuperclass opt rcv sel cl = findAndEvalMethodOrPrimitive opt rcv cl (St.stParse St.quotedSelector ('#' : fromUnicodeString sel)) []

objectPerform :: EvalOpt -> Object -> UnicodeString -> Vm Object
objectPerform opt rcv sel = objectClass rcv >>= \cl -> objectPerformInSuperclass opt rcv sel cl

-- * Trace

printTrace :: MonadIO m => String -> [Object] -> m ()
printTrace msg o = liftIO (putStr (msg ++ " with: ")) >> objectListPrint o >> return ()
