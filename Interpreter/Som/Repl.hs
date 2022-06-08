-- | Read evaluate print loop
module Interpreter.Som.Repl where

import System.Environment {- base -}
import System.IO {- base -}
import Text.Printf {- base -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Som as Som {- stsc3 -}

import Interpreter.Som.DictRef {- stsc3-som -}
import Interpreter.Som.Dir {- stsc3-som -}
import Interpreter.Som.Eval {- stsc3-som -}
import Interpreter.Som.Types {- stsc3-som -}

-- | Read lines from Handle while there is input waiting.
replReadInput :: String -> Handle -> IO String
replReadInput s h = do
  l <- hGetLine h -- no eol
  r <- hReady h
  let s' = s ++ (l ++ "\n")
  if r then replReadInput s' h else return s'

{- | The read-eval-print loop continue function.
     Read program text, evaluate it, report errors or result, continue with the modified state.
-}
replContinue :: EvalOpt -> VmState -> IO ()
replContinue opt vmState = do
  str <- replReadInput "" stdin
  (result,vmState') <- vmEval opt vmState str
  let (_,programCounter,_,_,_) = vmState'
  case result of
    Left (SystemError msg) -> putStrLn ("replContinue: system error: " ++ msg) >> replContinue opt vmState
    Left (Exception exc ctx) -> putStrLn ("replContinue: exception") >> objectInspectAndPrint exc >> vmPrintContext ctx >> replContinue opt vmState
    Left (NonLocalReturn pc blk obj) -> putStrLn (printf "replContinue: non-local return <pc:%d>" pc) >> objectInspectAndPrint blk >> objectInspectAndPrint obj >> replContinue opt vmState
    Right res -> putStr (printf "result<pc=%d>: " programCounter) >> objectPrint res >> replContinue opt vmState'

stStandardClassList :: [St.Identifier]
stStandardClassList =
    ["Object"
    ,"Behavior", "ClassDescription", "Class", "Metaclass"
    ,"BlockClosure"
    ,"InstructionStream", "Context", "Thread"
    ,"Boolean", "True", "False"
    ,"Collection", "HashedCollection", "Set", "SequenceableCollection", "ArrayedCollection", "Array", "String", "Symbol", "Dictionary"
    ,"Exception", "Error", "Halt"
    ,"Magnitude", "Character", "LookupKey", "Association", "Number", "Float", "Double", "Integer", "SmallInteger"
    ,"Method"
    ,"SmalltalkImage"
    ,"UndefinedObject", "Nil"
    ]

standardClassListFor :: SystemType -> [St.Identifier]
standardClassListFor sys =
  case sys of
    SomSystem -> Som.somStandardClassList
    SmalltalkSystem -> stStandardClassList

-- | Load the core Som classes and generate an object Table.
somLoadClassTable :: SystemType -> FilePath -> IO ObjectAssociationList
somLoadClassTable sys somDirectory = do
  classLibrary <- Som.somLoadClassList somDirectory (standardClassListFor sys)
  makeClassTable classLibrary

-- | The initial global dictionary holds the class table and the reserved identifiers table.
somInitialGlobalDictionary :: SystemType -> FilePath -> IO ObjectDictionary
somInitialGlobalDictionary sys somDirectory = do
  somClassTable <- somLoadClassTable sys somDirectory
  dictRefFromList (concat [somClassTable, reservedObjectTableFor sys])

{- | Main function for read-eval-print loop.
     Requires the SOM class directory.
-}
replMain :: EvalOpt -> FilePath -> IO ()
replMain opt dir = somInitialGlobalDictionary (evalOptTyp opt) dir >>= vmStateInit >>= replContinue opt

{- | Generate Smalltalk expression to load and run class.

> runSomClassSmalltalk "TestHarness" ["BlockTest"]
-}
runSomClassSmalltalk :: St.Identifier -> [String] -> String
runSomClassSmalltalk cl arg =
  let quote x = printf "'%s'" x
  in printf "%s new run: #(%s)" cl (unwords (map quote (cl : arg)))

{- | Load and run Smalltalk class.
     Requires the SOM class directory.

> loadAndRunClass "TestHarness" []
> loadAndRunClass "TestHarness" ["String"]
> loadAndRunClass "Harness" ["Bounce"]
-}
loadAndRunClass :: EvalOpt -> FilePath -> St.Identifier -> [String] -> IO ()
loadAndRunClass opt dir cl arg = do
  st <- somInitialGlobalDictionary (evalOptTyp opt) dir >>= vmStateInit
  (result,_) <- vmEval opt st (runSomClassSmalltalk cl arg)
  case result of
    Left (SystemError msg) -> putStrLn ("loadAndRunClass: system error: " ++ msg)
    Left (Exception {}) -> putStrLn ("loadAndRunClass: exception")
    Left (NonLocalReturn {}) -> putStrLn ("loadAndRunClass: non-local-return")
    Right res -> putStr "result: " >> objectPrint res >> return ()

{- | If there are no arguments start a read-evaluate-print loop.
     If there is on or more arguments,
     load the class defined at the first and call the run: method with the remainder.
-}
somReplMain :: EvalOpt -> IO ()
somReplMain opt = do
  dir <- somSystemClassPath
  arg <- getArgs
  case arg of
    [] -> replMain opt dir
    cl:somArg -> loadAndRunClass opt dir cl somArg
