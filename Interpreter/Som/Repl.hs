-- | Read evaluate print loop
module Interpreter.Som.Repl where

import System.Environment {- base -}
import System.IO {- base -}
import Text.Printf {- base -}

import qualified Language.Smalltalk.Som as Som {- stsc3 -}

import Interpreter.Som.Core {- stsc3 -}
import Interpreter.Som.DictRef {- stsc3 -}
import Interpreter.Som.Primitives.Som {- stsc3 -}
import Interpreter.Som.Types {- stsc3 -}

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
replContinue :: VmState -> IO ()
replContinue vmState = do
  str <- replReadInput "" stdin
  (result,vmState') <- vmEval somCoreOpt vmState str
  case result of
    Left msg -> putStrLn ("error: " ++ msg) >> replContinue vmState
    Right res -> putStr "result: " >> objectPrint res >> replContinue vmState'


-- | Load the core Som classes and generate an object Table.
somLoadClassTable :: FilePath -> IO ObjectAssociationList
somLoadClassTable somDirectory = do
  classLibrary <- Som.somLoadClassList somDirectory Som.somStandardClassList
  makeClassTable classLibrary

-- | The initial global dictionary holds the class table and the reserved identifiers table.
somInitialGlobalDictionary :: FilePath -> IO ObjectDictionary
somInitialGlobalDictionary somDirectory = do
  somClassTable <- somLoadClassTable somDirectory
  dictRefFromList (concat [somClassTable, reservedObjectTableFor SomSystem])

{- | Main function for read-eval-print loop.
     Requires the SOM class directory.
-}
replMain :: FilePath -> IO ()
replMain dir = somInitialGlobalDictionary dir >>= vmStateInit >>= replContinue

{- | Generate Smalltalk expression to load and run class.

> runSomClassSmalltalk "TestHarness" ["BlockTest"]
-}
runSomClassSmalltalk :: String -> [String] -> String
runSomClassSmalltalk cl arg =
  let quote x = printf "'%s'" x
  in printf "%s new run: #(%s)" cl (unwords (map quote (cl : arg)))

{- | Load and run Smalltalk class.
     Requires the SOM class directory.

> loadAndRunClass "TestHarness" []
> loadAndRunClass "TestHarness" ["String"]
> loadAndRunClass "Harness" ["Bounce"]
-}
loadAndRunClass :: FilePath -> String -> [String] -> IO ()
loadAndRunClass dir cl arg = do
  st <- somInitialGlobalDictionary dir >>= vmStateInit
  (result,_) <- vmEval somCoreOpt st (runSomClassSmalltalk cl arg)
  case result of
    Left msg -> putStrLn ("error: " ++ msg)
    Right res -> putStr "result: " >> objectPrint res >> return ()

{- | If there are no arguments start a read-evaluate-print loop.
     If there is on or more arguments,
     load the class defined at the first and call the run: method with the remainder.
-}
somReplMain :: IO ()
somReplMain = do
  dir <- Som.somSystemClassPath
  arg <- getArgs
  case arg of
    [] -> replMain dir
    cl:somArg -> loadAndRunClass dir cl somArg
