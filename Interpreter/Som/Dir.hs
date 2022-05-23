module Interpreter.Som.Dir where

import qualified Music.Theory.Directory as Directory {- hmt-base -}

import qualified Language.Smalltalk.Ansi as St {- stsc3 -}
import qualified Language.Smalltalk.Som as St {- stsc3 -}

-- | The name of the environment variable to read the Som class path from.
somClassPathEnvVar :: String
somClassPathEnvVar = "SOM_CLASS_PATH"

-- | Read the environment variable giving the sequence of directories to search for Som class files.
somClassPath :: IO [FilePath]
somClassPath = Directory.path_from_env somClassPathEnvVar

{- | The system class path must be the first entry of somClassPath.
     It is an error for it not to be set.
-}
somSystemClassPath :: IO FilePath
somSystemClassPath = do
  cp <- somClassPath
  case cp of
    sys:_ -> return sys
    _ -> error "somSystemClassPath"

{- | Find Som class definition file (recursively) on somClassPath.

> somFindClassFile "Array" -- Just ".../SOM/Smalltalk/Array.som"
-}
somFindClassFile :: St.Identifier -> IO (Maybe FilePath)
somFindClassFile cls = somClassPath >>= \path -> Directory.path_scan_recursively path (cls ++ ".som")

-- | Load the class file for a named class.
somLoadClassFile :: St.Identifier -> IO (Maybe St.ClassDefinition)
somLoadClassFile x = somFindClassFile x >>= mapM St.somLoadClassDefinition
