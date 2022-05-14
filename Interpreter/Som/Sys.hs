module Interpreter.Som.Sys where

import System.Directory {- directory -}

readFileMaybe :: FilePath -> IO (Maybe String)
readFileMaybe fn = do
  exists <- doesFileExist fn
  if exists then fmap Just (readFile fn) else return Nothing
