module Interpreter.Som.Error where

import Control.Exception

data SomError = SomError String deriving (Show)

instance Exception SomError

somError :: String -> t
somError errorText = throw (SomError errorText)

somErrorIO :: String -> IO t
somErrorIO errorText = throwIO (SomError errorText)
