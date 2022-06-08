{-# Language ConstraintKinds, FlexibleContexts #-}

module Interpreter.Som.Error where

import Control.Exception {- base -}

import qualified Control.Monad.Except as Except {- mtl -}

-- * Base

data SomError = SomError String deriving (Show)

instance Exception SomError

somError :: String -> t
somError errorText = throw (SomError errorText)

somErrorIO :: String -> IO t
somErrorIO errorText = throwIO (SomError errorText)

-- * Mtl

type StError m = Except.MonadError String m

