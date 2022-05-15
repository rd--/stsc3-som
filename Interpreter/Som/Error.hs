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

stError :: StError m => String -> m t
stError = Except.throwError

prError :: StError m => String -> m t
prError txt = stError ("Primitive error: " ++ txt)

vmError :: StError m => String -> m t
vmError txt = stError ("Virtual machine error: " ++ txt)
