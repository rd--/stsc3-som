{-# Language FlexibleContexts #-}

{- | Vec is a zero indexed mutable array type.
     VecRef is a mutable reference to a Vec.
-}
module Interpreter.Som.Vec where

import Control.Monad {- base -}
import Control.Monad.IO.Class {- base -}
import Data.IORef {- base -}

import qualified Data.Vector as Vector {- vector -}
import qualified Data.Vector.Mutable as Vector.Mutable {- vector -}

import Interpreter.Som.Error {- stsc3 -}
import Interpreter.Som.Ref {- stsc3 -}

type Vec t = Vector.Vector t

type VecRef t = Ref (Vec t)

vecAt :: Vec t -> Int -> t
vecAt vec ix = vec Vector.! ix

vecLength :: Vec t -> Int
vecLength = Vector.length

vecBoundsCheck :: StError m => String -> Vec t -> Int -> m ()
vecBoundsCheck msg vec ix =
  when
    (ix < 0 || ix >= vecLength vec)
    (stError (msg ++ ": index out of range"))

vecRefWrite :: (MonadIO m, StError m) => Ref (Vec t) -> Int -> t -> m t
vecRefWrite vecRef ix value = do
  vec <- deRef vecRef
  vecBoundsCheck "vecRefWrite" vec ix
  liftIO
    (writeIORef
      vecRef
      (Vector.modify (\mutVec -> Vector.Mutable.write mutVec ix value) vec))
  return value
