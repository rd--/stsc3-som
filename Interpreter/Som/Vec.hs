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

-- | Vector
type Vec t = Vector.Vector t

vecAt :: Vec t -> Int -> t
vecAt vec ix = vec Vector.! ix

vecAtMaybe :: Vec t -> Int -> Maybe t
vecAtMaybe vec ix =
  if ix > 0 && ix <= vecLength vec
  then Just (vecAt vec (ix - 1))
  else Nothing

vecLength :: Vec t -> Int
vecLength = Vector.length

vecToList :: Vec t -> [t]
vecToList = Vector.toList

vecFromList :: [t] -> Vec t
vecFromList = Vector.fromList

vecFind :: (t -> Bool) -> Vec t -> Maybe t
vecFind =  Vector.find

vecBoundsCheck :: StError m => String -> Vec t -> Int -> m ()
vecBoundsCheck msg vec ix =
  when
    (ix < 0 || ix >= vecLength vec)
    (stError (msg ++ ": index out of range"))

vecShallowCopy :: Vec t -> Vec t
vecShallowCopy v = Vector.generate (vecLength v) (\i -> vecAt v i)

-- | Reference to Vector
type VecRef t = Ref (Vec t)

vecRefFromList :: MonadIO m => [t] -> m (VecRef t)
vecRefFromList = toRef . vecFromList

-- | Vector.modify may update the vector in place or it may copy the vector, hence need for VecRef.
vecRefWrite :: (MonadIO m, StError m) => VecRef t -> Int -> t -> m t
vecRefWrite vecRef ix value = do
  vec <- deRef vecRef
  vecBoundsCheck "vecRefWrite" vec ix
  liftIO
    (writeIORef
      vecRef
      (Vector.modify (\mutVec -> Vector.Mutable.write mutVec ix value) vec))
  return value

vecRefAt :: MonadIO m => VecRef t -> Int -> m (Maybe t)
vecRefAt ref ix = do
  vec <- deRef ref
  return (vecAtMaybe vec ix)

vecRefShallowCopy :: MonadIO m => VecRef t -> m (VecRef t)
vecRefShallowCopy ref = do
  vec <- deRef ref
  toRef (vecShallowCopy vec)
