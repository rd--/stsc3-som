{-# Language FlexibleContexts #-}

{- | Vec is a 0-indexed mutable array type.
VecRef is a mutable reference to a Vec.
Vector.modify may update the vector in place or it may copy the vector, hence need for VecRef.
-}
module Interpreter.Som.Vec where

import Control.Monad.IO.Class {- base -}
import Data.IORef {- base -}

import qualified Data.Vector as Vector {- vector -}
import qualified Data.Vector.Mutable as Vector.Mutable {- vector -}

import Interpreter.Som.Ref {- stsc3 -}

type Vec t = Vector.Vector t

vecBoundsCheck :: Vec t -> Int -> Bool
vecBoundsCheck vec ix = (ix >= 0) && (ix < vecLength vec) -- 0-indexed

vecAt :: Vec t -> Int -> t
vecAt vec ix = vec Vector.! ix -- 0-indexed

vecAtMaybe :: Vec t -> Int -> Maybe t
vecAtMaybe vec ix =
  if vecBoundsCheck vec ix
  then Just (vecAt vec ix) -- 0-indexed
  else Nothing

vecLength :: Vec t -> Int
vecLength = Vector.length

vecToList :: Vec t -> [t]
vecToList = Vector.toList

vecFromList :: [t] -> Vec t
vecFromList = Vector.fromList

vecFind :: (t -> Bool) -> Vec t -> Maybe t
vecFind = Vector.find

vecShallowCopy :: Vec t -> Vec t
vecShallowCopy v = Vector.generate (vecLength v) (\i -> vecAt v i)

type VecRef t = Ref (Vec t)

vecRefFromList :: MonadIO m => [t] -> m (VecRef t)
vecRefFromList = toRef . vecFromList

vecRefToList :: MonadIO m => VecRef t -> m [t]
vecRefToList = fmap vecToList . deRef

vecRefAtMaybe :: MonadIO m => VecRef t -> Int -> m (Maybe t)
vecRefAtMaybe ref ix = do
  vec <- deRef ref
  return (vecAtMaybe vec ix) -- 0-indexed

vecRefAtPutMaybe :: MonadIO m => VecRef t -> Int -> t -> m (Maybe t)
vecRefAtPutMaybe vecRef ix value = do
  vec <- deRef vecRef
  case vecBoundsCheck vec ix of
    False -> return Nothing
    True -> liftIO (writeIORef vecRef (Vector.modify (\mutVec -> Vector.Mutable.write mutVec ix value) vec)) >> return (Just value)

vecRefShallowCopy :: MonadIO m => VecRef t -> m (VecRef t)
vecRefShallowCopy ref = do
  vec <- deRef ref
  toRef (vecShallowCopy vec)
