{-# Language FlexibleContexts #-}

-- | Dict
module Interpreter.Som.Dict where

import Control.Monad.IO.Class {- base -}
import Data.IORef {- base -}
import Data.Maybe {- base -}

import qualified Control.Monad.Except as Except {- mtl -}
import qualified Data.Map as Map {- containers -}

import Interpreter.Som.Ref

-- | Map with reference values.
type Dict k v = Map.Map k (IORef v)

dictMerge :: Ord k => Dict k v -> Dict k v -> Dict k v
dictMerge = Map.union

dictMergeList :: Ord k => [Dict k v] -> Dict k v
dictMergeList = Map.unions

dictHasKey :: Ord k => Dict k v -> k -> Bool
dictHasKey = flip Map.member

dictLookup :: (MonadIO m, Ord k) => Dict k v -> k -> m (Maybe v)
dictLookup dict key =
  case Map.lookup key dict of
    Just result -> fmap Just (deRef result)
    Nothing -> return Nothing

dictLookupError :: (MonadIO m, Except.MonadError String m, Ord k, Show k) => Dict k v -> k -> m v
dictLookupError dict key =
  case Map.lookup key dict of
    Just result -> deRef result
    Nothing -> Except.throwError ("dictLookupError: " ++ show key)

dictAssignMaybe :: (MonadIO m, Ord k) => Dict k v -> k -> v -> m (Maybe v)
dictAssignMaybe dict key value =
  case Map.lookup key dict of
    Just result -> rwRef result (const value) >> return (Just value)
    Nothing -> return Nothing

dictAssign :: (MonadIO m, Ord k) => Dict k v -> k -> v -> m Bool
dictAssign d k = fmap isJust . dictAssignMaybe d k

dictAssignList :: (MonadIO m, Ord k) => Dict k v -> [(k,v)] -> m ()
dictAssignList d = mapM_ (\(k,v) -> dictAssign d k v)

dictAssignMany :: (MonadIO m, Ord k) => Dict k v -> [k] -> v -> m ()
dictAssignMany d keys value = mapM_ (\k -> dictAssign d k value) keys

dictFromList :: (MonadIO m, Ord k) => [(k,v)] -> m (Dict k v)
dictFromList l = do
  let (k,v) = unzip l
  r <- mapM toRef v
  return (Map.fromList (zip k r))

dictToList :: MonadIO m => Dict k v -> m [(k,v)]
dictToList d = do
  let (k,r) = unzip (Map.toList d)
  v <- mapM deRef r
  return (zip k v)

dictCopy :: (MonadIO m, Ord k) => Dict k v -> m (Dict k v)
dictCopy d = dictToList d >>= dictFromList

dictPrint :: (Show k, Show v) => Dict k v -> IO ()
dictPrint d = dictToList d >>= print
