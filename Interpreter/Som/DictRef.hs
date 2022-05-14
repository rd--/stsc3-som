-- | DictRef
module Interpreter.Som.DictRef where

import Control.Monad.IO.Class {- base -}

import qualified Data.Map as Map {- containers -}

import Interpreter.Som.Dict
import Interpreter.Som.Ref

-- | Dictionary in reference.
type DictRef k v = Ref (Dict k v)

dictRefEmpty :: MonadIO m => m (DictRef k v)
dictRefEmpty = toRef Map.empty

dictRefKeys :: MonadIO m => DictRef k v -> m [k]
dictRefKeys = fmap Map.keys . deRef

dictRefLookup :: (MonadIO m, Ord k) => DictRef k v -> k -> m (Maybe v)
dictRefLookup r w = deRef r >>= \d -> dictLookup d w

dictRefInsert :: (MonadIO m, Ord k) => DictRef k v -> k -> v -> m ()
dictRefInsert dictRef key value = do
  valueRef <- toRef value
  rwRef dictRef (Map.insert key valueRef)

dictRefAssignMaybe :: (MonadIO m, Ord k) => DictRef k v -> k -> v -> m (Maybe v)
dictRefAssignMaybe r key value = deRef r >>= \d -> dictAssignMaybe d key value

dictRefAssign :: (MonadIO m, Ord k) => DictRef k v -> k -> v -> m Bool
dictRefAssign r key value = deRef r >>= \d -> dictAssign d key value

dictRefAssignMany :: (MonadIO m, Ord k) => DictRef k v -> [k] -> v -> m ()
dictRefAssignMany r keys value = deRef r >>= \d -> dictAssignMany d keys value

dictRefAssignList :: (MonadIO m, Ord k) => DictRef k v -> [(k,v)] -> m ()
dictRefAssignList r keysvalues = deRef r >>= \d -> dictAssignList d keysvalues

dictRefFromList :: (MonadIO m, Ord k) => [(k,v)] -> m (DictRef k v)
dictRefFromList l = dictFromList l >>= \d -> toRef d

dictRefCopy :: (MonadIO m, Ord k) => DictRef k v -> m (DictRef k v)
dictRefCopy r = deRef r >>= \d -> dictCopy d >>= toRef
