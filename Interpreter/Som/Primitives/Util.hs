-- | Primitive Constructors
module Interpreter.Som.Primitives.Util where

import Interpreter.Som.Int {- stsc3-som -}
import Interpreter.Som.Types {- stsc3-som -}

-- | Alias for Except.throwError
prError :: String -> VM t
prError = vmError

-- | Integer|Double -> Double
objectAsDouble :: Object -> VM Double
objectAsDouble o = case o of
  Object _ (DataInteger x) -> return (fromIntegral x)
  Object _ (DataDouble x) -> return x
  _ -> prError "objectAsDouble"

unaryPrimitive :: String -> (ObjectData -> Maybe Object) -> Primitive
unaryPrimitive nm fun o@(Object _ obj) arg = case arg of
  [] -> case fun obj of
          Just r -> return r
          Nothing -> objectError o ("unaryPrimitive: " ++ nm)
  _ -> prError ("unaryPrimitive: arity: " ++ nm)

binaryPrimitiveOr :: VM Object -> String -> (ObjectData -> ObjectData -> Maybe Object) -> Primitive
binaryPrimitiveOr def nm fun o@(Object _ obj) arg = case arg of
  [Object _ p1] -> case fun obj p1 of
            Just r -> return r
            Nothing -> def
  _ -> objectListError (o : arg) ("binaryPrimitive: arity: " ++ nm)

binaryPrimitive :: String -> (ObjectData -> ObjectData -> Maybe Object) -> Primitive
binaryPrimitive nm fun o arg = binaryPrimitiveOr (objectListError (o : arg) ("binaryPrimitive: " ++ nm)) nm fun o arg

ternaryPrimitive :: String -> (ObjectData -> ObjectData -> ObjectData -> Maybe Object) -> Primitive
ternaryPrimitive nm fun o@(Object _ obj) arg = case arg of
  [Object _ p1,Object _ p2] -> case fun obj p1 p2 of
               Just r -> return r
               Nothing -> objectError o ("ternaryPrimitive: " ++ nm)
  _ -> objectListError arg ("ternaryPrimitive: arity: " ++ nm)

-- | Integer if fractional part is zero, else Double.
doubleAsFractional :: Double -> Object
doubleAsFractional x =
  case properFraction x of
    (i,0) -> integerObject i
    _ -> doubleObject x

-- | Integer|Double -> Integer|Double
numNumPrimitive :: String -> (Double -> Double) -> Primitive
numNumPrimitive msg f rcv arg = case arg of
  [] -> do
    lhs <- objectAsDouble rcv
    return (doubleAsFractional (f lhs))
  _ -> prError msg

-- | Integer|Double -> Integer|Double -> Integer|Double
numNumNumPrimitive :: String -> (Double -> Double -> Double) -> Primitive
numNumNumPrimitive msg f rcv arg = case arg of
  [arg1] -> do
    lhs <- objectAsDouble rcv
    rhs <- objectAsDouble arg1
    return (doubleAsFractional (f lhs rhs))
  _ -> prError msg

-- | Integer -> Integer
intIntPrimitive :: String -> (LargeInteger -> LargeInteger) -> Primitive
intIntPrimitive nm fun = unaryPrimitive nm (\arg1 -> case arg1 of
  DataInteger p1 -> Just (integerObject (fun p1))
  _ -> Nothing)

-- | Integer -> Double
intDoublePrimitive :: String -> (LargeInteger -> Double) -> Primitive
intDoublePrimitive nm fun = unaryPrimitive nm (\arg1 -> case arg1 of
  DataInteger p1 -> Just (doubleObject (fun p1))
  _ -> Nothing)

-- | Integer -> Integer -> Integer
intIntIntPrimitive :: String -> (LargeInteger -> LargeInteger -> LargeInteger) -> Primitive
intIntIntPrimitive nm fun = binaryPrimitive nm (\arg1 arg2 -> case (arg1,arg2) of
  (DataInteger p1,DataInteger p2) -> Just (integerObject (fun p1 p2))
  _ -> Nothing)

-- | Integer -> Integer|Double -> Integer|Double
intNumNumPrimitive :: String -> (LargeInteger -> LargeInteger -> LargeInteger) -> (Double -> Double -> Double) -> Primitive
intNumNumPrimitive nm fun1 fun2 = binaryPrimitive nm (\arg1 arg2 -> case (arg1,arg2) of
  (DataInteger p1,DataInteger p2) -> Just (integerObject (fun1 p1 p2))
  (DataInteger p1,DataDouble p2) -> Just (doubleObject (fun2 (fromIntegral p1) p2))
  _ -> Nothing)

-- | Integer -> Integer|Double -> Bool (with default)
intNumBoolPrimitiveOr :: VM Object -> String -> (LargeInteger -> LargeInteger -> Bool) -> (Double -> Double -> Bool) -> Primitive
intNumBoolPrimitiveOr def nm fun1 fun2 = binaryPrimitiveOr def nm (\arg1 arg2 -> case (arg1,arg2) of
  (DataInteger p1,DataInteger p2) -> Just (booleanObject (fun1 p1 p2))
  (DataInteger p1,DataDouble p2) -> Just (booleanObject (fun2 (fromIntegral p1) p2))
  _ -> Nothing)

-- | Integer -> Integer|Double -> Bool
intNumBoolPrimitive :: String -> (LargeInteger -> LargeInteger -> Bool) -> (Double -> Double -> Bool) -> Primitive
intNumBoolPrimitive nm fun1 fun2 = binaryPrimitive nm (\arg1 arg2 -> case (arg1,arg2) of
  (DataInteger p1,DataInteger p2) -> Just (booleanObject (fun1 p1 p2))
  (DataInteger p1,DataDouble p2) -> Just (booleanObject (fun2 (fromIntegral p1) p2))
  _ -> Nothing)

-- | Double -> Double
doubleDoublePrimitive :: String -> (Double -> Double) -> Primitive
doubleDoublePrimitive nm fun = unaryPrimitive nm (\arg1 -> case arg1 of
  DataDouble p1 -> Just (doubleObject (fun p1))
  _ -> Nothing)

-- | Double -> Integer
doubleIntPrimitive :: String -> (Double -> LargeInteger) -> Primitive
doubleIntPrimitive nm fun = unaryPrimitive nm (\arg1 -> case arg1 of
  DataDouble p1 -> Just (integerObject (fun p1))
  _ -> Nothing)

-- | Double -> Integer|Double -> Double
doubleNumDoublePrimitive :: String -> (Double -> Double -> Double) -> Primitive
doubleNumDoublePrimitive nm fun = binaryPrimitive nm (\arg1 arg2 -> case (arg1,arg2) of
  (DataDouble p1,DataInteger p2) -> Just (doubleObject (fun p1 (fromIntegral p2)))
  (DataDouble p1,DataDouble p2) -> Just (doubleObject (fun p1 p2))
  _ -> Nothing)

-- | Double -> Integer|Double -> Bool
doubleNumBoolPrimitive :: String -> (Double -> Double -> Bool) -> Primitive
doubleNumBoolPrimitive nm fun = binaryPrimitive nm (\arg1 arg2 -> case (arg1,arg2) of
  (DataDouble p1,DataInteger p2) -> Just (booleanObject (fun p1 (fromIntegral p2)))
  (DataDouble p1,DataDouble p2) -> Just (booleanObject (fun p1 p2))
  _ -> Nothing)
