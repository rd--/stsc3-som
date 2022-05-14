-- | Primitive utilities
module Interpreter.Som.Primitives.Util where

import Interpreter.Som.Int {- stsc3-som -}
import Interpreter.Som.Types {- stsc3-som -}

prError :: String -> Vm t
prError txt = vmError ("Primitive error: " ++ txt)

objectDataAsDouble :: ObjectData -> Vm Double
objectDataAsDouble o =
  case o of
    DataInteger x -> return (fromIntegral x)
    DataDouble x -> return x
    _ -> prError "objectDataAsDouble"

-- | Integer if fractional part is zero, else Double.
doubleAsFractional :: Double -> Object
doubleAsFractional x =
  case properFraction x of
    (i,0) -> integerObject i
    _ -> doubleObject x

numNumPrimitive :: (Double -> Double) -> ObjectData -> Vm Object
numNumPrimitive f = fmap (doubleAsFractional . f) . objectDataAsDouble

numNumNumPrimitive :: (Double -> Double -> Double) -> ObjectData -> ObjectData -> Vm Object
numNumNumPrimitive f rcv arg = do
  lhs <- objectDataAsDouble rcv
  rhs <- objectDataAsDouble arg
  return (doubleAsFractional (f lhs rhs))

intNumNumPrimitive :: (LargeInteger -> LargeInteger -> LargeInteger) -> (Double -> Double -> Double) -> LargeInteger -> ObjectData -> Vm Object
intNumNumPrimitive f1 f2 lhs rhs =
  case rhs of
    DataInteger rhs' -> return (integerObject (f1 lhs rhs'))
    DataDouble rhs' -> return (doubleObject (f2 (fromIntegral lhs) rhs'))
    _ -> prError "intNumNumPrimitive"

intNumBoolPrimitive :: Vm Object -> (LargeInteger -> LargeInteger -> Bool) -> (Double -> Double -> Bool) -> LargeInteger -> ObjectData -> Vm Object
intNumBoolPrimitive def f1 f2 lhs rhs =
  case rhs of
    DataInteger rhs' -> return (booleanObject (f1 lhs rhs'))
    DataDouble rhs' -> return (booleanObject (f2 (fromIntegral lhs) rhs'))
    _ -> def

doubleNumDoublePrimitive :: (Double -> Double -> Double) -> Double -> ObjectData -> Vm Object
doubleNumDoublePrimitive f lhs rhs = fmap (doubleObject . f lhs) (objectDataAsDouble rhs)

doubleNumBoolPrimitive :: (Double -> Double -> Bool) -> Double -> ObjectData -> Vm Object
doubleNumBoolPrimitive f lhs rhs = fmap (booleanObject . f lhs) (objectDataAsDouble rhs)
