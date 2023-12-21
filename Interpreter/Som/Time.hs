module Interpreter.Som.Time where

import Control.Monad.IO.Class {- base -}

import qualified Data.Time.Clock.System as Time {- time -}
import qualified Data.Time.LocalTime as Time {- time -}

{- | Get system time in seconds (floating point).
This is elapsed time since the UTC epoch of 1970-01-01.

> tm <- getSystemTimeInSeconds
> let secondsInYear = 365 * 24 * 60 * 60
> tm / secondsInYear

70 * 365 * 24 * 60 * 60
2207520000
2177452800
(3831283062664445 / 1e6) / secondsInYear
-}
getSystemTimeInSeconds :: MonadIO m => m Double
getSystemTimeInSeconds = do
  tm <- liftIO Time.getSystemTime
  return (fromIntegral (Time.systemSeconds tm) + (fromIntegral (Time.systemNanoseconds tm) * 1.0e-9))

secondsToMicroseconds :: Double -> Int
secondsToMicroseconds = round . (* 1.0e6)

getSystemTimezoneInSeconds :: MonadIO m => m Int
getSystemTimezoneInSeconds = do
  tz <- liftIO Time.getCurrentTimeZone
  return (Time.timeZoneMinutes tz * 60)
