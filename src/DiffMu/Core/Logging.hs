
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.Logging where

import DiffMu.Prelude
import DiffMu.Abstract

instance Show (DMLogger) where
  show (DMLogger _ _ _) = "(hidden)"
    -- intercalate "\n\t" m

newtype DMLogMessages = DMLogMessages [DMLogMessage]

instance Semigroup DMLogMessages where
  (<>) (DMLogMessages xs) (DMLogMessages ys) = DMLogMessages (ys <> xs)

instance Monoid DMLogMessages where
  mempty = DMLogMessages []

data DMLogLocation = Location_INC | Location_Constraint | Location_Check | Location_Subtyping | Location_MonadicGraph | Location_All | Location_Unknown String
  deriving (Eq)

instance Show DMLogLocation where
  show Location_INC = "INC"
  show Location_Constraint = "Constr"
  show Location_All = "All"
  show Location_Check = "Check"
  show Location_Subtyping = "Subtyping"
  show Location_MonadicGraph = "MndGraph"
  show (Location_Unknown s) = red ("Unknown Location (" <> s <> ")")

fromString_DMLogLocation :: String -> DMLogLocation
fromString_DMLogLocation "INC" = Location_INC
fromString_DMLogLocation "Constr" = Location_Constraint
fromString_DMLogLocation "Check" = Location_Check
fromString_DMLogLocation "All" = Location_All
fromString_DMLogLocation "MndGraph" = Location_MonadicGraph
fromString_DMLogLocation "Subtyping" = Location_Subtyping
fromString_DMLogLocation s = Location_Unknown s

instance Ord (DMLogLocation) where
  a <= b | a == b = True
  x <= Location_All = True
  _ <= _ = False

instance Default (DMLogger) where
  def = DMLogger Debug Debug Location_All

data DMLogSeverity = Debug | Info | Force
  deriving (Eq,Ord)

data DMLogMessage = DMLogMessage DMLogSeverity DMLogLocation String

blue x = "\27[34m" <> x <> "\27[0m"
green x = "\27[32m" <> x <> "\27[0m"
yellow x = "\27[33m" <> x <> "\27[0m"
red x = "\27[31m" <> x <> "\27[0m"

instance Show DMLogSeverity where
  show Debug = blue "Debug"
  show Info = blue "Info"
  show Force = yellow "Force"

instance Show DMLogMessage where
  show (DMLogMessage s l m) = show s <> "[" <> show l <> "]: " <> m
    -- "[" <> blue (show l) <> "]\t" <> s <> blue ": \t" <> m

data DMLogger = DMLogger
  {
    _loggerBackupSeverity :: DMLogSeverity,
    _loggerCurrentSeverity :: DMLogSeverity,
    _loggerCurrentLocation :: DMLogLocation
    -- _loggerMessages :: [DMLogMessage]
  }
  deriving (Generic)

$(makeLenses ''DMLogger)


getLogMessages :: DMLogMessages -> DMLogSeverity -> [DMLogLocation] -> String
getLogMessages (DMLogMessages messages) sevR locsR =
  let filtered = [DMLogMessage s l m | DMLogMessage s l m <- messages, or [sevR <= s, or ((l <=) <$> locsR)]]
      reversed = reverse filtered
  in intercalate "\n" (show <$> reversed)


