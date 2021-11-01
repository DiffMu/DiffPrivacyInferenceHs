
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Core.Logging where

import DiffMu.Prelude
import DiffMu.Abstract
import GHC.Stack


import qualified Control.Monad.Except as QUAL

data DMLogLocation =
  Location_PreProcess
  | Location_PrePro_Demutation
  | Location_PrePro_Global
  | Location_PrePro_FLetReorder
  | Location_Unification
  | Location_Subst
  | Location_INC
  | Location_Constraint
  | Location_Check
  | Location_Subtyping
  | Location_MonadicGraph
  | Location_All
  | Location_Unknown String
  deriving (Eq)

-------
-- a partial singleton implementation for dmloglocation
-- we cannot use the standard singletons generated by Data.Singleton.TH
-- because the Location_Unknown string value cannot be lifted to the type level?
-- (it is simpler to have this custom implementation for now)
class ISing_DMLogLocation a where
  singDMLogLocation :: Proxy a -> DMLogLocation

instance ISing_DMLogLocation Location_PreProcess where
  singDMLogLocation _ = Location_PreProcess

instance ISing_DMLogLocation Location_PrePro_Demutation where
  singDMLogLocation _ = Location_PrePro_Demutation

instance ISing_DMLogLocation Location_PrePro_Global where
  singDMLogLocation _ = Location_PrePro_Global

instance ISing_DMLogLocation Location_PrePro_FLetReorder where
  singDMLogLocation _ = Location_PrePro_FLetReorder

-- END singleton
-------



data DMLogSeverity = Debug | Info | Warning | Force
  deriving (Eq,Ord)

data IsFollowUpMessage = FollowUpMessage | NotFollowUpMessage
  deriving (Eq)

data DMLogMessage = DMLogMessage DMLogSeverity DMLogLocation String

data DMLogMessageFU = DMLogMessageFU IsFollowUpMessage DMLogMessage


data DMLogger = DMLogger
  {
    _loggerBackupSeverity :: DMLogSeverity,
    _loggerCurrentSeverity :: DMLogSeverity,
    _loggerCurrentLocation :: DMLogLocation
    -- _loggerMessages :: [DMLogMessage]
  }
  deriving (Generic)

$(makeLenses ''DMLogger)

instance Show (DMLogger) where
  show (DMLogger _ _ _) = "(hidden)"
    -- intercalate "\n\t" m

newtype DMLogMessages = DMLogMessages [DMLogMessage]

instance Semigroup DMLogMessages where
  (<>) (DMLogMessages xs) (DMLogMessages ys) = DMLogMessages (ys <> xs)

instance Monoid DMLogMessages where
  mempty = DMLogMessages []




instance Show DMLogLocation where
  show Location_PreProcess = "PreProcess"
  show Location_PrePro_Demutation = "PrePro_Demutation"
  show Location_PrePro_Global = "PrePro_Global"
  show Location_PrePro_FLetReorder = "PrePro_FLetReorder"
  show Location_Unification = "Unification"
  show Location_Subst = "Subst"
  show Location_INC = "INC"
  show Location_Constraint = "Constr"
  show Location_All = "All"
  show Location_Check = "Check"
  show Location_Subtyping = "Subtyping"
  show Location_MonadicGraph = "MndGraph"
  show (Location_Unknown s) = red ("Unknown Location (" <> s <> ")")

fromString_DMLogLocation :: String -> DMLogLocation
fromString_DMLogLocation "Unification" = Location_Unification
fromString_DMLogLocation "Subst" = Location_Subst
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

blue x = "\27[34m" <> x <> "\27[0m"
green x = "\27[32m" <> x <> "\27[0m"
yellow x = "\27[33m" <> x <> "\27[0m"
red x = "\27[31m" <> x <> "\27[0m"
magenta x = "\27[35m" <> x <> "\27[0m"

instance Show DMLogSeverity where
  show Debug = blue "Debug"
  show Info = blue "Info"
  show Force = yellow "Force"
  show Warning = magenta "Warning"

instance Show DMLogMessage where
  show (DMLogMessage s l m) = show s <> "[" <> show l <> "]: " <> m
    -- "[" <> blue (show l) <> "]\t" <> s <> blue ": \t" <> m

instance Show DMLogMessageFU where
  show (DMLogMessageFU x (DMLogMessage s l m)) = prefix' <> m
    where
      showSevNoColor :: DMLogSeverity -> String
      showSevNoColor Debug   = "Debug"
      showSevNoColor Info    = "Info"
      showSevNoColor Force   = "Force"
      showSevNoColor Warning = "Warning"

      prefix        = show s           <> "[" <> show l <> "]: "
      prefixNoColor = showSevNoColor s <> "[" <> show l <> "]: "
      prefix' = case x of
        FollowUpMessage -> (\_ -> ' ') <$> prefixNoColor
        NotFollowUpMessage -> prefix



markFollowup :: Maybe DMLogMessage -> [DMLogMessage] -> [DMLogMessageFU]
markFollowup Nothing [] = []
markFollowup Nothing (x:xs) = (DMLogMessageFU NotFollowUpMessage x) : markFollowup (Just x) xs
markFollowup (Just top) [] = []
markFollowup (Just m1@(DMLogMessage s1 l1 t1)) (m2@(DMLogMessage s2 l2 t2):xs) = case and [s1 == s2 , l1 == l2] of
  True  -> DMLogMessageFU FollowUpMessage m2    : markFollowup (Just m2) xs
  False -> DMLogMessageFU NotFollowUpMessage m2 : markFollowup (Just m2) xs

getLogMessages :: DMLogMessages -> DMLogSeverity -> [DMLogLocation] -> String
getLogMessages (DMLogMessages messages) sevR locsR =
  let filtered = [DMLogMessage s l m | DMLogMessage s l m <- messages, or [sevR <= s, or ((l <=) <$> locsR)]]
      reversed = reverse filtered
  in intercalate "\n" (show <$> (markFollowup Nothing reversed))


throwError :: (MonadLog m, MonadError e m) => e -> m a
throwError e = do
  logForce $ "-------------------------\nError information:\n-----------------------\ncallstack: " <> show callStack <> "\n"
  QUAL.throwError e


