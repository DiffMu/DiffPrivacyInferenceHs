{-# LANGUAGE OverloadedLists #-}

module DiffMu.Typecheck.JuliaType where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Typecheck.Subtyping

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import qualified Data.POSet as PO
import Data.POSet (POSet)

-- local imports
import Algebra.PartialOrd

import Data.IORef
import System.IO.Unsafe

import           Foreign.C.String
import           Foreign.C.Types
import           Foreign.Ptr

import Debug.Trace


juliatype :: DMTypeOf k -> JuliaType
juliatype = undefined
-- juliatype (Numeric τ) = juliatype τ
-- juliatype DMInt = undefined

global_callback_issubtype :: IORef (DMEnv)
global_callback_issubtype = unsafePerformIO (newIORef makeEmptyDMEnv)

instance PartialOrd JuliaType where
  leq = undefined
  -- leq (JuliaType _ t) (JuliaType _ s) =
  --   let callback = (askJuliaSubtypeOf $ unsafePerformIO (readIORef global_callback_issubtype))
  --   in case (callback) of
  --     Nothing -> error "Julia callback (issubtype) is not set."
  --     Just f  -> call_StringStringBool f t s


foreign import ccall "dynamic" call_StringStringBool :: FunPtr (CString -> CString -> Bool) -> CString -> CString -> Bool


instance Solve MonadDMTC IsChoice (DMType, (HashMap [JuliaType] (DMType , Sensitivity))) where
  solve_ Dict _ name (IsChoice arg) = solveIsChoice name arg


solveIsChoice :: forall t. IsT MonadDMTC t => Symbol -> (DMType, (HashMap [JuliaType] (DMType , Sensitivity))) -> t ()
solveIsChoice =
  let matchArgs :: Symbol -> DMType -> HashMap [JuliaType] (DMType , Sensitivity) -> [DMType] -> t ()
      matchArgs name τ choices args = do
        let newchoices = H.filterWithKey (\s c -> choiceCouldMatch args s) choices
        if H.null newchoices
          then throwError (NoChoiceFoundError $ "No matching choice for " <> show τ <> " found in " <> show choices)
          else pure ()

        -- if there is no free tyepevars in τs arguments, throw out methods that are more general than others
        -- if we don't know all types we cannot do this, as eg for two methods
        -- (Int, Int) => T
        -- (Real, Number) => T
        -- and arg types (TVar, DMInt), both methods are in newchoices, but if we later realize the TVar
        -- is a DMReal, the first one does not match even though it's less general.
        let newchoices' = case and (null . freeVars @_ @TVarOf <$> args) of
              -- if no tvars are in the args
              True  -> keepLeastGeneral newchoices
              -- else we do not change them
              False -> newchoices

        case length newchoices' == length choices of
          -- no choices were discarded, the constraint could not be simplified.
          True -> return ()

          -- some choices were discarded, so we can continue
          False -> do

            -- null all flags of choices that were discarded, so their inferred sensitivities get nulled
            let discardedKeys = choices `H.difference` newchoices'
            mapM (\(_,(_, s)) -> s ==! zeroId) (H.toList discardedKeys)

            case H.toList newchoices' of
              -- only one left, we can pick that one
              -- even if there is free TVars, we don't have to add subtype constraints for the user-given signature,
              -- as it was encoded in the Arr type of the choice, so its arg types can only be refinements.
              -- set this ones flag to 1
              [(_, (cτ, s))] -> s ==! oneId >> cτ ⊑! τ >> dischargeConstraint name

              -- multiple are still left, we update the constraint
              _              -> updateConstraint name (Solvable (IsChoice (τ, newchoices')))

  in \name (τ,choices) -> case τ of
    args :->: _  -> matchArgs name τ choices (fstAnn <$> args)
    args :->*: _ -> matchArgs name τ choices (fstAnn <$> args)
    TVar _       -> case H.toList choices of
                      [(_,(cτ, s))] -> s ==! oneId >> cτ ⊑! τ >> dischargeConstraint name
                      _               -> pure ()
    t            -> internalError $ "The term " <> show t <> " is not supported in a choice."


keepLeastGeneral :: HashMap [JuliaType] (DMType , Sensitivity) -> HashMap [JuliaType] (DMType , Sensitivity)
keepLeastGeneral cs =
  let pos :: POSet [JuliaType]
      pos = PO.fromList (HS.toList (H.keysSet cs))
      mins = PO.lookupMin pos
      mins' = [(k, cs H.! k) | k <- mins]
  in H.fromList mins'

choiceCouldMatch :: [DMType] -> [JuliaType] -> Bool
choiceCouldMatch args cs =
  case length args == length cs of
    False -> False
    True -> let couldMatch t c = case isVar t of
                  Just (_ :: SymbolOf MainKind) -> True
                  Nothing -> juliatype t `leq` c
            in and (zipWith couldMatch args cs)


