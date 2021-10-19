
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.TopLevel where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Permutation
import DiffMu.Typecheck.Operations
import DiffMu.Core.DelayedScope
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.IsFunctionArgument
import DiffMu.Typecheck.Constraint.IsJuliaEqual
import DiffMu.Typecheck.Constraint.CheapConstraints
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace

type TLTC = LightTC DMLogLocation ()

data TopLevelInformation = TopLevelInformation
  {
    blackBoxNames :: [TeVar]
  , globalNames :: [TeVar]
  }


instance Show TopLevelInformation where
  show (TopLevelInformation bbs gls) = "globals: " <> show gls <> "\nblack boxes: " <> show bbs <> "\n"

-- Walk through the toplevel code and get a list of all top-level definitions.
-- These are the global captures which are implicitly applied to black boxes.
--
-- Furthermore, make sure that blackbox lets (BBLet) are only on the top level,
-- (to make sure that the only captured scope is really the top-level one)
-- And that their names do not intersect with any top level name.
--
-- returns (blackbox names, global names)

checkTopLevel :: MutDMTerm -> TLTC (TopLevelInformation, MutDMTerm)

-- if we have a black box
-- make sure that the name is not already taken by anything else
checkTopLevel (BBLet v body rest) = do
  (TopLevelInformation bbvars glvars, newRest) <- checkTopLevel rest

  case v `elem` bbvars of
    True -> throwError (BlackBoxError $ "Found multiple black boxes definitions for the name " <> show v <> ". Black boxes are only allowed to have a single implementation.")
    False -> pure ()

  case v `elem` glvars of
    True -> throwError (BlackBoxError $ "Found a global definition for the name " <> show v <> ". This is not allowed since there already is a black box with that name.")
    False -> pure ()


  return (TopLevelInformation (v : bbvars) (v : glvars), BBLet v body newRest)

-- if we have something else top level
checkTopLevel (SLet (v :- vt) body rest) = do
  checkNonTopLevelBB body
  (TopLevelInformation bbvars glvars, newRest) <- checkTopLevel rest

  case v `elem` bbvars of
    True -> throwError (BlackBoxError $ "Found a black box definition for the name " <> show v <> ". This is not allowed since there already is a global variable with that name.")
    False -> pure ()

  return (TopLevelInformation bbvars (v : glvars), SLet (v :- vt) body newRest)
checkTopLevel (FLet v body rest) = do
  checkNonTopLevelBB body
  (TopLevelInformation bbvars glvars, newRest)<- checkTopLevel rest

  case v `elem` bbvars of
    True -> throwError (BlackBoxError $ "Found a black box definition for the name " <> show v <> ". This is not allowed since there already is a global variable with that name.")
    False -> pure ()

  return (TopLevelInformation bbvars (v : glvars), FLet v body newRest)
checkTopLevel (TLet (vs) body rest) = do
  checkNonTopLevelBB body
  (TopLevelInformation bbvars glvars, newRest)<- checkTopLevel rest

  let letvars = fstA <$> vs

  let checkname v = case v `elem` bbvars of
        True -> throwError (BlackBoxError $ "Found a black box definition for the name " <> show v <> ". This is not allowed since there already is a global variable with that name.")
        False -> pure ()

  mapM checkname letvars

  return (TopLevelInformation bbvars (letvars <> glvars) , TLet (vs) body newRest)

-- all other terms mean that the top level scope is done.
-- we make sure that there are no BBLets there
checkTopLevel rest = do
  checkNonTopLevelBB rest
  return (TopLevelInformation [] [], LastTerm rest)


-- make sure that no black box definitions are here.
checkNonTopLevelBB :: MutDMTerm -> TLTC MutDMTerm
checkNonTopLevelBB (BBLet v jt rest) = throwError (BlackBoxError $ "Found a black box definition (" <> show v <> ") which is not in the top level scope. Black boxes can only be defined at the top level scope. " )
checkNonTopLevelBB term = recDMTermMSameExtension checkNonTopLevelBB term


