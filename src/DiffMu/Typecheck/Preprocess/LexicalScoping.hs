
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.LexicalScoping where

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
import DiffMu.Typecheck.Preprocess.TopLevel

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace


data LSFull = LSFull
  {
    _termVarsOfLS :: NameCtx
  }


type LSTC = LightTC Location_PrePro_Demutation LSFull

$(makeLenses ''LSFull)


-- new variables
newTeVarOfLS :: (MonadState LSFull m) => TeVar -> m (TeVar)
newTeVarOfLS hintVar = termVarsOfLS %%= (first GenTeVar . (newName (hint hintVar)))
  where
    hint (GenTeVar (Symbol x))   = x <> "_genls"
    hint (UserTeVar (Symbol x))  = x <> "_uls"

processLS :: DMTerm -> LSTC (DMTerm)
processLS = undefined



