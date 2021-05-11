
module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Symbolic
import {-# SOURCE #-} DiffMu.Core.Definitions

data Full

class (MonadImpossible (t), MonadWatch (t),
       MonadTerm DMTypeOf (t), MonadTerm SymTerm (t),
       MonadState (Full) (t),
       MonadError DMException (t),
       MonadInternalError t,
       -- MonadConstraint' Symbol (TC) (t),
       -- MonadConstraint Symbol (MonadDMTC) (t),
       MonadConstraint (MonadDMTC) (t),
       MonadNormalize t
       -- LiftTC t
      ) => MonadDMTC t where
