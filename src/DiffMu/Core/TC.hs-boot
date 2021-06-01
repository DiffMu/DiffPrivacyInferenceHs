
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Symbolic
import {-# SOURCE #-} DiffMu.Core.Definitions

data Full


class (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent (x :: *) where
instance (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent x where

class (MonadImpossible (t), MonadWatch (t),
       MonadTerm DMTypeOf (t),
       MonadTermDuplication DMTypeOf (t),
       MonadTerm SymTerm (t),
       MonadState (Full) (t),
       MonadError DMException (t),
       MonadInternalError t,
       -- MonadConstraint' Symbol (TC) (t),
       -- MonadConstraint Symbol (MonadDMTC) (t),
       MonadConstraint (MonadDMTC) (t),
       MonadNormalize t,
       ConstraintOnSolvable t ~ GoodConstraintContent
       -- LiftTC t
      ) => MonadDMTC (t :: * -> *) where

