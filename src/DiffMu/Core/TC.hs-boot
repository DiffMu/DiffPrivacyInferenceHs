
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Symbolic
import DiffMu.Core.Logging
import {-# SOURCE #-} DiffMu.Core.Definitions

data Full


class (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent (x :: *) where
instance (FreeVars TVarOf x, Substitute TVarOf DMTypeOf x) => GoodConstraintContent x where

class (FixedVars TVarOf x) => GoodConstraint (x :: *) where
instance (FixedVars TVarOf x) => GoodConstraint x where

class LiftTC (t :: * -> *)

class (MonadImpossible (t), MonadWatch (t), MonadLog t,
       MonadTerm DMTypeOf (t),
       MonadTerm SymTerm (t),
       MonadState (Full) (t),
       MonadWriter (DMMessages t) (t),
       MonadError LocatedDMException (t),
       MonadInternalError t,
       MonadUnificationError t,
       -- MonadConstraint' Symbol (TC) (t),
       -- MonadConstraint Symbol (MonadDMTC) (t),
       MonadConstraint (MonadDMTC) (t),
       MonadNormalize t,
       ContentConstraintOnSolvable t ~ GoodConstraintContent,
       ConstraintOnSolvable t ~ GoodConstraint,
       LiftTC t
      ) => MonadDMTC (t :: * -> *) where

