
module DiffMu.Core.TC where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.Term

type TSubs = Subs DMType

instance Term DMType where
  type Var DMType = Symbol
  var x = TVar x
  substituteAll f x = undefined

instance MonadTC DMType (TC e) where

instance MonadImpossible (TC e) where
  impossible err = throwError (ImpossibleError err)

instance Normalize (TC e) DMType where
  normalize n =
    do σ <- getSubs @DMType
       σ ↷ n

instance (Normalize t a, Normalize t b) => Normalize t (a :& b) where
  normalize (a :@ b) = (:@) <$> normalize a <*> normalize b

instance (Normalize t a) => Normalize t [a] where
  normalize as = mapM normalize as

instance Monad t => Normalize t DMNumType where
  normalize = pure

instance Normalize (TC e) Sensitivity where
  normalize n = impossible "not implemented!?"

-- instance Unifiable (TC e) DMType where











       -- σ <- getSubstitutions @_ @Sensitivity
       -- σ ↷ n








