
module DiffMu.Abstract.Data.Error where

import DiffMu.Prelude

type role DMPersistentMessage nominal
data DMPersistentMessage (t :: * -> *)
data DMException
data LocatedError (e :: *)
type LocatedDMException = LocatedError DMException
class MonadError e t => MonadDMError e t where
  isCritical :: e -> t Bool
  getPersistentErrorMessage :: e -> DMPersistentMessage t

