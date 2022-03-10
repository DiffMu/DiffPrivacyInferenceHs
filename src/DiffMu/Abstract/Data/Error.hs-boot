
module DiffMu.Abstract.Data.Error where

import DiffMu.Prelude

type role DMPersistentMessage nominal
data DMPersistentMessage (t :: * -> *)
data DMException
type role WithContext nominal representational
data WithContext (t :: * -> *) (e :: *)
type LocatedDMException t = WithContext t DMException
class MonadError e t => MonadDMError e t where
  isCritical :: e -> t Bool
  persistentError :: LocatedDMException t -> t ()
  catchAndPersist :: (Normalize t x, ShowPretty x, Show x) => t a -> (DMPersistentMessage t -> t (a, x)) -> t a
  enterNonPersisting :: t ()
  exitNonPersisting :: t ()

