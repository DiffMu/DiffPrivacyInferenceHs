
module DiffMu.Abstract.Data.Error where

import DiffMu.Prelude
-- import DiffMu.Abstract.Class.Log

import {-# SOURCE #-} DiffMu.Core.Definitions


-------------------------------------------------------------------------

data DMPersistentMessage t where
  DMPersistentMessage :: (Normalize t a, Show a) => a -> DMPersistentMessage t

instance Show (DMPersistentMessage t) where
  show (DMPersistentMessage msg) = show msg

instance Monad t => Normalize t (DMPersistentMessage t) where
  normalize e (DMPersistentMessage msg) = DMPersistentMessage <$> normalize e msg



--------------------------------------------------------------------------
-- Locations

data SourceLoc = SourceLoc
  {
    getLocFile  :: String
  , getLocBegin :: (Int,Int)
  , getLocEnd   :: (Int,Int)
  }
  deriving (Eq, Show)

data SourceLocExt = ExactLoc SourceLoc | RelatedLoc String SourceLocExt | UnknownLoc | NotImplementedLoc String
  deriving (Eq, Show)

data Located a = Located
  {
    getLocation :: SourceLocExt
  , getLocated :: a
}
  deriving (Functor, Foldable, Traversable, Eq, Show)

downgradeToRelated :: String -> SourceLocExt -> SourceLocExt
downgradeToRelated = RelatedLoc

notLocated :: a -> Located a
notLocated = Located UnknownLoc



--------------------------------------------------------------------------
-- DMException
--
-- The different kinds of errors we can throw.

data DMException where
  UnsupportedError        :: String -> DMException
  UnificationError        :: Show a => a -> a -> DMException
  WrongNumberOfArgs       :: Show a => a -> a -> DMException
  WrongNumberOfArgsOp     :: Show a => a -> Int -> DMException
  ImpossibleError         :: String -> DMException
  InternalError           :: String -> DMException
  VariableNotInScope      :: Show a => a -> DMException
  UnsatisfiableConstraint :: String -> DMException
  TypeMismatchError       :: String -> DMException
  NoChoiceFoundError      :: String -> DMException
  UnblockingError         :: String -> DMException
  DemutationError         :: String -> DMException
  DemutationDefinitionOrderError :: Show a => a -> DMException
  DemutationVariableAccessTypeError :: String -> DMException
  BlackBoxError           :: String -> DMException
  FLetReorderError        :: String -> DMException
  UnificationShouldWaitError :: DMTypeOf k -> DMTypeOf k -> DMException
  TermColorError          :: AnnotationKind -> String -> DMException
  ParseError              :: String -> String -> Int -> DMException -- error message, filename, line number
  DemutationMovedVariableAccessError :: Show a => a -> DMException
  DemutationNonAliasedMutatingArgumentError :: String -> DMException
  DemutationSplitMutatingArgumentError :: String -> DMException

instance Show DMException where
  show (UnsupportedError t) = "The term '" <> t <> "' is currently not supported."
  -- show (UnsupportedTermError t) = "The term '" <> show t <> "' is currently not supported."
  show (UnificationError a b) = "Could not unify '" <> show a <> "' with '" <> show b <> "'."
  show (WrongNumberOfArgs a b) = "While unifying: the terms '" <> show a <> "' and '" <> show b <> "' have different numbers of arguments"
  show (WrongNumberOfArgsOp op n) = "The operation " <> show op <> " was given a wrong number (" <> show n <> ") of args."
  show (ImpossibleError e) = "Something impossible happened: " <> e
  show (InternalError e) = "Internal error: " <> e
  show (VariableNotInScope v) = "Variable not in scope: " <> show v
  show (UnsatisfiableConstraint c) = "The constraint " <> c <> " is not satisfiable."
  show (TypeMismatchError e) = "Type mismatch: " <> e
  show (NoChoiceFoundError e) = "No choice found: " <> e
  show (UnificationShouldWaitError a b) = "Trying to unify types " <> show a <> " and " <> show b <> " with unresolved infimum (∧)."
  show (UnblockingError e) = "While unblocking, the following error was encountered:\n " <> e
  show (DemutationError e) = "While demutating, the following error was encountered:\n " <> e
  show (BlackBoxError e) = "While preprocessing black boxes, the following error was encountered:\n " <> e
  show (FLetReorderError e) = "While processing function signatures, the following error was encountered:\n " <> e
  show (ParseError e file line) = "Unsupported julia expression in file " <> file <> ", line " <> show line <> ":\n " <> e
  show (TermColorError color t) = "Expected " <> show t <> " to be a " <> show color <> " expression but it is not."
  show (DemutationDefinitionOrderError a) = "The variable '" <> show a <> "' has not been defined before being used.\n"
                                            <> "Note that currently every variable has to be assigned some value prior to its usage.\n"
                                            <> "Here, 'prior to usage' means literally earlier in the code.\n"
                                            <> "The actual value of that assignment is irrelevant, e.g., the first line of the following code is only there to fix the error which is currently shown:\n"
                                            <> ">  a = 0" <> "\n"
                                            <> ">  function f()" <> "\n"
                                            <> ">    a" <> "\n"
                                            <> ">  end" <> "\n"
                                            <> ">  a = 3" <> "\n"
                                            <> ">  f()" <> "\n"
  show (DemutationVariableAccessTypeError e) = "An error regarding variable access types occured:\n" <> e
  show (DemutationMovedVariableAccessError a) = "Tried to access the variable " <> show a <> ". But this variable is not valid anymore, because it was assigned to something else."
  show (DemutationNonAliasedMutatingArgumentError a) = "An error regarding non-aliasing of mutating arguments occured:\n" <> a
  show (DemutationSplitMutatingArgumentError a) = "An error regarding mutating arguments occured:\n" <> a

instance Eq DMException where
  -- UnsupportedTermError    a        == UnsupportedTermError    b       = True
  UnificationError        a a2     == UnificationError        b b2    = True
  WrongNumberOfArgs       a a2     == WrongNumberOfArgs       b b2    = True
  WrongNumberOfArgsOp     a a2     == WrongNumberOfArgsOp     b b2    = True
  ImpossibleError         a        == ImpossibleError         b       = True
  InternalError           a        == InternalError           b       = True
  VariableNotInScope      a        == VariableNotInScope      b       = True
  UnsatisfiableConstraint a        == UnsatisfiableConstraint b       = True
  TypeMismatchError       a        == TypeMismatchError       b       = True
  NoChoiceFoundError      a        == NoChoiceFoundError      b       = True
  UnificationShouldWaitError a a2  == UnificationShouldWaitError b b2 = True
  ParseError e1 file1 line1        == ParseError e2 file2 line2       = True
  FLetReorderError        a        == FLetReorderError        b       = True
  TermColorError      a b          == TermColorError c d              = True
  DemutationError a                == DemutationError         b       = True
  DemutationDefinitionOrderError a == DemutationDefinitionOrderError b = True
  DemutationVariableAccessTypeError a == DemutationVariableAccessTypeError b = True
  DemutationMovedVariableAccessError a       == DemutationMovedVariableAccessError b = True
  DemutationNonAliasedMutatingArgumentError a       == DemutationNonAliasedMutatingArgumentError b = True
  DemutationSplitMutatingArgumentError a       == DemutationSplitMutatingArgumentError b = True
  _ == _ = False

data LocatedError e = LocatedError e [(String,SourceLocExt)]
  deriving (Show,Eq,Functor,Foldable,Traversable)
type LocatedDMException = LocatedError DMException

-- throwLocatedError e xs = throwError (LocatedError e [(s,)])

isCriticalError e = case e of
  ImpossibleError s -> True
  InternalError s -> True
  _ -> False



class MonadError e t => MonadDMError e t where
  isCritical :: e -> t Bool
  getPersistentErrorMessage :: e -> DMPersistentMessage t
