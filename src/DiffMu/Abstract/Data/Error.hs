
{-# LANGUAGE UndecidableInstances #-}

module DiffMu.Abstract.Data.Error where

import DiffMu.Prelude
-- import DiffMu.Abstract.Class.Log
import DiffMu.Abstract.Data.ErrorReporting

import {-# SOURCE #-} DiffMu.Core.Definitions

import Debug.Trace
import Data.String (IsString)
import qualified Data.Text as T
import qualified Prelude as P
import Data.Graph (edges)

--------------------------------------------------------------------------
-- Printing


newlineIndentIfLong :: StringLike t => t -> t
newlineIndentIfLong xs = if length (linesS xs) <= 1
  then xs
  else "\n" <> indent xs

parenIfMultiple :: StringLike t => t -> t
parenIfMultiple xs = if length (wordsS xs) <= 1
  then xs
  else "(" <> xs <> ")"

-- parenIfMultiple xs = case ' ' `elem` xs of
--   False -> xs
--   True -> "(" <> xs <> ")"

parenIndent :: StringLike s => s -> s
parenIndent s = "\n(\n" <> unlinesS (fmap ("  " <>) (linesS s)) <> ")"

braceIndent :: StringLike s => s -> s
braceIndent s = "\n{\n" <> unlinesS (fmap ("  " <>) (linesS s)) <> "}"


-- justIndent :: String -> String
-- justIndent s = unlines (fmap ("  " <>) (lines s))

indent :: StringLike s => s -> s
indent s = unlinesS (fmap ("  " <>) (linesS s))



--------------------------------------------------------------------------
-- Locations

data SourceLoc = SourceLoc
  {
    getLocFile  :: Text
  , getLocBegin :: Int
  , getLocEnd   :: Int
  }
  deriving (Eq)

data SourceLocExt = ExactLoc SourceLoc | RelatedLoc Text SourceLocExt | UnknownLoc | NotImplementedLoc Text
  deriving (Eq)

data Located a = Located
  {
    getLocation :: SourceLocExt
  , getLocated :: a
}
  deriving (Functor, Foldable, Traversable, Eq)

instance Normalize t a => Normalize t (Located a) where
  normalize e (Located loc a) = Located loc <$> normalize e a

instance Show a => Show (Located a) where
  show (Located loc a) = show a


instance ShowLocated a => ShowLocated (Located a) where
  showLocated (Located loc a) = showLocated a

downgradeToRelated :: Text -> SourceLocExt -> SourceLocExt
downgradeToRelated = RelatedLoc

notLocated :: a -> Located a
notLocated = Located UnknownLoc

instance Monad t => Normalize t SourceLocExt where
  normalize e = pure

instance ShowPretty SourceLoc where
  showPretty (SourceLoc file begin end) | begin == end  = T.unpack file <> ": line " <> show begin
  showPretty (SourceLoc file begin end) = T.unpack file <> ": between lines " <> show begin <> " and " <> show end

instance Show SourceLocExt where
  show = showPretty

instance ShowLocated SourceLoc where
  showLocated loc@(SourceLoc file (begin) (end)) = do
    sourcelines <- printSourceLines (begin, end)
    return $ T.pack (showPretty loc) <> "\n"
             <> sourcelines

instance ShowPretty SourceLocExt where
  showPretty = \case
    ExactLoc sl -> showPretty sl
    RelatedLoc s sle -> showPretty s <> ": " <> showPretty sle
    UnknownLoc -> "Unknown location"
    NotImplementedLoc s -> "This location is currently ineffable. (" <> showPretty s <> ")"


instance ShowLocated SourceLocExt where
  showLocated = \case
    ExactLoc sl -> showLocated sl
    RelatedLoc s sle -> do s' <- showLocated s
                           sle' <- showLocated sle
                           return $ s' <> ": " <> sle'
    UnknownLoc -> pure "Unknown location"
    NotImplementedLoc s -> do
      s' <- showLocated s
      return $ "This location is currently ineffable. (" <> s' <> ")"


-------------------------------------------------------------------------
-- Printing source

--
-- conditions:
--  - `begin <= end`
--
printSourceLines :: MonadReader RawSource t => (Int,Int) -> t Text
printSourceLines (begin,end) = do
  let numbersize = length (show end)
  printed_lines <- mapM (printSourceLine numbersize) [begin .. (end - 1)]
  let edge = T.pack $ take (numbersize P.+ 2) (repeat ' ') <> "|"
  return $ edge <> "\n"
           <> T.intercalate "\n" printed_lines <> "\n"
           <> edge <> "\n"


--
-- conditions:
--  - `length(show(linenumber)) <= required_numbersize`
--
printSourceLine :: MonadReader RawSource t => Int -> Int -> t Text
printSourceLine required_numbersize linenumber = do
  let printed_linenumber = show linenumber
  let padded_linenumber = take (required_numbersize - length printed_linenumber) (repeat ' ') <> printed_linenumber
  RawSource source <- ask
  let required_line = source ! linenumber
  return $ " " <> T.pack padded_linenumber <> " |     " <> required_line


-------------------------------------------------------------------------
type MessageLike t a = (Normalize t a, Show a, ShowLocated a)

data DMPersistentMessage t where
  DMPersistentMessage :: MessageLike t a => a -> DMPersistentMessage t


-- instance ShowPretty (DMPersistentMessage t) where
--   showPretty (DMPersistentMessage msg) = showPretty msg

instance Show (DMPersistentMessage t) where
  show (DMPersistentMessage msg) = show msg

instance ShowLocated (DMPersistentMessage t) where
  showLocated (DMPersistentMessage msg) = showLocated msg

instance Monad t => Normalize t (DMPersistentMessage t) where
  normalize e (DMPersistentMessage msg) = DMPersistentMessage <$> normalize e msg

instance MonadReader RawSource t => SemigroupM t (DMPersistentMessage t) where
  (DMPersistentMessage a) ⋆ (DMPersistentMessage b) = return (DMPersistentMessage $ a :-----: b)

instance MonadReader RawSource t => MonoidM t (DMPersistentMessage t) where
  neutral = pure (DMPersistentMessage ())

instance Monad t => CheckNeutral t (DMPersistentMessage t) where
  checkNeutral b = pure False

data WithContext e t = WithContext e (DMPersistentMessage t)
  -- deriving (Functor,Foldable,Traversable)


instance ShowLocated e => ShowLocated (WithContext e t) where
  showLocated (WithContext e ctx) = do
    e' <- showLocated e
    ctx' <- showLocated ctx
    return $ e' <> "\n" <> indent ctx'


instance Show e => Show (WithContext e t) where
  show (WithContext e ctx) = show e

-- instance ShowPretty e => Show (WithContext e t) where
--   show (WithContext e ctx) = showPretty e <> "\n"
--                             <> indent (showPretty ctx)

withContext e x = WithContext e (DMPersistentMessage x)

type LocatedDMException t = WithContext DMException t


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
  ParseError              :: String -> String -> Int -> Int-> DMException -- error message, filename, line number, line number of next expression
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
  show (ParseError e file line nextline) = case line == nextline of
                                                True -> "Unsupported julia expression in file " <> file <> ", line " <> show line <> ":\n " <> e
                                                False -> "Unsupported julia expression in file " <> file <> ", between line " <> show line <> " and " <> show nextline <> ":\n " <> e
  show (TermColorError color t) = "Expected " <> show t <> " to be a " <> show color <> " expression but it is not."
  show (DemutationDefinitionOrderError a) = "The variable '" <> show a <> "' has not been defined before being used.\n"
                                            <> "Note that every variable has to be assigned some value prior to its usage.\n"
                                            <> "Here, 'prior to usage' means literally earlier in the code."
  show (DemutationVariableAccessTypeError e) = "An error regarding variable access types occured:\n" <> e
  show (DemutationMovedVariableAccessError a) = "Tried to access the variable " <> show a <> ". But this variable is not valid anymore, because it was assigned to something else."
  show (DemutationNonAliasedMutatingArgumentError a) = "An error regarding non-aliasing of mutating arguments occured:\n" <> a
  show (DemutationSplitMutatingArgumentError a) = "An error regarding mutating arguments occured:\n" <> a

instance ShowPretty (DMException) where
  showPretty = show

instance ShowLocated (DMException) where
  showLocated = return . T.pack . showPretty

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
  ParseError e1 file1 line1 nlne1  == ParseError e2 file2 line2 nlne2 = True
  FLetReorderError        a        == FLetReorderError        b       = True
  TermColorError      a b          == TermColorError c d              = True
  DemutationError a                == DemutationError         b       = True
  DemutationDefinitionOrderError a == DemutationDefinitionOrderError b = True
  DemutationVariableAccessTypeError a == DemutationVariableAccessTypeError b = True
  DemutationMovedVariableAccessError a       == DemutationMovedVariableAccessError b = True
  DemutationNonAliasedMutatingArgumentError a       == DemutationNonAliasedMutatingArgumentError b = True
  DemutationSplitMutatingArgumentError a       == DemutationSplitMutatingArgumentError b = True
  _ == _ = False


-- throwLocatedError e xs = throwError (WithContext e [(s,)])

isCriticalError e = case e of
  ImpossibleError s -> True
  InternalError s -> True
  _ -> False


data WrapMessageNatural s t e a = WrapMessageNatural (forall x. t x -> s (Maybe x)) a

instance Show a => Show (WrapMessageNatural s t e a) where show (WrapMessageNatural f a) = show a
-- instance ShowPretty a => ShowPretty (WrapMessageNatural s t e a) where showPretty (WrapMessageNatural f a) = showPretty a
instance (Monad s, ShowLocated a) => ShowLocated (WrapMessageNatural s t e a) where showLocated (WrapMessageNatural f a) = showLocated a
-- where showLocated (WrapMessageNatural f a) = do
--                                                                                                           x <- f $ showLocated a
--                                                                                                           case x of
--                                                                                                             Just a -> return a
--                                                                                                             Nothing -> return "[Error when generating Error]"

instance (Monad s, Normalize t a) => Normalize s (WrapMessageNatural s t e a) where
  normalize level (WrapMessageNatural f x) = WrapMessageNatural f <$> do
    x' <- f (normalize level x)
    case x' of
      Just x'' -> return x''
      Nothing -> pure x
    -- case f (normalize level x) of
                                                                           -- Just x -> x
                                                                           -- Nothing -> pure x

instance IsNaturalError (WithContext e) where
  functionalLift α (WithContext x (DMPersistentMessage msg)) = WithContext x (DMPersistentMessage (WrapMessageNatural @_ @_ @e α msg))

class IsNaturalError e where
  -- functionalLiftMaybe :: (Monad t, Monad s) => (forall a. t a -> s (Maybe a)) -> e t -> e s
  functionalLift :: (Monad t, Monad s) => (forall a. t a -> s (Maybe a)) -> e t -> e s


class (IsNaturalError e, MonadError (e t) t) => MonadDMError e t where
  isCritical :: e t -> t Bool
  persistentError :: LocatedDMException t -> t ()
  catchAndPersist :: MessageLike t x => t a -> (DMPersistentMessage t -> t (a, x)) -> t a
  enterNonPersisting :: t ()
  exitNonPersisting :: t ()


--------------------------------------------------------------------
----------------- message construction -----------------------------
--------------------------------------------------------------------



instance Monad t => Normalize t Char where
  normalize e = pure


-------------------------------------------------------------------------
-- Vertical combination

infixl 5 :-----:
data (:-----:) a b = (:-----:) a b
  deriving (Show)

instance (ShowLocated a, ShowLocated b) => ShowLocated (a :-----: b) where
  showLocated (a :-----: b) = do
    a' <- showLocated a
    b' <- showLocated b
    return $       a'
                   <> "\n"
                   <> "---------------------------------------------------------"
                   <> "\n"
                   <> b'

instance (Normalize t a, Normalize t b) => Normalize t (a :-----: b) where
  normalize e (a :-----: b) = (:-----:) <$> normalize e a <*> normalize e b

--------------

infixl 5 :\\:
data (:\\:) a b = (:\\:) a b
  deriving (Show)

instance (ShowLocated a, ShowLocated b) => ShowLocated (a :\\: b) where
  showLocated (a :\\: b) = do
    a' <- showLocated a
    b' <- showLocated b
    return $       a'
                   <> "\n"
                   <> b'

instance (Normalize t a, Normalize t b) => Normalize t (a :\\: b) where
  normalize e (a :\\: b) = (:\\:) <$> normalize e a <*> normalize e b

--------------

infixl 5 :\\->:
data (:\\->:) a b = (:\\->:) a b
  deriving (Show)

instance (ShowLocated a, ShowLocated b) => ShowLocated (a :\\->: b) where
  showLocated (a :\\->: b) = do
    a' <- showLocated a
    b' <- showLocated b
    return $ a' <> " " <> newlineIndentIfLong b'

instance (Normalize t a, Normalize t b) => Normalize t (a :\\->: b) where
  normalize e (a :\\->: b) = (:\\->:) <$> normalize e a <*> normalize e b


-------------------------------------------------------------------------
-- Horizontal combination

infixl 6 :<>:
data (:<>:) a b = (:<>:) a b
  deriving (Show)

instance (ShowLocated a, ShowLocated b) => ShowLocated (a :<>: b) where
  showLocated (a :<>: b) = do
    a' <- showLocated a 
    b' <- showLocated b 
    return $ a' <> " " <> b'

instance (Normalize t a, Normalize t b) => Normalize t (a :<>: b) where
  normalize e (a :<>: b) = (:<>:) <$> normalize e a <*> normalize e b


-- -------

-- data (:<.:) a = (:<.:) a String

-- instance (ShowPretty a) => ShowPretty (:<.:) a where
--   showPretty (a :<.: b) = showPretty a <> " " <> showPretty b

-- instance (Normalize t a) => Normalize t ((:<.:) a) where

