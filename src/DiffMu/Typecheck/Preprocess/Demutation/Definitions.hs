
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.Demutation.Definitions where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Permutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.TopLevel

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace

import qualified Prelude as P



--------------------------------------------------------------------------------------
-- Demutation Type
--------------------------------------------------------------------------------------


data IsMutated = Mutated | NotMutated
  deriving (Generic, Show, Eq)

data IsLocalMutation = LocalMutation | NotLocalMutation
  deriving (Show, Eq)

--
-- NOTE: We later sort `VarAccessType`s,
-- and we do not want that the `IsLocalMutation`
-- content influences this sort --- we need to know
-- which comes first.
--
-- Hence this type is "contractible".
--
instance Ord IsLocalMutation where
  a <= b = True

-- But we need a comparison anyways:
le_ilm :: IsLocalMutation -> IsLocalMutation -> Bool
le_ilm LocalMutation _ = True
le_ilm NotLocalMutation LocalMutation = False
le_ilm NotLocalMutation NotLocalMutation = True

onlyLocallyMutatedVariables :: [(TeVar,IsLocalMutation)] -> Bool
onlyLocallyMutatedVariables xs = [v | (v, NotLocalMutation) <- xs] == []

data PureType = UserValue | DefaultValue | SingleArg TeVar | SingleArgPart TeVar | PureTuple [PureType]
  deriving (Show)

data ImmutType = Pure PureType | VirtualMutated [(TeVar , MemVar)] -- PureBlackBox
  deriving (Show)

consumeDefaultValue :: ImmutType -> ImmutType
consumeDefaultValue (Pure DefaultValue) = Pure (UserValue (RAnonymous MemAny))
consumeDefaultValue a = a


-- the scope
-- type Scope = Ctx TeVar ImmutType
type Scope = Ctx TeVar MemVar


---------------------------------------------------
-- These types describe which variable names
-- are in the RHS and must be moved on tlet/slet assignment
-- See #171 #172
data MoveType = TupleMove [MoveType] | SingleMove TeVar | NoMove
  deriving (Eq, Show)

singleMoveMaybe :: Maybe TeVar -> MoveType
singleMoveMaybe (Just a) = SingleMove a
singleMoveMaybe Nothing  = NoMove

data MoveState = Moved | NotMoved

instance Monad m => SemigroupM m MoveState where
  (NotMoved) ⋆ b = pure b
  Moved ⋆ b = pure Moved
instance Monad m => MonoidM m MoveState where
  neutral = pure NotMoved
instance Monad m => CheckNeutral m MoveState where
  checkNeutral (NotMoved) = pure True
  checkNeutral (Moved) = pure False
  

type MoveCtx = Ctx TeVar MoveState


--------------------------------------------------



--------------------------------------------------------
-- monoid instance for isMutated

instance Monad m => SemigroupM m IsMutated where
  (NotMutated) ⋆ b = pure b
  Mutated ⋆ b = pure Mutated
instance Monad m => MonoidM m IsMutated where
  neutral = pure NotMutated
instance Semigroup IsMutated where
  (<>) = (⋆!)
instance Monad m => CheckNeutral m IsMutated where
  checkNeutral (NotMutated) = pure True
  checkNeutral (Mutated) = pure False


--------------------------------------------------------------------------------------
-- Variable Access Type
--------------------------------------------------------------------------------------

data VarAccessType = ReadSingle | ReadMulti | WriteSingleBase IsFLetDefined -- IsLocalMutation
  deriving (Show,Eq,Ord)

data IsFLetDefined = FLetDefined | NotFLetDefined
  deriving (Show,Eq,Ord)

pattern WriteSingle = WriteSingleBase NotFLetDefined
pattern WriteSingleFunction = WriteSingleBase FLetDefined

-- type ImVarAccessCtx = Ctx TeVar ()
type VarAccessCtx = Ctx TeVar (VarAccessType, ScopeVar)

type MemCtx = Ctx MemVar (MemType, IsMutated, ScopeVar)


computeVarAccessType :: TeVar -> (VarAccessType, ScopeVar) -> (VarAccessType, ScopeVar) -> MTC VarAccessType
computeVarAccessType var (a, l) (b, k) = do
  let cur = sort [(a,l),(b,k)]
  case cur of
    [(ReadSingle, a), (ReadSingle, b)] | a == b   -> pure (ReadSingle)
    [(ReadSingle, a), (ReadSingle, b)] | a /= b   -> pure (ReadMulti)
    [(ReadSingle, a), (ReadMulti, _)]             -> pure (ReadMulti)
    [(ReadSingle, a), (WriteSingle, b)] | a == b  -> pure (WriteSingle)
    [(ReadSingle, a), (WriteSingle, b)] | a /= b  -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                           <> "' is being mutated and read in two different scopes.\n"
                                                                           <> "This is not allowed."
    -- [ReadSingle a, WriteSingleFunction b] | a == b -> pure (WriteSingleFunction a)
    -- [ReadSingle a, WriteSingleFunction b] | a /= b -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
    --                                                                                <> "' is being mutated and read in two different scopes.\n"
    --                                                                                <> "This is not allowed."
    [(ReadSingle, a), (WriteSingleFunction, b)]   -> pure (WriteSingleFunction)
    [(ReadMulti, _),(ReadMulti, _)]               -> pure (ReadMulti)
    [(ReadMulti, _),(WriteSingle, _)]             -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                            <> "' is being mutated and read in two different scopes.\n"
                                                                            <> "This is not allowed."
    [(ReadMulti,_),(WriteSingleFunction, a)]       -> pure (WriteSingleFunction) -- because of flet reordering it is allowed to mutate functions
    [(WriteSingle, a), (WriteSingle, b)] | a == b              -> pure (WriteSingle)
    -- [(WriteSingle a l, WriteSingle b k] | a == b, le_ilm l k  -> pure (WriteSingle a l)
    -- [(WriteSingle a l, WriteSingle b k] | a == b -> throwError $ DemutationError $ "The function argument '" <> show var <> "' has been mutated.\n"
    --                                                                             <> "But then a statement follows which assigns a variable with the same name."
    --                                                                             <> "This is not allowed, please use a different name here."
    [(WriteSingle, a), (WriteSingle, b)]          -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                            <> "' is being mutated in two different scopes.\n"
                                                                            <> "This is not allowed."
    [(WriteSingle, _), (WriteSingleFunction, _)]  -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' is defined as function and as value."
                                                                            <> "This is not allowed."
    [(WriteSingleFunction, a), (WriteSingleFunction, b)] | a == b ->              pure (WriteSingleFunction)
    -- [(WriteSingleFunction a l, WriteSingleFunction b k] | a == b, le_ilm l k -> pure (WriteSingleFunction a k)
    -- [(WriteSingleFunction a l, WriteSingleFunction b k] | a == b         -> throwError $ DemutationError $ "The function argument '" <> show var <> "' has been mutated.\n"
    --                                                                             <> "But then a statement follows which assigns a variable with the same name."
    --                                                                             <> "This is not allowed, please use a different name here."
    [(WriteSingleFunction, a), (WriteSingleFunction, b)] | a /= b -> throwError $ DemutationVariableAccessTypeError $ "The variable '" <> show var <> "' "
                                                                            <> "' is being mutated in two different scopes.\n"
                                                                            <> "This is not allowed."
    _ -> impossible "In demutation, while computing var access type. This branch should be inaccessible."



--------------------------------------------------------------------------------------
-- Memory types and local aliasing
--------------------------------------------------------------------------------------

data MemType = MemTup [RValue] | MemAny | MemMutatingFun [IsMutated] | MemPureFun | MemPureBlackBox
  deriving (Eq,Show)

data RValue = RMem MemVar | RAnonymous MemType
  deriving (Eq,Show)

--------------------------------------------------------------------------------------
-- The demutation monad
--------------------------------------------------------------------------------------

data MFull = MFull
  {
    _memctx :: MemCtx
  , _vactx :: VarAccessCtx
    -- _mutTypes :: VarAccessCtx
  , _moveCtx :: MoveCtx
  , _termVarsOfMut :: NameCtx
  , _scopeNames :: NameCtx
  , _memNames :: NameCtx
  , _topLevelInfo :: TopLevelInformation
  }


type MTC = LightTC Location_PrePro_Demutation MFull

$(makeLenses ''MFull)


-- new variables
newTeVarOfMut :: (MonadState MFull m) => Text -> m (TeVar)
newTeVarOfMut hint = termVarsOfMut %%= (first GenTeVar . (newName hint))

newScopeVar :: (MonadState MFull m) => Text -> m (ScopeVar)
newScopeVar hint = scopeNames %%= (first ScopeVar . (newName hint))

newMemVar :: (MonadState MFull m) => Text -> m (MemVar)
newMemVar hint = scopeNames %%= (first MemVar . (newName hint))


