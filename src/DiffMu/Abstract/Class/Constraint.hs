
{-# LANGUAGE UndecidableInstances #-}


module DiffMu.Abstract.Class.Constraint where

import DiffMu.Prelude
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Log
import DiffMu.Abstract.Class.Term
-- import DiffMu.Abstract.Class.MonadTerm
import Debug.Trace

data SolvingMode = SolveExact | SolveAssumeWorst | SolveGlobal | SolveFinal | SolveSpecial
  deriving (Eq)

instance Show SolvingMode where
  show SolveExact = "exact"
  show SolveAssumeWorst = "worst"
  show SolveGlobal = "global"
  show SolveFinal = "final"
  show SolveSpecial = "special"

-- instance Ord SolvingMode where
--   SolveExact <= a = True
--   SolveAssumeWorst <= SolveExact = False
--   SolveAssumeWorst <= SolveAssumeWorst = True

class TCConstraint c where
  constr :: a -> c a
  runConstr :: c a -> a

  insideConstr :: (Monad t) => (a -> t a) -> c a -> t (c a)
  insideConstr f c = constr <$> f (runConstr c)

class TCConstraint c => Solve (isT :: (* -> *) -> Constraint) c a where
  solve_ :: Dict ((IsT isT t)) -> SolvingMode -> Symbol -> c a -> t ()

class MonadNormalize t where
  normalizeState :: t ()

data Solvable  (extraConstr :: * -> Constraint) (extraContentConstr :: * -> Constraint) isT where
  Solvable :: (Solve isT c a, (HasNormalize isT a), Show (c a), Typeable c, Typeable a, extraContentConstr a, extraConstr (c a)) => c a -> Solvable extraConstr extraContentConstr isT

-- solve' :: (Solve isT c a, IsT isT t, Normalize (t) a) => c a -> t ()
solve :: (Monad (t), IsT isT t) => SolvingMode -> Symbol -> (Solvable eC eC2 isT) -> t ()
solve mode name (Solvable (c :: c a) :: Solvable eC eC2 isT) = f Proxy
  where f :: (Monad (t), IsT isT t) => Proxy (t) -> t ()
        f (_ :: Proxy (t)) = (insideConstr normalize c >>= solve_ @isT Dict mode name)


instance (isT t, Monad (t)) => Normalize (t) (Solvable eC eC2 isT) where
  normalize (Solvable (c :: c a)) = (Solvable @isT <$> insideConstr (normalize @(t)) c)

instance Show (Solvable eC eC2 isT) where
  show (Solvable c) = show c

data CloseConstraintSetResult = ConstraintSet_WasEmpty | ConstraintSet_WasNotEmpty

class (Monad t) => MonadConstraint isT t | t -> isT where
-- class (IsT isT t) => MonadConstraint v isT t e | t -> isT where
  type ContentConstraintOnSolvable t :: * -> Constraint
  type ConstraintOnSolvable t :: * -> Constraint
  type ConstraintBackup t
  addConstraint :: Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT -> t Symbol
  getUnsolvedConstraintMarkNormal :: [SolvingMode] -> t (Maybe (Symbol , Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT, SolvingMode))
  dischargeConstraint :: Symbol -> t ()
  failConstraint :: Symbol -> t ()
  updateConstraint :: Symbol -> Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT -> t ()
  openNewConstraintSet :: t ()
  mergeTopConstraintSet :: t CloseConstraintSetResult
  logPrintConstraints :: t ()
  getConstraintsByType :: (Typeable c, Typeable a) => Proxy (c a) -> t [(Symbol, c a)]
  getAllConstraints :: t [(Symbol, Solvable (ConstraintOnSolvable t) (ContentConstraintOnSolvable t) isT)]
  clearSolvingEvents :: t [String]
  -- clearConstraints :: t (ConstraintBackup t)
  -- restoreConstraints :: ConstraintBackup t -> t ()


(==!) :: (MonadConstraint isT t, Solve isT IsEqual (a,a), (HasNormalize isT a), Show (a), Typeable a, IsT isT t, ContentConstraintOnSolvable t (a,a), ConstraintOnSolvable t (IsEqual (a,a))) => a -> a -> t ()
(==!) a b = addConstraint (Solvable (IsEqual (a,b))) >> pure ()

-- An abbreviation for adding a less equal constraint.
(≤!) :: (MonadConstraint isT t, Solve isT IsLessEqual (a,a), (HasNormalize isT a), Show (a), Typeable a, IsT isT t, ContentConstraintOnSolvable t (a,a), ConstraintOnSolvable t (IsLessEqual (a,a))) => a -> a -> t ()
(≤!) a b = addConstraint (Solvable (IsLessEqual (a,b))) >> pure ()


-- Basic constraints
newtype IsEqual a = IsEqual a
  deriving (Show)

instance TCConstraint IsEqual where
  constr = IsEqual
  runConstr (IsEqual c) = c


---- Less Equal (subtyping)
newtype IsLessEqual a = IsLessEqual a
  deriving (Show)

instance TCConstraint IsLessEqual where
  constr = IsLessEqual
  runConstr (IsLessEqual c) = c

---- Less (for sensitivities)
newtype IsLess a = IsLess a
  deriving (Show)

instance TCConstraint IsLess where
  constr = IsLess
  runConstr (IsLess c) = c

---- Sups
newtype IsSupremum a = IsSupremum a deriving Show

instance TCConstraint IsSupremum where
  constr = IsSupremum
  runConstr (IsSupremum c) = c

---- Infimum
newtype IsInfimum a = IsInfimum a deriving Show

instance TCConstraint IsInfimum where
  constr = IsInfimum
  runConstr (IsInfimum c) = c

---- Choices
newtype IsChoice a = IsChoice a deriving Show

instance TCConstraint IsChoice where
  constr = IsChoice
  runConstr (IsChoice c) = c

{-
---- Gauss or Mgauss?
newtype IsGaussResult a = IsGaussResult a deriving Show

instance TCConstraint IsGaussResult where
  constr = IsGaussResult
  runConstr (IsGaussResult c) = c
-}

----------------------------------------------------------
-- functions for Constraint


-- Iterates over all constraints which are currently in a "changed" state, and tries to solve them.
-- Returns if no "changed" constraints remains.
-- An unchanged constraint is marked "changed", if it is affected by a new substitution.
-- A changed constraint is marked "unchanged" if it is read by a call to `getUnsolvedConstraintMarkNormal`.
solveAllConstraints :: forall isT t eC. (MonadImpossible t, MonadLog t, MonadConstraint isT t, MonadNormalize t, IsT isT t) => [SolvingMode] -> t ()
solveAllConstraints modes = withLogLocation "Constr" $ do

  -- get events which came before us
  oldEvents <- clearSolvingEvents
  case oldEvents of
    [] -> pure ()
    xs -> do
      log $ "[Solver]: Before solving all constraints, the following events have accumulated unnoticed:"
      log $ intercalate "\n" (fmap ("           - " <>) xs)
      log ""

  normalizeState
  openConstr <- getUnsolvedConstraintMarkNormal modes

  case openConstr of
    Nothing -> return ()
    Just (name, constr, mode) -> do
      -- debug $ "[Solver]: Notice: BEFORE solving (" <> show mode <> ") " <> show name <> " : " <> show constr
      -- logPrintConstraints
      solve mode name constr

      -- check whether constraint disappeared
      allCs <- getAllConstraints
      let newConstrValue = filter (\(n',val) -> n' == name) allCs
      bDischarged <- case newConstrValue of
        []        -> pure True
        [(_,val)] -> pure False
        _ -> impossible "Found multiple constraints with the same name."

      -- check for events which happened
      events <- clearSolvingEvents

      -- print if something notable happened
      case (bDischarged, events) of
        (False,[]) -> pure ()
        (b,xs) -> do
          log $ "[Solver]: solving (" <> show mode <> ") " <> show name <> " : " <> show constr
          log $ intercalate "\n" (fmap ("             - " <>) xs)
          log $ "          => " <> if b then green "Discharged" else yellow "Wait/Update"

      solveAllConstraints modes

solvingAllNewConstraints :: (MonadImpossible t, MonadLog t, MonadConstraint isT t, MonadNormalize t, IsT isT t) => [SolvingMode] -> t a -> t (CloseConstraintSetResult, a)
solvingAllNewConstraints modes f = withLogLocation "Constr" $ do
  log ""
  log "============ BEGIN solve all new constraints >>>>>>>>>>>>>>>>"
  openNewConstraintSet
  logPrintConstraints
  res <- f
  solveAllConstraints modes
  log "============ AFTER solving all new constraints >>>>>>>>>>>>>>>>"
  logPrintConstraints
  closeRes <- mergeTopConstraintSet
  log "============ AFTER merging constraint sets >>>>>>>>>>>>>>>>"
  logPrintConstraints
  log "============ END solve all new constraints <<<<<<<<<<<<<<<<"
  return (closeRes, res)


solveAndNormalize :: forall a isT t eC. (MonadImpossible t, MonadLog t, MonadConstraint isT t, MonadNormalize t, IsT isT t, Normalize t a) => [SolvingMode] -> a -> t a
solveAndNormalize modes value = f 4 value
  where
    f :: Int -> a -> t a
    f n a0 | n <= 0 = impossible "Solving & normalizing needed more than 4 iterations. Cancelling."
    f n a0          = do

      -- get all constraint names
      allCs0 <- getAllConstraints
      let allNames0 = fst <$> allCs0

      solveAllConstraints modes
      a1 <- normalize a0

      allCs1 <- getAllConstraints
      let allNames1 = fst <$> allCs1

      case allNames0 == allNames1 of
        True  -> return a1
        False -> f (n-1) a1




