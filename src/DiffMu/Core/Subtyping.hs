
module DiffMu.Core.Subtyping where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.TC
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial2
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Core.INC
import DiffMu.Core.MonadicGraph

import Debug.Trace

subtypingGraph :: forall e t k. (SingI k, Typeable k, MonadDMTC e t) => NodeType -> [t e (DMTypeOf k,DMTypeOf k)]
subtypingGraph = case testEquality (typeRep @k) (typeRep @MainKind) of
  Just Refl -> \case { IsReflexive -> [ do a <- TVar <$> newTVar "a"
                                           s <- svar <$> newSVar @MainSensKind "s"
                                           b <- TVar <$> newTVar "b"
                                           return ([a :@ s] :->: b, [a :@ s] :->: b)
                                      ]
                     ; NotReflexive -> []
                     }
  Nothing -> case testEquality (typeRep @k) (typeRep @BaseNumKind) of
    Just Refl -> \case { IsReflexive -> [ return (DMInt, DMInt), return (DMReal, DMReal)]
                       ; NotReflexive -> [ return (DMInt, DMReal)]
                       }
    Nothing -> \case {_ -> []}

  -- f (demote @k)
  -- where
  --   f MainKind = [ return (Numeric (NonConst DMInt, NonConst DMInt))]
  --   f _ = undefined

solveSubtyping :: forall t e k. (SingI k, Typeable k, IsT MonadDMTC t) => Symbol -> (DMTypeOf k, DMTypeOf k) -> t e ()
solveSubtyping name path = do
  let relevance e = IsGraphRelevant
  res <- findPathM @(Full e) @_ @DMException relevance (GraphM subtypingGraph) path
  case res of
    Finished a -> traceM ("subtyping finished with: " <> show a) >> dischargeConstraint @MonadDMTC name
    Partial a -> updateConstraint name (Solvable (IsLessEqual a))
    Wait -> return ()
    Fail e -> throwError (UnsatisfiableConstraint (show (fst path) <> " ⊑ " <> show (snd path) <> "\n\n"
                         <> "Got the following errors while search the subtyping graph:\n"
                         <> show e))


instance (SingI k, Typeable k) => Solve MonadDMTC IsLessEqual (DMTypeOf k, DMTypeOf k) where
  -- solve_ (IsLessEqual (a,b)) = undefined
  solve_ Dict _ name (IsLessEqual (a,b)) = solveSubtyping name (a,b)



instance Solve MonadDMTC IsSupremum (DMTypeOf k, DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ _ a = pure () -- undefined







