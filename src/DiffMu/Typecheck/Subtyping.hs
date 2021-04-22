
module DiffMu.Typecheck.Subtyping where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
-- import DiffMu.Typecheck.Unification

import Debug.Trace


-- An abbreviation for adding a subtyping constraint.
(⊑!) :: (SingI k, Typeable k, MonadDMTC t) => DMTypeOf k -> DMTypeOf k -> t ()
(⊑!) a b = addConstraint (Solvable (IsLessEqual (a,b))) >> pure ()

-- A helper function used below in defining the subtyping graph.
getArrowLength :: DMType -> Maybe Int
getArrowLength (a :->: _) = Just (length a)
getArrowLength _         = Nothing

-- The subtyping graph for our type system.
subtypingGraph :: forall e t k. (SingI k, Typeable k, MonadDMTC t) => EdgeType -> [Edge t (DMTypeOf k)]
subtypingGraph =
  let case1 = testEquality (typeRep @k) (typeRep @MainKind)
      case2 = testEquality (typeRep @k) (typeRep @NumKind)
      case3 = testEquality (typeRep @k) (typeRep @BaseNumKind)
  in case (case1,case2,case3) of
    -- Main Kind
    (Just Refl, _, _) ->
      \case { IsReflexive IsStructural
              -> [ MultiEdge getArrowLength $
                   \n -> do
                     let f () = do a <- newVar
                                   b <- newVar
                                   b ⊑! a
                                   s <- newVar
                                   return (a :@ s, b :@ s)

                     args <- mapM f (take n $ repeat ())
                     let (args₀, args₁) = unzip args
                     r₀ <- newVar
                     r₁ <- newVar
                     r₀ ⊑! r₁
                     return (args₀ :->: r₀, args₁ :->: r₁)

                 , SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return (Numeric a₀, Numeric a₁)
                 ]
            ; IsReflexive NotStructural -> []
            ; NotReflexive -> []
            }

    -- Num Kind
    (_, Just Refl, _) ->
      \case { IsReflexive IsStructural
              -> []
            ; IsReflexive NotStructural
              -> [ SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return (NonConst a₀, NonConst a₁)
                 , SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      s₀ <- newVar
                      return (Const s₀ a₀, Const s₀ a₁)
                 ]
            ; NotReflexive
              -> [ SingleEdge $
                   do a₀ <- newVar
                      s₀ <- newVar
                      return (Const s₀ a₀, NonConst a₀)
                 ]
            }

    -- BaseNum Kind
    (_, _, Just Refl) ->
      \case { IsReflexive NotStructural
              -> [ SingleEdge $ return (DMInt, DMInt)
                 , SingleEdge $ return (DMReal, DMReal)
                 ]
            ; IsReflexive IsStructural
              -> []
            ; NotReflexive
              -> [ SingleEdge $ return (DMInt, DMReal)
                 ]
            }
    (_, _, _) -> \_ -> []


-- The actual solving is done here.
-- this simply uses the `findPathM` function from Abstract.Computation.MonadicGraph
solveSubtyping :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => Symbol -> (DMTypeOf k, DMTypeOf k) -> t ()
solveSubtyping name path = do
  -- Here we define which errors should be caught while doing our hypothetical computation.
  let relevance (UnificationError _ _)      = IsGraphRelevant
      relevance (UnsatisfiableConstraint _) = IsGraphRelevant
      relevance _                           = NotGraphRelevant

  -- traceM $ "Starting subtyping solving of " <> show path
  let graph = subtypingGraph @t
  -- traceM $ "I have " <> show (length (graph (IsReflexive NotStructural))) <> " candidates."

  -- Executing the computation
  res <- findPathM @(Full) @_ @DMException relevance (GraphM graph) path

  -- We look at the result and if necessary throw errors.
  case res of
    Finished a -> dischargeConstraint @MonadDMTC name
    Partial a  -> updateConstraint name (Solvable (IsLessEqual a))
    Wait       -> return ()
    Fail e     -> throwError (UnsatisfiableConstraint (show (fst path) <> " ⊑ " <> show (snd path) <> "\n\n"
                         <> "Got the following errors while search the subtyping graph:\n"
                         <> show e))


-- We can solve `IsLessEqual` constraints for DMTypes.
-- NOTE: IsLessEqual is interpreted as a subtyping relation.
instance (SingI k, Typeable k) => Solve MonadDMTC IsLessEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsLessEqual (a,b)) = solveSubtyping name (a,b)



------------------------------------------------------------
-- Solve supremum

-- The actual solving is done here.
-- this simply uses the `findSupremumM` function from Abstract.Computation.MonadicGraph
solveSupremum :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => Symbol -> (DMTypeOf k, DMTypeOf k, DMTypeOf k) -> t ()
solveSupremum name (a,b,x) = do
  -- Here we define which errors should be caught while doing our hypothetical computation.
  let relevance (UnificationError _ _)      = IsGraphRelevant
      relevance (UnsatisfiableConstraint _) = IsGraphRelevant
      relevance _                           = NotGraphRelevant

  -- traceM $ "Starting subtyping solving of " <> show path
  let graph = subtypingGraph @t
  -- traceM $ "I have " <> show (length (graph (IsReflexive NotStructural))) <> " candidates."

  -- Executing the computation
  res <- findSupremumM @(Full) @_ @DMException relevance (GraphM graph) (a,b,x)

  -- We look at the result and if necessary throw errors.
  case res of
    Finished a -> dischargeConstraint @MonadDMTC name
    Partial a  -> updateConstraint name (Solvable (IsSupremum a))
    Wait       -> return ()
    Fail e     -> throwError (UnsatisfiableConstraint ("sup(" <> show (a) <> ", " <> show b <> ") = " <> show x <> "\n\n"
                         <> "Got the following errors while search the subtyping graph:\n"
                         <> show e))


-- TODO: Check whether this does the correct thing.
instance (SingI k, Typeable k) => Solve MonadDMTC IsSupremum (DMTypeOf k, DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsSupremum a) = solveSupremum name a


