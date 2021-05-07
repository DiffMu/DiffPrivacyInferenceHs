
module DiffMu.Typecheck.Subtyping where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification

import Debug.Trace

-- An abbreviation for adding a subtyping constraint.
(⊑!) :: (SingI k, Typeable k, MonadDMTC t) => DMTypeOf k -> DMTypeOf k -> t ()
(⊑!) a b = addConstraint (Solvable (IsLessEqual (a,b))) >> pure ()


-- A helper function used below in defining the subtyping graph.
getArrowLength :: DMFun -> Maybe Int
getArrowLength (a :->: _) = Just (length a)
getArrowLength _         = Nothing

-- The subtyping graph for our type system.
subtypingGraph :: forall e t k. (SingI k, Typeable k, MonadDMTC t) => EdgeType -> [Edge t (DMTypeOf k)]
subtypingGraph =
  let case1 = testEquality (typeRep @k) (typeRep @FunKind)
      case2 = testEquality (typeRep @k) (typeRep @NoFunKind)
      case3 = testEquality (typeRep @k) (typeRep @NumKind)
      case4 = testEquality (typeRep @k) (typeRep @BaseNumKind)
  in case (case1,case2,case3,case4) of
    -- Main Kind
    (Just Refl, _, _, _) ->
      \case { IsReflexive IsStructural -> []
            ; _ -> []}
              -- -> [ MultiEdge getArrowLength $
              --      \n -> do
              --        let f () = do a <- newVar
              --                      b <- newVar
              --                      b ⊑! a
              --                      s <- newVar
              --                      return (a :@ s, b :@ s)

              --        args <- mapM f (take n $ repeat ())
              --        let (args₀, args₁) = unzip args
              --        r₀ <- newVar
              --        r₁ <- newVar
              --        r₀ ⊑! r₁
              --        return (args₀ :->: r₀,  args₁ :->: r₁)
              --    ]}

    (_, Just Refl, _, _) ->
      \case { IsReflexive IsStructural
            -> [
                 SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return (Numeric a₀, Numeric a₁)
                 ]
            ; IsReflexive NotStructural -> [ SingleEdge $
                   do nrm <- newVar
                      clp <- newVar
                      n <- newVar
                      m <- newVar
                      a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return ((DMMat nrm clp n m a₀), (DMMat nrm clp n m a₁))
                 , SingleEdge $ -- this is the conv rule made implicit, for converting DMData to DMReal
                   do nrm <- newVar
                      clp <- newVar
                      n <- newVar
                      m <- newVar
                      return ((DMMat nrm (Clip clp) n m (Numeric DMData)), (DMMat clp U n m (Numeric (NonConst DMReal))))
                 ]
            ; NotReflexive -> []
            }

    -- Num Kind
    (_, _, Just Refl, _) ->
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
                 , SingleEdge $ return (DMData, DMData)
                 ]
            ; NotReflexive
              -> [ SingleEdge $
                   do a₀ <- newVar
                      s₀ <- newVar
                      return (Const s₀ a₀, NonConst a₀)
                 , SingleEdge $ return (NonConst DMReal, DMData)
                 ]
            }

    -- BaseNum Kind
    (_, _, _, Just Refl) ->
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
    (_, _, _, _) -> \_ -> []


convertSubtypingToSupremum :: forall k t. (SingI k, Typeable k, IsT MonadDMTC t) => Symbol -> (DMTypeOf k, DMTypeOf k) -> t ()
convertSubtypingToSupremum name (lower, TVar upper) = do
  allSubtypings <- getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))
  -- TODO: We are actually not allowed to do this always, but only if there is nothing which could be broken...
  let withSameVar = [(name', lower') | (name', IsLessEqual (lower', TVar upper')) <- allSubtypings,
                              name' /= name,
                              upper' == upper]
  case withSameVar of
    [] -> return ()
    ((name',lower'):[]) -> do
      dischargeConstraint name'
      dischargeConstraint name
      addConstraint (Solvable (IsSupremum (lower, lower', TVar upper)))
      return ()
    ((name',lower'):xs) -> error "Not implemented yet: When more than two subtyping constrs are merged to a single supremum. Don't worry, this case shouldn't be hard!"
convertSubtypingToSupremum name _                   = pure ()

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
  res <- findPathM @(Full) relevance (GraphM graph) path

  -- We look at the result and if necessary throw errors.
  case res of
    Finished a -> dischargeConstraint @MonadDMTC name
    Partial a  -> updateConstraint name (Solvable (IsLessEqual a))
    Wait       -> convertSubtypingToSupremum name path -- in this case we try to change this one into a sup
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
  res <- findSupremumM @(Full) relevance (GraphM graph) (a,b,x)

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


-- TODO: Check whether this does the correct thing.
instance (SingI k, Typeable k) => Solve MonadDMTC IsInfimum (DMTypeOf k, DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ name (IsInfimum a) = pure ()

------------------------------------------------------------
-- Solve supremum (TODO this should live somewhere else.)


-- is it gauss or mgauss?
instance Solve MonadDMTC IsGaussResult (DMType, DMType) where
  solve_ Dict _ name (IsGaussResult (τgauss, τin)) =
     case τin of
        TVar x -> pure ()
        DMMat nrm clp n m τ -> do
           iclp <- newVar -- clip of input matrix can be anything
           -- set constraints for in- and output types as given in the rule
           addConstraint (Solvable (IsLessEqual (τin, (DMMat L2 iclp n m (Numeric (NonConst DMReal))))))
           addConstraint (Solvable (IsEqual (τgauss, (DMMat LInf U n m (Numeric (NonConst DMReal))))))
           dischargeConstraint @MonadDMTC name
        _ -> do -- regular gauss or invalid subtyping constraint later
           τ <- newVar
           addConstraint (Solvable (IsEqual (τin, Numeric τ)))
           addConstraint (Solvable (IsEqual (τgauss, Numeric (NonConst DMReal))))
           dischargeConstraint @MonadDMTC name
           return ()


