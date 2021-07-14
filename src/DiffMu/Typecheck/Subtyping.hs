
module DiffMu.Typecheck.Subtyping where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification


import qualified Data.HashMap.Strict as H

import Debug.Trace





---------------------------------------------------------------------
-- "Non strict subtyping"

-- An abbreviation for adding a subtyping constraint.
(⊑!) :: (SingI k, Typeable k, MonadDMTC t) => DMTypeOf k -> DMTypeOf k -> t ()
(⊑!) a b = addConstraint (Solvable (IsLessEqual (a,b))) >> pure ()


-- A helper function used below in defining the subtyping graph.
getArrowLength :: DMFun -> Maybe Int
getArrowLength (a :->: _) = Just (length a)
getArrowLength _         = Nothing

getFun :: DMMain -> INCRes () [DMTypeOf ForAllKind :@ Maybe [JuliaType]]
getFun (Fun xs) = Finished xs
getFun (TVar _) = Wait
getFun _ = Fail (UserError ())

getTupSize :: DMTypeOf NoFunKind -> INCRes () Int
getTupSize (DMTup xs) = Finished (length xs)
getTupSize (TVar a) = Wait
getTupSize _ = Fail (UserError ())

-- The subtyping graph for our type system.
subtypingGraph :: forall e t k. (SingI k, Typeable k, MonadDMTC t) => EdgeType -> [Edge t (DMTypeOf k)]
subtypingGraph =
  let case0 = testEquality (typeRep @k) (typeRep @MainKind)
      case1 = testEquality (typeRep @k) (typeRep @FunKind)
      case2 = testEquality (typeRep @k) (typeRep @NoFunKind)
      case3 = testEquality (typeRep @k) (typeRep @NumKind)
      case4 = testEquality (typeRep @k) (typeRep @BaseNumKind)
  in case (case0,case1,case2,case3,case4) of
    -- Main Kind
    (Just Refl, _, _, _, _) ->
      \case { IsReflexive NotStructural
              -> []
            ; IsReflexive IsStructural
              -> [ SingleEdge $ do
                     a0 <- newVar
                     a1 <- newVar
                     a0 ⊑! a1
                     return (NoFun a0, NoFun a1),

                   -- we do not have subtyping for arrows
                   MultiEdge getFun $ \a -> do
                     -- a0 <- newVar
                     -- a1 <- newVar
                     -- a0 ⊑! a1
                     return (Fun a, Fun a)
                 ]
            ; NotReflexive
              -> []
            }

    (_,Just Refl, _, _, _) ->
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

    (_,_, Just Refl, _, _) ->
      \case { IsReflexive IsStructural
            -> [
                 (SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return (Numeric a₀, Numeric a₁))
                 , (MultiEdge getTupSize $ \n ->
                   do
                     let f () = do a <- newVar
                                   b <- newVar
                                   a ⊑! b
                                   return (a, b)

                     args <- mapM f (take n $ repeat ())
                     let (args₀, args₁) = unzip args
                     return (DMTup args₀, DMTup args₁)
                     )
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
    (_,_, _, Just Refl, _) ->
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
    (_,_, _, _, Just Refl) ->
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
    (_,_, _, _, _) -> \_ -> []


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
      addConstraint (Solvable (IsSupremum ((lower, lower') :=: TVar upper)))
      logForce "Something very suspicious is happening, at least make sure that this is really the correct approach."
      logForce ("What happens is that we convert the subtyping constraint of " <> show (lower, TVar upper) <> " into the supremum " <> show ((lower, lower') :=: TVar upper))
      logForce "Whyever that is supposed to be correct..."
      return ()
    ((name',lower'):xs) -> error "Not implemented yet: When more than two subtyping constrs are merged to a single supremum. Don't worry, this case shouldn't be hard!"
convertSubtypingToSupremum name _                   = pure ()

-- The actual solving is done here.
-- this simply uses the `findPathM` function from Abstract.Computation.MonadicGraph
-- We return True if we could do something about the constraint
--    return False if nothing could be done
solveSubtyping :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => Symbol -> (DMTypeOf k, DMTypeOf k) -> t Bool
solveSubtyping name path = do
--  collapseSubtypingCycles path

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
    Finished a -> dischargeConstraint @MonadDMTC name >> return True
    Partial a  -> updateConstraint name (Solvable (IsLessEqual a)) >> return True
    Wait       -> convertSubtypingToSupremum name path >> return False -- in this case we try to change this one into a sup
    Fail e     -> throwError (UnsatisfiableConstraint (show (fst path) <> " ⊑ " <> show (snd path) <> "\n\n"
                         <> "Got the following errors while searching the subtyping graph:\n"
                         <> show e))

instance Typeable k => FixedVars TVarOf (IsLessEqual (DMTypeOf k, DMTypeOf k)) where
  fixedVars _ = mempty
instance Typeable k => FixedVars TVarOf (IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)) where
  fixedVars (IsSupremum (_ :=: a)) = freeVars a
instance Typeable k => FixedVars TVarOf (IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)) where
  fixedVars (IsInfimum (_ :=: a)) = freeVars a



tryContractEdge :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => Symbol -> (DMTypeOf k, DMTypeOf k) -> t ()
tryContractEdge name (TVar a,TVar b) = do
  ctrs_all_ab <- filterWithSomeVars [SomeK a,SomeK b] <$> getAllConstraints
  ctrs_relevant <- filterWithSomeVars [SomeK a, SomeK b] <$> fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))

  -- First we check that the only constraints containing a and b are subtyping constraints
  case length ctrs_all_ab == length ctrs_relevant of
    False -> return ()
    True -> do
      -- Next we check that if `a` occurs on the left side of a constraint, then we actually
      -- have the same constraint as the input is
      -- And the same with `b`
      let isGood (_,(x,y)) =
            or
              [ and [TVar a == x, TVar b == y]
              , not (or [SomeK a `elem` freeVars x, SomeK b `elem` freeVars y])
              ]

      let allRelevantAreGood = and (isGood <$> ctrs_relevant)
      case allRelevantAreGood of
        False -> return ()
        True -> do
          unify (TVar a) (TVar b)
          dischargeConstraint name

tryContractEdge name (_,_) = return ()


-- We can solve `IsLessEqual` constraints for DMTypes.
-- NOTE: IsLessEqual is interpreted as a subtyping relation.
instance (SingI k, Typeable k) => Solve MonadDMTC IsLessEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict mode name (IsLessEqual (a,b)) = do
    res <- solveSubtyping name (a,b)
    case (res, mode) of
      (False,SolveAssumeWorst) -> tryContractEdge name (a,b)
      (_,_) -> return ()



------------------------------------------------------------
-- Solve supremum

-- The actual solving is done here.
-- this simply uses the `findSupremumM` function from Abstract.Computation.MonadicGraph
solveSupremum :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> Symbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
solveSupremum graph name ((a,b) :=: x) = do

  -- Here we define which errors should be caught while doing our hypothetical computation.
  let relevance (UnificationError _ _)      = IsGraphRelevant
      relevance (UnsatisfiableConstraint _) = IsGraphRelevant
      relevance _                           = NotGraphRelevant

  -- traceM $ "Starting subtyping solving of " <> show path
  -- let graph = subtypingGraph @t
  -- traceM $ "I have " <> show (length (graph (IsReflexive NotStructural))) <> " candidates."

  -- Executing the computation
  res <- findSupremumM @(Full) relevance (graph) ((a,b) :=: x)

  -- We look at the result and if necessary throw errors.
  case res of
    Finished a -> dischargeConstraint @MonadDMTC name
    Partial a  -> updateConstraint name (Solvable (IsSupremum a))
    Wait       -> return ()
    Fail e     -> throwError (UnsatisfiableConstraint ("sup(" <> show (a) <> ", " <> show b <> ") = " <> show x <> "\n\n"
                         <> "Got the following errors while search the subtyping graph:\n"
                         <> show e))


-- TODO: Check whether this does the correct thing.
instance (SingI k, Typeable k) => Solve MonadDMTC IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) where
  solve_ Dict _ name (IsSupremum ((a,b) :=: x)) = do
     collapseSubtypingCycles (a,x)
     collapseSubtypingCycles (b,x)
     solveSupremum (GraphM subtypingGraph) name ((a,b) :=: x)


-- TODO: Check whether this does the correct thing.
instance (SingI k, Typeable k) => Solve MonadDMTC IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) where
  solve_ Dict _ name (IsInfimum ((a,b) :=: x)) = do
     collapseSubtypingCycles (x,a)
     collapseSubtypingCycles (x,b)
     solveSupremum (oppositeGraph (GraphM subtypingGraph)) name ((a,b) :=: x)


-- find all cyclic subtyping constraints, that is, chains of the form
-- a <= b <= c <= a
-- where for every constraint Sup(a,b) = c we also add additional a <= c and b <= c constraints (likewise for Inf).
-- all types in such a chain can be unified.
collapseSubtypingCycles :: forall k t. (SingI k, Typeable k, IsT MonadDMTC t) => (DMTypeOf k, DMTypeOf k) -> t ()
collapseSubtypingCycles (start, end) = do
  traceM $ ("~~~~ collapsing cycles of " <> show (start,end))
  allSubtypings <- getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))
  allInfima <- getConstraintsByType (Proxy @(IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))
  allSuprema <- getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))

  -- we build a graph of subtype relations, represented by adjacency lists stored in a hash map
  -- nodes are types that appear in <=, Inf or Sup constraints, edges are suptype relations
  let addEdge :: H.HashMap (DMTypeOf k) [DMTypeOf k] -> (DMTypeOf k, DMTypeOf k) -> H.HashMap (DMTypeOf k) [DMTypeOf k]
      addEdge graph (s, e) = case H.lookup s graph of
                               Nothing -> H.insert s [e] graph
                               Just sc -> H.insert s (e:sc) graph

  let graph1 = foldl addEdge H.empty [(s,e) | (_, IsLessEqual (s,e)) <- allSubtypings]
  let graph2 = foldl addEdge graph1 [(s,e) | (_, IsInfimum ((e,_) :=: s)) <- allInfima]
  let graph3 = foldl addEdge graph2 [(s,e) | (_, IsInfimum ((_,e) :=: s)) <- allInfima]
  let graph4 = foldl addEdge graph3 [(s,e) | (_, IsSupremum ((s,_) :=: e)) <- allSuprema]
  let graph = foldl addEdge graph4 [(s,e) | (_, IsSupremum ((_,s) :=: e)) <- allSuprema]

  traceM $ ("~~~~ graph is " <> show graph)--(H.insert end (start:[start]) H.empty))

  -- a simple search for the start node, returning all nodes on all paths from the
  -- input node to the start node. invoked with the end nodes successors as input, it gives all
  -- nodes that lie on a path from end to start. as the constraint start <= end is
  -- given, this means all nodes returned are on a cycle
  let allNodesFrom :: DMTypeOf k -> [DMTypeOf k]
      allNodesFrom s | s == start = [s] -- reached start from end, this is the cycles we like
      allNodesFrom s | s == end   = [] -- is an end-end cycle
      allNodesFrom s              = case H.lookup s graph of
                                       Just scs -> case concat (map allNodesFrom scs) of
                                                      [] -> []
                                                      sc -> (s : sc)
                                       _ -> [] -- has no successors

  -- all successors of the end node
  let ssucc = case H.lookup end graph of
                   Just s -> s
                   _ -> []

  -- find all paths from the ssucc to the start node, hence cycles that contain the start-end-edge
  let cycles = (concat (map allNodesFrom ssucc))

  traceM $ ("~~~~ found cycles " <> show cycles <> " unifying with " <> show end <> "\n")

  -- unify all types in all cycles with the end type
  foldM unify end cycles

  return ()
