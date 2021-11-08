
module DiffMu.Typecheck.Subtyping where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.Context
import DiffMu.Core.Logging
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification


import qualified Data.HashMap.Strict as H

import Debug.Trace

import qualified Prelude as P




---------------------------------------------------------------------
-- "Non strict subtyping"

-- An abbreviation for adding a subtyping constraint.
(⊑!) :: (SingI k, Typeable k, MonadDMTC t) => DMTypeOf k -> DMTypeOf k -> t ()
(⊑!) a b = addConstraint (Solvable (IsLessEqual (a,b))) >> pure ()


-- A helper function used below in defining the subtyping graph.
getArrowLength :: DMFun -> Maybe Int
getArrowLength (a :->: _) = Just (length a)
getArrowLength _         = Nothing

getFun :: DMMain -> INCRes () [DMTypeOf FunKind :@ Maybe [JuliaType]]
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
            ; _
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
                 , SingleEdge $
                   do nrm <- newVar
                      clp <- newVar
                      n <- newVar
                      a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return ((DMVec nrm clp n a₀), (DMVec nrm clp n a₁))
                      {-
                 , SingleEdge $ -- this is the conv rule made implicit, for converting DMData to DMReal
                   do nrm <- newVar
                      clp <- newVar
                      n <- newVar
                      m <- newVar
                      return ((DMMat nrm (Clip clp) n m (Numeric DMData)), (DMMat clp U n m (Numeric (NonConst DMReal))))
                    -}
                 , SingleEdge $
                   do m <- newVar
                      a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return ((DMParams m a₀), (DMParams m a₁)) -- TODO maybe we need conv rule for params?
                 , SingleEdge $
                   do nrm <- newVar
                      clp <- newVar
                      m <- newVar
                      a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return ((DMGrads nrm clp m a₀), (DMGrads nrm clp m a₁))
                 , SingleEdge $ -- this is the conv rule made implicit, for converting DMData to DMReal
                   do nrm <- newVar
                      clp <- newVar
                      m <- newVar
                      return ((DMGrads nrm (Clip clp) m (Numeric DMData)), (DMGrads clp U m (Numeric (NonConst DMReal))))
                 , SingleEdge $ -- this is the fr-sens rule made implicit, for converting from L1 norm to any other
                   do nrm <- newVar
                      clp <- newVar
                      t <- newVar
                      m <- newVar
                      return ((DMGrads L1 clp m (Numeric t)), (DMGrads nrm clp m (Numeric t)))
                  ]
            ; _ -> []
            }

    -- Num Kind
    (_,_, _, Just Refl, _) ->
      \case { IsReflexive IsStructural
              -> []
            ; IsReflexive IsLeftStructural
              -> [ SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return (NonConst a₀, NonConst a₁)
                 ]
            ; IsReflexive IsRightStructural
               -> [SingleEdge $
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
            ; _ -> []
            }

    -- BaseNum Kind
    (_,_, _, _, Just Refl) ->
      \case { IsReflexive IsRightStructural
              -> [ SingleEdge $ return (DMInt, DMInt) ]
            ; IsReflexive IsLeftStructural
              -> [ SingleEdge $ return (DMReal, DMReal) ]
            ; NotReflexive
              -> [ SingleEdge $ return (DMInt, DMReal)
                 ]
            ; _ -> []
            }
    (_,_, _, _, _) -> \_ -> []


-- If we have a bunch of subtyping constraints {β ≤ α, γ ≤ α, δ ≤ α} then it
-- /should/ be allowed to turn this into a supremum constraint, i.e. "sup{β,γ,δ} = α"
-- in the case that [... when exactly? ...]
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
    ((name',lower'):xs) -> internalError $ "Not implemented yet: When more than two subtyping constrs are merged to a single supremum. Don't worry, this case shouldn't be hard!"
convertSubtypingToSupremum name _                   = pure ()

-- The actual solving is done here.
-- this simply uses the `findPathM` function from Abstract.Computation.MonadicGraph
-- We return True if we could do something about the constraint
--    return False if nothing could be done
solveSubtyping :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => Symbol -> (DMTypeOf k, DMTypeOf k) -> t ()
solveSubtyping name path = withLogLocation "Subtyping" $ do

  -- Here we define which errors should be caught while doing our hypothetical computation.
  let relevance (UnificationError _ _)      = IsGraphRelevant
      relevance (UnsatisfiableConstraint _) = IsGraphRelevant
      relevance _                           = NotGraphRelevant

  -- traceM $ "Starting subtyping solving of " <> show path
  let graph = subtypingGraph @t
  -- traceM $ "I have " <> show (length (graph (IsReflexive NotStructural))) <> " candidates."

  -- Executing the computation
  (res) <- findPathM @(Full) relevance (GraphM graph) path

  -- We look at the result and if necessary throw errors.
  case res of
    Finished a     -> do
      log $ "Subtyping computation of " <> show path <> " finished with result " <> show res <> ". Discharging constraint " <> show name
      dischargeConstraint @MonadDMTC name
    Partial (a,_)  -> do
      log $ "Subtyping computation of " <> show path <> " gave partial result " <> show res <> ". Updating constraint " <> show name
      updateConstraint name (Solvable (IsLessEqual a))
    Wait           -> do
      log $ "Subtyping computation of " <> show path <> " returned `Wait`. Keeping constraint as is."
      npath <- normalize path
      log $ "(With normalizations applied the constraint is now " <> show npath <> " ; it should be the same as the input.)"
      convertSubtypingToSupremum name path -- in this case we try to change this one into a sup
    Fail e         -> throwError (UnsatisfiableConstraint (show (fst path) <> " ⊑ " <> show (snd path) <> "\n\n"
                         <> "Got the following errors while searching the subtyping graph:\n"
                         <> show e))

instance Typeable k => FixedVars TVarOf (IsLessEqual (DMTypeOf k, DMTypeOf k)) where
  fixedVars _ = mempty
instance Typeable k => FixedVars TVarOf (IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)) where
  fixedVars (IsSupremum (_ :=: a)) = freeVars a
instance Typeable k => FixedVars TVarOf (IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)) where
  fixedVars (IsInfimum (_ :=: a)) = freeVars a


data ContractionAllowed = ContractionAllowed | ContractionDisallowed

getBottoms :: forall k. (SingI k, Typeable k) => [DMTypeOf k]
getBottoms =
  case testEquality (typeRep @k) (typeRep @BaseNumKind) of
     Just Refl -> [DMInt]
     _ -> []

getTops :: forall k. (SingI k, Typeable k) => [DMTypeOf k]
getTops =
  case testEquality (typeRep @k) (typeRep @BaseNumKind) of
     Just Refl -> [DMReal]
     _ -> []

type TypeGraph k = H.HashMap (DMTypeOf k) [DMTypeOf k]

getCurrentConstraintSubtypingGraph :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => t (TypeGraph k)
getCurrentConstraintSubtypingGraph = do

  ctrs_relevant <- fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))
  ctrs_relevant_max <- fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))
  ctrs_relevant_min <- fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))

  let subFromSub (_,(a,b)) = [(a,b)]
  let subFromMax (_,((a,b) :=: c)) = [(a,c),(b,c)]
  let subFromMin (_,((a,b) :=: c)) = [(c,a),(c,b)]

  let edges = (ctrs_relevant >>= subFromSub)
              <> (ctrs_relevant_max >>= subFromMax)
              <> (ctrs_relevant_min >>= subFromMin)

  -- we build a graph of subtype relations, represented by adjacency lists stored in a hash map
  -- nodes are types that appear in <=, Inf or Sup constraints, edges are suptype relations
  -- for every node we also add edges from the bottom types (if existent for kind k) an to the top types.
  let addEdge :: H.HashMap (DMTypeOf k) [DMTypeOf k] -> (DMTypeOf k, DMTypeOf k) -> H.HashMap (DMTypeOf k) [DMTypeOf k]
      addEdge graph (s, e) = let
            tops = getTops @k
            -- add edges [s -> t for t in tops] and edge s -> e.
            graph'  = case H.lookup s graph of
                               Nothing -> H.insert s (e:tops) graph
                               Just sc -> H.insert s (e:sc) graph -- tops were added already in this case

            -- also add edges [e -> t for t in tops].
            graph'' = case H.lookup e graph' of
                               Nothing | not (null tops) -> H.insert e tops graph'
                               _ -> graph' -- if e has outgoing edges already, they were added above and tops are in.
         in graph''


  let graph = foldl addEdge H.empty edges
  let graph' = foldl addEdge graph [(b, e) | b <- getBottoms @k, e <- (H.keys graph)] -- add edges from bottoms to all other nodes.
  return graph'



-- all paths in the graph of length <= N connecting a0 and a1
allPathsN :: Int -> TypeGraph k -> (DMTypeOf k, DMTypeOf k) -> Maybe [[DMTypeOf k]]
allPathsN _ _ (a0,a1) | a0 == a1  = Just [[a0,a1]]
allPathsN 0 _ (a0,a1) = Nothing
allPathsN n graph (a0,a1) =
  let succ = case H.lookup a0 graph of -- successors of a0
                      Nothing -> []
                      Just s -> s
      smallerPaths = [allPathsN (n - 1) graph (b,a1) | b <- succ] -- all maybe-paths of length N-1 from successors to a1
      goodPaths = concat [p | Just p <- smallerPaths] -- the ones that actually exist
  in case goodPaths of
    [] -> Nothing
    ps -> Just [(a0:p) | p <- ps]


-- all paths in the graph connecting a0 and a1.
allPaths :: TypeGraph k -> (DMTypeOf k, DMTypeOf k) -> Maybe [[DMTypeOf k]]
allPaths graph (a0,a1) = allPathsN ((H.size graph) - 1) graph (a0,a1)


traceNot a x = x

-- given two vertices in the subtype relation graph, find all vertices that have an incoming
-- edge from both of them.
completeDiamondDownstream :: (SingI k, Typeable k) => TypeGraph k -> (DMTypeOf k, DMTypeOf k) -> [(DMTypeOf k, [DMTypeOf k])]
completeDiamondDownstream graph (a0,a1) =
  let graph'      = traceNot ("graph: " <> show graph) graph
      -- all one-edge long paths from any graph vertex from both a0 and a1, or Nothing if none exist
      doublePaths = [(allPathsN 1 graph (a0, x), allPathsN 1 graph (a1, x), x) | x <- (H.keys graph)]
      doublePaths' = traceNot ("doublePaths: " <> show doublePaths) doublePaths
      -- all x that actually have an edge.
      goodPaths   = [(x,concat (el1 <> el2)) | (Just el1, Just el2, x) <- doublePaths']
      goodPaths' = traceNot ("goodPaths: " <> show goodPaths) goodPaths
  in goodPaths'

-- given two vertices in the subtype relation graph, find all vertices that have an outgoing
-- edge from both of them.
completeDiamondUpstream :: (SingI k, Typeable k) => TypeGraph k -> (DMTypeOf k, DMTypeOf k) -> [(DMTypeOf k, [DMTypeOf k])]
completeDiamondUpstream graph (a0,a1) =
  let graph'      = traceNot ("graph: " <> show graph) graph
      -- all one-edge long paths from any graph vertex to both a0 and a1, or Nothing if none exist
      doublePaths = [(allPathsN 1 graph (x, a0), allPathsN 1 graph (x, a1), x) | x <- (H.keys graph)]
      doublePaths' = traceNot ("doublePaths: " <> show doublePaths) doublePaths
      -- all x that actually have an edge.
      goodPaths   = [(x,concat (el1 <> el2)) | (Just el1, Just el2, x) <- doublePaths']
      goodPaths' = traceNot ("goodPaths: " <> show goodPaths) goodPaths
  in goodPaths'



checkContractionAllowed :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => [(DMTypeOf k)] -> (DMTypeOf k, DMTypeOf k) -> t ContractionAllowed
checkContractionAllowed contrTypes (TVar a, TVar b) = do
  let acceptOnlyVar (TVar a) = Just a
      acceptOnlyVar _        = Nothing

      -- We check that all types which we want to contract are type variables
      -- if this returns `Just [xs]` then all types were actually vars
      contrVars' = mapM acceptOnlyVar contrTypes

  -- The actual case distinction
  case contrVars' of
    Nothing -> do
      debug "Contraction not allowed because the candidate list contains types which are not TVars."
      return ContractionDisallowed
    (Just contrVars') -> do
      let contrVars = (SomeK <$> contrVars')

      ctrs_all_ab <- filterWithSomeVars contrVars <$> getAllConstraints
      ctrs_relevant <- filterWithSomeVars contrVars <$> fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsLessEqual (DMTypeOf k, DMTypeOf k)))
      ctrs_relevant_max <- filterWithSomeVars contrVars <$> fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))
      ctrs_relevant_min <- filterWithSomeVars contrVars <$> fmap (second runConstr) <$> getConstraintsByType (Proxy @(IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k)))

      -- First we check that the only constraints containing contrVars are
      -- {subtyping,sup,inf} constraints
      let m = length ctrs_all_ab
          n = length ctrs_relevant P.+ length ctrs_relevant_max P.+ length ctrs_relevant_min
      case m == n of
        False -> return ContractionDisallowed
        True -> do
          -- Get all subtyping pairs
          let subFromSub (_,(a,b)) = [(a,b)]
          let subFromMax (_,((a,b) :=: c)) = [(a,c),(b,c)]
          let subFromMin (_,((a,b) :=: c)) = [(c,a),(c,b)]

          let subs = (ctrs_relevant >>= subFromSub)
                    <> (ctrs_relevant_max >>= subFromMax)
                    <> (ctrs_relevant_min >>= subFromMin)

          --
          -- NOTE: In the following, we only deal with edges here which are relevant,
          --       i.e. contain some of the contraction-variables
          --
          -- Next we check that all subtyping edges are good
          -- i.e., an edge is good if one of the following cases appears:
          let isGood (x,y) =
                or
                  [ -- the edge is fully part of the diamond to be contracted
                    and [x `elem` (contrTypes), y `elem` (contrTypes)]

                    -- the edge attaches to the input of the diamond, and in it's own input
                    -- does not reference any contraction-variables
                  , and [y == TVar a, freeVars x `intersect` contrVars == []]

                    -- the edge attaches to the output of the diamond, and in it's own output
                    -- does not reference any contraction-variables
                  , and [x == TVar b, freeVars y `intersect` contrVars == []]
                  ]

          let allRelevantAreGood = and (isGood <$> subs)
          case allRelevantAreGood of
            False -> return ContractionDisallowed
            True -> return ContractionAllowed

checkContractionAllowed _ _ = return ContractionDisallowed


-- We can solve `IsLessEqual` constraints for DMTypes.
-- NOTE: IsLessEqual is interpreted as a subtyping relation.
instance (SingI k, Typeable k) => Solve MonadDMTC IsLessEqual (DMTypeOf k, DMTypeOf k) where
  solve_ Dict SolveSpecial name (IsLessEqual (a,b)) = return ()
  solve_ Dict SolveExact name (IsLessEqual (a,b))  = solveSubtyping name (a,b)
  solve_ Dict SolveGlobal name (IsLessEqual path) = collapseSubtypingCycles path
  solve_ Dict SolveAssumeWorst name (IsLessEqual (a,b)) = return ()
  solve_ Dict SolveFinal name (IsLessEqual (a,b)) = do
    -- if we are in solve final, we try to contract the edge
        debug $ "Computing LessEqual: " <> show (a,b)
        allowed <- checkContractionAllowed [a,b] (a,b)
        case allowed of
          ContractionAllowed -> unify a b >> return ()
          ContractionDisallowed -> return ()





--------------------------------------------
-- wrapper for computing supremum
solveSupremum :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> Symbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
solveSupremum graph name ((a,b) :=: x) = callMonadicGraphSupremum graph name ((a,b) :=: x)

--------------------------------------------
-- wrapper for computing infimum
solveInfimum :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> Symbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
solveInfimum graph name ((a,b) :=: x) = callMonadicGraphSupremum (oppositeGraph graph) name ((a,b) :=: x)


----------------------------------------------------------------------------------------
-- solvers for special cases
-------------------
-- supremum
solveSupremumSpecial :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> Symbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
-- if one input is equal to the output we can skip the supremum computation,
-- then we only have to create a subtyping constraint
solveSupremumSpecial graph name ((a,b) :=: x) | a == x = do
  b ≤! x
  dischargeConstraint name

solveSupremumSpecial graph name ((a,b) :=: x) | b == x = do
  a ≤! x
  dischargeConstraint name

solveSupremumSpecial graph name ((a,b) :=: x) | elem a (getBottoms @k) = do
  unify b x
  dischargeConstraint name

solveSupremumSpecial graph name ((a,b) :=: x) | elem b (getBottoms @k) = do
  unify a x
  dischargeConstraint name

solveSupremumSpecial graph name ((a,b) :=: x) | otherwise = return ()

-------------------
-- infimum
solveInfimumSpecial :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> Symbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
solveInfimumSpecial graph name ((a,b) :=: x) | a == x = do
  x ≤! b
  dischargeConstraint name

solveInfimumSpecial graph name ((a,b) :=: x) | b == x = do
  x ≤! a
  dischargeConstraint name

solveInfimumSpecial graph name ((a,b) :=: x) | elem a (getTops @k) = do
  unify b x
  dischargeConstraint name

solveInfimumSpecial graph name ((a,b) :=: x) | elem b (getTops @k) = do
  unify a x
  dischargeConstraint name

solveInfimumSpecial graph name ((a,b) :=: x) | otherwise = return ()


--------------------------------------------
-- The actual solving is done here.
-- we call the `findSupremumM` function from Abstract.Computation.MonadicGraph
callMonadicGraphSupremum :: forall t k. (SingI k, Typeable k, IsT MonadDMTC t) => GraphM t (DMTypeOf k) -> Symbol -> ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) -> t ()
callMonadicGraphSupremum graph name ((a,b) :=: x) = do

  -- Here we define which errors should be caught while doing our hypothetical computation.
  let relevance (UnificationError _ _)      = IsGraphRelevant
      relevance (UnsatisfiableConstraint _) = IsGraphRelevant
      relevance _                           = NotGraphRelevant

  -- traceM $ "Starting subtyping solving of " <> show path
  -- let graph = subtypingGraph @t
  -- traceM $ "I have " <> show (length (graph (IsReflexive NotStructural))) <> " candidates."

  -- Executing the computation
  res <- findSupremumM @(Full) relevance (graph) ((a,b) :=: x, IsShortestPossiblePath)

  -- We look at the result and if necessary throw errors.
  case res of
    Finished a -> dischargeConstraint @MonadDMTC name
    Partial a  -> updateConstraint name (Solvable (IsSupremum a))
    Wait       -> return ()
    Fail e     -> throwError (UnsatisfiableConstraint ("sup(" <> show (a) <> ", " <> show b <> ") = " <> show x <> "\n\n"
                         <> "Got the following errors while search the subtyping graph:\n"
                         <> show e))


unifyAll :: (Typeable k, IsT MonadDMTC t) => [DMTypeOf k] -> t ()
unifyAll ([]) = return ()
unifyAll (x:[]) = return ()
unifyAll (x:y:vars) = do
  unify x y
  unifyAll (y:vars)

-- TODO: Check whether this does the correct thing.
instance (SingI k, Typeable k) => Solve MonadDMTC IsSupremum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) where
  solve_ Dict SolveExact name (IsSupremum ((a,b) :=: y)) = solveSupremum (GraphM subtypingGraph) name ((a,b) :=: y)
  solve_ Dict SolveSpecial name (IsSupremum ((a,b) :=: y)) = solveSupremumSpecial (GraphM subtypingGraph) name ((a,b) :=: y)

  solve_ Dict SolveGlobal name (IsSupremum ((a,b) :=: y)) = do
    collapseSubtypingCycles (a,y)
    collapseSubtypingCycles (b,y)

  solve_ Dict SolveFinal name (IsSupremum ((a,b) :=: y)) = do
    debug $ "Computing supremum (final solving mode): " <> show ((a,b) :=: y)

    graph <- getCurrentConstraintSubtypingGraph
    let contrCandidates = completeDiamondUpstream graph (a,b)
    let f (x,contrVars) = do

              debug $ "Trying to contract from " <> show (x,y) <> " with contrVars: " <> show contrVars
              allowed <- checkContractionAllowed (y:contrVars) (x,y)
              case allowed of
                ContractionAllowed -> unifyAll (y:contrVars) >> return True
                ContractionDisallowed -> return False

    let g f [] = return ()
        g f (x:xs) = do
          res <- f x
          case res of
            True -> return ()
            False -> g f xs

    g f contrCandidates

  solve_ Dict SolveAssumeWorst name (IsSupremum ((a,b) :=: y)) = return ()


-- TODO: Check whether this does the correct thing.
instance (SingI k, Typeable k) => Solve MonadDMTC IsInfimum ((DMTypeOf k, DMTypeOf k) :=: DMTypeOf k) where
  solve_ Dict SolveExact name (IsInfimum ((a,b) :=: x)) = solveInfimum (GraphM subtypingGraph) name ((a,b) :=: x)
  solve_ Dict SolveSpecial name (IsInfimum ((a,b) :=: x)) = solveInfimumSpecial (GraphM subtypingGraph) name ((a,b) :=: x)
  solve_ Dict SolveGlobal name (IsInfimum ((a,b) :=: x)) = do
    collapseSubtypingCycles (x,a)
    collapseSubtypingCycles (x,b)

  solve_ Dict SolveFinal name (IsInfimum ((a,b) :=: x)) = do
    debug $ "Computing infimum (final solving): " <> show ((a,b) :=: x)
    graph <- getCurrentConstraintSubtypingGraph

    let contrCandidates = completeDiamondDownstream graph (a,b)
    let f (y,contrVars) = do

              debug $ "Trying to contract from " <> show (x,y) <> " with contrVars: " <> show contrVars
              allowed <- checkContractionAllowed (x:contrVars) (x,y)
              case allowed of
                ContractionAllowed -> unifyAll (x:contrVars) >> return True
                ContractionDisallowed -> return False

    let g f [] = return ()
        g f (x:xs) = do
          res <- f x
          case res of
            True -> return ()
            False -> g f xs

    g f contrCandidates

    solveInfimum (GraphM subtypingGraph) name ((a,b) :=: x)

  solve_ Dict SolveAssumeWorst name (IsInfimum ((a,b) :=: x)) = return ()

-- find all cyclic subtyping constraints, that is, chains of the form
-- a <= b <= c <= a
-- where for every constraint Sup(a,b) = c we also add additional a <= c and b <= c constraints (likewise for Inf).
-- all types in such a chain can be unified.
collapseSubtypingCycles :: forall k t. (SingI k, Typeable k, IsT MonadDMTC t) => (DMTypeOf k, DMTypeOf k) -> t ()
collapseSubtypingCycles (start, end) = withLogLocation "Subtyping" $ do
  debug $ ("~~~~ collapsing cycles of " <> show (start,end))
  graph <- getCurrentConstraintSubtypingGraph

  debug $ ("~~~~ graph is " <> show graph)--(H.insert end (start:[start]) H.empty))

  -- find all paths from the ssucc to the start node, hence cycles that contain the start-end-edge
  let cycles = concat (allPaths graph (end, start))

  debug $ ("~~~~ found cycles " <> show cycles <> " unifying with " <> show end <> "\n")

  -- unify all types in all cycles with the end type
  unifyAll (concat cycles)

  return ()
