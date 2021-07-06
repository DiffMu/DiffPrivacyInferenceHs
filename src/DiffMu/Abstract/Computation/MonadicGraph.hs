
module DiffMu.Abstract.Computation.MonadicGraph where

import DiffMu.Prelude
import DiffMu.Abstract.Computation.INC
import DiffMu.Abstract.Class.Constraint
import DiffMu.Abstract.Class.IsT
import DiffMu.Abstract.Class.Log
import DiffMu.Abstract.Class.Unify

import Debug.Trace

-- Since our nodes/edges live in a monad, the source/target of an edge need not necessarily be *really* equal, for the edge to having to be considered as reflexive.
-- Thus we add this as annotation.
data EdgeType = IsReflexive Structurality | NotReflexive

-- A reflexive edge is structural if matching on one side already is enough to know that
-- we got the correct edge.
-- For example, the (a₀ -> b₀ ⊑ a₁ -> b₁) rule/edge is structural, because an arrow is
-- only subtype of an arrow.
-- On the other hand, the rule (Const s₀ a₀ ⊑ Const s₁ a₁) is not structural, because
-- in the case of checking (Const s₀ a₀ ⊑ b) even though we matched on the left hand side,
-- it is still possible that the rule (Const s₀ a₀ ⊑ NonConst a₀) is the one which actually
-- should be used.
data Structurality = IsStructural | NotStructural

newtype EdgeFamily m a b = EdgeFamily (a -> m (Maybe b), b -> m (a,a))

data Edge m a where
  SingleEdge :: m (a,a) -> Edge m a
  MultiEdge :: Eq b => (a -> Maybe b) -> (b -> m (a,a)) -> Edge m a


newtype GraphM m a = GraphM (EdgeType -> [Edge m a])

data ErrorRelevance = IsGraphRelevant | NotGraphRelevant



oppositeGraph :: forall m a. Monad m => GraphM m a -> GraphM m a
oppositeGraph (GraphM graph) = GraphM (opp graph)
  where oppositeEdge :: Edge m a -> Edge m a
        oppositeEdge (SingleEdge x) = SingleEdge ((\(a,b) -> (b,a)) <$> x)
        oppositeEdge (MultiEdge pre fam) = MultiEdge pre ((\x -> (\(a,b) -> (b,a)) <$> x) . fam)

        opp :: (EdgeType -> [Edge m a]) -> (EdgeType -> [Edge m a])
        opp f ty = oppositeEdge <$> f ty

-- findPathM :: forall s m e a. (Show e, Show a, MonadError e m, MonadState s m, MonoidM m a, CheckNeutral m a) => (e -> ErrorRelevance) -> GraphM m a -> (a,a) -> m (INCRes e (a,a))
findPathM :: forall s m isT e a. (Show e, Show a, MonadConstraint isT m, IsT isT m, Normalize m a, MonadNormalize m, MonadError e m, MonadState s m, MonadLog m, Unify isT a, CheckNeutral m a) => (e -> ErrorRelevance) -> GraphM m a -> (a,a) -> m (INCRes e (a,a))
findPathM relevance (GraphM g) path =
  let both (Just a) (Just b) | a == b = Just a
      both _ _                          = Nothing

      atLeastOne (Just a) Nothing = Just a
      atLeastOne Nothing (Just b) = Just b
      atLeastOne (Just a) (Just b) | a == b = Just a
      atLeastOne _ _ = Nothing

      checkSingle getIdx a x =
        do ia <- getIdx a
           case ia of
             Just c -> x c
             Nothing -> return Wait

      -- we check the neutrality of a and b
      -- And wait either - only if both are not neutral
      --          or     - if at least one is not neutral
      checkPair op getIdx a b x = do
        ia <- getIdx a
        ib <- getIdx b
        case (op ia ib) of
          Just c -> x c
          Nothing -> return Wait


      checkByStructurality IsStructural  getIdx a b x = checkPair atLeastOne getIdx a b x
      checkByStructurality NotStructural getIdx a b x = checkPair both       getIdx a b x


      f_refl :: Eq b => Structurality -> EdgeFamily m a b -> (a,a) -> m (INCRes e (a,a))
      f_refl s (EdgeFamily (getIdx,edge)) (start,goal) =
        checkByStructurality s getIdx start goal $ \idx -> do
          (n₀, n₁) <- edge idx
          n₀'' <- unify start n₀
          n₁'' <- unify n₁ goal
          return (Finished (n₀'', n₁''))

      fromLeft :: EdgeFamily m a b -> (a,a) -> m (INCRes e (a,a))
      fromLeft (EdgeFamily (getIdx,edge)) (start,goal) =
        checkSingle getIdx start $ \idx -> do
          (n₀,n₁) <- edge idx
          n₀'' <- unify start n₀
          return (Partial (n₁, goal))

      fromRight :: EdgeFamily m a b -> (a,a) -> m (INCRes e (a,a))
      fromRight (EdgeFamily (getIdx,edge)) (start,goal) =
        checkSingle getIdx goal $ \idx -> do
          (n₀,n₁) <- edge idx
          n₁'' <- unify n₁ goal
          return (Partial (start, n₀))

      catchRelevant :: forall a b. (a -> m (INCRes e a)) -> (a -> m (INCRes e a))
      catchRelevant f a =
        catchError (f a) $ \e -> case relevance e of
                                   IsGraphRelevant -> return (Fail (UserError e))
                                   NotGraphRelevant -> throwError e


      checkNeutrality a = do
        na <- checkNeutral a
        case na of
          True -> return Nothing
          False -> return $ Just ()

      checkNeutrality' getIdx a = do
        na <- checkNeutral a
        case na of
          True -> return Nothing
          False -> return (getIdx a)

      withFamily :: forall x. (forall b. Eq b => EdgeFamily m a b -> x) -> Edge m a -> x
      withFamily f (SingleEdge edge)       = f (EdgeFamily (checkNeutrality, \() -> edge))
      withFamily f (MultiEdge getIdx edge) = f (EdgeFamily (checkNeutrality' getIdx, edge))

      computations = [catchRelevant (withFamily (f_refl IsStructural) a)  | a <- g (IsReflexive IsStructural)]
                  <> [catchRelevant (withFamily (f_refl NotStructural) a) | a <- g (IsReflexive NotStructural)]
                  <> [catchRelevant (withFamily fromLeft a)   | a <- g NotReflexive]
                  <> [catchRelevant (withFamily fromRight a)  | a <- g NotReflexive]

  in evalINC (INC computations) path


findSupremumM :: forall s m isT e a. (Show e, Show a, MonadError e m, MonadConstraint isT m, IsT isT m, Unify isT (a), Normalize m a, MonadNormalize m, MonadState s m, MonadLog m, CheckNeutral m a) => (e -> ErrorRelevance) -> GraphM m a -> (a,a,a) -> m (INCRes e (a,a,a))
findSupremumM relevance (GraphM graph) (a,b,x) =
  let
    -------------
    -- This is copy paste from above

      both (Just a) (Just b) | a == b = Just a
      both _ _                          = Nothing

      atLeastOne (Just a) Nothing = Just a
      atLeastOne Nothing (Just b) = Just b
      atLeastOne (Just a) (Just b) | a == b = Just a
      atLeastOne _ _ = Nothing

      checkPair op getIdx a b x = do
        ia <- getIdx a
        ib <- getIdx b
        case (op ia ib) of
          Just c -> x c
          Nothing -> return Wait


      checkByStructurality IsStructural  getIdx a b x = checkPair atLeastOne getIdx a b x
      checkByStructurality NotStructural getIdx a b x = checkPair both       getIdx a b x

      catchRelevant :: forall a b. (a -> m (INCRes e a)) -> (a -> m (INCRes e a))
      catchRelevant f a =
        catchError (f a) $ \e -> case relevance e of
                                   IsGraphRelevant -> return (Fail (UserError e))
                                   NotGraphRelevant -> throwError e
      checkNeutrality a = do
        na <- checkNeutral a
        case na of
          True -> return Nothing
          False -> return $ Just ()

      checkNeutrality' getIdx a = do
        na <- checkNeutral a
        case na of
          True -> return Nothing
          False -> return (getIdx a)

      withFamily :: forall x. (forall b. Eq b => EdgeFamily m a b -> x) -> Edge m a -> x
      withFamily f (SingleEdge edge)       = f (EdgeFamily (checkNeutrality, \() -> edge))
      withFamily f (MultiEdge getIdx edge) = f (EdgeFamily (checkNeutrality' getIdx, edge))

   -- end copy paste
   -------------

      fromLeft :: Eq b => Bool -> EdgeFamily m a b -> (a,a,a) -> m (INCRes e (a,a,a))
      fromLeft failhere (EdgeFamily (getIdx,edge)) (start₀,start₁,goal) =
        checkPair both getIdx start₀ start₁ $ \idx -> do
          openNewConstraintSet
          ((n₀, n₁)) <- edge idx
          n₀'' <- unify start₀ n₀
          (rpath) <- findPathM relevance (GraphM graph) (start₁,n₁)
          solveAllConstraints SolveExact
          log "============ AFTER solving all new constraints >>>>>>>>>>>>>>>>"
          logPrintConstraints
          closedRes <- mergeTopConstraintSet
          case closedRes of
            ConstraintSet_WasNotEmpty -> return Wait
            ConstraintSet_WasEmpty -> case rpath of
              Wait -> return Wait
              Fail e -> case failhere of
                          -- If have a reflexive edge, and failed, then we do not continue
                          True  -> return $ Fail e
                          -- If we mereley had a non-reflexive edge, we try again with the target of that edge
                          False -> traceShow ("=> [Left] Finding path " <> show (start₁,n₁) <> " failed. Now computing sup " <> show (n₁, start₁, goal)) (findSupremumM relevance (GraphM graph) (n₁, start₁, goal))
              Partial x -> return Wait
              Finished (a₀,a₁) -> do goal' <- unify goal a₁
                                     return $ Finished (n₀'' , a₀ , goal')

      fromRight :: Eq b => Bool -> EdgeFamily m a b -> (a,a,a) -> m (INCRes e (a,a,a))
      fromRight failhere (EdgeFamily (getIdx,edge)) (start₀,start₁,goal) =
        checkPair both getIdx start₀ start₁ $ \idx -> do
          openNewConstraintSet
          (n₀, n₁) <- edge idx
          n₀'' <- unify start₁ n₀
          (rpath) <- findPathM relevance (GraphM graph) (start₀,n₁)
          solveAllConstraints SolveExact
          log "============ AFTER solving all new constraints >>>>>>>>>>>>>>>>"
          logPrintConstraints
          closedRes <- mergeTopConstraintSet
          case closedRes of
            ConstraintSet_WasNotEmpty -> return Wait
            ConstraintSet_WasEmpty -> case rpath of
              Wait -> return Wait
              Fail e -> case failhere of
                          -- If have a reflexive edge, and failed, then we do not continue
                          True  -> return $ Fail e
                          -- If we mereley had a non-reflexive edge, we try again with the target of that edge
                          False -> do
                            log ("=> [Right] Finding path " <> show (start₀,n₁) <> " failed. Now computing sup " <> show (start₀, n₁, goal))
                            (findSupremumM relevance (GraphM graph) (start₀, n₁, goal))
              Partial x -> return Wait
              Finished (a₀,a₁) -> do goal' <- unify goal a₁
                                     return $ Finished (a₀ , n₀'' , goal')


      computations =  [catchRelevant (withFamily (fromLeft True) a)  | a <- graph (IsReflexive IsStructural)]
                     <> [catchRelevant (withFamily (fromLeft True) a)  | a <- graph (IsReflexive NotStructural)]
                     <> [catchRelevant (withFamily (fromLeft False) a)  | a <- graph (NotReflexive)]

                     <> [catchRelevant (withFamily (fromRight True) a)  | a <- graph (IsReflexive IsStructural)]
                     <> [catchRelevant (withFamily (fromRight True) a)  | a <- graph (IsReflexive NotStructural)]
                     <> [catchRelevant (withFamily (fromRight False) a)  | a <- graph (NotReflexive)]


  in withLogLocation "INC" $ evalINC (INC computations) (a,b,x)

findInfimumM :: forall s m isT e a. (Show e, Show a, MonadError e m, MonadConstraint isT m, IsT isT m, Unify isT (a), Normalize m a, MonadNormalize m, MonadState s m, MonadLog m, CheckNeutral m a) => (e -> ErrorRelevance) -> GraphM m a -> (a,a,a) -> m (INCRes e (a,a,a))
findInfimumM relevance graph z = findSupremumM relevance (oppositeGraph graph) z

