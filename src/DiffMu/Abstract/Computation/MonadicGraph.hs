
module DiffMu.Abstract.Computation.MonadicGraph where

import DiffMu.Prelude
import DiffMu.Abstract.Computation.INC

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

findPathM :: forall s m e a. (Show e, Show a, MonadError e m, MonadState s m, MonoidM m a, CheckNeutral m a) => (e -> ErrorRelevance) -> GraphM m a -> (a,a) -> m (INCRes e (a,a))
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
          n₀'' <- start ⋆ n₀
          n₁'' <- n₁ ⋆ goal
          return (Finished (n₀'', n₁''))

      fromLeft :: EdgeFamily m a b -> (a,a) -> m (INCRes e (a,a))
      fromLeft (EdgeFamily (getIdx,edge)) (start,goal) =
        checkSingle getIdx start $ \idx -> do
          (n₀,n₁) <- edge idx
          n₀'' <- start ⋆ n₀
          return (Partial (n₁, goal))

      fromRight :: EdgeFamily m a b -> (a,a) -> m (INCRes e (a,a))
      fromRight (EdgeFamily (getIdx,edge)) (start,goal) =
        checkSingle getIdx goal $ \idx -> do
          (n₀,n₁) <- edge idx
          n₁'' <- n₁ ⋆ goal
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




