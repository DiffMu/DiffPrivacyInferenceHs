
module DiffMu.Abstract.Data.Permutation where

import DiffMu.Prelude
import qualified Prelude as P

-- apply the permutation given by the integer list
permute :: [Int] -> [a] -> [a]
permute (i:is) as = as !! i : permute is as
permute [] as = []


-- for every element in as, we find the position
-- at which it is in bs
--
-- this means that we have `permute (getPermutation as bs) as == bs`
getPermutation :: forall m a. (MonadInternalError m, Eq a, Show a) => [a] -> [a] -> m [Int]
getPermutation xs ys = mapM (findPos ys) xs
  where
    findPos :: [a] -> a -> m Int
    findPos (b:bs) a | a == b    = pure 0
    findPos (b:bs) a | otherwise = (1 P.+) <$> findPos bs a
    findPos []     a             = internalError $ "While searching for a permutation to map "
                                                   <> show xs <> " ↦ " <> show ys
                                                   <> ", could not find the element " <> show a
                                                   <> "in the second list."





