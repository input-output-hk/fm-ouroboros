{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.DeltaQ.PList
    ( MList (..)
    , mnil
    , mcons
    , mflatten
    , PList (..)
    , toPList
    , toPList'
    ) where

import           Control.Monad.Operational
import           Data.DeltaQ.Probability
import           Data.Foldable             (foldl')
import           Data.List                 (sortBy)
import qualified Data.List.NonEmpty        as NE
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as M

newtype MList m a = MList {getMList :: m (Maybe (a, MList m a))}
    deriving Functor

mnil :: Monad m => MList m a
mnil = MList $ return Nothing

mcons :: Monad m => a -> MList m a -> MList m a
mcons a xs = MList $ return $ Just (a, xs)

mflatten :: Monad m => MList m a -> m [a]
mflatten (MList l) = do
    m <- l
    case m of
        Nothing      -> return []
        Just (a, l') -> (a :) <$> mflatten l'

data PTerm p a = PTerm !(Prob p) (PList p a)
    deriving (Show, Eq, Ord)

scalePTerm :: (Ord p, Num p) => Prob p -> PTerm p a -> PTerm p a
scalePTerm p (PTerm q xs) = PTerm (p * q) $ scalePList p xs

addPTerms :: (Ord p, Num p, Ord a) => PTerm p a -> PTerm p a -> PTerm p a
addPTerms (PTerm p xs) (PTerm q ys) = PTerm (p + q) $ addPLists xs ys

newtype PList p a = PList (Map a (PTerm p a))
    deriving (Show, Eq, Ord)

scalePList :: (Ord p, Num p) => Prob p -> PList p a -> PList p a
scalePList p (PList m) = PList $ scalePTerm p <$> m

addPLists :: (Ord p, Num p, Ord a) => PList p a -> PList p a -> PList p a
addPLists (PList m) (PList n) = PList $ M.unionWith addPTerms m n

newtype PList' p a = PList' [(Prob p, a, PList' p a)]
    deriving (Show, Eq, Ord)

toPList' :: forall p a. Ord p => PList p a -> PList' p a
toPList' (PList m) = PList' $ sortBy g $ map f $ M.toList m
  where
    f :: (a, PTerm p a) -> (Prob p, a, PList' p a)
    f (a, PTerm p xs) = (p, a, toPList' xs)

    g :: (Prob p, a, PList' p a) -> (Prob p, a, PList' p a) -> Ordering
    g (p, _, _) (q, _, _) = compare q p

toPList :: forall p a. (Ord p, Fractional p, Ord a) => MList (ProbM p) a -> PList p a
toPList (MList (ProbT l)) = go $ view l
  where
    go :: ProgramView (ProbI p) (Maybe (a, MList (ProbM p) a)) -> PList p a
    go (Return Nothing)        = PList M.empty
    go (Return (Just (a, l'))) = PList $ M.singleton a $ PTerm 1 (toPList l')
    go (Coin p x y :>>= cont)
        | p == 0               = go' $ cont y
        | p == 1               = go' $ cont x
        | otherwise            = scalePList p       (go' $ cont x) `addPLists`
                                 scalePList (1 - p) (go' $ cont y)
    go (Elements xs :>>= cont) =
        let s  = prob $ recip $ fromIntegral $ NE.length xs
            ys = fmap (scalePList s . go' . cont) xs
        in  foldl' addPLists (PList M.empty) ys

    go' :: Program (ProbI p) (Maybe (a, MList (ProbM p) a)) -> PList p a
    go' = toPList . MList . ProbT

test :: MList (ProbM Rational) Char
test = MList $ coin 0.3 (Just ('x', MList $ return $ Just ('y', MList $ return Nothing)))
                        (Just ('x', MList $ return $ Just ('z', MList $ return Nothing)))