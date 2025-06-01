{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use drop1" #-}

module Data.Autodiff (D, autodiff, asConst) where

import Data.Autodiff.Mode (Mode (..))
import Data.Autodiff.VectorSpace (InnerSpace (..), VectorSpace (..))
import Data.Bifunctor (Bifunctor (bimap))
import Data.Functor.Invariant (Invariant (..))
import Data.List (unfoldr)
import Data.Maybe (fromMaybe, listToMaybe)
import GHC.IsList (IsList (..))

data D s m a = MkD a (m a)

autodiff :: (Mode m, Start m a) => (forall s. D s m a -> D s m b) -> a -> (b, m b)
autodiff f x = case f (MkD x start) of
  MkD y f' -> (y, f')

asConst :: (Real a, Fractional b) => D s m a -> b
asConst (MkD x _) = realToFrac x

instance (InnerSpace a, VectorSpace (m a), Scalar (m a) ~ Scalar a, Invariant m) => VectorSpace (D s m a) where
  type Scalar (D s m a) = D s m (Scalar a)
  zero = MkD zero zero
  MkD x x' .+ MkD y y' = MkD (x .+ y) (x' .+ y')
  MkD x x' .* MkD y y' = MkD (x .* y) (x .* y' .+ invmap (.* y) (inner y) x')

instance (Num a, VectorSpace (m a), Scalar (m a) ~ a) => Num (D s m a) where
  MkD x x' + MkD y y' = MkD (x + y) (x' .+ y')
  MkD x x' * MkD y y' = MkD (x * y) (x .* y' .+ y .* x')
  negate (MkD x x') = MkD (-x) ((-1) .* x')
  abs (MkD x x') = MkD (abs x) (signum x .* x')
  signum (MkD x _) = MkD (signum x) zero
  fromInteger x = MkD (fromInteger x) zero

instance (Fractional a, VectorSpace (m a), Scalar (m a) ~ a) => Fractional (D s m a) where
  recip (MkD x x') = MkD (1 / x) ((-1) / (x * x) .* x')
  fromRational x = MkD (fromRational x) zero

instance (Floating a, VectorSpace (m a), Scalar (m a) ~ a) => Floating (D s m a) where
  pi = MkD pi zero
  exp (MkD x x') = let y = exp x in MkD y (y .* x')
  log (MkD x x') = MkD (log x) (1 / x .* x')
  sin (MkD x x') = MkD (sin x) (cos x .* x')
  cos (MkD x x') = MkD (cos x) ((-sin x) .* x')
  asin (MkD x x') = MkD (asin x) (1 / sqrt (1 - x * x) .* x')
  acos (MkD x x') = MkD (acos x) ((-1) / sqrt (1 - x * x) .* x')
  atan (MkD x x') = MkD (atan x) (1 / (1 + x * x) .* x')
  sinh (MkD x x') = MkD (sinh x) (cosh x .* x')
  cosh (MkD x x') = MkD (cosh x) (sinh x .* x')
  asinh (MkD x x') = MkD (asinh x) (1 / sqrt (x * x + 1) .* x')
  acosh (MkD x x') = MkD (acosh x) (1 / sqrt (x * x - 1) .* x')
  atanh (MkD x x') = MkD (atanh x) (1 / (1 - x * x) .* x')

instance (Eq b) => Eq (D m a b) where
  MkD x _ == MkD y _ = x == y

instance (Ord b) => Ord (D m a b) where
  compare (MkD x _) (MkD y _) = compare x y

instance (IsList l, Invariant m, VectorSpace (m [Item l]), Num (Item l)) => IsList (D s m l) where
  type Item (D s m l) = D s m (Item l)
  fromList = uncurry MkD . bimap fromList (invmap fromList toList . test) . unzip . fmap (\(MkD x x') -> (x, x'))
  fromListN n = uncurry MkD . bimap (fromListN n) (invmap (fromListN n) toList . test) . unzip . fmap (\(MkD x x') -> (x, x'))
  toList (MkD xs xs') = zipWith MkD (toList xs) $ test' $ invmap toList fromList xs'

headOr0 :: (Num a) => [a] -> a
headOr0 = fromMaybe 0 . listToMaybe

test :: (Invariant m, VectorSpace (m [a]), Num a) => [m a] -> m [a]
test = foldr (\x xs -> invmap (: []) headOr0 x .+ invmap (0 :) (drop 1) xs) zero

test' :: (Invariant m, Num a) => m [a] -> [m a]
test' = unfoldr $ \xs -> Just (invmap headOr0 (: []) xs, invmap (drop 1) (0 :) xs)
