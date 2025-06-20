module Data.Autodiff (D, autodiff, gradient, asConst, asConstD) where

import Data.Autodiff.DVec (DVec (MkV))
import Data.Autodiff.Internal (D (..))
import Data.Autodiff.Mode (Mode (..), ReverseMode, getGradient)
import Data.Autodiff.VectorSpace (VectorSpace (zero))

autodiff :: (Mode m, Start m a) => (forall s. D s m a -> D s m b) -> a -> (b, m b)
autodiff f x = case f (MkD x start) of
  MkD y f' -> (y, f')

gradient :: (VectorSpace (v a), Num b) => (forall s. DVec v (D s (ReverseMode (v a)) a) -> D s (ReverseMode (v a)) b) -> v a -> (b, v a)
gradient f x = case f (MkV (MkD x start)) of
  MkD y f' -> (y, getGradient f')

asConst :: (Real a, Fractional b) => D s m a -> b
asConst (MkD x _) = realToFrac x

asConstD :: (VectorSpace (m a)) => D s m a -> D s' m a
asConstD (MkD x _) = MkD x zero
