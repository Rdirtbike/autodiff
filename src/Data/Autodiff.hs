module Data.Autodiff (D, autodiff, asConst, asConstD) where

import Data.Autodiff.Internal (D (..))
import Data.Autodiff.Mode (Mode (..))
import Data.Autodiff.VectorSpace (VectorSpace (zero))

autodiff :: (Mode m, Start m a) => (forall s. D s m a -> D s m b) -> a -> (b, m b)
autodiff f x = case f (MkD x start) of
  MkD y f' -> (y, f')

asConst :: (Real a, Fractional b) => D s m a -> b
asConst (MkD x _) = realToFrac x

asConstD :: (VectorSpace (m a)) => D s m a -> D s' m a
asConstD (MkD x _) = MkD x zero
