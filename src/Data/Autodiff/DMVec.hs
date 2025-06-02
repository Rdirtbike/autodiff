{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DMVec (DMVec (..)) where

import Control.Monad.ST (ST)
import Data.Autodiff.Internal (D (..))
import Data.Autodiff.VectorSpace (VectorSpace (zero, (.+)))
import Data.Functor.Invariant (Invariant (..))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef)
import Data.Vector.Generic (Mutable, Vector, drop, length, replicate, snoc, take, unsafeUpd, (!?), (++))
import Data.Vector.Generic.Mutable (MVector (..))
import Prelude hiding (drop, length, read, replicate, take, (++))

data family DMVec :: (Type -> Type) -> Type -> Type -> Type

data instance DMVec v s (D q m a) = MkMV (Mutable v s a) (ST s (STRef s (m (v a))))

instance (Vector v a, Invariant m, Num a, VectorSpace (m (v a))) => MVector (DMVec v) (D q m a) where
  basicLength (MkMV v _) = basicLength v
  basicUnsafeSlice i n (MkMV v mv) = MkMV (basicUnsafeSlice i n v) $ mv >>= \v' -> v' <$ modifySTRef' v' (invmap (take n . drop i) (replicate i 0 ++))
  basicOverlaps (MkMV v _) (MkMV w _) = basicOverlaps v w
  basicUnsafeNew n = liftA2 MkMV (basicUnsafeNew n) $ pure <$> newSTRef zero
  basicInitialize (MkMV v _) = basicInitialize v
  basicUnsafeRead (MkMV v mv) i = liftA2 MkD (basicUnsafeRead v i) $ invmap (fromMaybe 0 . (!? i)) (snoc $ replicate i 0) <$> (mv >>= readSTRef)
  basicUnsafeWrite (MkMV v mv) i (MkD x x') =
    basicUnsafeWrite v i x
      >> mv
      >>= flip modifySTRef' (\v' -> invmap clearI clearI v' .+ invmap (snoc $ replicate i 0) (fromMaybe 0 . (!? i)) x')
    where
      clearI y = if i < length y then unsafeUpd y [(i, 0)] else y
