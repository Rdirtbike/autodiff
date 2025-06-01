{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DMVec (DMVec (..)) where

import Control.Monad.ST
import Data.Autodiff.Internal
import Data.Autodiff.VectorSpace
import Data.Functor.Invariant
import Data.Kind
import Data.STRef
import Data.Vector.Generic (Mutable, Vector, replicate, snoc, unsafeIndex, unsafeUpd, (++))
import Data.Vector.Generic qualified as I
import Data.Vector.Generic.Mutable hiding (replicate)
import Prelude hiding (replicate, (++))

data family DMVec :: (Type -> Type) -> Type -> Type -> Type

data instance DMVec v s (D q m a) = MkMV (Mutable v s a) (ST s (STRef s (m (v a))))

instance (Vector v a, Invariant m, Num a, VectorSpace (m (v a))) => MVector (DMVec v) (D q m a) where
  basicLength (MkMV v _) = basicLength v
  basicUnsafeSlice i n (MkMV v mv) = MkMV (basicUnsafeSlice i n v) $ mv >>= \v' -> v' <$ modifySTRef v' (invmap (I.basicUnsafeSlice i n) (replicate i 0 ++))
  basicOverlaps (MkMV v _) (MkMV w _) = basicOverlaps v w
  basicUnsafeNew n = flip MkMV (newSTRef zero) <$> basicUnsafeNew n
  basicInitialize (MkMV v _) = basicInitialize v
  basicUnsafeRead (MkMV v mv) i = liftA2 MkD (basicUnsafeRead v i) $ invmap (`unsafeIndex` i) (snoc $ replicate i 0) <$> (mv >>= readSTRef)
  basicUnsafeWrite (MkMV v mv) i (MkD x x') =
    basicUnsafeWrite v i x
      >> mv
      >>= flip modifySTRef (\v' -> invmap (`unsafeUpd` [(i, 0)]) (`unsafeUpd` [(i, 0)]) v' .+ invmap (snoc $ replicate i 0) (`unsafeIndex` i) x')
