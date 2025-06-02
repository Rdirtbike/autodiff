{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DMVec (DMVec (..), getOr0, prepend0s) where

import Data.Autodiff.Internal (D (..))
import Data.Autodiff.VectorSpace (VectorSpace (zero, (.+)))
import Data.Functor.Invariant (Invariant (..))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef)
import Data.Vector.Generic (Mutable, Vector, length, replicate, snoc, unsafeUpd, (!?))
import Data.Vector.Generic.Mutable (MVector (..))
import Prelude hiding (length, replicate)

data family DMVec :: (Type -> Type) -> Type -> Type -> Type

data instance DMVec v s (D q m a) = MkMV Int Int (Mutable v s a) (STRef s (m (v a)))

getOr0 :: (Vector v a, Num a) => Int -> v a -> a
getOr0 i = fromMaybe 0 . (!? i)

prepend0s :: (Vector v a, Num a) => Int -> a -> v a
prepend0s i = snoc $ replicate i 0

instance (Vector v a, Invariant m, Num a, VectorSpace (m (v a))) => MVector (DMVec v) (D q m a) where
  basicLength (MkMV _ _ v _) = basicLength v
  basicUnsafeSlice i n (MkMV o _ v vr) = MkMV (o + i) n (basicUnsafeSlice i n v) vr
  basicOverlaps (MkMV _ _ v _) (MkMV _ _ w _) = basicOverlaps v w
  basicUnsafeNew n = MkMV 0 n <$> basicUnsafeNew n <*> newSTRef zero
  basicInitialize (MkMV _ _ v _) = basicInitialize v
  basicUnsafeRead (MkMV o _ v vr) i = MkD <$> basicUnsafeRead v i <*> (invmap (getOr0 $ i + o) (prepend0s $ i + o) <$> readSTRef vr)
  basicUnsafeWrite (MkMV o _ v vr) i (MkD x x') = basicUnsafeWrite v i x *> modifySTRef' vr (\v' -> invmap clearI clearI v' .+ invmap (prepend0s $ i + o) (getOr0 $ i + o) x')
    where
      clearI y = if i + o < length y then unsafeUpd y [(i + o, 0)] else y
