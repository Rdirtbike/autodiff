{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DMVec (DMVec (..)) where

import Control.Monad.ST.Unsafe
import Data.Autodiff.Internal (D (..))
import Data.Autodiff.VectorSpace (VectorSpace (zero, (.+)))
import Data.Functor.Invariant (Invariant (..))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef)
import Data.Vector.Generic (Mutable, Vector, drop, length, replicate, snoc, take, unsafeUpd, (!?), (++))
import Data.Vector.Generic.Mutable (MVector (..))
import System.IO.Unsafe
import Prelude hiding (drop, length, read, replicate, take, (++))

data family DMVec :: (Type -> Type) -> Type -> Type -> Type

data instance DMVec v s (D q m a) = MkMV (Mutable v s a) (STRef s (m (v a)))

instance (Vector v a, Invariant m, Num a, VectorSpace (m (v a))) => MVector (DMVec v) (D q m a) where
  basicLength (MkMV v _) = basicLength v
  basicUnsafeSlice i n (MkMV v vr) = MkMV (basicUnsafeSlice i n v) $ unsafePerformIO $ unsafeSTToIO $ vr <$ modifySTRef' vr (invmap (take n . drop i) (replicate i 0 ++))
  basicOverlaps (MkMV v _) (MkMV w _) = basicOverlaps v w
  basicUnsafeNew n = MkMV <$> basicUnsafeNew n <*> newSTRef zero
  basicInitialize (MkMV v _) = basicInitialize v
  basicUnsafeRead (MkMV v vr) i = MkD <$> basicUnsafeRead v i <*> (invmap (fromMaybe 0 . (!? i)) (snoc $ replicate i 0) <$> readSTRef vr)
  basicUnsafeWrite (MkMV v vr) i (MkD x x') = basicUnsafeWrite v i x *> modifySTRef' vr (\v' -> invmap clearI clearI v' .+ invmap (snoc $ replicate i 0) (fromMaybe 0 . (!? i)) x')
    where
      clearI y = if i < length y then unsafeUpd y [(i, 0)] else y
