{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DMVec (DMVec (..)) where

import Control.Arrow ((&&&))
import Data.Autodiff.Internal (D (..), indexV')
import Data.Autodiff.Mode (Mode (dmap, lift, liftD2))
import Data.Kind (Type)
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef)
import Data.Vector.Generic (Mutable, Vector, replicate, sum, unsafeIndex, unsafeTake, unsafeUpd)
import Data.Vector.Generic.Mutable (MVector (..))
import Prelude hiding (replicate, sum)

data family DMVec :: (Type -> Type) -> Type -> Type -> Type

data instance DMVec v s (D q m a) = MkMV Int (Mutable v s a) (STRef s (m (v a)))

instance (Mode m, Vector v a, Num a) => MVector (DMVec v) (D q m a) where
  basicLength (MkMV _ v _) = basicLength v
  basicUnsafeSlice i n (MkMV o v vr) = MkMV (o + i) (basicUnsafeSlice i n v) vr
  basicOverlaps (MkMV _ v vr) (MkMV _ w wr) = vr == wr || basicOverlaps v w
  basicUnsafeNew n = MkMV 0 <$> basicUnsafeNew n <*> newSTRef (lift $ replicate n 0)
  basicInitialize (MkMV _ v _) = basicInitialize v
  basicUnsafeReplicate n (MkD x x') = MkMV 0 <$> basicUnsafeReplicate n x <*> newSTRef (dmap (replicate n) (sum . unsafeTake n) x')
  basicUnsafeRead (MkMV o v vr) i =
    let i' = i + o
     in MkD <$> basicUnsafeRead v i <*> (indexV' (basicLength v + o) i' <$> readSTRef vr)
  basicUnsafeWrite (MkMV o v vr) i (MkD x xd) = do
    basicUnsafeWrite v i x
    let i' = i + o
    modifySTRef' vr $ liftD2 (\x' v' -> unsafeUpd v' [(i', x')]) ((`unsafeIndex` i') &&& (`unsafeUpd` [(i', 0)])) xd
