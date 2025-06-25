{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DMVec (DMVec (..)) where

import Control.Arrow ((&&&))
import Data.Autodiff.Internal (D (..), indexV')
import Data.Autodiff.Mode (Mode (dmap, lift, liftD2))
import Data.Functor.Contravariant (Op)
import Data.Kind (Type)
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef)
import Data.Vector.Generic
  ( Mutable,
    Vector,
    cons,
    replicate,
    sum,
    unsafeDrop,
    unsafeIndex,
    unsafeSlice,
    unsafeTake,
    (++),
  )
import Data.Vector.Generic.Mutable (MVector (..))
import Data.Vector.Unboxed qualified as U
import Prelude hiding (replicate, sum, (++))

data family DMVec :: (Type -> Type) -> Type -> Type -> Type

-- Invariants:
--   If m is covariant: The vector from the derivative will be at least as long as the main vector plus the offset
--   If m in contravariant: The vector given to the derivative will be as least as long as the main vector plus the offset
data instance DMVec v s (D q m a) = MkMV Int (Mutable v s a) (STRef s (m (v a)))

instance (Mode m, Vector v a, Num a) => MVector (DMVec v) (D s m a) where
  {-# SPECIALIZE instance MVector (DMVec U.Vector) (D s (Op (U.Vector Double)) Double) #-}
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
        setI x' v' = unsafeTake i' v' ++ x' `cons` unsafeDrop (i' + 1) v'
    modifySTRef' vr $ liftD2 setI ((`unsafeIndex` i') &&& setI 0) xd
  basicSet (MkMV o v vr) (MkD x xd) = do
    basicSet v x
    let n = basicLength v
        setRange x' v' = unsafeTake o v' ++ replicate n x' ++ unsafeDrop (o + n) v'
    modifySTRef' vr $ liftD2 setRange (sum . unsafeSlice o n &&& setRange 0) xd
  basicUnsafeCopy (MkMV o v vr) (MkMV i w wr) = do
    basicUnsafeCopy v w
    wd <- readSTRef wr
    let n = basicLength v
        copyRange w' v' = unsafeTake o v' ++ unsafeSlice i n w' ++ unsafeDrop (o + n) v'
        extractSub v' = replicate i 0 ++ unsafeSlice o n v'
        clearSub v' = unsafeTake o v' ++ replicate n 0 ++ unsafeDrop (o + n) v'
    modifySTRef' vr $ liftD2 copyRange (extractSub &&& clearSub) wd
  basicUnsafeMove (MkMV o v vr) (MkMV i w wr) = do
    basicUnsafeMove v w
    wd <- readSTRef wr
    let n = basicLength v
        copyRange w' v' = unsafeTake o v' ++ unsafeSlice i n w' ++ unsafeDrop (o + n) v'
        extractSub v' = replicate i 0 ++ unsafeSlice o n v'
        clearSub v' = unsafeTake o v' ++ replicate n 0 ++ unsafeDrop (o + n) v'
    modifySTRef' vr $ liftD2 copyRange (extractSub &&& clearSub) wd
  basicUnsafeGrow (MkMV o v vr) by = do
    w <- basicUnsafeGrow v by
    v' <- readSTRef vr
    let n = basicLength v
    wr <- newSTRef $ dmap ((++ replicate by 0) . unsafeSlice o n) ((replicate o 0 ++) . unsafeTake n) v'
    pure $ MkMV 0 w wr
