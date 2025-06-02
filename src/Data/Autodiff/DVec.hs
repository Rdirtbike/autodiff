{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DVec (DVec (..)) where

import Data.Autodiff.DMVec (DMVec (MkMV))
import Data.Autodiff.Internal (D (..))
import Data.Autodiff.VectorSpace (VectorSpace)
import Data.Functor.Invariant (Invariant (..))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.STRef (newSTRef, readSTRef)
import Data.Vector.Fusion.Util (Box (..))
import Data.Vector.Generic (Mutable, Vector (..), drop, replicate, snoc, take, (!?), (++))
import Prelude hiding (drop, replicate, take, (++))

data family DVec :: (Type -> Type) -> Type -> Type

newtype instance DVec v (D s m a) = MkV {getV :: D s m (v a)}

type instance Mutable (DVec v) = DMVec v

instance (Vector v a, Invariant m, Num a, VectorSpace (m (v a))) => Vector (DVec v) (D s m a) where
  basicUnsafeFreeze (MkMV x x') = MkV <$> liftA2 MkD (basicUnsafeFreeze x) (x' >>= readSTRef)
  basicUnsafeThaw (MkV (MkD x x')) = liftA2 MkMV (basicUnsafeThaw x) $ pure <$> newSTRef x'
  basicLength (MkV (MkD x _)) = basicLength x
  basicUnsafeSlice i n (MkV (MkD x x')) = MkV $ MkD (basicUnsafeSlice i n x) $ invmap (take n . drop i) (replicate i 0 ++) x'
  basicUnsafeIndexM (MkV (MkD x x')) i = liftA2 MkD (basicUnsafeIndexM x i) $ Box $ invmap (fromMaybe 0 . (!? i)) (snoc $ replicate i 0) x'
  elemseq (MkV (MkD v _)) (MkD x _) = elemseq v x
