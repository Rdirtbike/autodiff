{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DVec (DVec (..)) where

import Data.Autodiff.DMVec (DMVec (MkMV))
import Data.Autodiff.Internal (D (..))
import Data.Autodiff.VectorSpace (VectorSpace)
import Data.Functor.Invariant (Invariant (..))
import Data.Kind (Type)
import Data.STRef (newSTRef, readSTRef)
import Data.Vector.Fusion.Util (Box (..))
import Data.Vector.Generic (Mutable, Vector (..), replicate, snoc, (++))
import Prelude hiding (replicate, (++))

data family DVec :: (Type -> Type) -> Type -> Type

newtype instance DVec v (D s m a) = MkV {getV :: D s m (v a)}

type instance Mutable (DVec v) = DMVec v

instance (Vector v a, Invariant m, Num a, VectorSpace (m (v a))) => Vector (DVec v) (D s m a) where
  basicUnsafeFreeze (MkMV x x') = MkV <$> liftA2 MkD (basicUnsafeFreeze x) (x' >>= readSTRef)
  basicUnsafeThaw (MkV (MkD x x')) = flip MkMV (newSTRef x') <$> basicUnsafeThaw x
  basicLength (MkV (MkD x _)) = basicLength x
  basicUnsafeSlice i n (MkV (MkD x x')) = MkV $ MkD (basicUnsafeSlice i n x) $ invmap (basicUnsafeSlice i n) (replicate i 0 ++) x'
  basicUnsafeIndexM (MkV (MkD x x')) i = liftA2 MkD (basicUnsafeIndexM x i) $ Box $ invmap (unBox . (`basicUnsafeIndexM` i)) (snoc $ replicate i 0) x'
  elemseq (MkV (MkD v _)) (MkD x _) = elemseq v x
