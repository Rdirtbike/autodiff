{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DVec (DVec (..)) where

import Data.Autodiff.Internal (D (..))
import Data.Functor.Invariant (Invariant (..))
import Data.Kind (Type)
import Data.Vector.Fusion.Util (Box (..))
import Data.Vector.Generic (Mutable, Vector (..), replicate, snoc, (++))
import Data.Vector.Generic.Mutable (MVector)
import Data.Vector.Generic.Mutable qualified
import Prelude hiding (replicate, (++))

data family DVec :: (Type -> Type) -> Type -> Type

newtype instance DVec v (D s m a) = MkV {getV :: D s m (v a)}

data DMVec v s a

type instance Mutable (DVec v) = DMVec v

instance MVector (DMVec v) a where
  basicLength x = case x of {}
  basicUnsafeSlice _ _ x = case x of {}
  basicOverlaps x = case x of {}
  basicUnsafeNew _ = pure $ error "Cannot create a mutable differential vector, no implementation"
  basicInitialize x = case x of {}
  basicUnsafeRead x = case x of {}
  basicUnsafeWrite x = case x of {}

instance (Vector v a, Invariant m, Num a) => Vector (DVec v) (D s m a) where
  basicUnsafeFreeze x = case x of {}
  basicUnsafeThaw _ = pure $ error "No mutable differential vector implementation"
  basicLength (MkV (MkD x _)) = basicLength x
  basicUnsafeSlice i n (MkV (MkD x x')) = MkV $ MkD (basicUnsafeSlice i n x) $ invmap (basicUnsafeSlice i n) (replicate i 0 ++) x'
  basicUnsafeIndexM (MkV (MkD x x')) i = liftA2 MkD (basicUnsafeIndexM x i) $ Box $ invmap (unBox . (`basicUnsafeIndexM` i)) (snoc $ replicate i 0) x'
  elemseq (MkV (MkD v _)) (MkD x _) = elemseq v x
