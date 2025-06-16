{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Autodiff.DVec (DVec (..), liftV, liftS) where

import Data.Autodiff.DMVec (DMVec (..), getOr0, prepend0s)
import Data.Autodiff.Internal (D (..))
import Data.Autodiff.VectorSpace (InnerSpace, VectorSpace (Scalar))
import Data.Coerce (coerce)
import Data.Functor.Invariant (Invariant (..))
import Data.Kind (Type)
import Data.STRef (newSTRef, readSTRef)
import Data.Vector.Generic (Mutable, Vector (..), drop, replicate, take, (++))
import GHC.IsList (IsList (Item))
import Prelude hiding (drop, replicate, take, (++))

data family DVec :: (Type -> Type) -> Type -> Type

newtype instance DVec v (D s m a) = MkV {getV :: D s m (v a)} deriving (Eq, Ord)

deriving instance (Invariant m, InnerSpace (v a), VectorSpace (m (v a)), Scalar (v a) ~ Scalar (m (v a))) => VectorSpace (DVec v (D s m a))

deriving instance (Invariant m, IsList (v a), VectorSpace (m [Item (v a)]), Num (Item (v a))) => IsList (DVec v (D s m a))

liftV :: (DVec v (D s m a) -> DVec w (D s m b)) -> D s m (v a) -> D s m (w b)
liftV = coerce

liftS :: (DVec v (D s m a) -> D s m b) -> D s m (v a) -> D s m b
liftS = coerce

type instance Mutable (DVec v) = DMVec v

instance (Vector v a, Invariant m, Num a, VectorSpace (m (v a))) => Vector (DVec v) (D s m a) where
  basicUnsafeFreeze (MkMV o n x x') = MkV <$> (MkD <$> basicUnsafeFreeze x <*> (invmap (take n . drop o) (replicate o 0 ++) <$> readSTRef x'))
  basicUnsafeThaw (MkV (MkD x x')) = MkMV 0 maxBound <$> basicUnsafeThaw x <*> newSTRef x'
  basicLength (MkV (MkD x _)) = basicLength x
  basicUnsafeSlice i n (MkV (MkD x x')) = MkV $ MkD (basicUnsafeSlice i n x) (invmap (take n . drop i) (replicate i 0 ++) x')
  basicUnsafeIndexM (MkV (MkD x x')) i = MkD <$> basicUnsafeIndexM x i <*> pure (invmap (getOr0 i) (prepend0s i) x')
  elemseq _ (MkD x _) = elemseq (undefined :: v a) x
