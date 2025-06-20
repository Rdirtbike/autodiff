{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DVec (DVec (..), liftV, liftS) where

import Data.Autodiff.DMVec (DMVec (..), getOr0, prepend0s)
import Data.Autodiff.Internal (D (..))
import Data.Autodiff.Mode (Mode (dmap))
import Data.Autodiff.VectorSpace (InnerSpace, VectorSpace)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.STRef (newSTRef, readSTRef)
import Data.Vector.Generic (Mutable, Vector (..), drop, replicate, take, (++))
import Data.Vector.Generic.Mutable qualified as M (length)
import Data.Vector.Unboxed qualified as U
import GHC.IsList (IsList)
import Prelude hiding (drop, replicate, take, (++))

data family DVec :: (Type -> Type) -> Type -> Type

newtype instance DVec v (D s m a) = MkV {getV :: D s m (v a)} deriving (Eq, Ord)

deriving instance (Mode m, InnerSpace (v a)) => VectorSpace (DVec v (D s m a))

deriving instance (Mode m, U.Unbox a, Num a) => IsList (DVec U.Vector (D s m a))

liftV :: (DVec v (D s m a) -> DVec w (D s m b)) -> D s m (v a) -> D s m (w b)
liftV = coerce

liftS :: (DVec v (D s m a) -> D s m b) -> D s m (v a) -> D s m b
liftS = coerce

type instance Mutable (DVec v) = DMVec v

instance (Mode m, Vector v a, Num a) => Vector (DVec v) (D s m a) where
  basicUnsafeFreeze (MkMV o x x') =
    let takeLen = take (M.length x)
     in MkV <$> (MkD <$> basicUnsafeFreeze x <*> (dmap (takeLen . drop o) ((replicate o 0 ++) . takeLen) <$> readSTRef x'))
  basicUnsafeThaw (MkV (MkD x x')) = MkMV 0 <$> basicUnsafeThaw x <*> newSTRef x'
  basicLength (MkV (MkD x _)) = basicLength x
  basicUnsafeSlice i n (MkV (MkD x x')) = MkV $ MkD (basicUnsafeSlice i n x) (dmap (take n . drop i) (replicate i 0 ++) x')
  basicUnsafeIndexM (MkV (MkD x x')) i = MkD <$> basicUnsafeIndexM x i <*> pure (dmap (getOr0 i) (prepend0s i) x')
  elemseq _ (MkD x _) = elemseq (undefined :: v a) x
