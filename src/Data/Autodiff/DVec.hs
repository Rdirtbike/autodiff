{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.DVec (DVec (..), liftV, liftS) where

import Control.Arrow ((&&&))
import Data.Autodiff.DMVec (DMVec (..))
import Data.Autodiff.Internal (D (..), indexV')
import Data.Autodiff.Mode (Mode (dmap, liftD2))
import Data.Autodiff.VectorSpace (InnerSpace, VectorSpace)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.STRef (modifySTRef', newSTRef, readSTRef)
import Data.Vector.Generic (Mutable, Vector (..), length, replicate, unsafeDrop, unsafeSlice, unsafeTake, (++))
import Data.Vector.Generic.Mutable qualified as M
import Data.Vector.Unboxed qualified as U
import GHC.IsList (IsList)
import Prelude hiding (drop, length, replicate, take, (++))

data family DVec :: (Type -> Type) -> Type -> Type

-- Invariants:
--   If m is covariant: The vector from the derivative will be at least as long as the main vector
--   If m in contravariant: The vector given to the derivative will be as least as long as the main vector
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
    let n = M.length x
     in MkV <$> (MkD <$> basicUnsafeFreeze x <*> (dmap (unsafeSlice o n) ((replicate o 0 ++) . unsafeTake n) <$> readSTRef x'))
  basicUnsafeThaw (MkV (MkD x x')) = MkMV 0 <$> basicUnsafeThaw x <*> newSTRef x'
  basicLength (MkV (MkD x _)) = basicLength x
  basicUnsafeSlice i n (MkV (MkD x x')) =
    let padding = length x - i - n
        pad xs = replicate i 0 ++ unsafeTake n xs ++ replicate padding 0
     in MkV $ MkD (basicUnsafeSlice i n x) (dmap (unsafeSlice i n) pad x')
  basicUnsafeIndexM (MkV (MkD x x')) i = MkD <$> basicUnsafeIndexM x i <*> pure (indexV' (length x) i x')
  basicUnsafeCopy (MkMV o v vr) (MkV (MkD x xd)) = do
    basicUnsafeCopy v x
    let n = length x
        copyRange x' v' = unsafeTake o v' ++ unsafeTake n x' ++ unsafeDrop (o + n) v'
        clearSub v' = unsafeTake o v' ++ replicate n 0 ++ unsafeDrop (o + n) v'
    modifySTRef' vr $ liftD2 copyRange (unsafeSlice o n &&& clearSub) xd
  elemseq _ (MkD x _) = elemseq (undefined :: v a) x
