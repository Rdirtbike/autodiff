{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Autodiff.FixedVec (V) where

import Data.Autodiff.Mode (HasBasis (..))
import Data.Autodiff.VectorSpace (InnerSpace (..), VectorSpace (..))
import Data.Foldable (traverse_)
import Data.List qualified as L
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as M
import Data.Vector.Unboxed hiding (toList)
import GHC.IsList (IsList (..))
import GHC.TypeNats (KnownNat (..), natVal)
import Prelude hiding (concat, map, replicate, sum, zipWith)

newtype V n a = MkV (Vector a) deriving (Show, Eq, Ord)

knownNatAsInt :: forall n. (KnownNat n) => Int
knownNatAsInt = fromIntegral $ natVal $ natSing @n

instance (KnownNat n, Unbox a, VectorSpace a) => VectorSpace (V n a) where
  type Scalar (V n a) = Scalar a
  zero = MkV $ replicate (knownNatAsInt @n) zero
  MkV x .+ MkV y = MkV $ zipWith (.+) x y
  x .* MkV y = MkV $ map (x .*) y

instance (KnownNat n, Unbox a, InnerSpace a, Unbox (Scalar a), Num (Scalar a)) => InnerSpace (V n a) where
  inner (MkV v) (MkV w) = sum $ zipWith inner v w

instance (KnownNat n, Unbox a, Num a) => HasBasis (V n) (V n a) where
  diag = MkV $ MkVV $ create $ do
    let n = knownNatAsInt @n
    v <- M.new (n * n)
    v <$ traverse_ (\i -> M.write v (i * (n + 1)) 1) [0 .. n - 1]

instance (KnownNat n, Unbox a, VectorSpace a) => IsList (V n a) where
  type Item (V n a) = a
  fromList xs = let n = knownNatAsInt @n in MkV $ replicate n zero `unsafeUpd` L.zip [0 ..] (L.take n xs)
  toList (MkV v) = toList v

newtype instance MVector s (V n a) = MkM (MVector s a)

instance (KnownNat n, Unbox a) => M.MVector MVector (V n a) where
  basicLength (MkM v) = M.length v `div` knownNatAsInt @n
  basicUnsafeSlice i n (MkM v) = let m = knownNatAsInt @n in MkM $ M.basicUnsafeSlice (i * m) (n * m) v
  basicOverlaps (MkM v) (MkM w) = M.basicOverlaps v w
  basicUnsafeNew n = MkM <$> M.basicUnsafeNew (n * knownNatAsInt @n)
  basicInitialize (MkM v) = M.basicInitialize v
  basicUnsafeReplicate n (MkV v) = MkM <$> thaw (concat $ L.replicate n v)
  basicUnsafeRead (MkM v) i = let n = knownNatAsInt @n in MkV <$> freeze (M.basicUnsafeSlice (i * n) n v)
  basicUnsafeWrite (MkM v) i (MkV w) = let n = knownNatAsInt @n in G.basicUnsafeCopy (M.basicUnsafeSlice (i * n) n v) w
  basicClear (MkM v) = M.basicClear v
  basicSet x@(MkM v) (MkV w) = G.basicUnsafeCopy v $ concat $ L.replicate (M.length x) w
  basicUnsafeCopy (MkM v) (MkM w) = M.basicUnsafeCopy v w
  basicUnsafeMove (MkM v) (MkM w) = M.basicUnsafeMove v w
  basicUnsafeGrow (MkM v) n = MkM <$> M.basicUnsafeGrow v (n * knownNatAsInt @n)

newtype instance Vector (V n a) = MkVV (Vector a)

instance (KnownNat n, Unbox a) => G.Vector Vector (V n a) where
  basicUnsafeFreeze (MkM v) = MkVV <$> G.basicUnsafeFreeze v
  basicUnsafeThaw (MkVV v) = MkM <$> G.basicUnsafeThaw v
  basicLength (MkVV v) = G.length v `div` knownNatAsInt @n
  basicUnsafeSlice i n (MkVV v) = let m = knownNatAsInt @n in MkVV $ G.basicUnsafeSlice (i * m) (n * m) v
  basicUnsafeIndexM (MkVV v) i = let n = knownNatAsInt @n in pure $ MkV $ G.basicUnsafeSlice (i * n) n v
  basicUnsafeCopy (MkM v) (MkVV w) = G.basicUnsafeCopy v w
  elemseq _ = G.elemseq @Vector undefined

instance (KnownNat n, Unbox a) => Unbox (V n a)
