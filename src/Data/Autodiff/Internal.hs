{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Autodiff.Internal (D (..), indexV') where

import Control.Arrow ((&&&))
import Data.Autodiff.Mode (Mode (dmap, lift, liftD2))
import Data.Autodiff.VectorSpace (InnerSpace (..), VectorSpace (..))
import Data.Functor.Contravariant (Op)
import Data.List (uncons, unfoldr)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Vector qualified as Vector
import Data.Vector.Generic qualified as G
import Data.Vector.Primitive qualified as Primitive
import Data.Vector.Storable qualified as Storable
import Data.Vector.Strict qualified as Strict
import Data.Vector.Unboxed qualified as U
import GHC.IsList (IsList (..))

data D s m a = MkD a (m a)

scalar :: (Mode m, Num a) => (a -> a) -> (a -> a) -> D s m a -> D s m a
scalar f f' (MkD x x') = MkD (f x) $ dmap (* f' x) (* f' x) x'

instance (Mode m, InnerSpace a) => VectorSpace (D s m a) where
  {-# SPECIALIZE instance VectorSpace (D s (Op (U.Vector Double)) Double) #-}
  type Scalar (D s m a) = D s m (Scalar a)
  zero = MkD zero $ lift zero
  MkD x xd .+ MkD y yd = MkD (x .+ y) $ liftD2 (.+) (id &&& id) xd yd
  MkD x xd .* MkD y yd = MkD (x .* y) $ liftD2 (\x' y' -> x' .* y .+ x .* y') (inner y &&& (.*) x) xd yd

instance (Mode m, Num a) => Num (D s m a) where
  {-# SPECIALIZE instance Num (D s (Op (U.Vector Double)) Double) #-}
  MkD x xd + MkD y yd = MkD (x + y) $ liftD2 (+) (id &&& id) xd yd
  MkD x xd * MkD y yd = MkD (x * y) $ liftD2 (\x' y' -> x' * y + x * y') ((*) y &&& (*) x) xd yd
  MkD x xd - MkD y yd = MkD (x - y) $ liftD2 (-) (id &&& negate) xd yd
  negate = scalar negate negate
  abs = scalar abs signum
  signum (MkD x _) = MkD (signum x) $ lift 0
  fromInteger x = MkD (fromInteger x) $ lift 0

instance (Mode m, Fractional a) => Fractional (D s m a) where
  {-# SPECIALIZE instance Fractional (D s (Op (U.Vector Double)) Double) #-}
  MkD x xd / MkD y yd = MkD (x / y) $ liftD2 (\x' y' -> (x' * y - x * y') / (y * y)) ((/ y) &&& (*) -(x / (y * y))) xd yd
  recip = scalar recip $ \x -> -1 / (x * x)
  fromRational x = MkD (fromRational x) $ lift 0

instance (Mode m, Floating a) => Floating (D s m a) where
  {-# SPECIALIZE instance Floating (D s (Op (U.Vector Double)) Double) #-}
  pi = MkD pi $ lift 0
  exp = scalar exp exp
  log = scalar log recip
  sin = scalar sin cos
  cos = scalar cos (negate . sin)
  asin = scalar asin $ \x -> 1 / sqrt (1 - x * x)
  acos = scalar acos $ \x -> -1 / sqrt (1 - x * x)
  atan = scalar atan $ \x -> 1 / (1 + x * x)
  sinh = scalar sinh cosh
  cosh = scalar cosh sinh
  asinh = scalar asinh $ \x -> 1 / sqrt (x * x + 1)
  acosh = scalar acosh $ \x -> 1 / sqrt (x * x - 1)
  atanh = scalar atanh $ \x -> 1 / (1 - x * x)

instance Eq a => Eq (D s m a) where
  {-# SPECIALIZE instance Eq (D s (Op (U.Vector Double)) Double) #-}
  MkD x _ == MkD y _ = x == y

instance Ord a => Ord (D s m a) where
  {-# SPECIALIZE instance Ord (D s (Op (U.Vector Double)) Double) #-}
  compare (MkD x _) (MkD y _) = compare x y

instance (Mode m, IsList l, Num (Item l)) => IsList (D s m l) where
  type Item (D s m l) = D s m (Item l)
  fromList xs =
    MkD (fromList $ fmap (\(MkD x _) -> x) xs) . dmap fromList toList $
      foldr (\(MkD _ x') xs' -> liftD2 (:) (fromMaybe (0, []) . uncons) x' xs') (lift []) xs
  fromListN n xs =
    MkD (fromListN n $ fmap (\(MkD x _) -> x) xs) . dmap (fromListN n) toList $
      foldr (\(MkD _ x') xs' -> liftD2 (:) (fromMaybe (0, []) . uncons) x' xs') (lift []) xs
  toList (MkD xs xs') =
    zipWith MkD (toList xs)
      . unfoldr (\x -> Just (dmap (sum . listToMaybe) (: []) x, dmap (drop 1) (0 :) x))
      $ dmap toList fromList xs'

{-# INLINEABLE toV #-}
toV :: (Mode m, G.Vector v a, Num a) => [D s m a] -> D s m (v a)
toV xs =
  MkD (G.fromList $ fmap (\(MkD x _) -> x) xs) . dmap G.fromList G.toList $
    foldr (\(MkD _ x') -> liftD2 (:) (fromMaybe (0, []) . uncons) x') (lift []) xs

{-# INLINEABLE toVN #-}
toVN :: (Mode m, G.Vector v a, Num a) => Int -> [D s m a] -> D s m (v a)
toVN n xs =
  MkD (G.fromListN n $ fmap (\(MkD x _) -> x) xs) . dmap (G.fromListN n) G.toList $
    foldr (\(MkD _ x') -> liftD2 (:) (fromMaybe (0, []) . uncons) x') (lift []) xs

{-# INLINEABLE indexV' #-}
indexV' :: (Mode m, G.Vector v a, Num a) => Int -> Int -> m (v a) -> m a
indexV' n i = dmap (`G.unsafeIndex` i) (\x -> G.replicate i 0 G.++ x `G.cons` G.replicate (n - i - 1) 0)

{-# INLINEABLE fromV #-}
fromV :: (Mode m, G.Vector v a, Num a) => D s m (v a) -> [D s m a]
fromV (MkD xs xs') =
  zipWith MkD (G.toList xs) $
    fmap (\i -> indexV' n i xs') [0 .. n - 1]
 where
  n = G.length xs

instance {-# OVERLAPPING #-} (Mode m, U.Unbox a, Num a) => IsList (D s m (U.Vector a)) where
  {-# SPECIALIZE instance IsList (D s (Op (U.Vector Double)) (U.Vector Double)) #-}
  type Item (D s m (U.Vector a)) = D s m (Item (U.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV

instance {-# OVERLAPPING #-} (Mode m, Num a) => IsList (D s m (Vector.Vector a)) where
  type Item (D s m (Vector.Vector a)) = D s m (Item (Vector.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV

instance {-# OVERLAPPING #-} (Mode m, Storable.Storable a, Num a) => IsList (D s m (Storable.Vector a)) where
  type Item (D s m (Storable.Vector a)) = D s m (Item (Storable.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV

instance {-# OVERLAPPING #-} (Mode m, Primitive.Prim a, Num a) => IsList (D s m (Primitive.Vector a)) where
  type Item (D s m (Primitive.Vector a)) = D s m (Item (Primitive.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV

instance {-# OVERLAPPING #-} (Mode m, Num a) => IsList (D s m (Strict.Vector a)) where
  type Item (D s m (Strict.Vector a)) = D s m (Item (Strict.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV
