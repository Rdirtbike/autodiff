{-# HLINT ignore "Use drop1" #-}
{-# HLINT ignore "Parenthesize unary negation" #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Data.Autodiff.Internal (D (..)) where

import Control.Arrow ((&&&))
import Data.Autodiff.Mode (Mode (dmap, lift, liftD2))
import Data.Autodiff.VectorSpace (InnerSpace (..), VectorSpace (..))
import Data.Bool (bool)
import Data.Foldable (foldl')
import Data.List (uncons, unfoldr)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Vector qualified as V
import Data.Vector.Generic qualified as G
import Data.Vector.Primitive qualified as P
import Data.Vector.Storable qualified as S
import Data.Vector.Unboxed qualified as U
import GHC.IsList (IsList (..))

data D s m a = MkD a (m a)

scalar :: (Mode m, Num a) => (a -> a) -> (a -> a) -> D s m a -> D s m a
scalar f f' (MkD x x') = MkD (f x) $ dmap (* f' x) (* f' x) x'

instance (Mode m, InnerSpace a) => VectorSpace (D s m a) where
  type Scalar (D s m a) = D s m (Scalar a)
  zero = MkD zero $ lift zero
  MkD x xd .+ MkD y yd = MkD (x .+ y) $ liftD2 (.+) (id &&& id) xd yd
  MkD x xd .* MkD y yd = MkD (x .* y) $ liftD2 (\x' y' -> x' .* y .+ x .* y') (inner y &&& (.*) x) xd yd

instance (Mode m, Num a) => Num (D s m a) where
  MkD x xd + MkD y yd = MkD (x + y) $ liftD2 (+) (id &&& id) xd yd
  MkD x xd * MkD y yd = MkD (x * y) $ liftD2 (\x' y' -> x' * y + x * y') ((*) y &&& (*) x) xd yd
  MkD x xd - MkD y yd = MkD (x - y) $ liftD2 (-) (id &&& negate) xd yd
  negate = scalar negate negate
  abs = scalar abs signum
  signum (MkD x _) = MkD (signum x) $ lift 0
  fromInteger x = MkD (fromInteger x) $ lift 0

instance (Mode m, Fractional a) => Fractional (D s m a) where
  MkD x xd / MkD y yd = MkD (x / y) $ liftD2 (\x' y' -> (x' * y - x * y') / (y * y)) ((/ y) &&& (*) (-x / (y * y))) xd yd
  recip = scalar recip $ \x -> -1 / (x * x)
  fromRational x = MkD (fromRational x) $ lift 0

instance (Mode m, Floating a) => Floating (D s m a) where
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

instance (Eq b) => Eq (D m a b) where
  MkD x _ == MkD y _ = x == y

instance (Ord b) => Ord (D m a b) where
  compare (MkD x _) (MkD y _) = compare x y

instance (Mode m, IsList l, Num (Item l)) => IsList (D s m l) where
  type Item (D s m l) = D s m (Item l)
  fromList xs =
    MkD (fromList $ map (\(MkD x _) -> x) xs) $
      dmap fromList toList $
        foldr (\(MkD _ x') xs' -> liftD2 (:) (fromMaybe (0, []) . uncons) x' xs') (lift []) xs
  fromListN n xs =
    MkD (fromListN n $ map (\(MkD x _) -> x) xs) $
      dmap (fromListN n) toList $
        foldr (\(MkD _ x') xs' -> liftD2 (:) (fromMaybe (0, []) . uncons) x' xs') (lift []) xs
  toList (MkD xs xs') =
    zipWith MkD (toList xs) $
      unfoldr (\x -> Just (dmap (fromMaybe 0 . listToMaybe) (: []) x, dmap (drop 1) (0 :) x)) $
        dmap toList fromList xs'

toV :: (Mode m, G.Vector v a, Num a) => [D s m a] -> D s m (v a)
toV xs =
  MkD (G.fromList $ map (\(MkD x _) -> x) xs) $
    foldr (\(MkD _ x') xs' -> liftD2 G.cons (G.unsafeHead &&& G.unsafeTail) x' xs') (lift G.empty) xs

toVN :: (Mode m, G.Vector v a, Num a) => Int -> [D s m a] -> D s m (v a)
toVN n xs =
  MkD (G.fromListN n $ map (\(MkD x _) -> x) xs) . snd $
    foldl'
      (\(i, xs') (MkD _ x') -> (i + 1, liftD2 (\x v -> G.unsafeUpd v [(i, x)]) ((`G.unsafeIndex` i) &&& id) x' xs'))
      (0, lift $ G.replicate n 0)
      xs

fromV :: (Mode m, G.Vector v a, Num a) => D s m (v a) -> [D s m a]
fromV (MkD xs xs') =
  zipWith MkD (G.toList xs) $
    map (\i -> dmap (`G.unsafeIndex` i) (\x -> G.generate n $ bool 0 x . (==) i) xs') [0 .. n - 1]
  where
    n = G.length xs

instance {-# OVERLAPPING #-} (Mode m, U.Unbox a, Num a) => IsList (D s m (U.Vector a)) where
  type Item (D s m (U.Vector a)) = D s m (Item (U.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV

instance {-# OVERLAPPING #-} (Mode m, Num a) => IsList (D s m (V.Vector a)) where
  type Item (D s m (V.Vector a)) = D s m (Item (V.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV

instance {-# OVERLAPPING #-} (Mode m, S.Storable a, Num a) => IsList (D s m (S.Vector a)) where
  type Item (D s m (S.Vector a)) = D s m (Item (S.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV

instance {-# OVERLAPPING #-} (Mode m, P.Prim a, Num a) => IsList (D s m (P.Vector a)) where
  type Item (D s m (P.Vector a)) = D s m (Item (P.Vector a))
  fromList = toV
  fromListN = toVN
  toList = fromV
