{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.VectorSpace (VectorSpace (..), InnerSpace (..)) where

import Data.Vector.Unboxed (Unbox, Vector, empty)
import Data.Vector.Unboxed qualified as U

class VectorSpace v where
  type Scalar v
  type Scalar v = v

  zero :: v
  default zero :: (Num v, Scalar v ~ v) => v
  zero = 0

  (.+) :: v -> v -> v
  default (.+) :: (Num v, Scalar v ~ v) => v -> v -> v
  (.+) = (+)

  (.*) :: Scalar v -> v -> v
  default (.*) :: (Num v, Scalar v ~ v) => Scalar v -> v -> v
  (.*) = (*)

infixl 6 .+

infixl 7 .*

class VectorSpace v => InnerSpace v where
  inner :: v -> v -> Scalar v
  default inner :: (Num v, Scalar v ~ v) => v -> v -> Scalar v
  inner x y = x * y

instance VectorSpace Double

instance InnerSpace Double

instance VectorSpace Float

instance InnerSpace Float

instance VectorSpace Int

instance InnerSpace Int

instance VectorSpace Integer

instance InnerSpace Integer

instance Num a => VectorSpace [a] where
  type Scalar [a] = a
  zero = []
  (x : xs) .+ (y : ys) = x + y : xs .+ ys
  [] .+ ys = ys
  xs .+ [] = xs
  (.*) = map . (*)

instance Num a => InnerSpace [a] where
  inner x = sum . zipWith (*) x

instance (Unbox a, Num a) => VectorSpace (Vector a) where
  {-# SPECIALIZE instance VectorSpace (Vector Double) #-}
  type Scalar (Vector a) = a
  zero = empty
  xs .+ ys =
    let lx = U.length xs
        ly = U.length ys
        n = max lx ly
        xs' = U.replicate (n - lx) 0
        ys' = U.replicate (n - ly) 0
    in U.zipWith (+) (xs <> xs') (ys <> ys')
  (.*) = U.map . (*)

instance (Unbox a, Num a) => InnerSpace (Vector a) where
  {-# SPECIALIZE instance InnerSpace (Vector Double) #-}
  inner x = U.sum . U.zipWith (*) x
