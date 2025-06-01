{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.VectorSpace (VectorSpace (..), InnerSpace (..)) where

import Data.Autodiff.Mode (ForwardMode, ReverseMode, ScalarMode)
import Data.Functor.Contravariant (Op (Op))
import Data.Functor.Identity (Identity (..))
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

class (VectorSpace v) => InnerSpace v where
  inner :: v -> v -> Scalar v
  default inner :: (Num v, Scalar v ~ v) => v -> v -> Scalar v
  inner x y = x * y

infixl 6 .+

infixl 7 .*

instance VectorSpace Double

instance InnerSpace Double

instance VectorSpace Float

instance InnerSpace Float

instance VectorSpace Int

instance InnerSpace Int

instance VectorSpace Integer

instance InnerSpace Integer

instance (Num a) => VectorSpace [a] where
  type Scalar [a] = a
  zero = []
  (x : xs) .+ (y : ys) = x + y : xs .+ ys
  [] .+ ys = ys
  xs .+ [] = xs
  (.*) = map . (*)

instance (Num a) => InnerSpace [a] where
  inner x = sum . zipWith (*) x

instance (Unbox a, Num a) => VectorSpace (Vector a) where
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
  inner x = U.sum . U.zipWith (*) x

instance (Num a) => VectorSpace (ScalarMode a) where
  type Scalar (ScalarMode a) = a
  zero = 0
  (.+) = (+)
  (.*) = (*) . Identity

instance (Num a) => InnerSpace (ScalarMode a) where
  inner x = runIdentity . (*) x

instance (VectorSpace b) => VectorSpace (ForwardMode a b) where
  type Scalar (ForwardMode _ b) = Scalar b
  zero = const zero
  (.+) = liftA2 (.+)
  (.*) = fmap . (.*)

instance (VectorSpace a) => VectorSpace (ReverseMode a b) where
  type Scalar (ReverseMode a _) = Scalar a
  zero = Op $ const zero
  Op f .+ Op g = Op $ liftA2 (.+) f g
  x .* Op f = Op $ (x .*) . f
