{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Autodiff.VectorSpace (VectorSpace (..)) where

class VectorSpace v where
  type Scalar v
  zero :: v
  (.+) :: v -> v -> v

infixl 6 .+

newtype Field a = MkF a

instance Num a => VectorSpace (Field a) where
  type Scalar (Field a) = a
  zero = MkF 0
  MkF x .+ MkF y = MkF $ x + y

deriving via Field Double instance VectorSpace Double

deriving via Field Float instance VectorSpace Float

deriving via Field Int instance VectorSpace Int

deriving via Field Word instance VectorSpace Word

instance Num a => VectorSpace [a] where
  type Scalar [a] = a
  zero = []
  (x : xs) .+ (y : ys) = x + y : xs .+ ys
  xs .+ [] = xs
  [] .+ ys = ys
