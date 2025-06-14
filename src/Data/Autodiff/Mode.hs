{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.Mode
  ( Mode (..),
    ScalarMode,
    getScalar,
    ForwardMode,
    getDeriv,
    directionalDeriv,
    ReverseMode,
    getGradient,
    directionalGrad,
    HasBasis (..),
  )
where

import Data.Functor.Contravariant (Op (Op))
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Constraint)

class Mode m where
  type Start m a :: Constraint
  start :: (Start m a) => m a

type ScalarMode = Identity

getScalar :: ScalarMode a -> a
getScalar = runIdentity

instance Mode ScalarMode where
  type Start ScalarMode a = Num a
  start = 1

type ForwardMode = (->)

getDeriv :: (Num a) => ForwardMode a b -> b
getDeriv f = f 1

directionalDeriv :: a -> ForwardMode a b -> b
directionalDeriv = flip ($)

instance Mode (ForwardMode a) where
  type Start (ForwardMode a) b = a ~ b
  start = id

type ReverseMode = Op

getGradient :: (Num b) => ReverseMode a b -> a
getGradient (Op f) = f 1

directionalGrad :: b -> ReverseMode a b -> a
directionalGrad x (Op f) = f x

instance Mode (ReverseMode a) where
  type Start (ReverseMode a) b = a ~ b
  start = Op id

class HasBasis f v | v -> f where
  diag :: f v

instance (Num a) => HasBasis [] [a] where
  diag = [replicate i 0 ++ [1] | i <- [0 ..]]

instance Mode [] where
  type Start [] a = HasBasis [] a
  start = diag
