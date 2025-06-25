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
  )
where

import Data.Autodiff.VectorSpace (VectorSpace (zero, (.+)))
import Data.Functor.Contravariant (Op (Op), contramap)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Constraint)
import Data.Vector.Unboxed qualified as U

class Mode m where
  type Start m a :: Constraint
  start :: (Start m a) => m a
  dmap :: (a -> b) -> (b -> a) -> m a -> m b
  liftD2 :: (a -> b -> c) -> (c -> (a, b)) -> m a -> m b -> m c
  lift :: a -> m a

type ScalarMode = Identity

getScalar :: ScalarMode a -> a
getScalar = runIdentity

instance Mode ScalarMode where
  type Start ScalarMode a = Num a
  start = 1
  dmap f _ = fmap f
  liftD2 f _ = liftA2 f
  lift = pure

type ForwardMode = (->)

getDeriv :: (Num a) => ForwardMode a b -> b
getDeriv f = f 1

directionalDeriv :: a -> ForwardMode a b -> b
directionalDeriv = flip ($)

instance Mode (ForwardMode a) where
  type Start (ForwardMode a) b = a ~ b
  start = id
  dmap f _ = fmap f
  liftD2 f _ = liftA2 f
  lift = pure

type ReverseMode = Op

{-# SPECIALIZE getGradient :: Op (U.Vector Double) Double -> U.Vector Double #-}
getGradient :: (Num b) => ReverseMode a b -> a
getGradient (Op f) = f 1

directionalGrad :: b -> ReverseMode a b -> a
directionalGrad x (Op f) = f x

instance (VectorSpace a) => Mode (ReverseMode a) where
  {-# SPECIALIZE instance Mode (Op (U.Vector Double)) #-}
  type Start (ReverseMode a) b = a ~ b
  start = Op id
  dmap _ = contramap
  liftD2 _ f (Op g) (Op h) = Op $ \x -> case f x of
    (y, z) -> g y .+ h z
  lift _ = Op $ const zero
