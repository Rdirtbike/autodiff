{- HLINT ignore "Redundant fromInteger" -}

module Data.Autodiff.MNum (MNum (..), (^), MFractional (..), MFloating (..)) where

import Data.Coerce
import Data.Functor.Identity
import Prelude hiding (fromInteger, (*), (^))
import Prelude qualified as P

class MNum m a where
  (+), (-), (*) :: a -> a -> m a
  negate, abs, signum :: a -> m a
  fromInteger :: Integer -> m a

instance Num a => MNum Identity a where
  (+) = coerce $ (P.+) @a
  (-) = coerce $ (P.-) @a
  (*) = coerce $ (P.*) @a
  negate = coerce $ P.negate @a
  abs = coerce $ P.abs @a
  signum = coerce $ P.signum @a
  fromInteger = coerce $ P.fromInteger @a

{-# INLINE (^) #-}
(^) :: (MNum m a, Monad m) => a -> Word -> m a
_ ^ 0 = fromInteger 1
x ^ n = powImpl x n

{-# INLINABLE powImpl #-}
powImpl :: (MNum m a, Monad m) => a -> Word -> m a
powImpl x n
  | even n = x * x >>= (^ (n `quot` 2))
  | n == 1 = pure x
  | otherwise = x * x >>= \y -> powImplAcc y (n `quot` 2) x

{-# INLINABLE powImplAcc #-}
powImplAcc :: (MNum m a, Monad m) => a -> Word -> a -> m a
powImplAcc x 1 z = x * z
powImplAcc x n z
  | even n = x * x >>= \y -> powImplAcc y (n `quot` 2) z
  | otherwise = do
      y <- x * x
      z' <- z * x
      powImplAcc y (n `quot` 2) z'

class MFractional m a where
  (/) :: a -> a -> m a
  recip :: a -> m a
  fromRational :: Rational -> m a

instance Fractional a => MFractional Identity a where
  (/) = coerce $ (P./) @a
  recip = coerce $ P.recip @a
  fromRational = coerce $ P.fromRational @a

class MFloating m a where
  pi :: m a
  exp, log, sqrt, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh :: a -> m a
  (**), logBase :: a -> a -> m a

instance Floating a => MFloating Identity a where
  pi = coerce $ P.pi @a
  exp = coerce $ P.exp @a
  log = coerce $ P.log @a
  sqrt = coerce $ P.sqrt @a
  (**) = coerce $ (P.**) @a
  logBase = coerce $ P.logBase @a
  sin = coerce $ P.sin @a
  cos = coerce $ P.cos @a
  tan = coerce $ P.tan @a
  asin = coerce $ P.asin @a
  acos = coerce $ P.acos @a
  atan = coerce $ P.atan @a
  sinh = coerce $ P.sinh @a
  cosh = coerce $ P.cosh @a
  tanh = coerce $ P.tanh @a
  asinh = coerce $ P.asinh @a
  acosh = coerce $ P.acosh @a
  atanh = coerce $ P.atanh @a
