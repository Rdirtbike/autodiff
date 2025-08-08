{-# LANGUAGE Strict #-}

module Data.Autodiff (D, autodiff) where

import Control.Monad.ST (ST)
import Data.Autodiff.MNum (MFloating, MFractional, MNum)
import Data.Autodiff.MNum qualified
import Data.Primitive.ByteArray (MutableByteArray, fillByteArray, newByteArray, readByteArray, writeByteArray)
import Data.Primitive.Types (Prim)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

newtype M s a = MkM
  {runM :: forall r. STRef s Int -> (a -> ST s (r, MutableByteArray s)) -> ST s (r, MutableByteArray s)}
  deriving Functor

instance Applicative (M s) where
  pure x = MkM $ const ($ x)
  MkM f <*> MkM x = MkM $ \n k -> f n $ \g -> x n (k . g)
  x *> y = x >>= const y

instance Monad (M s) where
  MkM m >>= f = MkM $ \n k -> m n $ \x -> runM (f x) n k

data D s a = MkD a Int

{-# INLINEABLE autodiff #-}
autodiff :: forall a b s. (Prim a, Num b, Prim b) => (D s a -> M s (D s b)) -> a -> ST s (b, a)
autodiff f x = do
  nr <- newSTRef 1
  (y, a) <- runM (f $ MkD x 0) nr $ \(MkD y i) -> do
    n <- readSTRef nr
    a <- newByteArray $ n * 8
    fillByteArray a 0 (n * 8) 0
    writeByteArray @b a i 1
    pure (y, a)
  y' <- readByteArray a 0
  pure (y, y')

{-# INLINE lift #-}
lift :: Num a => a -> M s (D s a)
lift x = MkM $ \nr k -> do
  i <- readSTRef nr
  writeSTRef nr $! i + 1
  k $! MkD x i

{-# INLINE lift1 #-}
lift1 :: (Num a, Prim a) => (a -> a) -> (a -> a -> a -> a) -> D s a -> M s (D s a)
lift1 f f' (MkD x ix) = MkM $ \nr k -> do
  iy <- readSTRef nr
  writeSTRef nr $! iy + 1
  (y, a) <- k $! MkD (f x) iy
  y' <- readByteArray a iy
  x' <- readByteArray a ix
  writeByteArray a ix $! f' x y' x'
  pure (y, a)

{-# INLINE lift2 #-}
lift2 :: (Num a, Prim a) => (a -> a -> a) -> (a -> a -> a -> a -> a) -> (a -> a -> a -> a -> a) -> D s a -> D s a -> M s (D s a)
lift2 f f1' f2' (MkD x ix) (MkD y iy) = MkM $ \nr k -> do
  iz <- readSTRef nr
  writeSTRef nr $! iz + 1
  (z, a) <- k $! MkD (f x y) iz
  z' <- readByteArray a iz
  x' <- readByteArray a ix
  writeByteArray a ix $! f1' x y z' x'
  y' <- readByteArray a iy
  writeByteArray a iy $! f2' x y z' y'
  pure (z, a)

instance (Num a, Prim a) => MNum (M s) (D s a) where
  (+) = lift2 (+) (\_ _ z' -> (+ z')) (\_ _ z' -> (+ z'))
  (*) = lift2 (*) (\_ y z' -> (+ z' * y)) (\x _ z' -> (+ z' * x))
  (-) = lift2 (-) (\_ _ z' -> (+ z')) (\_ _ z' -> (- z'))
  negate = lift1 negate $ \_ y' -> (- y')
  abs = lift1 abs $ \x y' -> (+ y' * signum x)
  signum (MkD x _) = lift $ signum x
  fromInteger n = lift $ fromInteger n

instance (Fractional a, Prim a) => MFractional (M s) (D s a) where
  (/) = lift2 (/) (\_ y z' -> (+ z' / y)) (\x y z' -> (- z' * x / (y * y)))
  recip = lift1 recip $ \x y' -> (- y' / (x * x))
  fromRational x = lift $ fromRational x

instance (Floating a, Prim a) => MFloating (M s) (D s a) where
  pi = lift pi
  exp = lift1 exp $ \x y' -> (+ y' * exp x)
  log = lift1 log $ \x y' -> (+ y' / x)
  sqrt = lift1 sqrt $ \x y' -> (- y' / sqrt x)
  (**) = lift2 (**) (\x y z' -> (+ z' * y * x ** (y - 1))) (\x y z' -> (+ z' * log x * x ** y))
  logBase = lift2 logBase (\x y z' -> (- z' * log y / (x * log x ^ (2 :: Int)))) (\x y z' -> (+ z' / (y * log x)))
  sin = lift1 sin $ \x y' -> (+ y' * cos x)
  cos = lift1 cos $ \x y' -> (- y' * sin x)
  tan = lift1 tan $ \x y' -> (+ y' / cos x ^ (2 :: Int))
  asin = lift1 asin $ \x y' -> (+ y' / sqrt (1 - x * x))
  acos = lift1 acos $ \x y' -> (- y' / sqrt (1 - x * x))
  atan = lift1 acos $ \x y' -> (+ y' / (1 + x * x))
  sinh = lift1 sinh $ \x y' -> (+ y' * cosh x)
  cosh = lift1 cosh $ \x y' -> (+ y' * sinh x)
  tanh = lift1 tanh $ \x y' -> (+ y' / cosh x ^ (2 :: Int))
  asinh = lift1 asinh $ \x y' -> (+ y' / sqrt (x * x + 1))
  acosh = lift1 acosh $ \x y' -> (+ y' / sqrt (x * x - 1))
  atanh = lift1 atanh $ \x y' -> (+ y' / (1 - x * x))

instance Eq a => Eq (D s a) where
  MkD x _ == MkD y _ = x == y

instance Ord a => Ord (D s a) where
  compare (MkD x _) (MkD y _) = compare x y
