module Data.Autodiff (D, autodiff) where

import Control.Monad.ST (ST, runST)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT (..))
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef, writeSTRef)

data D s a = MkD a (ContT () (ST s) (STRef s a))

autodiff :: (Num a, Num b) => (forall s. D s a -> D s b) -> a -> (b, a)
autodiff f x = runST $ do
  r <- newSTRef 0
  let MkD y yd = f $ MkD x $ pure r
  runContT yd (`writeSTRef` 1)
  y' <- readSTRef r
  pure (y, y')

{-# INLINE lift1 #-}
lift1 :: Num a => (a -> a) -> (a -> a -> a -> a) -> D s a -> D s a
lift1 f f' (MkD x xd) = MkD (f x) $ do
  !x' <- xd
  ContT $ \k -> do
    r <- newSTRef 0
    k r
    y' <- readSTRef r
    modifySTRef' x' $ f' x y'

{-# INLINE lift2 #-}
lift2 :: Num a => (a -> a -> a) -> (a -> a -> a -> a -> a) -> (a -> a -> a -> a -> a) -> D s a -> D s a -> D s a
lift2 f f1' f2' (MkD x xd) (MkD y yd) = MkD (f x y) $ do
  !x' <- xd
  !y' <- yd
  ContT $ \k -> do
    r <- newSTRef 0
    k r
    z' <- readSTRef r
    modifySTRef' x' (f1' x y z')
    modifySTRef' y' (f2' x y z')

instance Num a => Num (D s a) where
  (+) = lift2 (+) (\_ _ z' -> (+ z')) (\_ _ z' -> (+ z'))
  (*) = lift2 (*) (\_ y z' -> (+ z' * y)) (\x _ z' -> (+ z' * x))
  (-) = lift2 (-) (\_ _ z' -> (+ z')) (\_ _ z' -> (- z'))
  negate = lift1 negate $ \_ y' -> (- y')
  abs = lift1 abs $ \x y' -> (+ y' * signum x)
  signum (MkD x _) = MkD (signum x) $ lift $ newSTRef 0
  fromInteger n = MkD (fromInteger n) $ lift $ newSTRef 0

instance Fractional a => Fractional (D s a) where
  (/) = lift2 (/) (\_ y z' -> (+ z' / y)) (\x y z' -> (- z' * x / (y * y)))
  recip = lift1 recip $ \x y' -> (- y' / (x * x))
  fromRational x = MkD (fromRational x) $ lift $ newSTRef 0

instance Floating a => Floating (D s a) where
  pi = MkD pi $ lift $ newSTRef 0
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
