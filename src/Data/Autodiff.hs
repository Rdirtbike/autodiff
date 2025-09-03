module Data.Autodiff (D, autodiff, asConst) where

import Control.Monad (join)
import Data.Autodiff.VectorSpace (VectorSpace (..))
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafeDupablePerformIO)

data D s a = MkD !a {-# UNPACK #-} !(IORef a)

{-# NOINLINE tape #-}
tape :: IORef (IO ())
tape = unsafeDupablePerformIO $ newIORef mempty

{-# INLINEABLE asConst #-}
asConst :: (Integral a, Num b) => D s a -> b
asConst (MkD x _) = fromIntegral x

{-# INLINEABLE autodiff #-}
autodiff :: (VectorSpace a, Num b) => (forall s. D s a -> D s b) -> a -> (b, a)
autodiff f x = unsafeDupablePerformIO $ do
  writeIORef tape mempty
  r <- newIORef zero
  let MkD y y' = f $ MkD x r
  writeIORef y' 1
  join $ readIORef tape
  x' <- readIORef r
  pure (y, x')

{-# INLINE lift #-}
lift :: a -> a -> D s a
lift z x = unsafeDupablePerformIO $ do
  r <- newIORef z
  pure $ MkD x r

{-# INLINE lift1 #-}
lift1 ::
  b ->
  (a -> b) ->
  (a -> b -> a -> a) ->
  D s a ->
  D s b
lift1 z f f' (MkD x x') = unsafeDupablePerformIO $ do
  r <- newIORef z
  modifyIORef' tape $ \backprop -> do
    y' <- readIORef r
    modifyIORef' x' $ f' x y'
    backprop
  pure $ MkD (f x) r

{-# INLINE lift2 #-}
lift2 ::
  b ->
  (a -> a -> b) ->
  (a -> a -> b -> a -> a) ->
  (a -> a -> b -> a -> a) ->
  D s a ->
  D s a ->
  D s b
lift2 z f f1' f2' (MkD x x') (MkD y y') = unsafeDupablePerformIO $ do
  r <- newIORef z
  modifyIORef' tape $ \backprop -> do
    z' <- readIORef r
    modifyIORef' x' $ f1' x y z'
    modifyIORef' y' $ f2' x y z'
    backprop
  pure $ MkD (f x y) r

{-# INLINE project #-}
project :: (a -> b -> c) -> D s a -> D s b -> c
project f (MkD x _) (MkD y _) = f x y

instance Num a => Num (D s a) where
  (+) = lift2 0 (+) (\_ _ z' -> (+ z')) (\_ _ z' -> (+ z'))
  (*) = lift2 0 (*) (\_ y z' -> (+ z' * y)) (\x _ z' -> (+ z' * x))
  (-) = lift2 0 (-) (\_ _ z' -> (+ z')) (\_ _ z' -> (- z'))
  negate = lift1 0 negate $ \_ y' -> (- y')
  abs = lift1 0 abs $ \x y' -> (+ y' * signum x)
  signum (MkD x _) = lift 0 $ signum x
  fromInteger n = lift 0 $ fromInteger n

instance Fractional a => Fractional (D s a) where
  (/) = lift2 0 (/) (\_ y z' -> (+ z' / y)) (\x y z' -> (- z' * x / (y * y)))
  recip = lift1 0 recip $ \x y' -> (- y' / (x * x))
  fromRational x = lift 0 $ fromRational x

instance Floating a => Floating (D s a) where
  pi = lift 0 pi
  exp = lift1 0 exp $ \x y' -> (+ y' * exp x)
  log = lift1 0 log $ \x y' -> (+ y' / x)
  sqrt = lift1 0 sqrt $ \x y' -> (+ 0.5 * y' / sqrt x)
  (**) =
    lift2
      0
      (**)
      (\x y z' -> (+ z' * y * x ** (y - 1)))
      (\x y z' -> (+ z' * log x * x ** y))
  logBase =
    lift2
      0
      logBase
      (\x y z' -> (- z' * log y / (x * log x ^ (2 :: Int))))
      (\x y z' -> (+ z' / (y * log x)))
  sin = lift1 0 sin $ \x y' -> (+ y' * cos x)
  cos = lift1 0 cos $ \x y' -> (- y' * sin x)
  tan = lift1 0 tan $ \x y' -> (+ y' / cos x ^ (2 :: Int))
  asin = lift1 0 asin $ \x y' -> (+ y' / sqrt (1 - x * x))
  acos = lift1 0 acos $ \x y' -> (- y' / sqrt (1 - x * x))
  atan = lift1 0 acos $ \x y' -> (+ y' / (1 + x * x))
  sinh = lift1 0 sinh $ \x y' -> (+ y' * cosh x)
  cosh = lift1 0 cosh $ \x y' -> (+ y' * sinh x)
  tanh = lift1 0 tanh $ \x y' -> (+ y' / cosh x ^ (2 :: Int))
  asinh = lift1 0 asinh $ \x y' -> (+ y' / sqrt (x * x + 1))
  acosh = lift1 0 acosh $ \x y' -> (+ y' / sqrt (x * x - 1))
  atanh = lift1 0 atanh $ \x y' -> (+ y' / (1 - x * x))

instance Eq a => Eq (D s a) where
  (==) = project (==)
  (/=) = project (/=)

instance Ord a => Ord (D s a) where
  compare = project compare
  (<) = project (<)
  (>) = project (>)
  (<=) = project (<=)
  (>=) = project (>=)
