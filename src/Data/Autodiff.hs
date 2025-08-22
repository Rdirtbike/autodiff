module Data.Autodiff (D, autodiff) where

import Control.Monad (join)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)

data D a = MkD !a {-# UNPACK #-} !(IORef a)

{-# NOINLINE backprop #-}
backprop :: IORef (IO ())
backprop = unsafePerformIO $ newIORef mempty

{-# INLINEABLE autodiff #-}
autodiff :: (Num a, Num b) => (D a -> D b) -> a -> (b, a)
autodiff f x = unsafeDupablePerformIO $ do
  writeIORef backprop mempty
  r <- newIORef 0
  let MkD y y' = f $ MkD x r
  writeIORef y' 1
  join $ readIORef backprop
  x' <- readIORef r
  pure (y, x')

{-# INLINE lift #-}
lift :: Num a => a -> D a
lift x = unsafeDupablePerformIO $ MkD x <$> newIORef 0

{-# INLINE lift1 #-}
lift1 ::
  Num a =>
  (a -> a) ->
  (a -> a -> a -> a) ->
  D a ->
  D a
lift1 f f' (MkD x x') = unsafeDupablePerformIO $ do
  r <- newIORef 0
  modifyIORef' backprop $ \g -> do
    y' <- readIORef r
    modifyIORef' x' $ f' x y'
    g
  pure $ MkD (f x) r

{-# INLINE lift2 #-}
lift2 ::
  Num a =>
  (a -> a -> a) ->
  (a -> a -> a -> a -> a) ->
  (a -> a -> a -> a -> a) ->
  D a ->
  D a ->
  D a
lift2 f f1' f2' (MkD x x') (MkD y y') = unsafeDupablePerformIO $ do
  r <- newIORef 0
  modifyIORef' backprop $ \g -> do
    z' <- readIORef r
    modifyIORef' x' $ f1' x y z'
    modifyIORef' y' $ f2' x y z'
    g
  pure $ MkD (f x y) r

instance Num a => Num (D a) where
  (+) = lift2 (+) (\_ _ z' -> (+ z')) (\_ _ z' -> (+ z'))
  (*) = lift2 (*) (\_ y z' -> (+ z' * y)) (\x _ z' -> (+ z' * x))
  (-) = lift2 (-) (\_ _ z' -> (+ z')) (\_ _ z' -> (- z'))
  negate = lift1 negate $ \_ y' -> (- y')
  abs = lift1 abs $ \x y' -> (+ y' * signum x)
  signum (MkD x _) = lift $ signum x
  fromInteger n = lift $ fromInteger n

instance Fractional a => Fractional (D a) where
  (/) = lift2 (/) (\_ y z' -> (+ z' / y)) (\x y z' -> (- z' * x / (y * y)))
  recip = lift1 recip $ \x y' -> (- y' / (x * x))
  fromRational x = lift $ fromRational x

instance Floating a => Floating (D a) where
  pi = lift pi
  exp = lift1 exp $ \x y' -> (+ y' * exp x)
  log = lift1 log $ \x y' -> (+ y' / x)
  sqrt = lift1 sqrt $ \x y' -> (+ 0.5 * y' / sqrt x)
  (**) =
    lift2
      (**)
      (\x y z' -> (+ z' * y * x ** (y - 1)))
      (\x y z' -> (+ z' * log x * x ** y))
  logBase =
    lift2
      logBase
      (\x y z' -> (- z' * log y / (x * log x ^ (2 :: Int))))
      (\x y z' -> (+ z' / (y * log x)))
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

instance Eq a => Eq (D a) where
  MkD x _ == MkD y _ = x == y

instance Ord a => Ord (D a) where
  compare (MkD x _) (MkD y _) = compare x y
