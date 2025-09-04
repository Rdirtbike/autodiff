module Data.Autodiff.Dual (Dual (..), tape) where

import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import System.IO.Unsafe (unsafeDupablePerformIO)

data Dual a = MkD !a {-# UNPACK #-} !(IORef a)

{-# NOINLINE tape #-}
tape :: IORef (IO ())
tape = unsafeDupablePerformIO $ newIORef mempty

{-# INLINE lift #-}
lift :: a -> a -> Dual a
lift z x = unsafeDupablePerformIO $ do
  r <- newIORef z
  pure $ MkD x r

{-# INLINE lift1 #-}
lift1 ::
  b ->
  (a -> b) ->
  (a -> b -> a -> a) ->
  Dual a ->
  Dual b
lift1 z f f' (MkD x x') = unsafeDupablePerformIO $ do
  r <- newIORef z
  modifyIORef' tape $ \backprop -> do
    y' <- readIORef r
    modifyIORef' x' $ f' x y'
    backprop
  pure $ MkD (f x) r

{-# INLINE lift2 #-}
lift2 ::
  c ->
  (a -> b -> c) ->
  (a -> b -> c -> a -> a) ->
  (a -> b -> c -> b -> b) ->
  Dual a ->
  Dual b ->
  Dual c
lift2 z f f1' f2' (MkD x x') (MkD y y') = unsafeDupablePerformIO $ do
  r <- newIORef z
  modifyIORef' tape $ \backprop -> do
    z' <- readIORef r
    modifyIORef' x' $ f1' x y z'
    modifyIORef' y' $ f2' x y z'
    backprop
  pure $ MkD (f x y) r

{-# INLINE project #-}
project :: (a -> b -> c) -> Dual a -> Dual b -> c
project f (MkD x _) (MkD y _) = f x y

instance Num a => Num (Dual a) where
  (+) = lift2 0 (+) (\_ _ z' -> (+ z')) (\_ _ z' -> (+ z'))
  (*) = lift2 0 (*) (\_ y z' -> (+ z' * y)) (\x _ z' -> (+ z' * x))
  (-) = lift2 0 (-) (\_ _ z' -> (+ z')) (\_ _ z' -> (- z'))
  negate = lift1 0 negate $ \_ y' -> (- y')
  abs = lift1 0 abs $ \x y' -> (+ y' * signum x)
  signum (MkD x _) = lift 0 $ signum x
  fromInteger n = lift 0 $ fromInteger n

instance Fractional a => Fractional (Dual a) where
  (/) = lift2 0 (/) (\_ y z' -> (+ z' / y)) (\x y z' -> (- z' * x / (y * y)))
  recip = lift1 0 recip $ \x y' -> (- y' / (x * x))
  fromRational x = lift 0 $ fromRational x

instance Floating a => Floating (Dual a) where
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

instance Eq a => Eq (Dual a) where
  (==) = project (==)
  (/=) = project (/=)

instance Ord a => Ord (Dual a) where
  compare = project compare
  (<) = project (<)
  (>) = project (>)
  (<=) = project (<=)
  (>=) = project (>=)
