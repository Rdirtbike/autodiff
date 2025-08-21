module Data.Autodiff (D, autodiff) where

import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Unique (Unique, newUnique)
import System.IO.Unsafe (unsafeDupablePerformIO)

data D s a = MkD a Unique ((IORef a -> IO ()) -> IO ())

{-# INLINEABLE autodiff #-}
autodiff :: (Num a, Num b) => (forall s. D s a -> D s b) -> a -> (b, a)
autodiff f x = unsafeDupablePerformIO $ do
  u <- newUnique
  r <- newIORef 0
  let MkD y _ g = f $ MkD x u ($ r)
  g (`writeIORef` 1)
  y' <- readIORef r
  pure (y, y')

{-# INLINE lift #-}
lift :: Num a => a -> D s a
lift x = unsafeDupablePerformIO $ do
  u <- newUnique
  pure $ MkD x u (newIORef 0 >>=)

{-# INLINE lift1 #-}
lift1 ::
  Num a =>
  (a -> a) ->
  (a -> a -> a -> a) ->
  D s a ->
  D s a
lift1 f f' (MkD x _ xd) = unsafeDupablePerformIO $ do
  uy <- newUnique
  pure $ MkD (f x) uy $ \k -> xd $ \x' -> do
    r <- newIORef 0
    k r
    y' <- readIORef r
    modifyIORef' x' $ f' x y'

{-# INLINE lift2 #-}
lift2 ::
  Num a =>
  (a -> a -> a) ->
  (a -> a -> a -> a -> a) ->
  (a -> a -> a -> a -> a) ->
  D s a ->
  D s a ->
  D s a
lift2 f f1' f2' (MkD x ux xd) (MkD y uy yd) = unsafeDupablePerformIO $ do
  uz <- newUnique
  pure $ MkD (f x y) uz $ \k -> xd $ \x' ->
    if ux == uy
      then do
        r <- newIORef 0
        k r
        z' <- readIORef r
        modifyIORef' x' $ f1' x y z' . f2' x y z'
      else yd $ \y' -> do
        r <- newIORef 0
        k r
        z' <- readIORef r
        modifyIORef' x' $ f1' x y z'
        modifyIORef' y' $ f2' x y z'

instance Num a => Num (D s a) where
  (+) = lift2 (+) (\_ _ z' -> (+ z')) (\_ _ z' -> (+ z'))
  (*) = lift2 (*) (\_ y z' -> (+ z' * y)) (\x _ z' -> (+ z' * x))
  (-) = lift2 (-) (\_ _ z' -> (+ z')) (\_ _ z' -> (- z'))
  negate = lift1 negate $ \_ y' -> (- y')
  abs = lift1 abs $ \x y' -> (+ y' * signum x)
  signum (MkD x _ _) = lift $ signum x
  fromInteger n = lift $ fromInteger n

instance Fractional a => Fractional (D s a) where
  (/) = lift2 (/) (\_ y z' -> (+ z' / y)) (\x y z' -> (- z' * x / (y * y)))
  recip = lift1 recip $ \x y' -> (- y' / (x * x))
  fromRational x = lift $ fromRational x

instance Floating a => Floating (D s a) where
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

instance Eq a => Eq (D s a) where
  MkD x _ _ == MkD y _ _ = x == y

instance Ord a => Ord (D s a) where
  compare (MkD x _ _) (MkD y _ _) = compare x y
