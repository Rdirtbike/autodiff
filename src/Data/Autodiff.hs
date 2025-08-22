{-# LANGUAGE Strict #-}

module Data.Autodiff (D, autodiff) where

import Control.Monad.Primitive (RealWorld)
import Data.IORef (IORef, atomicModifyIORef', modifyIORef, newIORef, readIORef, writeIORef)
import Data.Primitive.ByteArray (MutableByteArray, fillByteArray, newByteArray, readByteArray, writeByteArray)
import Data.Primitive.Types (Prim)
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)

type IOByteArray = MutableByteArray RealWorld

data D a = MkD a Int

{-# NOINLINE supply #-}
supply :: IORef Int
supply = unsafePerformIO $ newIORef 0

{-# INLINE next #-}
next :: IO Int
next = atomicModifyIORef' supply $ \i -> (i + 1, i)

{-# NOINLINE backprop #-}
backprop :: IORef (IOByteArray -> IO ())
backprop = unsafePerformIO $ newIORef mempty

{-# INLINEABLE autodiff #-}
autodiff :: forall a b. (Num a, Prim a, Num b, Prim b) => (D a -> D b) -> a -> (b, a)
autodiff f x = unsafeDupablePerformIO $ do
  writeIORef supply 1
  writeIORef backprop mempty
  let !(MkD y iy) = f $ MkD x 0
  n <- (8 *) <$> readIORef supply
  a <- newByteArray n
  fillByteArray a 0 n 0
  writeByteArray a iy (1 :: b)
  g <- readIORef backprop
  g a
  y' <- readByteArray a 0
  pure (y, y')

{-# INLINE lift #-}
lift :: Num a => a -> D a
lift x = unsafeDupablePerformIO $ MkD x <$> next

{-# INLINE lift1 #-}
lift1 ::
  (Num a, Prim a) =>
  (a -> a) ->
  (a -> a -> a -> a) ->
  D a ->
  D a
lift1 f f' (MkD x ix) = unsafeDupablePerformIO $ do
  iy <- next
  modifyIORef backprop $ \g a -> do
    y' <- readByteArray a iy
    x' <- readByteArray a ix
    writeByteArray a ix $ f' x y' x'
    g a
  pure $ MkD (f x) iy

{-# INLINE lift2 #-}
lift2 ::
  (Num a, Prim a) =>
  (a -> a -> a) ->
  (a -> a -> a -> a -> a) ->
  (a -> a -> a -> a -> a) ->
  D a ->
  D a ->
  D a
lift2 f f1' f2' (MkD x ix) (MkD y iy) = unsafeDupablePerformIO $ do
  iz <- next
  modifyIORef backprop $ \g a -> do
    z' <- readByteArray a iz
    x' <- readByteArray a ix
    writeByteArray a ix $ f1' x y z' x'
    y' <- readByteArray a iy
    writeByteArray a iy $ f2' x y z' y'
    g a
  pure $ MkD (f x y) iz

instance (Num a, Prim a) => Num (D a) where
  (+) = lift2 (+) (\_ _ z' -> (+ z')) (\_ _ z' -> (+ z'))
  (*) = lift2 (*) (\_ y z' -> (+ z' * y)) (\x _ z' -> (+ z' * x))
  (-) = lift2 (-) (\_ _ z' -> (+ z')) (\_ _ z' -> (- z'))
  negate = lift1 negate $ \_ y' -> (- y')
  abs = lift1 abs $ \x y' -> (+ y' * signum x)
  signum (MkD x _) = lift $ signum x
  fromInteger n = lift $ fromInteger n

instance (Fractional a, Prim a) => Fractional (D a) where
  (/) = lift2 (/) (\_ y z' -> (+ z' / y)) (\x y z' -> (- z' * x / (y * y)))
  recip = lift1 recip $ \x y' -> (- y' / (x * x))
  fromRational x = lift $ fromRational x

instance (Floating a, Prim a) => Floating (D a) where
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
