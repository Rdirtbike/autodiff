{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff (D, autodiff, asConst) where

import Control.Monad (join, replicateM, zipWithM_)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import GHC.IsList (IsList (..))
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)

class VectorSpace v where
  zero :: v
  (.+) :: v -> v -> v

infixl 6 .+

instance Num a => VectorSpace [a] where
  zero = []

  (x : xs) .+ (y : ys) = x + y : xs .+ ys
  xs .+ [] = xs
  [] .+ ys = ys

newtype Field a = MkF a

instance Num a => VectorSpace (Field a) where
  zero = MkF 0
  MkF x .+ MkF y = MkF $ x + y

deriving via Field Double instance VectorSpace Double

deriving via Field Float instance VectorSpace Float

deriving via Field Int instance VectorSpace Int

deriving via Field Word instance VectorSpace Word

data D s a = MkD !a {-# UNPACK #-} !(IORef a)

{-# INLINEABLE asConst #-}
asConst :: (Integral a, Num b) => D s a -> b
asConst (MkD x _) = fromIntegral x

{-# NOINLINE backprop #-}
backprop :: IORef (IO ())
backprop = unsafePerformIO $ newIORef mempty

{-# INLINEABLE autodiff #-}
autodiff :: (VectorSpace a, Num b) => (forall s. D s a -> D s b) -> a -> (b, a)
autodiff f x = unsafeDupablePerformIO $ do
  writeIORef backprop mempty
  r <- newIORef zero
  let MkD y y' = f $ MkD x r
  writeIORef y' 1
  join $ readIORef backprop
  x' <- readIORef r
  pure (y, x')

{-# INLINE lift #-}
lift :: a -> a -> D s a
lift z x = unsafeDupablePerformIO $ MkD x <$> newIORef z

{-# INLINE lift1 #-}
lift1 ::
  b ->
  (a -> b) ->
  (a -> b -> a -> a) ->
  D s a ->
  D s b
lift1 z f f' (MkD x x') = unsafeDupablePerformIO $ do
  r <- newIORef z
  modifyIORef' backprop $ \g -> do
    y' <- readIORef r
    modifyIORef' x' $ f' x y'
    g
  pure $ MkD (f x) r

{-# INLINE lift2 #-}
lift2 ::
  c ->
  (a -> b -> c) ->
  (a -> b -> c -> a -> a) ->
  (a -> b -> c -> b -> b) ->
  D s a ->
  D s b ->
  D s c
lift2 z f f1' f2' (MkD x x') (MkD y y') = unsafeDupablePerformIO $ do
  r <- newIORef z
  modifyIORef' backprop $ \g -> do
    z' <- readIORef r
    modifyIORef' x' $ f1' x y z'
    modifyIORef' y' $ f2' x y z'
    g
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

instance Num a => IsList (D s [a]) where
  type Item (D s [a]) = D s a
  toList (MkD xs x') = unsafeDupablePerformIO $ do
    rs <- replicateM (length xs) $ newIORef 0
    modifyIORef' backprop $ \g -> do
      xs' <- traverse readIORef rs
      modifyIORef' x' (.+ xs')
      g
    pure $ zipWith MkD xs rs
  fromList xs = unsafeDupablePerformIO $ do
    r <- newIORef []
    modifyIORef' backprop $ \g -> do
      xs' <- readIORef r
      zipWithM_ (\xr x' -> modifyIORef' xr (+ x')) (fmap (\(MkD _ x') -> x') xs) xs'
      g
    pure $ MkD (fmap (\(MkD x _) -> x) xs) r
