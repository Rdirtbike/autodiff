module Data.Autodiff (D, autodiff, asConst) where

import Control.Monad (join)
import Data.Autodiff.Internal (D (..), tape)
import Data.Autodiff.VectorSpace (VectorSpace (zero))
import Data.IORef (newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafeDupablePerformIO)

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

{-# INLINEABLE asConst #-}
asConst :: (Integral a, Num b) => D s a -> b
asConst (MkD x _) = fromIntegral x
