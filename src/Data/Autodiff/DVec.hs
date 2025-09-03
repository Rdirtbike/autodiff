{-# LANGUAGE GADTs #-}

{- HLINT ignore "Use <>" -}

module Data.Autodiff.DVec (DVec, autodiffV, toVec, fromVec) where

import Control.Monad
import Data.Autodiff.Internal
import Data.IORef
import Data.Vector.Generic hiding (iforM_)
import Data.Vector.Generic.Mutable hiding (length, replicate)
import Data.Vector.Generic.Mutable qualified as M
import System.IO.Unsafe
import Prelude hiding (length, replicate, zipWith, (++))

data DVec v d = forall s a. d ~ D s a => MkV (v a) (Mutable v RealWorld a)

autodiffV :: (Vector v a, Num a, Num b) => (forall s. DVec v (D s a) -> D s b) -> v a -> (b, v a)
autodiffV f v = unsafeDupablePerformIO $ do
  writeIORef tape mempty
  vr <- M.replicate (length v) 0
  let MkD y y' = f $ MkV v vr
  writeIORef y' 1
  join $ readIORef tape
  v' <- unsafeFreeze vr
  pure (y, v')

toVec :: (Num a, Vector v a) => D s (v a) -> DVec v (D s a)
toVec (MkD v r) = unsafeDupablePerformIO $ do
  vr <- M.replicate (length v) 0
  modifyIORef' tape $ \backprop -> do
    v' <- unsafeFreeze vr
    modifyIORef' r $ zipWith (+) v'
    backprop
  pure $ MkV v vr

fromVec :: (Vector v a, Num a) => DVec v (D s a) -> D s (v a)
fromVec (MkV v vr) = unsafeDupablePerformIO $ do
  r <- newIORef $ replicate (length v) 0
  modifyIORef' tape $ \backprop -> do
    v' <- readIORef r
    iforM_ vr $ \i x' -> unsafeWrite vr i $ x' + unsafeIndex v' i
    backprop
  pure $ MkD v r
