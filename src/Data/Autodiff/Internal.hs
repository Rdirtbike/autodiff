{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.Autodiff.Internal (D, autodiff) where

import Data.IORef
import GHC.Exts
import GHC.IO

data Tag a = MkT (PromptTag# a)

newTag :: IO (Tag a)
newTag = IO $ \s -> case newPromptTag# s of
  (# s', t #) -> (# s', MkT t #)

prompt :: Tag a -> IO a -> IO a
prompt (MkT t) (IO f) = IO $ \s -> prompt# t f s

control0 :: Tag a -> ((b -> IO a) -> IO a) -> IO b
control0 (MkT t) f = IO $ \s -> control0# t (\g -> unIO $ f $ \x -> IO $ g (# ,x #)) s

data D a = MkD a (Tag () -> IO (IORef a))

autodiff :: (Num a, Num b) => (D a -> D b) -> a -> IO (b, a)
autodiff f x = do
  r <- newIORef 0
  t <- newTag
  case f $ MkD x $ \_ -> pure r of
    MkD y yd -> do
      prompt t $ yd t >>= (`writeIORef` 1)
      y' <- readIORef r
      pure (y, y')

lift :: Num a => (a -> a) -> (a -> a) -> D a -> D a
lift f f' (MkD x xd) = MkD (f x) $ \t -> do
  x' <- xd t
  control0 t $ \k -> do
    r <- newIORef 0
    prompt t $ k r
    y' <- readIORef r
    modifyIORef' x' (+ f' x * y')

lift2 :: Num a => (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> D a -> D a -> D a
lift2 f f1' f2' (MkD x xd) (MkD y yd) = MkD (f x y) $ \t -> do
  x' <- xd t
  y' <- yd t
  control0 t $ \k -> do
    r <- newIORef 0
    prompt t $ k r
    z' <- readIORef r
    modifyIORef' x' (+ f1' x y * z')
    modifyIORef' y' (+ f2' x y * z')

instance Num a => Num (D a) where
  (+) = lift2 (+) (\_ _ -> 1) (\_ _ -> 1)
  (*) = lift2 (*) (\_ y -> y) const
  negate = lift negate (const $ -1)
  abs = lift abs signum
  signum = lift abs (const 0)
  fromInteger n = MkD (fromInteger n) $ \_ -> newIORef 0
