{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.Autodiff (D, autodiff) where

import Data.IORef
import GHC.Exts
import GHC.IO

data Tag a = MkT {-# UNPACK #-} !(PromptTag# a)

newTag :: IO (Tag a)
newTag = IO $ \s -> case newPromptTag# s of
  (# s', t #) -> (# s', MkT t #)

reset :: Tag a -> IO a -> IO a
reset (MkT t) (IO f) = IO $ \s -> prompt# t f s

shift0 :: Tag a -> ((b -> IO a) -> IO a) -> IO b
shift0 (MkT t) f = IO $ \s -> control0# t (\g -> unIO $ f $ \x -> IO $ prompt# t $ g (# ,x #)) s

data D a = MkD a (Tag () -> IO (IORef a))

autodiff :: (Num a, Num b) => (D a -> D b) -> a -> IO (b, a)
autodiff f x = do
  r <- newIORef 0
  t <- newTag
  let MkD y yd = f $ MkD x $ \_ -> pure r
  reset t $ yd t >>= (`writeIORef` 1)
  y' <- readIORef r
  pure (y, y')

{-# INLINE lift #-}
lift :: Num a => (a -> a) -> (a -> a) -> D a -> D a
lift f f' (MkD x xd) = MkD (f x) $ \t -> do
  x' <- xd t
  shift0 t $ \k -> do
    r <- newIORef 0
    k r
    y' <- readIORef r
    modifyIORef' x' (+ f' x * y')

{-# INLINE lift2 #-}
lift2 :: Num a => (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> D a -> D a -> D a
lift2 f f1' f2' (MkD x xd) (MkD y yd) = MkD (f x y) $ \t -> do
  x' <- xd t
  y' <- yd t
  shift0 t $ \k -> do
    r <- newIORef 0
    k r
    z' <- readIORef r
    modifyIORef' x' (+ f1' x y * z')
    modifyIORef' y' (+ f2' x y * z')

instance Num a => Num (D a) where
  (+) = lift2 (+) (\_ _ -> 1) (\_ _ -> 1)
  (*) = lift2 (*) (\_ y -> y) const
  (-) = lift2 (-) (\_ _ -> 1) (\_ _ -> -1)
  negate = lift negate (const $ -1)
  abs = lift abs signum
  signum = lift abs (const 0)
  fromInteger n = MkD (fromInteger n) $ \_ -> newIORef 0
