{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.Autodiff.Internal where

import Data.IORef
import GHC.Exts
import GHC.IO

data Tag a = MkT (PromptTag# a)

newTag :: IO (Tag a)
newTag = IO $ \s -> case newPromptTag# s of
  (# s', t #) -> (# s', MkT t #)

prompt :: Tag a -> IO a -> IO a
prompt (MkT t) (IO f) = IO $ \s -> prompt# t f s

control :: Tag a -> ((b -> IO a) -> IO a) -> IO b
control (MkT t) f = IO $ \s -> control0# t (\g -> unIO $ f $ \x -> IO $ g (# ,x #)) s

data D a = MkD (Tag ()) a (IO (IORef a)) | MkC a

autodiff :: (Num a, Num b) => (D a -> D b) -> a -> IO (b, a)
autodiff f x = do
  r <- newIORef 0
  t <- newTag
  case f $ MkD t x $ pure r of
    MkC y -> pure (y, 0)
    MkD _ y yd -> do
      prompt t $ yd >>= (`writeIORef` 1)
      y' <- readIORef r
      pure (y, y')

lift :: Num a => (a -> a) -> (a -> a) -> D a -> D a
lift f _ (MkC x) = MkC $ f x
lift f f' (MkD t x xd) = MkD t (f x) $ do
  x' <- xd
  control t $ \k -> do
    r <- newIORef 0
    prompt t $ k r
    y' <- readIORef r
    modifyIORef' x' (+ f' x * y')

lift2 :: Num a => (a -> a -> a) -> (a -> a -> a) -> (a -> a -> a) -> D a -> D a -> D a
lift2 f _ f2' (MkC x) y = lift (f x) (f2' x) y
lift2 f f1' _ x (MkC y) = lift (`f` y) (`f1'` y) x
lift2 f f1' f2' (MkD t x xd) (MkD _ y yd) = MkD t (f x y) $ do
  x' <- xd
  y' <- yd
  control t $ \k -> do
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
  fromInteger n = MkC $ fromInteger n
