{-# LANGUAGE LexicalNegation #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE UnboxedTuples #-}

{- HLINT ignore "Parenthesize unary negation" -}

module Data.Autodiff (D, autodiff) where

import Data.IORef
import GHC.Exts
import GHC.IO

data Tag a = MkT {-# UNPACK #-} !(PromptTag# a)

{-# INLINE newTag #-}
newTag :: IO (Tag a)
newTag = IO $ \s -> case newPromptTag# s of
  (# s', t #) -> (# s', MkT t #)

{-# INLINE reset #-}
reset :: Tag a -> IO a -> IO a
reset (MkT t) (IO f) = IO $ \s -> prompt# t f s

{-# INLINE shift0 #-}
shift0 :: Tag a -> ((b -> IO a) -> IO a) -> IO b
shift0 (MkT t) f = IO $ \s -> control0# t (\g -> unIO $ f $ \x -> IO $ prompt# t $ g (# ,x #)) s

data D a = MkD a (Tag () -> IO (IORef a))

autodiff :: (Num a, Num b) => (D a -> D b) -> a -> (b, a)
autodiff f x = unsafeDupablePerformIO $ do
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
  negate = lift negate (const -1)
  abs = lift abs signum
  signum = lift abs (const 0)
  fromInteger n = MkD (fromInteger n) $ \_ -> newIORef 0

instance Fractional a => Fractional (D a) where
  (/) = lift2 (/) (\_ y -> 1 / y) (\x y -> -x / (y * y))
  recip = lift recip $ \x -> -1 / (x * x)
  fromRational x = MkD (fromRational x) $ \_ -> newIORef 0
