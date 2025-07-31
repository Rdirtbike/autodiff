{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.Autodiff (D, autodiff) where

import Control.Monad.ST (RealWorld, ST)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT (..))
import Data.Autodiff.MNum (MFloating, MFractional, MNum)
import Data.Autodiff.MNum qualified
import Data.Primitive.MutVar (MutVar, modifyMutVar', newMutVar, readMutVar, writeMutVar)
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (IO), unIO, unsafeIOToST)

data Tag = MkT {-# UNPACK #-} !(PromptTag# ())

{-# INLINE newTag #-}
newTag :: IO Tag
newTag = IO $ \s -> case newPromptTag# s of
  (# s', t #) -> (# s', MkT t #)

{-# INLINE reset #-}
reset :: Tag -> IO () -> IO ()
reset (MkT t) (IO f) = IO $ prompt# t f

{-# INLINE shift0 #-}
shift0 :: ((a -> IO ()) -> IO ()) -> ReaderT Tag IO a
shift0 f = ReaderT $ \(MkT t) -> IO $ control0# t $ \g -> unIO $ f $ \x -> IO $ prompt# t $ g (# ,x #)

newtype M s a = MkM (ReaderT Tag IO a) deriving (Functor, Applicative, Monad)

data D s a = MkD !a {-# UNPACK #-} !(MutVar RealWorld a)

{-# INLINEABLE autodiff #-}
autodiff :: (Num a, Num b) => (D s a -> M s (D s b)) -> a -> ST s (b, a)
autodiff f x = unsafeIOToST $ do
  r <- newMutVar 0
  r' <- newMutVar 0
  t <- newTag
  let MkM yd = f $ MkD x r'
  reset t $ do
    MkD y y' <- runReaderT yd t
    writeMutVar y' 1
    writeMutVar r y
  y <- readMutVar r
  y' <- readMutVar r'
  pure (y, y')

{-# INLINE lift1 #-}
lift1 :: Num a => (a -> a) -> (a -> a -> a -> a) -> D s a -> M s (D s a)
lift1 f f' (MkD x x') = MkM $ shift0 $ \k -> do
  r <- newMutVar 0
  k $ MkD (f x) r
  y' <- readMutVar r
  modifyMutVar' x' $ f' x y'

{-# INLINE lift2 #-}
lift2 :: Num a => (a -> a -> a) -> (a -> a -> a -> a -> a) -> (a -> a -> a -> a -> a) -> D s a -> D s a -> M s (D s a)
lift2 f f1' f2' (MkD x x') (MkD y y') = MkM $ shift0 $ \k -> do
  r <- newMutVar 0
  k $ MkD (f x y) r
  z' <- readMutVar r
  modifyMutVar' x' (f1' x y z')
  modifyMutVar' y' (f2' x y z')

instance Num a => MNum (M s) (D s a) where
  (+) = lift2 (+) (\_ _ z' -> (+ z')) (\_ _ z' -> (+ z'))
  (*) = lift2 (*) (\_ y z' -> (+ z' * y)) (\x _ z' -> (+ z' * x))
  (-) = lift2 (-) (\_ _ z' -> (+ z')) (\_ _ z' -> (- z'))
  negate = lift1 negate $ \_ y' -> (- y')
  abs = lift1 abs $ \x y' -> (+ y' * signum x)
  signum (MkD x _) = MkM $ MkD (signum x) <$> lift (newMutVar 0)
  fromInteger n = MkM $ MkD (fromInteger n) <$> lift (newMutVar 0)

instance Fractional a => MFractional (M s) (D s a) where
  (/) = lift2 (/) (\_ y z' -> (+ z' / y)) (\x y z' -> (- z' * x / (y * y)))
  recip = lift1 recip $ \x y' -> (- y' / (x * x))
  fromRational x = MkM $ MkD (fromRational x) <$> lift (newMutVar 0)

instance Floating a => MFloating (M s) (D s a) where
  pi = MkM $ MkD pi <$> lift (newMutVar 0)
  exp = lift1 exp $ \x y' -> (+ y' * exp x)
  log = lift1 log $ \x y' -> (+ y' / x)
  sqrt = lift1 sqrt $ \x y' -> (- y' / sqrt x)
  (**) = lift2 (**) (\x y z' -> (+ z' * y * x ** (y - 1))) (\x y z' -> (+ z' * log x * x ** y))
  logBase = lift2 logBase (\x y z' -> (- z' * log y / (x * log x ^ (2 :: Int)))) (\x y z' -> (+ z' / (y * log x)))
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
  MkD x _ == MkD y _ = x == y

instance Ord a => Ord (D s a) where
  compare (MkD x _) (MkD y _) = compare x y
