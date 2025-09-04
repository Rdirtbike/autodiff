{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Autodiff (Diff (D), Dual, autodiff, D0 (..), D1 (..), D2 (..)) where

import Control.Monad
import Data.Autodiff.Dual
import Data.Bitraversable
import Data.IORef

class Diff a where
  type D a
  start :: a -> IO (D a)
  cotangent :: D a -> IO a

autodiff :: forall a b. (Diff a, Num b) => (D a -> Dual b) -> a -> IO (b, a)
autodiff f x = do
  writeIORef tape mempty
  xd <- start x
  let MkD y y' = f xd
  writeIORef y' 1
  join $ readIORef tape
  x' <- cotangent xd
  pure (y, x')

newtype D0 a = Mk0 a

instance Num a => Diff (D0 a) where
  type D (D0 a) = Dual a
  start (Mk0 x) = MkD x <$> newIORef 0
  cotangent (MkD _ x') = Mk0 <$> readIORef x'

newtype D1 f a = Mk1 (f a)

instance (Traversable f, Diff a) => Diff (D1 f a) where
  type D (D1 f a) = f (D a)
  start (Mk1 x) = traverse start x
  cotangent x = Mk1 <$> traverse cotangent x

newtype D2 f a b = Mk2 (f a b)

instance (Bitraversable f, Diff a, Diff b) => Diff (D2 f a b) where
  type D (D2 f a b) = f (D a) (D b)
  start (Mk2 x) = bitraverse start start x
  cotangent x = Mk2 <$> bitraverse cotangent cotangent x

deriving via D0 Double instance Diff Double

deriving via D0 Float instance Diff Float

deriving via D0 Int instance Diff Int

deriving via D0 Integer instance Diff Integer

deriving via D0 Word instance Diff Word

deriving via D1 [] a instance Diff a => Diff [a]

deriving via D2 (,) a b instance (Diff a, Diff b) => Diff (a, b)
