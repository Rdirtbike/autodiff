{-# LANGUAGE TypeFamilies #-}

module Data.Autodiff.Massiv (Diff, Array (..)) where

import Data.Autodiff.Internal
import Data.Autodiff.Mode
import Data.Kind (Type)
import Data.Massiv.Array.Unsafe (unsafeResize)
import Data.Massiv.Core
import Data.Massiv.Vector (size)
import Data.Typeable

data Diff (m :: Type -> Type) (r :: Type)

data instance Array (Diff m r) sh e where
  MkA :: {getA :: D s m (Array r sh a)} -> Array (Diff m r) sh (D s m a)

instance (Mode m, Typeable m, Strategy r) => Strategy (Diff m r) where
  setComp c (MkA (MkD a a')) = MkA $ MkD (setComp c a) $ dmap (setComp c) (setComp c) a'
  getComp (MkA (MkD a _)) = getComp a

instance (Mode m, Size r) => Size (Diff m r) where
  size (MkA (MkD a _)) = size a
  unsafeResize s (MkA (MkD a a')) = MkA $ MkD (unsafeResize s a) $ dmap (unsafeResize s) (unsafeResize $ size a) a'
