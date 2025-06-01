module Data.Autodiff.DMVec (DMVec) where

import Data.Vector.Generic.Mutable (MVector (..))

data DMVec v s a

instance MVector (DMVec v) a where
  basicLength x = case x of {}
  basicUnsafeSlice _ _ x = case x of {}
  basicOverlaps x = case x of {}
  basicUnsafeNew _ = pure $ error "Cannot create a mutable differential vector, no implementation"
  basicInitialize x = case x of {}
  basicUnsafeRead x = case x of {}
  basicUnsafeWrite x = case x of {}
