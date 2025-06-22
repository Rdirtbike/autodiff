module Main (main) where

import Data.Autodiff
import Data.Autodiff.Mode
import Data.Bifunctor
import Data.Vector.Unboxed (Vector)
import GHC.IsList

main :: IO ()
main = print $ second getDeriv $ autodiff f 5

f :: (Mode m) => D s m Int -> D s m (Vector Int)
f x = fromList $ zipWith (^) (replicate 5 x) [1 :: Int ..]
