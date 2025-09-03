module Main (main) where

import Data.Autodiff (autodiff)
import GHC.IsList (toList)
import System.Environment (getArgs)

main :: IO ()
main = do
  [ns] <- getArgs
  n <- readIO @Double ns
  let !(!_, !_) = autodiff (product . toList) [1 .. n]
  pure ()
