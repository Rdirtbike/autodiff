module Main (main) where

import Data.Autodiff (autodiff)
import System.Environment (getArgs)

main :: IO ()
main = do
  [ns] <- getArgs
  n <- readIO @Int ns
  let !(!_, !_) = autodiff (^ n) (2 :: Integer)
  pure ()
