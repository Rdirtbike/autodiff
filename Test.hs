module Main (main) where

import Data.Autodiff (autodiff)
import System.Environment (getArgs)

main :: IO ()
main = do
  [ns] <- getArgs
  n <- readIO @Double ns
  (!_, !_) <- autodiff product [1..n]
  pure ()
