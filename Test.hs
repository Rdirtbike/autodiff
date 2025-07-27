module Main (main) where

import Control.Exception
import Data.Autodiff
import Data.Functor
import System.Environment

main :: IO ()
main = do
  [ns] <- getArgs
  n <- readIO @Int ns
  y <- autodiff (^ n) (2 :: Int)
  void $ evaluate y
