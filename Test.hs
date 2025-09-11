module Main (main) where

import Data.Autodiff (autodiff)
import System.Environment (getArgs)

fib :: (Num a, Ord a) => a -> a
fib n
  | n <= 1 = n
  | otherwise = fib (n - 1) + fib (n - 2)

main :: IO ()
main = do
  [ns] <- getArgs
  n <- readIO @Int ns
  (!_, !_) <- autodiff fib n
  pure ()
