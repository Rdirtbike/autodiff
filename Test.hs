module Main (main) where

import Data.Autodiff (autodiff)
import System.Environment (getArgs)

fib :: (Num a, Ord a) => a -> a
fib n = if n <= 1 then n else fib (n - 1) + fib (n - 2)

main :: IO ()
main = do
  [ns] <- getArgs
  n <- readIO @Int ns
  print $ autodiff fib n
