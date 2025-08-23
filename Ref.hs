module Main (main) where

import Numeric.AD (grad')
import System.Environment (getArgs)

main :: IO ()
main = do
  [ns] <- getArgs
  n <- readIO @Double ns
  let !(!_, !_) = grad' product [1 .. n]
  pure ()
