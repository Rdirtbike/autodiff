module Main (main) where

import Control.Monad.ST (stToIO)
import Data.Autodiff (autodiff)
import Data.Autodiff.MNum ((^))
import System.Environment (getArgs)
import Prelude hiding ((^))

main :: IO ()
main = do
  [ns] <- getArgs
  n <- readIO ns
  (!_, !_) <- stToIO $ autodiff (^ n) (2 :: Integer)
  pure ()
