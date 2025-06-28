module Main (main) where

import Data.Autodiff
import Data.Vector.Generic qualified as V
import Data.Vector.Unboxed qualified as U
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "Need arguemnt"
    x : _ -> do
      n <- readIO @Int x
      print $ gradient V.product $ U.enumFromN (1 :: Double) n
