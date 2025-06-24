module Main (main) where

import Data.Autodiff
import Data.Autodiff.Mode
import Data.Bifunctor
import Data.Vector.Unboxed (Vector)
import GHC.IsList
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "Need arguemnt"
    x : _ -> do
      n <- readIO @Int x
      print $ second getGradient $ autodiff (product . toList) $ fromList @(Vector _) [1 .. n]
