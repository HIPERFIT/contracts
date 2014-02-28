module Main where

import qualified ETest as E
import qualified DTest as D
import qualified CTest as C
import qualified TTest as T

main = do putStrLn "running all tests"
          E.runtests
          D.runtests
          C.runtests
          T.runtests
