module TTest where

import Contract
import Contract.Analysis

-- simple tests for trigger analysis

ms n = n*30
ys n  = n*360

-- Barrier option on "Carlsberg" stock
equity = "Carlsberg"
maturity = ms 3
ex4if = checkWithin (strike !<! theobs) maturity
                    (scale (theobs - strike) (transfOne EUR "you" "me")) zero
    where strike = r 50.0
          theobs = obs (equity,0)

mkOpt i s = checkWithin (strike !<! theobs) (ms i)
            (scale (theobs - strike) (transfOne EUR "you" "me")) zero
    where strike = r s
          theobs = obs (equity,0)

test1 = allCs [ mkOpt 3 (40 + fromIntegral di) | di <- [0,1,2]]
test2 = allCs [ mkOpt i (fromIntegral i + 42) | i <- [0,1,2,3,4,5]]
test3 = allCs [test1,test2]


runtests = do putStrLn ("Carlsberg barrier options (settled):\n" ++
                        ppContr test3)
              putStrLn ("Contract horizon: " ++ show (horizon test3))
              putStrLn "Trigger values:"
              putStrLn (ppTriggers (triggers (0,10) test3))
