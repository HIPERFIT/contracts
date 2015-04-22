module TTest where

import Contract
import Contract.Analysis
import Contract.ExprIO

import Contract.Transform -- for branch elimination

import Contract.Date(Date, addDays) -- should be exported from Contract.hs...

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

c_d = read "2001-01-01"
e_d = read "2001-02-15"

elimEnv = addFixings ("Carlsberg", e_d) [40.5] (emptyFrom c_d)

runtests = do putStrLn ("Carlsberg barrier options (settled):\n" ++
                        ppContr test3)
              putStrLn ("Contract horizon: " ++ show (horizon test3))
              putStrLn "Trigger values:"
              putStrLn (ppTriggers (triggers (0,10) test3))
              putStrLn "\nEliminating branches from test1:"
              putStrLn $ ppContr $ snd (elimBranches elimEnv (c_d,test1))
