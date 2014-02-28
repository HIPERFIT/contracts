module DTest where

import Contract.Date

import qualified Control.Exception as E

testPP :: (a -> String) -> String -> a -> a -> IO ()
testPP pp s e1 e2 = let pr msg = putStrLn (s ++ ": " ++ msg)
                        pp1    = pp e1
                        pp2    = pp e2
                    in E.catch (if pp1 == pp2 then pr ": OK"
                                else pr (": ERROR, expected " ++ pp1
                                         ++ ", got " ++ pp2))
                           (\e -> pr ("EXN, " ++ show (e::E.SomeException)))

dtest :: (String, Date, Date) -> IO ()
dtest (s,d1,d2) = testPP ppDate s d1 d2

today = read "2013-01-01"

tests1 = [ ("add nothing", read "2013-01-01", addDays 0 today)
             , ("add one day", read "2013-01-02", addDays 1 today)
             , ("add one (non-leap) year", read "2014-01-01", addDays 365 today)
             , ("add January", read "2013-02-01", addDays 31 today)
             , ("add first 6 months of the year", 
                read "2013-07-01", addDays (31+28+31+30+31+30) today)
             ]

testDiff i = testPP show ("dateDiff test with difference " ++ show i)
                    i (dateDiff today (addDays i today))
testDiff2 dt i = dt ("dateDiff back and forth",
                     today, addDays (-i) (addDays i today))

runtests = do mapM_ testDiff [ 10*i-31 | i <- [0..35]]
              mapM_ (testDiff2 dtest) [ 25+10*i | i <- [0..9]]
              mapM_ dtest tests1
