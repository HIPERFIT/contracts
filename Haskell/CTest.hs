module CTest where

import Contract
import Contract.Date
import Contract.Expr(ppReal)
import Contract.Transform(advance, simplify, dual)

-- simple tests for contracts (was "basiccontracts.sml")

you2me (d,v,c) = flow d (r v) c "you" "me"
me2you = dual . you2me

now = 0
today = read "2013-01-01" :: Date

todayIs = putStrLn ("Today is " ++ ppDate today ++ "\n")

months n = n*30
years n = n*360


report s (d,c) =
  do putStrLn "\n---REPORT BEGIN---"
     putStrLn ("Today is " ++ ppDate d)
     putStrLn (s ++ " - Contract:\n" ++ ppContr c)
     putStrLn "Cashflows:"
     putStrLn (ppCashflows (cashflows (d,c)))
     putStrLn "---REPORT END---"

-- (* Simple amortized loan *)
ex1 =
    let coupon = 11000.0
        principal = 30000.0
    in allCs [you2me(now,principal,EUR),
              me2you(months 1,coupon,EUR),
              me2you(months 2,coupon,EUR),
              me2you(months 3,coupon,EUR)]


-- (* Cross currency swap *)
ex2 =
    let coupon_eur = 1000.0
        coupon_dkk = 7000.0
    in allCs [allCs [me2you(months 0,coupon_dkk,DKK),
                     me2you(months 1,coupon_dkk,DKK),
                     me2you(months 2,coupon_dkk,DKK)],
            me2you(months 0,coupon_eur,EUR),
            me2you(months 1,coupon_eur,EUR),
            me2you(months 2,coupon_eur,EUR)]

ex2m = (today,ex2)

ex3 = advance 15 ex2m

-- (* Call option on "Carlsberg" stock *)
equity = "Carlsberg"
maturity = years 1
ex4 =
    let strike = 50.0
        nominal = 1000.0
        theobs = maxx (r 0.0) (obs (equity,0) - r strike)
    in scale (r nominal)
             (transl maturity
                     (scale theobs (transfOne EUR "you" "me")))

mature s c p =
    let m = (today, c)
        -- () = report (s ++ " - initial") m
        menv0 = emptyFrom today
        menv = addFixing (equity, addDays maturity today,p) menv0
        m' = simplify menv m
        m'' = advance maturity m'
    in report (s ++ " - at maturity; price(maturity)=" ++ ppReal p) m''

-- (* same call option, expressed with If *)
ex4if =
    let strike = 50.0
        nominal = 1000.0
        theobs = obs (equity,0)
    in scale (r nominal)
             (transl maturity
                    (iff (r strike !<! theobs)
                          (scale (theobs - r strike)
                                 (transfOne EUR "you" "me"))
                         zero))

-- (* should be:
-- val () = mature "Ex4if-79 (call option, strike=50.0)" ex4if 79.0
-- val () = mature "Ex4if-46 (call option, strike=50.0)" ex4if 46.0
--   (correct it alongside the tests.ok text file... *)

-- transfers once a week
onceAWeek c = foreach [0,7,14,21,28] c
payments = onceAWeek (scale 10 (transfOne DKK "you" "me"))

runtests =
  do todayIs
     report "Ex1 (swap)" (today,ex1)
     report "Ex2 (Fx-swap)" ex2m

     putStrLn "\nEx3: Cross-currency swap advanced half a month:"
     putStrLn (ppCashflows(cashflows ex3))

     mature "Ex4-79 (call option, strike=50.0)" ex4 79.0

     mature "Ex4if-79 (call option, strike=50.0)" ex4 79.0
     mature "Ex4if-46 (call option, strike=50.0)" ex4 46.0
     
