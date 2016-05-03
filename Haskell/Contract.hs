module Contract
    ( Contract -- without constructors
    , MContract
    , Party
    -- smart constructors and convenience functions, defined in Contract.Type
    , zero, transfOne, transl, iff, checkWithin, both, allCs, scale, flow, foreach
    , ppContr
    -- dates:
    , Date, DateError, dateDiff, at, addDays, ppDate, ppDays
    -- expressions:
    , Var, Currency(..) -- all constructors exported
    , BoolE, IntE, RealE -- Expr itself is not exported
    -- constructors
    , i, r, b, v, pair, first, second, acc, obs, chosenBy
    -- operators, unless in Num instance
    , (!<!), (!=!), (!|!), maxx, minn, nott
    -- predicates, expression translate
    , certainExp, translExp
    -- pretty-printer
    , ppExp
    -- evaluation
    , MEnv, emptyFrom, emptyEnv
    , addFixing, addFixings, fixings
    , promoteEnv
    , simplifyExp
    , eval -- , evalI, evalR, evalB
    -- printing cashflows:
    , Cashflow, ppCashflow, ppCashflows, cashflows
    ) where

import Contract.Date
import Contract.Expr
import Contract.ExprIO
import Contract.Type
import Contract.Environment

import Data.List(sortBy)
import Data.Ord(comparing)

type Cashflow = (Date, Currency, Party, Party, Bool, RealE)

-- format a cash flow
ppCashflow :: Int -> Cashflow -> String
ppCashflow w (d,cur,p1,p2,certain,e) =
    unwords [ ppDate d, ppCertain certain, pad w (sq (p1 ++ "->" ++ p2)),
              show cur, ppExp (simplifyExp emptyEnv e)]
    where sq s = "[" ++ s ++ "]"
          pad w s = s ++ replicate (w - length s) ' '
          ppCertain b = if b then "Certain" else "Uncertain"

-- | print a series of cashflows (no sorting applied here)
ppCashflows :: [Cashflow] -> String
ppCashflows [] = "no cashflows"
ppCashflows l = unlines (map (ppCashflow sz) l)
    where sz = maximum $
               map (\(_,_,p1,p2,_,_) -> length p1 + length p2 + 4) l

-- | extract all (certain and uncertain) cashflows of a contract, sorted by date
cashflows :: (Date, Contract) -> [ Cashflow ]
cashflows (d,c) = sortBy (comparing cfDate) (cf (d, c, 1, True))
    where cfDate (d,_,_,_,_,_) = d
          cf (d,c,s,certain) =
            case c of
                Zero -> []
                TransfOne c p1 p2 -> [(d,c,p1,p2,certain,s)]
                Both c1 c2 -> cf (d,c1,s,certain) ++ cf (d,c2,s,certain)
                Scale s' c -> cf (d,c,s * s',certain)
                Transl i c2 -> cf (addDays i d, c2, s, certain)
                If b c1 c2 -> cf (d,c1,s,False) ++ cf (d,c2,s,False)
                CheckWithin e i c1 c2 ->
                    if i < 0 then cf (d,c1,s,False) ++ cf (d,c2,s,False)
                    else cf (d,c1,s,False) ++
                         cf(addDays 1 d,
                            checkWithin (translExp e 1) (i-1) c1 c2,
                            s, certain)
              -- Let(v,e,c) -> cf (d,c,s,certain) (* MEMO: check this *)

-- more here?
