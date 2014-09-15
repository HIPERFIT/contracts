{-# LANGUAGE GADTs #-}
module Contract.Analysis
    ( horizon
    , Trigger
    , triggers
    , branchBounds
    , ppTriggers
    -- dependencies
    , Dependencies(..), Dependency(..), eDependsOn, cDependsOn
    ) where

import Contract.Type
import Contract.Expr
import Contract.Date
import Contract.Environment

import Data.Maybe
import Data.List
import Text.Printf

-- | horizon of a contract, i.e. maximum time until fulfilment. Never negative.
horizon :: Contract -> Int
horizon     Zero       = 0
horizon (TransfOne _ _ _) = 0
horizon (Scale _ c)    = horizon c
horizon (Both c1 c2)   = max (horizon c1) (horizon c2)
horizon (Transl i c)   = i + horizon c -- (* negative if i < 0 *)
horizon (If _ c1 c2)   = max (horizon c1) (horizon c2)
horizon (CheckWithin _ i c1 c2) = i + max (horizon c1) (horizon c2)
-- horizon (Let(_,_,c)) = horizon c


-- contract trigger value analysis, helper functions

-- | merge two sorted lists, dropping identical values
mergeUniq :: Ord a => [a] -> [a] -> [a]
mergeUniq xs [] = xs
mergeUniq [] ys = ys
mergeUniq (x:xs) (y:ys) = case compare x y of
                            LT -> x : mergeUniq xs (y:ys)
                            GT -> y : mergeUniq (x:xs) ys
                            EQ -> x : mergeUniq xs ys

-- | trigger representation: Obs. string, time range (from,to), values
data Trigger = Trig {tr_obs :: String,
                     tr_start, tr_end :: Int,
                     tr_values :: [Double] }
trig :: String -> Int -> Int -> [Double] -> Trigger
trig = Trig

-- | trigger merge helper.
trMerge' :: Trigger -> [Trigger] -> [Trigger]
trMerge' tr [] = [tr]
trMerge' tr@Trig {tr_obs=s, tr_start=d1, tr_end=d2, tr_values=vs }
         (tr'@Trig {tr_obs=s',tr_start=d1', tr_end=d2', tr_values=vs' } : trs)
    | s /= s' = tr' : trMerge' tr trs -- different observables
    | s == s' =
{-   compares intervals and splits into several (2 or 3) resulting ones:
        ---------------------  (3 resulting, overlap)
----------------------

   -------------
----------------------         (3 resulting, inclusion)

-------    -------             (2 resulting, disjoint)

       -----------             (2 results, simple inclusion)
------------------

------|----- and vs = vs'      (merge opportunity)
-}
        {- merge opportunity. However, might be desirable to keep apart
        if vs == vs' && (d2 == d1'+1 || d1 == d2'+1)
        then trMerge' tr{tr_start=min d1 d1', tr_end=max d2 d2'} trs
        else -}
        if d2 < d1' || d2' < d1 -- disjoint, continue merging
        then tr' : trMerge' tr trs
        else
            if d1 == d1'
            then if d2 == d2' -- identical ranges:
                 then tr{tr_values = mergeUniq vs vs'} : trs
                 else -- simple inclusion, and we know d2 /= d2'
                     let lo   = min d2 d2'
                         t1   = tr { tr_end = lo,
                                     tr_values = mergeUniq vs vs' }
                         t2   = tr { tr_start=lo+1, tr_end=max d2 d2',
                                     tr_values= if d2 < d2' then vs' else vs }
                     in trMerge (t1 : t2 : trs)
            else if d2 == d2' -- simple inclusion, d1 /= d1'
             then let hi   = max d1 d1'
                      t1   = tr {tr_start=min d1 d1', tr_end = hi,
                                 tr_values = if d1 < d1' then vs else vs' }
                      t2   = tr {tr_start=hi+1, tr_end=d2,
                                 tr_values= mergeUniq vs vs' }
                  in trMerge (t1 : t2 : trs)
             else -- d1 /= d1', d2 /= d2'
                 if d1 < d1' && d2' < d2 -- inclusion of tr'
                 then trMerge ( tr { tr_end = d1'-1 } :
                                tr' { tr_values = mergeUniq vs vs'} :
                                tr { tr_start=d2'+1 } : trs )
                 else if d1' < d1 && d2 < d2' -- inclusion of tr
                  then trMerge ( tr' { tr_end=d1-1 } :
                                 tr  { tr_values=mergeUniq vs vs' } :
                                 tr' { tr_start=d2+1} : trs )
                  else -- real overlap
                      let (mid1,mid2) = (max d1 d1', min d2 d2')
                          t1 = tr { tr_start=min d1 d1', tr_end=mid1-1,
                                    tr_values= if d1 < d1' then vs else vs' }
                          t2 = tr { tr_start=mid1, tr_end=mid2,
                                    tr_values=mergeUniq vs vs' }
                          t3 = tr { tr_start=mid2+1, tr_end=max d2 d2',
                                    tr_values= if d2 < d2' then vs' else vs }
                      in trMerge ( t1 : t2 : t3 : trs )

-- | merging all triggers in the list (foldr) 
trMerge :: [Trigger] -> [Trigger]
trMerge = foldr trMerge' []

tryEvalR :: RealE -> Maybe Double
tryEvalR e = case eval emptyEnv e of { R d -> Just d; _ -> Nothing }

-- | analyses an expression for triggers. Returns list of triggers, using given time range as starting point for the analysis
triggersExp :: (Int,Int) -> BoolE -> [Trigger]
triggersExp (x,y) (Less (R v) (Obs (str,day)))
    = [ trig str (x+day) (y+day) [v] ]
triggersExp (x,y) (Less e1 (Obs (str,day)))
    = maybe [] (\v -> [ trig str (x+day) (y+day) [v] ] ) (tryEvalR e1)
triggersExp (x,y) (Less (Obs(s,d)) e1) 
    = maybe [] (\v -> [trig s (x+d) (y+d) [v] ] ) (tryEvalR e1)
triggersExp (x,y) (Or e1 e2)
    = trMerge (triggersExp (x,y) e1 ++ triggersExp (x,y) e2)
triggersExp (x,y) (Not e1) = triggersExp (x,y) e1
-- more cases? We do not consider "Equal", would require modified result type
{-
triggersExp ts exp = []
-}
triggersExp ts e = error ("nope " ++ show e ++ ", " ++ show ts)

-- | determine all trigger values for a contract, considering the given relative time range (starting at (0,0), expanded any time a construct introduces a duration
triggers :: (Int,Int) -> Contract -> [Trigger] 
triggers  _ (Zero) = []
triggers _ (TransfOne _ _ _) = []
triggers ts (Scale _ c) = triggers ts c
triggers ts (Both c1 c2) = trMerge (triggers ts c1 ++ triggers ts c2)
triggers (t1,t2) (Transl i c) = triggers (t1+i, t2+i) c
triggers (t1,t2) (If e c1 c2) 
    = trMerge (triggersExp (t1,t2) e ++ -- triggering this decision
               triggers (t1,t2) c1 ++ triggers (t1,t2) c2) -- further
triggers (t1,t2) (CheckWithin e d c1 c2) 
    = trMerge (triggersExp (t1,t2+d) e ++ -- triggering this decision
               triggers (t1,t2+d) c1 ++ triggers (t1+d, t2+d) c2) -- further

-- | format a list of triggers, one per line
ppTriggers :: [Trigger] -> String
ppTriggers     [] = ""
ppTriggers (tr:rest) 
    = tr_obs tr ++ " from day " ++ show (tr_start tr) ++ " to " 
      ++ show (tr_end tr) ++ ": "
      ++ concat (intersperse ", " (map ppReal (tr_values tr))) ++
      "\n" ++ ppTriggers rest

branchBounds :: MContract -> [Trigger]
branchBounds (d,c) = triggers (0,0) c

-----------------------------------------------------------------------


-- | dependency (of an expression or contract) on a single observable
data Dependency 
    = Dep { d_obs :: String,      -- ^ observable
            d_start, d_end :: Int -- ^ dependency range (Note: from
                                  -- start to end-1)
          }
      deriving (Eq,Show)

-- | represents all dependencies 
data Dependencies
    = Deps [Dependency] -- ^ list sorted by observable, then by start
                        -- No range overlaps allowed.
      deriving (Eq,Show)

-- helper functions
-- | insert a 'Dependency' into 'Dependencies'
insertD :: Dependency -> Dependencies -> Dependencies
insertD d (Deps ds) = Deps (ds1 ++ ins d ds2)
    where (ds1, ds2) = break ((d_obs d ==) . d_obs) ds
          ins d [] = [d]
          ins d (d':ds) | d_end d   < d_start d' = d : d' : ds
                        | d_end d'  < d_start d  = d' : ins d ds
                        -- otherwise: overlap, merge d with d'
                        | otherwise 
                            = d {d_start = min (d_start d) (d_start d'),
                                 d_end = max (d_end d) (d_end d')} 
                              : ds

-- | merge two dependencies
mergeDs :: Dependencies -> Dependencies -> Dependencies
mergeDs (Deps ds1) ds2 = foldr insertD ds2 ds1

-- | extracts all observables/choices an expression 'eDependsOn' 
eDependsOn :: Expr a -> Dependencies
-- base functionality:
eDependsOn (Obs (s,d)) = Deps [Dep s d (d+1)] 
eDependsOn (ChosenBy (s,d)) = Deps [Dep s d (d+1)]
-- Note: +1 on the end. This representation is easier to merge.
-- recursion: easy cases
eDependsOn (Pair a b) = mergeDs (eDependsOn a) (eDependsOn b)
eDependsOn (Fst p) = eDependsOn p -- MEMO: can lead to fake dep.s!
eDependsOn (Snd p) = eDependsOn p
eDependsOn (Not a) = eDependsOn a
eDependsOn (Arith _ a b) = mergeDs (eDependsOn a) (eDependsOn b)
eDependsOn (Less a b)  = mergeDs (eDependsOn a) (eDependsOn b)
eDependsOn (Equal a b) = mergeDs (eDependsOn a) (eDependsOn b)
-- more interesting case
eDependsOn (Acc (_,a) d b) = mergeDs (eDependsOn b) (extendD d (eDependsOn a))
-- boring cases: I R B V
eDependsOn _ = Deps [] -- no dependencies

-- | extend dependencies by a number of days
extendD :: Int -> Dependencies -> Dependencies
extendD i (Deps ds) 
    = foldr insertD (Deps []) (map ext ds) -- eliminate new overlaps
    where ext d = d { d_end = d_end d + i }

-- | translate dependencies by a given offset
transD :: Int -> Dependencies -> Dependencies
transD i (Deps ds) = Deps (map tr ds)
    where tr d = d { d_start = d_start d + i, d_end = d_end d + i }

-- | collects all 'Dependencies' on which a contract depends
cDependsOn :: Contract -> Dependencies
cDependsOn (Scale e c) = mergeDs (eDependsOn e) (cDependsOn c)
cDependsOn (Transl i c) = transD i (cDependsOn c)
cDependsOn (Both c1 c2) = mergeDs (cDependsOn c1) (cDependsOn c2)
cDependsOn (If e c1 c2) 
    = mergeDs (eDependsOn e) (mergeDs (cDependsOn c1) (cDependsOn c2))
cDependsOn (CheckWithin e d c1 c2) 
    = mergeDs (extendD d (eDependsOn e)) 
         (mergeDs (extendD d (cDependsOn c1)) (transD d (cDependsOn c2)))
-- Zero and TransfOne: no dependencies
cDependsOn _ = Deps []
