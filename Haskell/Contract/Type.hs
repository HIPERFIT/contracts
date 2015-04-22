{-# LANGUAGE ExistentialQuantification #-}

module Contract.Type
    ( Contract(..) -- constructors exported
    , MContract -- managed contract, including a start date
    , Party
    -- smart constructors and convenience functions
    , zero, transfOne, transl, iff, checkWithin, both, allCs, scale, flow
    -- pretty-printer
    , ppContr
    ) where

import Contract.Expr
import Contract.ExprIO
import Contract.Date
import Contract.Hash

-- | party of a contract. A simple string
type Party = String

-- | a managed contract is a contract with a start date
type MContract = (Date, Contract)

-- | the contract representation type
data Contract = Zero
              | TransfOne Currency Party Party -- ^ Atom: Transfer money
              | Scale RealE Contract -- ^ Scaling a contract by a RealE
              | Transl Int Contract -- ^ Translating a contract into the future
              | Both Contract Contract -- ^ Combining two contracts
              | If BoolE Contract Contract -- ^ Conditional contract
              | CheckWithin BoolE Int Contract Contract
                -- ^ Repeatedly checks every day, until given end, whether condition is true. When it is true, the first contract argument comes into effect. Otherwise (never true until end) the second contract comes into effect.
--              | forall a . Let (Expr a) (Expr a -> Contract)
                deriving (Show)

-- | computes hash of a contract, considering symmetry of 'Both' constructor
hashContr :: [Var] -> Contract -> Hash -> Hash
hashContr vs c a = 
    let ps = hashPrimes
    in case c of
         Zero -> hash (ps!!0) a
         -- symmetric
         Both c1 c2 -> hashContr vs c1 0 + hashContr vs c2 0 + a
         TransfOne cur p1 p2 -> 
             hashStr (show cur) (hashStr p1 (hashStr p2 (hash (ps!!1) a)))
         If e c1 c2 -> 
             hashContr vs c1 (hashContr vs c2 (hashExp vs e (hash (ps!!2) a)))
         Scale e c -> hashExp vs e (hashContr vs c (hash (ps!!3) a))
         Transl i c -> hash i (hashContr vs c (hash (ps!!4) a))
         CheckWithin e1 i c1 c2 -> 
             hashContr vs c1 (hashContr vs c2 (hashExp vs e1 
                                               (hash i (hash (ps!!5) a))))
--         Let e f  -> hashContr(v::vs,c,hashExp(vs,e,H(17,a)))

-- | hash-based equality, levelling out some symmetries
instance Eq Contract where
    c1 == c2 = hashContr [] c1 0 == hashContr [] c2 0

-- | pretty-prints a contract.
ppContr :: Contract -> String
ppContr c = 
    case c of
      TransfOne c p1 p2 -> "TransfOne" ++ par (show c ++ "," ++ p1 ++ "," ++ p2)
      Scale e c -> "Scale" ++ par (ppExp e ++ "," ++ ppContr c)
      Transl i c -> "Transl" ++ par (ppDays i ++ "," ++ ppContr c)
      Zero -> "zero"
      Both c1 c2 -> "Both" ++ par (ppContrs[c1,c2])
      If e c1 c2 -> "If" ++ par (ppExp e ++ ", " ++ ppContr c1 ++ ", " ++ ppContr c2)
      CheckWithin e i c1 c2 -> 
           "CheckWithin" ++ par (ppExp e ++ ", " ++ ppDays i ++ ", "  ++ ppContr c1 ++ ", " ++ ppContr c2)
      --   | Let(v,e,c) -> "Let" ++ par (v ++ "," ++ ppExp e ++ "," ++ ppContr c)
    where par s = "(" ++ s ++ ")"

ppContrs [] = ""
ppContrs [c] = ppContr c
ppContrs (c:cs) = ppContr c ++ ", " ++ ppContrs cs

-- smart constructors (for reexport) TODO make them smarter!

-- | the empty contract
zero = Zero

-- | Transfer one unit. Rarely used...
transfOne = TransfOne

-- | translate a contract into the future by a number of days
transl :: Int -> Contract -> Contract
transl d c | d < 0 = error "transl: negative time"
transl 0 c = c
transl _ Zero = Zero
transl d (Transl d' c) = Transl (d+d') c
transl d c = Transl d c

-- | conditional contract (two branches)
iff = If

-- | repeatedly checking condition for the given number of days, branching into first contract when true, or else into second contract at the end 
checkWithin = CheckWithin 

-- | two contracts
both c1 Zero = c1
both Zero c2 = c2
both c1 c2 | c1 == c2 = scale (r 2) c1
           | otherwise = Both c1 c2

-- | many contracts (a 'book')
allCs :: [Contract] -> Contract
allCs []  = Zero
allCs [c] = c
allCs (Zero:cs) = allCs cs
allCs (c:cs) = both c (allCs cs)

-- | scaling a contract by a 'RealE' expression
scale _ Zero = Zero
scale r (Scale r' c) = Scale (r*r') c
scale r c | r == 0 = Zero
          | r == 1 = c
          | otherwise = Scale r c

-- | straightforward money transfer (translate, scale, transfOne): after given number of days, transfer from one party to another the given amount in the given currency
flow :: Int -> RealE -> Currency -> Party -> Party -> Contract
flow d amount cur from to = transl d (scale amount (transfOne cur from to))
