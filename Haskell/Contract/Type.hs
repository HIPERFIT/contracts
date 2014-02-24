module Contract.Type
    ( Contract -- no constructors exported
    , Days, Party
    -- smart constructors and convenience functions
    , zero, transfOne, transl, iff, checkWithin, both, allCs, scale, flow
    -- pretty-printer
    , ppContr
    ) where

import Contract.Expr

type Days = Int
type Party = String

data Contract = Zero
              | TransfOne Currency Party Party
              | Scale RealE Contract
              | Transl Days Contract 
              | Both Contract Contract
              | If BoolE Contract Contract
              | CheckWithin BoolE Int Contract Contract
--              | Let Var (ExprG a) Contract -- problem: free a
                deriving (Show)

hashContr :: Contract -> Integer
hashContr = error "must be copied from ML code"

-- | hash-based equality, levelling out some symmetries
instance Eq Contract where
    c1 == c2 = hashContr c1 == hashContr c2

ppContr :: Contract -> String
ppContr = error "not defined yet"


-- smart constructors:

-- | the empty contract
zero = Zero

-- | Transfer one unit. Rarely used...
transfOne = TransfOne

-- | translate a contract into the future by a number of days
transl :: Days -> Contract -> Contract
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
both = Both
-- | many contracts (a 'book')
allCs :: [Contract] -> Contract
allCs []  = Zero
allCs [c] = c
allCs (c:cs) = both c (allCs cs)

-- | scaling a contract by a 'RealE' expression
scale _ Zero = Zero
scale r (Scale r' c) = Scale (r*r') c
scale r c | r == 0 = Zero
          | r == 1 = c
          | otherwise = Scale r c

-- | straightforward money transfer (translate, scale, transfOne): after given number of days, transfer from one party to another the given amount in the given currency
flow :: Int -> RealE -> Currency -> Party -> Party -> Contract
flow d amount cur from to = Transl d (Scale amount (transfOne cur from to))
