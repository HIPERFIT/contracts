module Contract.Environment
    ( MEnv(..), Env -- MEnv constructor for internal use only!
    -- operations only on managed environments
    , emptyEnv, emptyFrom
    , addFix, addFixing, addFixings, fixings
    , promote, promoteEnv
    )
where

import Contract.Date

-- | An environment is a partial mapping from (String, Int) to Double. The keys carry an identifying string and an offset value (days), yielding a Double value.
type Env = (String,Int) -> Maybe Double  -- Hack: should use Bool for choice

--  not using Data.Map here, infinite domain might be useful (see "Time")

-- | construct an empty environment. "Time" is always defined
emptyEnv :: Env
emptyEnv ("Time",i) = Just (fromIntegral i)
emptyEnv   other    = Nothing

-- ideas:
-- unify :: Env -> Env -> Env

-- | A managed environment is an environment together with a start date.
data MEnv = Env Date Env

-- | an empty managed environment, from a given start date
emptyFrom :: Date -> MEnv
emptyFrom d = Env d emptyEnv

-- | promoting an environment by a given date offset into the future
-- (or past, if negative)
promote :: Env -> Int -> Env
promote e i = e . (\(s,x) -> (s,x+i))

-- | promoting a managed environment by a given date offset. See 'promote'
promoteEnv :: MEnv -> Int -> MEnv
promoteEnv (Env d e) i = Env d (promote e i)

-- | adding a fixing to an environment.
-- New values take precedence with this definition
addFix :: (String, Int, Double) -> Env -> Env
addFix (s,d,r) e = \x -> if x == (s,d) then Just r else e x

-- | adding a fixing to a managed environment
addFixing :: (String, Date, Double) -> MEnv -> MEnv
addFixing (s,d,r) (Env e_d e_f) = 
    let off = dateDiff e_d d
    in Env e_d (\x -> if x == (s,off) then Just r else e_f x)


addFixings :: (String, Date) -> [Double] -> MEnv -> MEnv
addFixings (s,d) [] e = e
addFixings (s,d) vs (Env e_d e_f) =
    let l = length vs
        o = dateDiff e_d d
        f (s',n) = if s == s' && n >= o && n < l + o
                     then Just (vs!!(n-o)) else e_f (s',n)
    in Env e_d f

fixings :: String -> Date -> [Double] -> MEnv
fixings s d vs = addFixings (s,d) vs (emptyFrom d)

-- | join two environments (first one takes precedence)
union :: Env -> Env -> Env
union e1 e2 = \obs -> case e1 obs of
                        Just x  -> Just x
                        Nothing -> e2 obs

-- | join two managed environments (first one takes precedence)
unionEnv :: MEnv -> MEnv -> MEnv
unionEnv (Env d1 e1) (Env d2 e2) = Env d1 (union e1 e2')
    where e2' = promote e2 (dateDiff d2 d1)
