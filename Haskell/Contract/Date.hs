{-# LANGUAGE DeriveDataTypeable #-}
module Contract.Date
    ( Date -- incl. Ord instance providing compare function and (<)
    , DateError
    , at -- was "?" in SML. Use the Read instance instead
    , addDays, dateDiff, ppDate
    ) where


-- to define the exception
import Control.Exception as E
import Data.Typeable

import Data.Char(isDigit)
import Text.Printf

-- everything implemented "on foot". Could use a library module

type Year = Int
type Month = Int
type Day = Int

-- | Dates are represented as year, month, and day.
data Date = Date Year Month Day
          deriving (Eq,Ord, Show)

isLeapYear :: Year -> Bool
isLeapYear year = year `mod` 400 == 0 || 
                  (not (year `mod` 100 == 0) && year `mod` 4 == 0)
    
daysInYear year = if isLeapYear year then 366 else 365

daysInMonth :: Year -> Month -> Int
daysInMonth year m =
    let m31 = [1,3,5,7,8,10,12]
        daysInFeb = if isLeapYear year then 29 else 28
    in if m `elem` m31 then 31
       else if m == 2 then daysInFeb else 30

data DateError = DateError String deriving (Typeable,Show)
instance Exception DateError

check :: Date -> Date
check d@(Date year month day) = if
    year >= 1 && year <= 9999 && -- there is no such thing as year 0!
    month >= 1 && month <= 12 &&
    day >= 1 && day <= daysInMonth year month 
        then d else dateError (ppDate d)

dateError s = -- print (s ++ "\n")
     throw (DateError ("Expecting date in the form YYYY-MM-DD - got " ++ s))

-- | read a date from a string in format yyyy-mm-dd
at :: String -> Date
at s | length s /= 10 = dateError s
     | s!!4 /= '-'    = dateError s
     | s!!7 /= '-'    = dateError s
     | not allDigits  = dateError s
     | otherwise = check result
     where substr a b = take b (drop a s)
           y = substr 0 4
           m = substr 5 2
           d = substr 8 2
           allDigits = all isDigit (y++m++d)
           result = Date (read y) (read m) (read d)
                    -- (\e -> dateError (s ++ "\n" ++ show (e::ErrorCall)))

-- | Dates can only be read in format yyyy-mm-dd
instance Read Date where
    readsPrec _ d = [(at (take 10 d), drop 10 d)]

-- | print a date in format yyyy-mm-dd (padding with zeros)
ppDate :: Date -> String
ppDate (Date year month day) = printf "%04d-%02d-%02d" year month day

-- | add given number of days to a date (result date is checked)
addDays :: Int -> Date -> Date
addDays 0 d = check d
addDays i (d@(Date year month day))
    | i < 0 = subDays (-i) d
    | otherwise = let days = daysInMonth year month
                      n    = days - day
                      next = if month == 12 then Date (year+1) 1 1
                                            else Date year (month+1) 1
                  in if i <= n then check (Date year month (day+i))
                     else addDays (i-n-1) next

-- | subtract days (used for adding negative amount of days to a date)
subDays 0 d = check d
subDays i (d@(Date year month day))
    | i < 0 = addDays (-i) d -- should not occur, not directly callable
    | otherwise = if i < day then check (Date year month (day-i))
                  else let (y,m) = if month == 1 then (year-1,12)
                                                 else (year,month-1)
                           d     = daysInMonth y m
                       in subDays (i-day) (Date y m d)

-- derived Ord, comparisons component-wise left-to-right, no big deal
-- fun compare ({year=y1,month=m1,day=d1}, {year=y2,month=m2,day=d2}) =
--     if y1 < y2 then LESS
--     else (if y1 = y2 then
--             if m1 < m2 then LESS
--             else if m1 = m2 then
--               (if d1 < d2 then LESS
--                else if d1 = d2 then EQUAL
--                else GREATER)
--             else GREATER
--           else GREATER)
                 
-- | compute day difference to go from d1 to d2
dateDiff :: Date -> Date -> Int
dateDiff d1@(Date y1 m1 n1) d2@(Date y2 m2 n2)
    = case compare d1 d2 of
                   EQ -> 0
                   GT -> - (dateDiff d2 d1)
                   LT -> --  d1 < d2
                         if y1 == y2 then
                             if m1 == m2 then n2 - n1
                             else -- m1 < m2, go to next month
                                 daysInMonth y1 m1 - n1 + 1 + 
                                 dateDiff (Date y1 (m1+1) 1) d2
                         else -- y1 < y2, but step fwd in months (leapyears!)
                              let next = if m1 == 12 then Date (y1+1) 1 n1
                                                     else Date y1 (m1+1) n1
                              in daysInMonth y1 m1 + dateDiff next d2
