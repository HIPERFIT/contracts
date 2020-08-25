-- | Utility module for hashing expressions and contracts
module Contract.Hash
    ( Hash
    , hash, hashStr, hashPrimes, index, hashSigned
    ) where

import Data.Char
import Data.List

-- | the Hash value is an Integer
type Hash = Integer

-- | list of prime numbers to use as seeds in the hash
hashPrimes :: [Hash]
hashPrimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,
              53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]
             -- let sieve (p:ps) = p : [x | x <- ps , rem x p /= 0 ]
             -- in sieve [2..]
alpha, beta :: Hash
alpha = 65599 -- but it is not used...
beta = 19 -- next prime number after the hashPrimes

-- | hashing an integral number
hash :: Integral a => a -> Hash -> Hash
hash 0 a = a
hash p a = fromIntegral p * (a + 1)

-- | hashing an integral number to non-negative hash
hashSigned :: Integral a => a -> Hash -> Hash
hashSigned p | p < 0 = hash 2 . hash (negate p) 
             | otherwise = hash 3 . hash p


-- | 
hashAdd :: Integral a => a -> Hash -> Hash
hashAdd w acc = fromIntegral w + acc * beta


hashStr :: String -> Hash -> Hash
hashStr s a = go 0 a
    where sz = length s
	  go n a = if n >= sz then a
		   else go (n+1) (hashAdd  (ord (s!!n)) a)

index v vs = findIndex (==v) vs
