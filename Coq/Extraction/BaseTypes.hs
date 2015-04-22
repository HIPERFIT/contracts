module BaseTypes where

data Asset = EUR | DKK | USD | JPY | CHF
             deriving (Show, Ord, Eq)

data BoolObs = Decision Party String
             | Default Party
               deriving (Show, Ord, Eq)

data RealObs = FX Asset Asset
             | Clock
               deriving (Show, Ord, Eq)

data Party = X | Y | Z | P1 | P2 | P3 deriving (Show, Ord, Eq)
