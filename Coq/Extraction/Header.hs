{-# LANGUAGE GADTs #-}
module Contract where

import Prelude hiding (EQ, LT)

data Env a v where
  Empty :: (v -> a) -> Env a v
  Extend :: a -> Env a v -> Env a (Succ v)

data PEnv a v v' where
  PEmpty :: (v -> a) -> PEnv a v v
  PExtend :: a -> PEnv a v v' -> PEnv a (Succ v) v'
  PSkip :: PEnv a v v' -> PEnv a (Succ v) (Succ v')

data ZeroT

unsafeCoerce = id

