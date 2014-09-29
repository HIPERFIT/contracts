{-# LANGUAGE GADTs #-}

import Prelude hiding (EQ, LT)

data Env a v where
  Empty :: (v -> a) -> Env a v
  Extend :: a -> Env a v -> Env a (Succ v)

unsafeCoerce = id

