{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

import Contract

class Elem v a where
  inj :: v -> a


instance Elem v (Vars a v) where
  inj = New 

instance Elem v a => Elem v (Vars a v') where
  inj = Old . inj

racc :: (forall v. v -> Rexp' (Vars a v)) -> Int -> (Rexp' a) -> Rexp' a
racc f l z = RAcc (f ()) l z

rvar :: (Elem v a) => v -> Rexp' a
rvar v = RVar (inj v)

-- | HOAS combinator for building an accumulator
acc :: (forall v. (forall a'. Elem v a' => Rexp' a') -> Rexp' (Vars a v)) -> Int -> (Rexp' a) -> Rexp' a
acc f l z = racc (\ x -> f  (rvar x)) l z


example :: Rexp
example = acc (\ x -> RBin Add (acc (\y -> RBin Add x y) 1 (RLit 1)) (RLit 1)) 1 (RLit 1)

deriving instance Show BinOp
deriving instance Show ZeroT
deriving instance (Show a, Show v) => Show (Vars a v)
deriving instance Show a => Show (Rexp' a) 
