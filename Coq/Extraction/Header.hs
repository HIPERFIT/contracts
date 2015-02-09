{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-unused-matches #-}

module Contract (module Contract, module BaseTypes) where

import Control.Monad (liftM,liftM2,liftM3)
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map

import Prelude hiding (map)
import qualified Prelude as P
import BaseTypes

type List a = [a]
type FMap = Map ((Party,Party),Asset) Double

unionWith :: Ord k => (a -> a -> Maybe a) -> Map k a -> Map k a -> Map k a
unionWith f = Map.mergeWithKey (const f) id id

