{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-unused-matches #-}

module Contract where

import Control.Monad (liftM,liftM2,liftM3)

type List a = [a]

type Party = String
type Asset = String
