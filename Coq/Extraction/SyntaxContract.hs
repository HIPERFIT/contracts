{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module SyntaxContract (
-- * Data types used in contracts
Currency,
Party,

Exp,
acc,
-- * Real expression combinators
RExp,
rLit,
rObs,


-- * Boolean expression combinators
BExp,
false, true,
(!<!), (!<=!), (!=!), (!>!), (!>=!), (!&!), (!|!),
bNot,

bObs,

-- * Contract combinators
Contr,
zero,
transfer,
scale,
both,
translate,
ifWithin,

-- * Operations on contracts
ObsLabel (..),
ExtEnv,
Trans,
horizon,
advance,
specialise,

ExpHoas,
R, B

) where


import Contract hiding (Exp,translate)
import qualified Contract as C

deriving instance Show Var
deriving instance Show Contr
deriving instance Show ObsLabel
deriving instance Show Op
deriving instance Show C.Exp

toVar :: Int -> Var
toVar 0 = V1
toVar n = VS (toVar (n-1))

data R
data B

class ExpHoas' exp where
    iff :: exp B -> exp t -> exp t -> exp t
    opE :: Op -> [exp t'] -> exp t
    obs :: ObsLabel -> Int -> exp t
    acc :: (exp t -> exp t) -> Int -> exp t -> exp t

newtype DB t = DB {unDB :: Int -> C.Exp}

instance ExpHoas' DB where
    iff b e1 e2 = DB (\ i -> OpE Cond [unDB b i, unDB e1 i, unDB e2 i])
    opE op args = DB (\ i -> OpE op (map (($ i) . unDB) args))
    obs l t = DB (\i -> Obs l t)
    acc f t e = DB (\i -> let v = \ j -> VarE (toVar (j-(i+1))) 
                          in Acc (unDB (f (DB v)) (i+1)) t (unDB e i))


rLit :: Double -> RExp
rLit r = opE (RLit r) []

instance Num (DB R) where
    x + y = opE Add [x,y]
    x * y = opE Mult [x,y]
    x - y = opE Sub [x,y]
    abs x = iff (x !<! 0) (- x) x
    signum x = iff (x !<! 0) (- 1) (iff (x !>! 0) 1 0)
    fromInteger i = rLit (fromInteger i)

instance Fractional (DB R) where
    fromRational r = rLit (fromRational r)
    x / y =  opE Div [x,y]
    


class (Num (exp R), ExpHoas' exp) => ExpHoas exp

instance ExpHoas DB

type Exp t = forall exp . ExpHoas exp => exp t

toExp :: Exp t -> C.Exp
toExp t = unDB t 0



rObs :: ExpHoas exp => String -> Int -> exp R
rObs l i = obs (LabR l) i

type RExp = Exp R
type BExp = Exp B

(!=!) :: ExpHoas exp => exp R -> exp R -> exp B
x !=! y = opE Equal [x, y]

(!<!) :: ExpHoas exp => exp R -> exp R -> exp B
x !<! y = opE Less [x, y]

(!<=!) :: ExpHoas exp => exp R -> exp R -> exp B
x !<=! y = opE Leq [x, y]


(!>!) :: ExpHoas exp => exp R -> exp R -> exp B
(!>!) = (!<!)

(!>=!) :: ExpHoas exp => exp R -> exp R -> exp B
(!>=!) = (!<=!)


(!&!) :: ExpHoas exp => exp B -> exp B -> exp B
x !&! y = opE And [x, y]

(!|!) :: ExpHoas exp => exp B -> exp B -> exp B
x !|! y = opE Or [x, y]

bNot :: ExpHoas exp => exp B -> exp B
bNot x =  opE Not [x]

bObs :: ExpHoas exp => String -> Int -> exp B
bObs l i = obs (LabB l) i


false :: BExp
false = opE (BLit False) []

true :: BExp
true = opE (BLit True) []

zero :: Contr
zero = Zero

transfer :: Party -> Party -> Currency -> Contr
transfer = Transfer

scale :: RExp -> Contr -> Contr
scale e = Scale (toExp e)

both :: Contr -> Contr -> Contr
both = Both

translate :: Int -> Contr -> Contr
translate = Translate

ifWithin :: BExp -> Int -> Contr -> Contr -> Contr
ifWithin e = If (toExp e)



example :: RExp
example = acc (\ x -> (acc (\y -> iff (x !=! 1) (x + y) 2) 1 1) + 1) 1 1


advance :: Contr -> ExtEnv -> Maybe (Contr, Trans)
advance = redFun

ex1 :: Contr
ex1 = both (scale 1 zero) (scale 2 zero)
