{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}

-- module QCHash where

-- quickcheck test for hash functions (expression and contract)

import Contract.Expr
import Contract.Type

import Contract.Hash

import Test.QuickCheck

import Control.Monad
import Control.Applicative
import System.Environment

-- smallcheck
import qualified Test.SmallCheck as SC
import Test.SmallCheck.Series

instance Monad m => Serial m AOp where
    series = foldl1 (\/) (map return  [Plus, Minus, Times, Max, Min])

instance Monad m => Serial m RealE where
    series = cons1 (V . ('v':)) \/ cons1 R \/ cons3 Arith \/ cons3 Acc

instance Monad m => Serial m IntE where
    series = cons1 (V . ('v':)) \/ cons1 I \/ cons3 Arith \/ cons3 Acc

instance Monad m => Serial m BoolE where
    series = cons1 (V . ('v':)) \/ cons1 B \/ cons3 Acc \/ 
             cons2 Or \/ cons1 Not \/
             cons2 (Equal :: RealE -> RealE -> BoolE) \/ 
             cons2 (Less ::  RealE -> RealE -> BoolE) \/
             cons2 (Equal :: IntE -> IntE -> BoolE) \/ 
             cons2 (Less ::  IntE -> IntE -> BoolE) \/
             cons2 (Equal :: BoolE -> BoolE -> BoolE)

instance Arbitrary RealE where
    -- arbitrary :: Gen (Expr a)
    arbitrary = sized realE
realE 0 = oneof  [arbitrary >>= return . R, arbitrary >>= return . V]
realE n | n > 0 = oneof [lit, var, op (n `div` 2), ac (n `div` 2)]
        where lit = arbitrary >>= return . R
              var = arbitrary >>= return . V . ('v':)
              op n = do e1 <- realE n
                        e2 <- realE n
                        op <- oneof (map return [(+), (-), (*), maxx, minn])
                        return (op e1 e2)
              ac n = do e1 <- realE n
                        e2 <- realE n
                        i  <- arbitrary
                        (V s) <- var
                        return (Acc (s, e1) i e2)

-- although we do not really use intE...
instance Arbitrary IntE where
    -- arbitrary :: Gen (Expr a)
    arbitrary = sized intE
intE 0 = oneof  [arbitrary >>= return . I, arbitrary >>= return . V]
intE n | n > 0 = oneof [lit, var, op (n `div` 2), ac (n `div` 2)]
        where lit = arbitrary >>= return . I
              var = arbitrary >>= return . V . ('v':)
              op n = do e1 <- intE n
                        e2 <- intE n
                        op <- oneof (map return [(+), (-), (*), maxx, minn])
                        return (op e1 e2)
              ac n = do e1 <- intE n
                        e2 <- intE n
                        i  <- arbitrary
                        (V s) <- var
                        return (Acc (s, e1) i e2)

instance Arbitrary BoolE where
    -- arbitrary :: Gen (Expr a)
    arbitrary = sized boolE

boolE 0 = oneof [arbitrary >>= return . B, arbitrary >>= return . V]
boolE n | n > 0 = oneof ([var, lit] ++
                         map (\f -> f (n `div` 2)) [not, opR, opI, opB, ac])
        where lit = arbitrary >>= return . B
              var = arbitrary >>= return . V . ('v':)
              not n = boolE n >>= return . Not
              opR n = do e1 <- realE n
                         e2 <- realE n
                         op <- oneof (map return [Equal, Less])
                         return (op e1 e2)
              opI n = do e1 <- intE n
                         e2 <- intE n
                         op <- oneof (map return [Equal, Less])
                         return (op e1 e2)
              opB n = do e1 <- boolE n
                         e2 <- boolE n
                         op <- oneof (map return [Equal, Or])
                         return (op e1 e2)
              ac n = do e1 <- boolE n
                        e2 <- boolE n
                        i  <- arbitrary
                        (V s) <- var
                        return (Acc (s, e1) i e2)

-- too generic, needs type annotation when used
prop_eqExpr :: Expr a -> Expr a -> Property
prop_eqExpr e1 e2 = (e1 == e2) ==> equivExp e1 e2
      {- Equality defined as i.e. hashExp [] e1 0 /= hashExp [] e2 0 -}

prop_eqE :: RealE -> RealE -> Bool
prop_eqE e1 e2 = equivExp e1 e2 && e1 == e2
                 || not (equivExp e1 e2) && e1 /= e2

prop_eqB :: BoolE -> BoolE ->  Bool
prop_eqB e1 e2 = equivExp e1 e2 && e1 == e2
                 || not (equivExp e1 e2) && e1 /= e2

-- extensive equality test on expressions, considering symmetries
equivExp :: Expr a -> Expr b -> Bool
equivExp (Arith op1 e1 e2) (Arith op2 e3 e4)
    = op1 == op2 && (equivExp e1 e3 && equivExp e2 e4 ||
                     op1 `elem` [Plus, Times, Max, Min]
                     && equivExp e1 e4 && equivExp e2 e3)
equivExp (Or e1 e2) (Or e3 e4)
    = equivExp e1 e3 && equivExp e2 e4 || equivExp e1 e4 && equivExp e2 e3
equivExp (Equal e1 e2) (Equal e3 e4)
    = equivExp e1 e3 && equivExp e2 e4 || equivExp e1 e4 && equivExp e2 e3
equivExp (Acc (v, e1) i e2) (Acc (w,e3) j e4)
    = i == j && equivExp e1 e3 && equivExp e2 (rename (w, v) e4)
-- -- boring cases:
equivExp (V v1) (V v2) = v1 == v2
equivExp (I i1) (I i2) = i1 == i2
equivExp (R r1) (R r2) = r1 == r2
equivExp (B b1) (B b2) = b1 == b2

equivExp (Pair a b) (Pair c d) = equivExp a c && equivExp b d
equivExp (Fst a) (Fst b) = equivExp a b
equivExp (Snd a) (Snd b) = equivExp a b

equivExp (Obs (x,i)) (Obs (y,j)) = x == y && i == j
equivExp (ChosenBy (p,i)) (ChosenBy (q,j)) = p == q && i == j
equivExp (Not a) (Not b) = equivExp a b
equivExp (Less e1 e2) (Less e3 e4) = equivExp e1 e3 && equivExp e2 e4
equivExp _ _ = False

instance Arbitrary Currency where
    arbitrary = oneof (map return [EUR, DKK, SEK, USD, GBP, JPY])

instance Arbitrary Contract where
    arbitrary = sized contr

contr 0 = oneof [return Zero, liftM3 transfOne arbitrary arbitrary arbitrary]
contr n | n > 0 = oneof (contr 0 :
                         map (\f -> f (n `div` 2)) [sc, tr, bo, iff, cw])
        where sc n = do e <- realE n
                        c <- contr n
                        return (Scale e c)
              tr n = do c <- contr n
                        i <- choose (0,n)
                        return (Transl i c)
              bo n = do c1 <- contr n
                        c2 <- contr n
                        return (Both c1 c2)
              iff n = do b <- boolE n
                         c1 <- contr n
                         c2 <- contr n
                         return (If b c1 c2)
              cw n = do b <- boolE n
                        i <- choose (0,n)
                        c1 <- contr n
                        c2 <- contr n
                        return (CheckWithin b i c1 c2)


prop_eqC :: Contract -> Contract -> Bool
prop_eqC c1 c2 = c1 == c2 && equivC c1 c2
                 || not (equivC c1 c2) && c1 /= c2

equivC :: Contract -> Contract -> Bool
equivC Zero Zero = True
equivC (TransfOne c1 p1 p2) (TransfOne c2 p3 p4)
    = c1 == c2 && p1 == p3 && p2 == p4
equivC (Scale e1 c1) (Scale e2 c2) = equivExp e1 e2 && equivC c1 c2
equivC (Transl i1 c1) (Transl i2 c2) = i1 == i2 && equivC c1 c2
equivC (Both c1 c2) (Both c3 c4)
    = equivC c1 c3 && equivC c2 c4 || equivC c1 c4 && equivC c2 c3
equivC (If b1 c1 c2) (If b2 c3 c4)
    = equivExp b1 b2 &&             equivC c1 c3 && equivC c2 c4
equivC (CheckWithin b1 i1 c1 c2) (CheckWithin b2 i2 c3 c4)
    = equivExp b1 b2 && i1 == i2 && equivC c1 c3 && equivC c2 c4
equivC _ _ = False

-- main program (you want to run compiled code for this!!!)
main = do args <- getArgs
          let size = if null args then 8 else read (head args)
              params = stdArgs { maxSize = 2^size }
          -- long live the monomorphism restriction, yeuch
          putStrLn ("Testing all properties with max size " ++ show size)
          quickCheckWith params prop_eqE
          putStrLn "Done with R expressions"
          quickCheckWith params prop_eqB
          putStrLn "Done with B expressions"
          quickCheckWith params prop_eqC
          putStrLn "Done with contracts"

          putStrLn ("Do you have time, should I test with smallCheck (depth "
                    ++ show size ++ ")? (y/n)")
          c <- getChar
          if c == 'y' then do SC.smallCheck size prop_eqE
                              putStrLn "done with eqE"
                              SC.smallCheck size prop_eqB
                              putStrLn "Done"
                      else putStrLn "OK, maybe next time."

rename :: (Var,Var) -> Expr a -> Expr a
rename (x,y) (V s) | s == x    = V y
                   | otherwise = V s
rename xy (Pair a b) = Pair (rename xy a) (rename xy b)
rename xy (Fst p)    = Fst (rename xy p)
rename xy (Snd p)    = Snd (rename xy p)
rename xy (Not b)    = Not (rename xy b)
rename xy (Arith o a b) = Arith o (rename xy a) (rename xy b)
rename xy (Less a b) = Less (rename xy a) (rename xy b)
rename xy (Equal a b)= Equal (rename xy a) (rename xy b)
rename xy (Or a b)   = Or (rename xy a) (rename xy b)
rename _   e = e -- boring cases: I R B Obs ChosenBy

-- maybe use this one in hashExp, put it into Expr.hs?
allRename :: Expr a -> Expr a
allRename = aR (vars ['a'..'z'])
aR :: [Var] -> Expr a -> Expr a
aR vs (Pair a b) = Pair (aR (evens vs) a) (aR (odds vs) b)
aR vs (Fst x)    = Fst (aR vs x)
aR vs (Snd x)    = Snd (aR vs x)
aR vs (Not b)    = Not (aR vs b)
aR vs (Arith o a b) = Arith o (aR (evens vs) a) (aR (odds vs) b)
aR vs (Less a b) = Less (aR (evens vs) a) (aR (odds vs) b)
aR vs (Equal a b)= Equal (aR (evens vs) a) (aR (odds vs) b)
aR vs (Or a b)   = Or (aR (evens vs) a) (aR (odds vs) b)
aR vs e = e -- boring cases: V I R B Obs ChosenBy

vars :: [Char] -> [Var]
vars cs = [ c : s | s <- "" : vars cs, c <- cs ]

evens, odds :: [a] -> [a]
evens (x:xs) = x:odds xs -- index 0 is even.
odds  (x:xs) = evens xs

{-
Thanks to smallcheck, we get some insight:

Prelude Contract.Expr> hashExp [] (Equal (I (-1)) (I 1)) 0 
175
Prelude Contract.Expr> hashExp [] (Equal (I (-2)) (I 2)) 0 
175

Surprisingly:
Prelude Contract.Expr> hashExp [] (Equal (-1) 1) 0 
225378657556
Prelude Contract.Expr> hashExp [] (Equal 0 0) 0 
23787057471

Because:
Prelude Contract.Expr> hashExp [] (Equal (R (-1)) (R 1)) 0 
225378657556

-}
