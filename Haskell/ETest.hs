module Main
    where

import Contract.Expr
import Control.DeepSeq

import qualified Control.Exception as E

testPP :: (a -> String) -> String -> a -> a -> IO ()
testPP pp s e1 e2 = let pr msg = putStrLn (s ++ ": " ++ msg)
                        pp1    = pp e1
                        pp2    = pp e2
                    in E.catch (if pp1 == pp2 then pr ": OK"
                                else pr (": ERROR, expected " ++ pp1
                                         ++ ", got " ++ pp2))
                           (\e -> pr ("EXN, " ++ show (e::E.SomeException)))

etestE :: String -> ExprG a -> ExprG a -> Env -> IO ()
etestE s e1 e2 env = testPP ppExp s e1 (simplifyExp env e2)

etest s e1 e2 = etestE s e1 e2 emptyEnv


runtests = do etest  "test + - i" (i 4) (i 3 + 1)
              etest  "test + - r" (r 4.0) (r 3.0 + 1)

              etest  "test - - i" (i 4) (5 - 1)
              etest  "test - - r" (r 4.0) (5 - 1)

              etest  "test * - i" (i 6) (3 * 2)
              etest  "test * - r" (r 6.0) (3 * r 2.0)

              etest  "test !<! - rt" (b True) (r 2.0 !<! r 3.0)
              etest  "test !<! - it" (b True) (i 2 !<! i 3)
              etest  "test !<! - rf" (b False) (r 4.0 !<! 3)
              etest  "test !<! - rfe" (b False) (r 3.0 !<! 3)
              etest  "test !<! - if" (b False) (i 4 !<! 3)
              etest  "test !<! - ife" (b False) (i 3 !<! 3)

              etest  "test max - rfst" (r 45.0) (maxx (r 45.0) (r 34.0))
              etest  "test max - rsnd" (r 45.0) (maxx (r 21.0) (r 45.0))
              etest  "test min - rfst" (r 34.0) (minn (r 45.0) (r 34.0))
              etest  "test min - rsnd" (r 21.0) (minn (r 21.0) (r 45.0))
              etest  "test max - ifst" (i 45) (maxx 45 (i 34))
              etest  "test max - isnd" (i 45) (maxx  21 (i 45))
              etest  "test min - ifst" (i 34) (minn 45  (i 34))
              etest  "test min - isnd" (i 21) (minn 21 45)

              etest  "test !|! - t" (b True) (b True !|! b True)
              etest  "test !|! - tfst" (b True) (b True !|! b False)
              etest  "test !|! - tsnd" (b True) (b False !|! b True)
              etest  "test !|! - f" (b False) (b False !|! b False)
              
              etest  "test not - t" (b True) ( nott (b False))
              etest  "test not - f" (b False) (nott (b True))
              

              etest  "test pair" (i 34)
                         (second (first (pair (pair (i 23) (i 34)) (r 32.0))))

              etest  "test !=! - it" (b True) (4 !=! i 4)
              etest  "test !=! - if" (b False) (i 4 !=! i 3)
              etest  "test !=! - rt" (b True) (r 4.0 !=! r 4.0)
              etest  "test !=! - rf" (b False) (r 4.0 !=! r 3.0)
              etest  "test !=! - bt" (b True) (b True !=! b True)
              etest  "test !=! - bf" (b False) (b True !=! b False)

{-
              etest  "test iff - t" (I 34) (fn () => ifExpr(B true,I 33 !+! I 1, I 22))
              etest  "test iff - f" (I 22) (fn () => ifExpr(not(B true),I 33 !+! I 1, I 22))
-}

main = runtests
