{-# LANGUAGE GADTs, StandaloneDeriving #-} 
module Contract.ExprIO where

import Contract.Expr
-- Show/Read instances and other pretty-printing related stuff

deriving instance Show (Expr a)

{-
-- | Operators can be read in
instance Read AOp where
    readsPrec _ ('+':rest) = [(Plus,rest)]
    readsPrec _ ('-':rest) = [(Minus,rest)]
    readsPrec _ ('*':rest) = [(Times,rest)]
    readsPrec _ ('/':rest) = [(Div,rest)]
    readsPrec _ ('m':'a':'x':rest) = [(Max,rest)]
    readsPrec _ ('m':'i':'n':rest) = [(Min,rest)]
    readsPrec _ _ = []
-}

-----------------------------------------------------------------
-- Pretty-print an expression (not the same as the Show instance)

-- | internal: print an expression, using an int printing function
ppExp0 :: (Int -> String) -> Expr a -> String
ppExp0 ppInt e = 
    case e of
           V s -> s
           I i -> ppInt i
           R r -> ppReal r
           B b -> show b
           Pair e1 e2 -> par (ppExp0 ppInt e1 ++ "," ++ ppExp0 ppInt e2)
           Fst e -> "first" ++ par (ppExp0 ppInt e)
           Snd e -> "second" ++ par (ppExp0 ppInt e)
           Acc f i e -> "acc" ++ par(ppFun f ++ "," ++ show i ++ "," ++ ppExp e)
           Obs (s,off) -> "Obs" ++ par (s ++ "@" ++ ppInt off)
           ChosenBy (p,i) -> "Chosen by " ++ p ++ " @ " ++ ppInt i
           Not e1 -> "not" ++ par (ppExp e1)
           Arith op e1 e2 -> let (c,infx) = ppOp op
                             in if infx then par(ppExp e1 ++ c ++ ppExp e2)
                                else c ++ par (ppExp e1) ++ ' ':par(ppExp e2)
           Less e1 e2 -> par(ppExp0 ppInt e1 ++ " < " ++ ppExp0 ppInt e2)
           Equal e1 e2 -> par(ppExp0 ppInt e1 ++ "==" ++ ppExp0 ppInt e2)
           Or e1 e2 ->  par(ppExp e1 ++ "||" ++ ppExp e2)
    where ppExp e = ppExp0 ppInt e
          ppFun (v,e) = "\\" ++ v ++ " -> " ++ ppExp e

-- | pretty-printing an expression, using normal printer for Int
ppExp = ppExp0 show

-- parenthesis around a string
par s = "(" ++ s ++ ")"
