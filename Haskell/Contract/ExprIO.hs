{-# LANGUAGE GADTs #-} 
module Contract.ExprIO where

import Contract.Expr
-- Show/Read instances and other pretty-printing related stuff

-- | Show instance for debugging (cannot be derived automatically for GADTs)
instance Show (Expr a) where
    show (I n) = "I " ++ show n
    show (R r) = "R " ++ ppReal r
    show (B b) = "B " ++ show b
    show (V v) = "V " ++ show v
    show (Pair e1 e2) = "Pair " ++ par (show e1) ++ par (show e2)
    show (Fst e) = "Fst " ++ par (show e)
    show (Snd e) = "Snd " ++ par (show e)
    show (Obs (s,i)) = "Obs " ++ par (show s ++ "," ++ show i)
    show (ChosenBy (p,i)) = "ChosenBy " ++ par (show p ++ "," ++ show i)
    show (Acc (v,e) i a) = "Acc " ++ unwords [par (show v ++ "," ++ show e),
                                             show i, par (show a)]
    show (Not e) = "Not " ++ par (show e)
    show (Arith op e1 e2) = "Arith " ++ unwords [show op, par (show e1),
                                                 par (show e2)]
    show (Less e1 e2) = "Less " ++ unwords [par (show e1), par (show e2)]
    show (Equal e1 e2) = "Equal " ++ unwords [par (show e1), par (show e2)]
    show (Or e1 e2) = "Or " ++ unwords [par (show e1), par (show e2)]

-- | Operators can be read in
instance Read AOp where
    readsPrec _ ('+':rest) = [(Plus,rest)]
    readsPrec _ ('-':rest) = [(Minus,rest)]
    readsPrec _ ('*':rest) = [(Times,rest)]
    readsPrec _ ('/':rest) = [(Div,rest)]
    readsPrec _ ('m':'a':'x':rest) = [(Max,rest)]
    readsPrec _ ('m':'i':'n':rest) = [(Min,rest)]
    readsPrec _ _ = []

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
