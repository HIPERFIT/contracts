
-- | Implementation of pretty printing for contracts.


module PrettyPrinting where

import Contract hiding (map)
import Data.Maybe

instance Show ObsLabel where
    show (LabR l) = l
    show (LabB l) = l

varName :: Int -> String
varName i = "x"++show i

ppBool :: Bool -> String
ppBool True = "true"
ppBool False = "false"

parentheses str = "(" ++ str ++ ")"

ppBinOp :: String -> String -> String -> String
ppBinOp op e1 e2 = parentheses (e1 ++ " " ++ op ++ " " ++ e2)

ppUnOp :: String -> String -> String
ppUnOp op e = op ++ " " ++ e

ppOp :: Op -> [String] -> String
ppOp (BLit b) [] = ppBool b
ppOp (RLit r) [] = show r
ppOp Add [x,y] = ppBinOp "+" x y
ppOp Mult [x,y] = ppBinOp "*" x y
ppOp Sub [x,y] = ppBinOp "-" x y
ppOp Div [x,y] = ppBinOp "/" x y
ppOp And [x,y] = ppBinOp "&&" x y
ppOp Or [x,y] = ppBinOp "||" x y
ppOp Less [x,y] = ppBinOp "<" x y
ppOp Leq [x,y] = ppBinOp "<=" x y
ppOp Equal [x,y] = ppBinOp "==" x y
ppOp Not [x] = ppUnOp "not" x
ppOp Neg [x] = ppUnOp "-" x
ppOp Cond [b,x,y] = "if " ++ b ++ " then " ++ x ++ " else " ++ y
ppOp _ _ = error "pretty printing: expression is illformed"

ppExp :: Int -> Env' Int -> Exp -> String
ppExp c names e = 
    case e of
      VarE v -> varName (fromJust (lookupEnv v names))
      OpE op args -> ppOp op (map (ppExp c names) args)
      Obs l n -> "obs(" ++ show l ++ ", " ++ show n ++ ")"
      Acc f l z -> "acc(\\ " ++ varName c ++ " -> " ++ ppExp c' names' f 
                   ++ ", " ++ show l ++ ", " ++ ppExp c names z ++")"
          where c' = c + 1
                names' = c : names


ppContr :: Int -> Env' Int -> Contr -> String
ppContr cur names c = case c of
                        Zero -> "zero"
                        Translate l c -> parentheses (show l ++ " ! " ++ ppContr cur names c)
                        Scale e c -> parentheses (ppExp cur names e ++ " # " ++ ppContr cur names c)
                        Transfer p1 p2 a -> a ++ "(" ++ p1 ++ " -> " ++ p2 ++ ")"
                        Both c1 c2 -> parentheses (ppContr cur names c1 ++ " & " ++ ppContr cur names c2)
                        If b l c1 c2 -> "if " ++ ppExp cur names b ++ within ++ " then " ++
                                        ppContr cur names c1 ++ " else " ++ ppContr cur names c2
                            where within = if l == 0 then "" else " within " ++ show l
                        Let e c -> "let " ++ varName cur ++ " = " ++ ppExp cur names e 
                                     ++ " in " ++ ppContr cur' names' c
                            where cur' = cur + 1
                                  names' = cur : names
