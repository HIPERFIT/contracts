import SyntaxContract

iff(be,c1,c2) = ifWithin(be,0,c1,c2)

ex1 = iff(bLit False,zero,both(transfOne("ME","YOU","EUR"),
                               scale(rLit 3.2, transfOne("ME","YOU","EUR"))))

ex1s = specialise ex1 envEmpty

res = advance ex1 envEmpty 

pp :: Maybe(Contract,Trans) -> String
pp Nothing = "Nothing"
pp (Just (c,t)) = "New Contract: " ++ show c ++ "\nTrans: " ++ show (t "ME" "YOU" "EUR")
