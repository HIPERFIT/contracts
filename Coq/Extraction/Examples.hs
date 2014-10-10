import SyntaxContract

iff(be,c1,c2) = ifWithin(be,0,c1,c2)

ex1 = iff(bLit False,zero,transfOne("EUR","ME","YOU"))

ex1s = specialise ex1 envEmpty
