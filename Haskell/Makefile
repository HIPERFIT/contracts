
GHC=`which ghc`

MODULES = Contract.hs Contract/*.hs
TESTS   = ETest.hs DTest.hs CTest.hs TTest.hs Test.hs

all : Test

Test: 	$(MODULES) $(TESTS)
	$(GHC) -O2 --make Test.hs

qc:	${MODULES} QCHash.hs
	${GHC} -O2 --make QCHash.hs -o qc && ./qc



.PHONY: clean
clean:
	rm  *.hi *.o Contract/*.hi Contract/*.o Test qc
