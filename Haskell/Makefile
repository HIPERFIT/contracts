
GHC=`which ghc`

MODULES = Contract.hs Contract/*.hs
TESTS   = ETest.hs DTest.hs CTest.hs TTest.hs Test.hs

all : Test

Test: 	$(MODULES) $(TESTS)
	$(GHC) -O2 --make Test.hs

.PHONY: clean
clean:
	rm  *.hi *.o Contract/*.hi Contract/*.o Test
