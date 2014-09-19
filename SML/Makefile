MLCOMP=mlkit
#MLCOMP=mlton

MOSMLC=mosmlc
MOSML=mosml

# All infrastructure modules (not tests). Order matters here:

COREFILES=DateUtil.sig DateUtil.sml ListSort.sig ListSort.sml CURRENCY.sig Currency.sml ContractBase.sml CONTRACTSIG.sig Contract.sig Contract.sml ContractSafe.sml ContractTransform.sml Instruments.sml
MOSMLFILES=LargeInt.sml $(COREFILES)

SMLFILES=$(COREFILES) ContractMonad.sml

all: contract.exe

.PHONY: help clean
help:
	@echo " Target             Purpose                                remarks"
	@echo "-------------------------------------------------------------------"
	@echo "contractmos         runs loadscript in interpreter         mosml"
	@echo "                    (loading some essential modules)"
	@echo "mosmodules          compiles all basic modules with data   mosml"
	@echo "                    types and manipulation functions)"
	@echo "portfolio           compiles portfolio module              mosml"
	@echo "                    (depends on above modules)"
	@echo "pftest BROKEN!      portfolio test program                 mosml"
	@echo "contract.exe        compiles contracts mlb                 mlkit"
	@echo "                    (Instruments_test.sml)"
	@echo ""
	@echo "multicontracts.exe  multiparty contracts mlb               old"

contract.exe: contract.mlb $(SMLFILES)
	$(MLCOMP) -output $@ contract.mlb

multicontracts.exe: multicontracts.mlb multicontracts.sml $(SMLFILES)
	$(MLCOMP) -output $@ multicontracts.mlb

#multimos: $(MOSMLFILES) test.sml 
#	$(MOSMLC) -o multimos $^

contractmos: $(MOSMLFILES)
	$(MOSML) loadscript

clean:
	rm -rf MLB *~ *.exe *.ui *.uo multimos run doc/*~
	make -C test clean

mosmodules: $(MOSMLFILES)
	for F in  $(MOSMLFILES); do $(MOSMLC) -c $${F}; done

portfolio.uo: mosmodules portfolio.sml
	$(MOSMLC) -c portfolio.sml

pftest:	portfolio.uo pftest.sml
	@echo -----------------------------------------------------------
	@echo pftest in MosML is broken since ContractSafe was introduced
	@echo -----------------------------------------------------------
	# doznwok: $(MOSMLC) -o pftest pftest.sml

.PHONY: test
test:
	$(MAKE) -C test all
