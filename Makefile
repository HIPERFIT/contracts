MLCOMP=mlkit
#MLCOMP=mlton

MOSMLC=mosmlc
MOSML=mosml

# order matters here:
SMLFILES=DateUtil.sml ListSort.sig ListSort.sml CURRENCY.sml Currency.sml ContractBase.sml CONTRACT.sig Contract.sml Instruments.sml

all: contract.exe

contract.exe: contract.mlb $(SMLFILES)
	$(MLCOMP) -output $@ contract.mlb

multicontracts.exe: multicontracts.mlb multicontracts.sml $(SMLFILES)
	$(MLCOMP) -output $@ multicontracts.mlb

multimos: $(SMLFILES) multicontracts.sml test.sml 
	$(MOSMLC) -o multimos $^

contractmos: $(SMLFILES)
	$(MOSMLC) -c $(SMLFILES)
	$(MOSML) loadscript
clean:
	rm -rf MLB *~ *.exe *.ui *.uo multimos run
