#MLCOMP=mlkit
MLCOMP=mlton

MOSMLC=mosmlc
MOSML=mosml

# order matters here:
SMLFILES=DateUtil.sml ListSort.sig ListSort.sml ContractTypes.sml ContractUtil.sml

all: contracts.exe

contracts.exe: contracts.mlb contracts.sml $(SMLFILES)
	$(MLCOMP) -output $@ contracts.mlb

multicontracts.exe: multicontracts.mlb multicontracts.sml $(SMLFILES)
	$(MLCOMP) -output $@ multicontracts.mlb

multimos: $(SMLFILES) multicontracts.sml test.sml 
	$(MOSMLC) -o multimos $^

contractmos:	$(SMLFILES)
	$(MOSMLC) -c $(SMLFILES)
	$(MOSML) loadscript
clean:
	rm -rf MLB *~ *.exe *.ui *.uo multimos
