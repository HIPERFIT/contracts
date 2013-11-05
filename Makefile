#MLCOMP=mlkit
MLCOMP=mlton

MOSMLC=mosmlc

UTILFILES=ListSort.sig ListSort.sml

all: contracts.exe

contracts.exe: contracts.mlb contracts.sml $(UTILFILES)
	$(MLCOMP) -output $@ contracts.mlb

multicontracts.exe: multicontracts.mlb multicontracts.sml $(UTILFILES)
	$(MLCOMP) -output $@ multicontracts.mlb

multimos: $(UTILFILES) multicontracts.sml 
	$(MOSMLC) -o multimos $^

clean:
	rm -rf MLB *~ *.exe *.ui *.uo multimos
