#MLCOMP=mlkit
MLCOMP=mlton

UTILFILES=MYLIST_SORT.sig MyListSort.sml

all: contracts.exe

contracts.exe: contracts.mlb contracts.sml $(UTILFILES)
	$(MLCOMP) -output $@ contracts.mlb

multicontracts.exe: multicontracts.mlb multicontracts.sml $(UTILFILES)
	$(MLCOMP) -output $@ multicontracts.mlb

clean:
	rm -rf MLB *~ *.exe
