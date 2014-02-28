
all: CpdtTactics.vo
	coqc Contr2.v

CpdtTactics.vo: CpdtTactics.v
	coqc $<

clean:
	rm -rf *.vo *.glob *~ *.hs
