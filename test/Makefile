
ifeq ($(strip $(MLCOMP)),) 
	MLCOMP=mlkit
endif

FILES=Makefile $(shell ls -1 *.mlb *.sml)

all: tests.out expr.out contract.out date.out

%.out: %.exe
	./$< > $@
	diff -q $@ $*.ok

%.exe: $(FILES)
	$(MLCOMP) -output $@ $*.mlb

clean:
	rm -rf MLB *~ *.exe *.ui *.uo run *.res *.out
