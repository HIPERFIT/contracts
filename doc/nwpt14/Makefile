#Makefile originally by Tom Hvitved <hvitved@diku.dk>
# adapted/extended by Jost Berthold

DOCUMENT = NWPT14Contracts
GRAPHICSPATH = graphics
ABSTRACT = NWPT14Contracts


TEXFILES = $(wildcard *.tex)
GRAPHICS = $(wildcard $(GRAPHICSPATH)/*)
BIBFILES = $(wildcard *.bib)

# LaTeX/BiBTeX re-run conditions
RERUN = "Rerun to get (cross-references|the bars|citations)"
RERUNBIB = "No file.*\.bbl|Citation.*undefined"

LATEX = latex
PDFLATEX = pdflatex
BIBTEX = bibtex
DEL = @rm -f

# later we might add these in the right place...
PDFOPTS=-dEmbedAllFonts=true -dPDFSETTINGS=/prepress

default: paper

paper:	$(DOCUMENT).pdf

abstract: $(ABSTRACT).pdf

checkfonts: paper
	@pdffonts $(DOCUMENT).pdf

recodeforfonts: paper
	@pdf2ps $(DOCUMENT).pdf
	@ps2pdf $(PDFOPTS) $(DOCUMENT).ps $(DOCUMENT).pdf

$(DOCUMENT).pdf: $(DOCUMENT).tex bib $(GRAPHICS)
	@$(PDFLATEX) $(DOCUMENT).tex
	@grep -E $(RERUNBIB) $(DOCUMENT).log && ($(BIBTEX) ;$(PDFLATEX) $(DOCUMENT).tex) ; true
	@grep -E $(RERUN) $(DOCUMENT).log && ($(PDFLATEX) $(DOCUMENT).tex) ; true
	@grep -E $(RERUN) $(DOCUMENT).log && ($(PDFLATEX) $(DOCUMENT).tex) ; true

$(ABSTRACT).pdf: $(ABSTRACT).tex abstractbib $(GRAPHICS)
	@$(PDFLATEX) $(ABSTRACT).tex
	@grep -E $(RERUNBIB) $(ABSTRACT).log && ($(BIBTEX) ;$(PDFLATEX) $(ABSTRACT).tex) ; true
	@grep -E $(RERUN) $(ABSTRACT).log && ($(PDFLATEX) $(ABSTRACT).tex) ; true
	@grep -E $(RERUN) $(ABSTRACT).log && ($(PDFLATEX) $(ABSTRACT).tex) ; true

abstractbib: $(BIBFILES) $(ABSTRACT).aux
	$(BIBTEX) $(ABSTRACT)

%.aux: %.tex
	$(PDFLATEX) $<

dvi: $(TEXFILES)
#	@$(MAKE) -C gfx
	@$(LATEX) $(DOCUMENT).tex
	@grep -E $(RERUNBIB) $(DOCUMENT).log && ($(BIBTEX) $(DOCUMENT);$(LATEX) $(DOCUMENT).tex); true
	@grep -E $(RERUN) $(DOCUMENT).log && ($(LATEX) $(DOCUMENT).tex) ; true
	@grep -E $(RERUN) $(DOCUMENT).log && ($(LATEX) $(DOCUMENT).tex) ; true

pdf: $(TEXFILES) $(GRAPHICS) $(BIBFILES)
#	@$(MAKE) -C gfx
	@$(PDFLATEX) $(DOCUMENT).tex
	($(BIBTEX) $(DOCUMENT);$(PDFLATEX) $(DOCUMENT).tex)
	@grep -E $(RERUN) $(DOCUMENT).log && ($(PDFLATEX) $(DOCUMENT).tex) ; true
	@grep -E $(RERUN) $(DOCUMENT).log && ($(PDFLATEX) $(DOCUMENT).tex) ; true

bib: $(BIBFILES) $(DOCUMENT).aux
	$(BIBTEX) $(DOCUMENT)

clean:
	$(DEL) $(TEXFILES:tex=aux)
	$(DEL) $(TEXFILES:tex=log)
	$(DEL) $(DOCUMENT).dvi $(DOCUMENT).idx $(DOCUMENT).log $(DOCUMENT).pdf
	$(DEL) $(DOCUMENT).ilg $(DOCUMENT).ind $(DOCUMENT).toc $(DOCUMENT).lox
	$(DEL) $(DOCUMENT).bbl $(DOCUMENT).blg $(DOCUMENT).out $(DOCUMENT).rel
	$(DEL) $(DOCUMENT).nav $(DOCUMENT).snm
	$(DEL) *~ # emacs temporary files
	$(DEL) $(DOCUMENT).ps # from embedding the fonts
