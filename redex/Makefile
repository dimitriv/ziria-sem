#_QUIET = @

LHS2TEX   = lhs2TeX
LATEX     = latex
PDFLATEX  = pdflatex
XELATEX   = xelatex
DVIPDFM   = dvipdfmx
PS2PDF    = ps2pdf
PDFJAM    = pdfjam
DOT       = dot
PIC       = dpic

USE_BIBTEX = YES
USE_PDFTEX = YES

UNAME := $(shell uname -s)

TEXFLAGS = -shell-escape --synctex=1

define latex
	latexmk -dvi -latex="latex $(TEXFLAGS) %O '$(3)\errorstopmode \input '%S" -jobname=$(2) $(1).tex
endef

define pslatex
	latexmk -ps -latex="latex $(TEXFLAGS) %O '$(3)\errorstopmode \input '%S" -jobname=$(2) $(1).tex
endef

define pdflatex
	latexmk -pdf -pdflatex="pdflatex $(TEXFLAGS) %O '$(3)\errorstopmode \input '%S" -jobname=$(2) $(1).tex
endef

define dvipdf
	set -e; \
	$(DVIPDFM) $(1) -o $(notdir $@) $(notdir $<)
endef

TEX_CRUFT = *.aux *.log \
	    *.toc *.out *.ptb \
	    *.bbl *.blg \
	    *.idx *.ilg *.ind \
	    *.cb *.cb2 \
	    *.nav *.snm *.vrb \
	    *.synctex.gz \
	    *.pyg \
	    *.fdb_latexmk *.fls \
	    head.tmp body.tmp texput.log \
            auto _minted*

.PHONY : all
all: ziria-sem.pdf

.PHONY : clean
clean:
	rm -rf ziria-sem.pdf $(TEX_CRUFT) *~ compiled *.pdf

%.pdf : %.tex
	@echo "Creating PDF from" $<
	$(_QUIET)$(call pdflatex,$*,$*)
