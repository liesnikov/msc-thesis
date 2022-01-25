.PHONY: all clean thesis thesis.pdf

all: thesis

thesis: thesis.pdf

ipm-diagram-eps-converted-to.pdf: ipm-diagram.eps
	ps2pdf $^ $@

logo-eps-converted-to.pdf: logo.eps
	ps2pdf $^ $@

thesis.pdf: thesis.tex Environments.tex Macros.tex abstract.tex acknowledgements.tex chapterAppendix.tex chapterEight.tex chapterFive.tex chapterFour.tex chapterOne.tex chapterSeven.tex chapterSix.tex chapterThree.tex chapterThreeAndAHalf.tex chapterTwo.tex header.tex logo-eps-converted-to.pdf ipm-diagram-eps-converted-to.pdf
	    "latexmk" -pdf thesis.tex
clean:
	rm -rf *.out *.dvi *.log *.out *.aux *.pdf *.bbl *.blg *.fdb_latexmk *.glo *.glsdefs *.ist *.synctex *.thm *.toc *.tdo *.fls
