default : CS410.pdf

CS410.tex : CS410.lagda Introduction.lagda
	lhs2TeX --agda CS410.lagda > CS410.tex

CS410.aux : CS410.tex
	latex CS410

CS410.blg : CS410.aux CS410.bib
	bibtex CS410

CS410.dvi : CS410.tex CS410.blg
	latex CS410
	latex CS410

CS410.pdf : CS410.tex CS410.blg
	pdflatex CS410
