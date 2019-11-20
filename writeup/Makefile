LATEX=pdflatex -shell-escape -output-directory=dist

default : $(shell find src -type f)
	@mkdir -p dist
	lhs2TeX -o dist/index.tex src/index.lhs
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) dist/index.tex 

images: src/img/$(wildcard *.svg)
	make -C src/img

all: default images

dist/$(TGT).aux: default

bib: references.bib dist/index.aux
	bibtex dist/index.aux
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) dist/index.tex

camerardy: default
	zip dist/camera-rdy.zip dist/index.tex references.bib 

clean :
	cd dist && rm -rf * && cd ..
