OUTDIR=latex

all: init check build

quick: init gen build

.DEFAULT_GOAL=all

clean:
		rm -rf ${OUTDIR}
		rm -f *.agdai

init:
		mkdir -p ${OUTDIR}
		cp -n reedthesis.cls ${OUTDIR}
		cp citations.bib ${OUTDIR}

check: init
		rm -f ${OUTDIR}/*.tex
		parallel agda --latex --latex-dir=${OUTDIR} {} ::: *.lagda.tex

gen: init
		rm -f ${OUTDIR}/*.tex
		parallel agda --latex --latex-dir=${OUTDIR} --only-scope-checking {} ::: *.lagda.tex

build:
		cd ${OUTDIR} && latexmk -pdf Thesis.tex

