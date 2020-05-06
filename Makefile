OUTDIR=latex

all: init check thesis

quick: init gen thesis

.DEFAULT_GOAL=all

clean:
		rm -rf ${OUTDIR}

init:
		mkdir -p ${OUTDIR}
		cp -n tex/reedthesis.cls ${OUTDIR}
		cp tex/citations.bib ${OUTDIR}

check: init
		rm -f ${OUTDIR}/*.tex
		parallel agda --latex --latex-dir=${OUTDIR} {} ::: tex/*.lagda.tex

gen: init
		rm -f ${OUTDIR}/*.tex
		parallel agda --latex --latex-dir=${OUTDIR} --only-scope-checking {} ::: tex/*.lagda.tex

thesis:
		cd ${OUTDIR} && latexmk -pdf Thesis.tex && cp Thesis.pdf McKeanAlice_FinalDraft.pdf

pres:
		mkdir -p ${OUTDIR}
		cp tex/citations.bib ${OUTDIR}
		agda --latex --latex-dir=${OUTDIR} defense/Pres.lagda.tex
		cd ${OUTDIR} && latexmk -pdf Pres.tex
