OUTDIR=latex

clean:
		rm -rf ${OUTDIR}
		rm -f *.agdai

copy:
		mkdir -p ${OUTDIR}
		cp -n reedthesis.cls ${OUTDIR}
		cp citations.bib ${OUTDIR}

agda:
		rm -rf ${OUTDIR}/*.tex
		agda --latex --latex-dir=${OUTDIR} Thesis.lagda.tex
		agda --latex --latex-dir=${OUTDIR} Abstract.lagda.tex
		agda --latex --latex-dir=${OUTDIR} Chapter1.lagda.tex
		agda --latex --latex-dir=${OUTDIR} Conclusion.lagda.tex

build:
		cd ${OUTDIR} && latexmk -pdf Thesis.tex

all: copy agda build

.DEFAULT_GOAL=all
