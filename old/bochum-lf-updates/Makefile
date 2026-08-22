VOLUME = lf
VOLUMENAME = Logical Foundations
VOLUMENUMBER = 1
VERSION = 7.1
define AUTHORS
Benjamin C. Pierce and
		      Arthur Azevedo de Amorim and
		      Chris Casinghino and
		      Marco Gaboardi and
		      Michael Greenberg and
		      Cătălin Hriţcu and
		      Vilhelm Sjöberg and
		      Brent Yorgey
endef
FIRSTAUTHOR = Pierce

# (The order here determines the order of chapters in the
# generated table of contents.)
#
# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
# IMPORTANT!!!  If you add a file here, make sure to
# fix up the dependencies in deps.dot
# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
EXPORTS = \
	   Preface.v \
	   Basics.v \
	   Induction.v \
	   Lists.v \
	   Poly.v \
	   Tactics.v \
	   Logic.v \
	   IndProp.v \
	   Maps.v \
	   ProofObjects.v \
	   IndPrinciples.v \
		 CurryHoward.v \
	   Rel.v \
	   Imp.v \
	   ImpParser.v \
	   ImpCEvalFun.v \
	   Extraction.v \
	   Auto.v \
	   AltAuto.v \
	   Postscript.v \
	   Bib.v \

NOEXPORT = Review1.v Review2.v

MORETAGS = TODO

EXTRACLEAN := imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

## I'm commenting this out -- feel free to delete if the new simplegrader is working. -- Caleb, 2017-10-15
# Temporary
# BROKENTESTERS = ProofObjects.v IndProp.v Imp.v Types.v Sub.v \
#                 RecordSub.v Rel.v ImpParser.v ImpCEvalFun.v Extraction.v \
#                 References.v LibTactics.v UseTactics.v UseAuto.v PE.v \
#                 Maps.v Auto.v

# Grab the common parts of the build procedure from upstairs
include ../Top.Makefile

##############################################################################
# Extraction

toplevel:: extraction

# extraction: extraction1 extraction2
extraction: impdriver

impdriver: ImpParser.vo Extraction.vo
	ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
#	./impdriver

extraction2: NormInType.vo Extraction.vo Extraction2.vo
	ocamlc -w -20 -o normdriver norm.mli norm.ml normdriver.ml
#	./normdriver

EXTRAEXPORTS += impdriver.ml

clean::
	$(V)rm -f normdriver impdriver
	$(V)rm -f *.o *.cmo *.cmi $(EXTRACLEAN) norm.ml norm.mli

#############################################################################
# Experimental

wholebib:
	(cd $(HOME)/tmp; export TMPDIR=.; \
	bibtex2html \
	   -use-keys -nodoc -nobibsource -noabstract -dl \
	   -o $(PWD)/temp \
	   ~/common/bib/bcp.bib)
