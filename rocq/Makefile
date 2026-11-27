# Makefile to translate lp files to rocq

# Because, in Lambdapi, the definitions/proofs of opaque symbols is
# not recorded in lpo files, and the stt_rocq export works on
# non-elaborated terms, to translate lp files to rocq, for the moment,
# we need to proceed in several steps:

# 1) we remove the "opaque" keywords
# 2) we translate lp files to fully elaborated dk files
# 3) we translate dk files to rocq files

# These intermediate steps could be removed in the future by allowing
# the translation of lp files to rocq after elaboration.

MAKEFLAGS += -r -k -j$(shell nproc)

.PREFIX:

.PHONY: default
default:
	$(MAKE) lp
	$(MAKE) dk
	#$(MAKE) INCLUDE_DKO_MK=1 dko
	$(MAKE) v
	$(MAKE) vo

##############################################################################
# generation of patched lp files

# 1) We remove the "opaque" keywords so that proofs are recorded.
# 2) We rename the root_path so that it does not clash with Rocq's Stdlib.
# 3) Set.lp is renamed to Sets.lp because "Require Set" fails in Rocq.
# 4) Prop.lp is renamed to Props.lp because "Require Prop" fails in Rocq.

LPFILES := $(shell ls ../*.lp | sed -e 's/..\///g' -e 's/Set\.lp/Sets.lp/' -e 's/Prop\.lp/Props.lp/')

.PHONY: lp
lp: lambdapi.pkg $(LPFILES)

lambdapi.pkg: ../lambdapi.pkg
	sed -e 's/Stdlib/Lambdapi/' $< > $@

SED := sed -e 's/^opaque //' -e 's/ Stdlib\./ Lambdapi./g'

Sets.lp: ../Set.lp
	$(SED) $< > $@

Props.lp: ../Prop.lp
	$(SED) $< > $@

%.lp: ../%.lp
	$(SED) -e 's/\.Set\([ ;]\)/.Sets\1/' -e 's/\.Prop\([ ;]\)/.Props\1/' $< > $@

KEEP := encoding mapping renaming
EXCEPT := $(KEEP:%=-a ! -name %.lp)

.PHONY: clean-lp
clean-lp:
	-find . -name '*.lp' $(EXCEPT) -delete

##############################################################################
# generation of dk files

DKFILES := $(LPFILES:%.lp=%.dk)

.PHONY: dk
dk: $(DKFILES)

%.dk: %.lp
	lambdapi export -o dk -w -v 0 $< > $@

.PHONY: clean-dk
clean-dk: clean-dko clean-v
	-find . -name '*.dk' -delete
	-rm -f dko.mk

##############################################################################
# verification of dk files (optional)

.PHONY: dko
dko: $(DKFILES:%.dk=%.dko)

DKCHECK := dk check -e

%.dko: %.dk
	$(DKCHECK) $<

ifeq ($(INCLUDE_DKO_MK),1)
include dko.mk

dko.mk: $(DKFILES)
	dk dep -q $^ > $@
endif

.PHONY: clean-dko
clean-dko:
	-find -name '*.dko' -delete

##############################################################################
# generate renaming.lp to handle names that are invalid in rocq

renaming.lp: renaming renaming.sed /tmp/invalid-names
	./renaming < /tmp/invalid-names > $@

/tmp/invalid-names: $(DKFILES:%.dk=/tmp/%.dk-invalid-names)
	@cat $^ | sort -u > $@

EXPORT := lambdapi export -w -o stt_rocq --encoding encoding.lp --mapping mapping.lp --requiring mapping --use-notations

/tmp/%.dk-invalid-names: encoding.lp mapping.lp %.dk
	@echo check names in $*.dk ...
	@$(EXPORT) --only-check-names $*.dk > $@

##############################################################################
# generation of rocq files

VFILES := $(DKFILES:%.dk=%.v)

.PHONY: v
v: $(VFILES)

%.v: encoding.lp mapping.lp renaming.lp %.dk
	@echo lambdapi export -o stt_rocq $*.dk > $@
	@$(EXPORT) --renaming renaming.lp $*.dk > $@

.PHONY: clean-v
clean-v: clean-vo
	-find . -name '*.v' -a ! -name mapping.v -delete
	-find . -name '*.glob'
	-rm -f rocq.mk rocq.mk.conf

##############################################################################
# verification of rocq files

.PHONY: vo
vo: rocq.mk
	$(MAKE) -f rocq.mk

%.vo: rocq.mk %.v
	$(MAKE) -f rocq.mk $@

rocq.mk: _CoqProject
	rocq makefile -f $< -o $@

.PHONY: clean-vo
clean-vo:
	-find -name '*.vo*' -delete

##############################################################################
# cleaning every thing

.PHONY: clean
clean: clean-lp
