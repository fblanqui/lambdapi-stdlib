# Makefile to translate lp files to rocq

# Because, in Lambdapi, the definitions/proofs of opaque symbols is
# not recorded in lpo files, and the stt_coq export works on
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
	$(MAKE) check-names
	$(MAKE) v
	$(MAKE) vo

##############################################################################
# generation of patched lp files (removal of the "opaque" keywords)

ORIG_LPFILES := $(wildcard ../*.lp)
LPFILES := $(ORIG_LPFILES:../%=%)

.PHONY: lp
lp: $(LPFILES)

%.lp: ../%.lp
	sed -e 's/^opaque //' $< > $@

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
# check the validity of names in rocq

.PHONY: check-names
check-names: $(DKFILES:%.dk=%.dk.check-names)

%.dk.check-names: %.dk
	@lambdapi export -o stt_coq --encoding encoding.lp --renaming renaming.lp --mapping mapping.lp --requiring mapping --use-notations --only-check-names $*.dk

##############################################################################
# generation of rocq files

VFILES := $(DKFILES:%.dk=%.v)

.PHONY: v
v: $(VFILES)

%.v: encoding.lp mapping.lp renaming.lp %.dk
	@echo lambdapi export -o stt_coq $*.dk > $@
	@lambdapi export -o stt_coq --encoding encoding.lp --renaming renaming.lp --mapping mapping.lp --requiring mapping --use-notations $*.dk > $@

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
clean: clean-dk
