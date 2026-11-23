MAKEFLAGS += -r -k -j$(shell nproc)

.PREFIX:

.PHONY: default
default:
	$(MAKE) lp
	$(MAKE) dk
	#$(MAKE) INCLUDE_DKO_MK=1 dko
	$(MAKE) v
	$(MAKE) vo

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

DKFILES := $(LPFILES:%.lp=%.dk)

.PHONY: dk
dk: $(DKFILES)

%.dk: %.lp
	lambdapi export -o dk -w -v 0 $< > $@

.PHONY: clean-dk
clean-dk: clean-dko clean-v
	-find . -name '*.dk' -delete
	-rm -f dko.mk

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

VFILES_TODO := $(DKFILES:%.dk=%.v)

.PHONY: v
v: $(VFILES_TODO)

%.v: encoding.lp mapping.lp renaming.lp %.dk
	lambdapi export -o stt_coq --encoding encoding.lp --renaming renaming.lp --mapping mapping.lp --requiring mapping --use-notations $*.dk > $@

.PHONY: clean-v
clean-v: clean-vo
	-find . -name '*.v' -a ! -name mapping.v -delete
	-find . -name '*.glob'
	-rm -f rocq.mk rocq.mk.conf

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

.PHONY: clean
clean: clean-dk
