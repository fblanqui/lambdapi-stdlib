LPFILES := $(wildcard ../*.lp)
VFILES := $(LPFILES:../%.lp=%.v)
VOFILES := $(VFILES:%=%o)
PARTIAL_STDLIB_DIR := partial_stdlib
PARTIAL_STDLIB_ORDER := $(PARTIAL_STDLIB_DIR)/order.txt
ROCQ_COMPILE ?= rocq compile
ROCQ_MAKEFILE ?= rocq makefile

default: v

v: $(VFILES)

%.v: encoding.lp mappings.lp ../%.lp
	lambdapi export -o stt_coq --encoding encoding.lp --use-notations --mapping mappings.lp --requiring mappings ../$*.lp > $@ #--renaming $(HOL2DK_DIR)/renaming.lp --requiring "$(REQUIRING)"

clean-v:
	rm -f $(VFILES)

.PHONY: partial-stdlib
partial-stdlib:
	cd $(PARTIAL_STDLIB_DIR) && xargs -n1 $(ROCQ_COMPILE) < order.txt

rocq.mk: _CoqProject
	$(ROCQ_MAKEFILE) -f _CoqProject -o $@

vo: rocq.mk
	$(MAKE) -f rocq.mk

clean-vo:
	rm -f $(VOFILES)
	find $(PARTIAL_STDLIB_DIR) -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' | xargs rm -f
