LPFILES := $(wildcard ../*.lp)
VFILES := $(LPFILES:../%.lp=%.v)
VOFILES := $(VFILES:%=%o)

.PHONY: default
default:
	$(MAKE) v
	$(MAKE) vo

.PHONY: v
v: $(VFILES)

%.v: encoding.lp mappings.lp ../%.lp
	lambdapi export -o stt_coq --encoding encoding.lp --renaming renaming.lp --mapping mappings.lp --requiring mappings --use-notations ../$*.lp > $@

.PHONY: clean-v
clean-v: clean-vo
	rm -f $(VFILES)

rocq.mk: _CoqProject
	rocq makefile -f _CoqProject -o $@

.PHONY: vo
vo: rocq.mk
	$(MAKE) -f rocq.mk

.PHONY: clean-vo
clean-vo:
	rm -f *.vo*

.PHONY: clean
clean: clean-v
	rm -f rocq.mk rocq.mk.conf *.glob
