.POSIX:
.SUFFIXES:

.PHONY: default
default: lpo

LP := $(filter-out encoding.lp mappings.lp,$(wildcard *.lp))

LPO := $(LP:%.lp=%.lpo)
.PHONY: lpo
lpo: $(LPO)

.PHONY: clean-lpo
clean-lpo:
	-rm -f $(LPO)

%.lpo: %.lp
	lambdapi check --gen-obj $<

.PHONY: install
install: lambdapi.pkg $(LP) $(LPO)
	lambdapi install $+

.PHONY: uninstall
uninstall: lambdapi.pkg
	lambdapi uninstall lambdapi.pkg

DK := $(LP:%.lp=%.dk)

.PHONY: dk
dk: $(DK)

%.dk: %.lp
	lambdapi export -o dk $< > $@

.PHONY: clean-dk
clean-dk: clean-dko
	-rm -f $(DK)

DKO := $(DK:%.dk=%.dko)

.PHONY: dko
dko: $(DKO)

%.dko: %.dk
	dk check -I . -e $<

.PHONY: clean-dko
clean-dko:
	-rm -f $(DKO)

V := $(DK:%.dk=%.v)

.PHONY: v
v: $(V)

%.v: %.dk
	lambdapi export -o stt_coq --encoding encoding.lp --use-notations --mapping mappings.lp --requiring mappings $< > $@

.PHONY: clean-v
clean-v: clean-vo
	-find . -name '*.v' -a ! -name mappings.v -delete

.PHONY: clean-vo
clean-vo:
	-find . -name '*.vo' -delete

.PHONY: clean
clean: clean-lpo clean-dk
