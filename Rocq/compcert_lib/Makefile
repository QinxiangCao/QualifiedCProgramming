CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

COQ_FLAG = -R . compcert.lib

DEP_FLAG = -R . compcert.lib

FILES = \
  Coqlib.v Integers.v Zbits.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob
	@rm -f *.vo */*.vo
	@rm -f *.vok */*.vok
	@rm -f *.vos */*.vos 
	@rm -f .*.aux */.*.aux
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend
