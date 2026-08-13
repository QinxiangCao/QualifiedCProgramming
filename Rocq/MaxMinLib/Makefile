CURRENT_DIR=.
SETS_DIR = ../sets

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) MaxMinLib -R $(SETS_DIR) SetsClass
DEP_FLAG = -Q $(CURRENT_DIR) MaxMinLib -R $(SETS_DIR) SetsClass

EXTREMUM_FILES = MaxMin.v Interface.v

FILES = \
 $(EXTREMUM_FILES) \

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

world: \
  $(FILES:%.v=%.vo)

all: world 

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob;
	@rm -f *.vo */*.vo;
	@rm -f *.vok */*.vok;
	@rm -f *.vos */*.vos;
	@rm -f .*.aux */.*.aux;
	@rm -f .depend;

.DEFAULT_GOAL := all

include .depend
