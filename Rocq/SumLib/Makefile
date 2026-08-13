CURRENT_DIR=.

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) SumLib \
           -R ../sets SetsClass \
           -R ../compcert_lib compcert.lib \
           -R ../auxlibs AUXLib \
           -R ../listlib ListLib \
           -R ../Common SimpleC.Common \
           -R ../GraphLib GraphLib

DEP_FLAG = $(COQ_FLAG)

LIB_FILES = \
	Sum.v \
	ZRange.v \
	ZRect.v \
	ListMember.v \
	GraphSum.v \
	SumLib.v

FILES = $(LIB_FILES)

$(LIB_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

world: \
  $(FILES:%.v=%.vo)

all: world

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(LIB_FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(LIB_FILES) > .depend

clean:
	@rm -f *.glob;
	@rm -f *.vo;
	@rm -f *.vok;
	@rm -f *.vos;
	@rm -f .*.aux;
	@rm -f .lia.cache .nia.cache;
	@rm -f .depend;

.DEFAULT_GOAL := all

-include .depend
