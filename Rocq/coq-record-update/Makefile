CURRENT_DIR=.

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

RECORD_UPDATE_FLAG = -Q $(CURRENT_DIR)/src RecordUpdate

DEP_FLAG = -Q $(CURRENT_DIR)/src RecordUpdate

RECORD_UPDATE_FILES_NAMES = \
  src/Lens.v \
  src/RecordEta.v \
  src/RecordSet.v \
  src/RecordUpdate.v

RECORD_UPDATE_FILES=$(RECORD_UPDATE_FILES_NAMES:%.v=$(CURRENT_DIR)/%.v)

FILES = $(RECORD_UPDATE_FILES)

$(RECORD_UPDATE_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(RECORD_UPDATE_FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f src/*.vo src/*.glob src/*.vos src/*.vok src/.*.aux .depend

.DEFAULT_GOAL := all

-include .depend

