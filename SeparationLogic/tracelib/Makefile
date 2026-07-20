CURRENT_DIR=.
SETS_DIR = ../sets
FIXPOINT_DIR = ../fixedpoints
MONAD_DIR = ../MonadLib
GRAPH_DIR = ../GraphLib

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

FLAG = \
-R $(SETS_DIR) SetsClass \
-R $(FIXPOINT_DIR) FP \
-R $(MONAD_DIR) MonadLib \
-R $(CURRENT_DIR) TraceLib \
-R $(GRAPH_DIR) GraphLib \
-R ../coq-record-update/src RecordUpdate


BASE_FILES = CommonTactics.v TraceBasic.v TraceRecur.v TraceLogic.v TraceStatement.v GhostCode.v TraceLoop.v MapLib.v \
TraceLib.v

STATEREL_FILES = \
StateRel/StateRelCommonTactics.v \
StateRel/StateRelGhostCode.v \
StateRel/StateRelTraceBasic.v \
StateRel/StateRelTraceRecur.v \
StateRel/StateRelTraceLoop.v \
StateRel/StateRelTraceLib.v

MONADERR_FILES = \
MonadErr/CommonTacticsErr.v \
MonadErr/GhostCodeErr.v \
MonadErr/TraceBasicErr.v \
MonadErr/TraceRecurErr.v \
MonadErr/TraceLoopErr.v \
MonadErr/TraceLibErr.v

FILES = $(BASE_FILES) $(STATEREL_FILES) $(MONADERR_FILES)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(FLAG) $(FILES) > .depend

clean:
	@rm -f *.vo *.glob *.vos *.vok .*.aux
	@rm -f */*.vo */*.glob */*.vos */*.vok */.*.aux

.DEFAULT_GOAL := all

-include .depend
