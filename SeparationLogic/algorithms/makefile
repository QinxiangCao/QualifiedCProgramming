CURRENT_DIR=.
SETS_DIR = ../sets
FIXPOINT_DIR = ../fixedpoints
MONAD_DIR = ../MonadLib
GRAPH_DIR = ../GraphLib
LISTLIB_DIR = ../listlib
MaxMin_DIR = ../MaxMinLib
TRACE_DIR = ../tracelib

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) Algorithms \
		-R $(SETS_DIR) SetsClass \
		-R $(FIXPOINT_DIR) FP \
		-R $(MONAD_DIR) MonadLib \
		-R $(GRAPH_DIR) GraphLib \
		-R ../coq-record-update/src RecordUpdate \
		-R $(LISTLIB_DIR) ListLib \
		-R $(MaxMin_DIR) MaxMinLib \
		-R $(TRACE_DIR) TraceLib

DEP_FLAG = -Q $(CURRENT_DIR) Algorithms \
		-R $(SETS_DIR) SetsClass \
		-R $(FIXPOINT_DIR) FP \
		-R $(MONAD_DIR) MonadLib \
		-R $(GRAPH_DIR) GraphLib \
		-R ../coq-record-update/src RecordUpdate \
		-R $(LISTLIB_DIR) ListLib \
		-R $(MaxMin_DIR) MaxMinLib \
		-R $(TRACE_DIR) TraceLib

Floyd_FILES = Floyd/Floyd.v 
Dijkstra_FILES = Dijkstra/Dijkstra.v Dijkstra/Dijkstra_trace.v
Prim_FILES = Prim/Prim.v 
Kruskal_FILES = Kruskal/Kruskal.v
DFS_FILES = DFS/DFS.v DFS/DFS_traditional.v DFS/C10909_MonadProg_DFS.v
BFS_FILES = BFS/BFS.v BFS/BFS_path.v BFS/Go.v
Tarjan_FILES = Tarjan/Tarjan.v Tarjan/Tarjan_tactics.v Tarjan/Tarjan_set_tree.v Tarjan/Tarjan_basics.v Tarjan/Tarjan_basics_ex.v Tarjan/Tarjan_is_dfn.v Tarjan/Tarjan_is_low.v Tarjan/Tarjan_no_cross_edge.v Tarjan/Tarjan_bridge_iff.v Tarjan/Tarjan_tarjan.v Tarjan/Tarjan_bridge_iff_ex.v

Kosaraju_FILES = Kosaraju/SCC.v Kosaraju/Kosaraju.v

FILES = \
 MapLib.v \
 Tactics.v \
 $(Floyd_FILES) \
 $(Dijkstra_FILES) \
 $(Prim_FILES) \
 $(Kruskal_FILES) \
 $(DFS_FILES) \
 $(BFS_FILES) \
 $(Tarjan_FILES) \
 $(Kosaraju_FILES)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(COQ_FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '.*.aux' -o -name '.lia.cache' \) -delete;
	@rm -f .depend;

.DEFAULT_GOAL := all

-include .depend
