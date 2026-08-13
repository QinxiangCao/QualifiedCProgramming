CURRENT_DIR=.

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) GraphLib \
           -R ../sets SetsClass \
		   -R ../MaxMinLib MaxMinLib \
		   -R ../listlib ListLib
DEP_FLAG = -Q $(CURRENT_DIR) GraphLib \
           -R ../sets SetsClass \
		   -R ../MaxMinLib MaxMinLib \
		   -R ../listlib ListLib

BASE_FILES = graph_basic.v Syntax.v GraphLib.v
REACHABLE_FILES = \
reachable/reachable_basic.v reachable/reachable_restricted.v \
reachable/bfs_dist.v \
reachable/path_basic.v reachable/path.v \
reachable/vpath.v reachable/epath.v \
reachable/Zweight.v
DIRECTED_FILES = directed/rootedtree.v directed/dfstree.v
SUBGRAPH_FILES = subgraph/subgraph.v
UNDIRECTED_FILES = undirected/undirected_basic.v undirected/tree.v
EXAMPLES_FILES = examples/floyd.v examples/dijkstra.v examples/prim.v examples/kruskal.v examples/tarjan.v 

FILES = \
 $(BASE_FILES) \
 $(REACHABLE_FILES) \
 $(DIRECTED_FILES) \
 $(SUBGRAPH_FILES) \
 $(UNDIRECTED_FILES) \
 $(EXTREMUM_FILES) \
 $(EXAMPLES_FILES) \

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

world: \
  $(FILES:%.v=%.vo)

all: world 

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
