CURRENT_DIR=.
COQBIN ?=
SUF ?=
empty :=
space := $(empty) $(empty)
comma := ,
powershell_list = $(subst $(space),$(comma) ,$(strip $(foreach item,$(1),'$(item)')))

-include CONFIGURE

# Cygwin also exports OS=Windows_NT, but its make is built for *-cygwin and
# expects POSIX recipes.  Native/MinGW/MSYS make must use the Windows branch.
USE_WINDOWS_COMMANDS := $(if $(and $(filter Windows_NT,$(OS)),$(if $(findstring cygwin,$(MAKE_HOST)),,yes)),yes)

ifeq ($(USE_WINDOWS_COMMANDS),yes)
SHELL := cmd
	print_line = @powershell -NoProfile -Command "[Console]::Out.Write('$(1)' + [char]10)"
	timeit = $(call print_line,$(1)) && $(2)

define MOVE_FILE
powershell -NoProfile -Command "Move-Item -Force '$(1)' '$(2)'"
endef

define CONCAT_FILES
powershell -NoProfile -Command "Get-Content -LiteralPath $(call powershell_list,$(1)) | Set-Content -Encoding ASCII '$(2)'"
endef

define REMOVE_FILES
powershell -NoProfile -Command "Remove-Item -Force -LiteralPath $(call powershell_list,$(1)) -ErrorAction SilentlyContinue; exit 0"
endef

define REMOVE_TREE_OUTPUTS
powershell -NoProfile -Command "Get-ChildItem -Path $(call powershell_list,$(1)) -Recurse -Force -Include *.vo,*.glob,*.vos,*.vok,.*.aux,.lia.cache -ErrorAction SilentlyContinue | Remove-Item -Force -ErrorAction SilentlyContinue; exit 0"
endef
else
	print_line = @printf "%s\n" "$(1)"
	timeit = @printf "%-70s" "$(1)"; t0=`date +%s`; $(2); t1=`date +%s`; echo "$$((t1 - t0)) s"

define MOVE_FILE
mv -f $(1) $(2)
endef

define CONCAT_FILES
cat $(1) > $(2)
endef

define REMOVE_FILES
rm -f $(1)
endef

define REMOVE_TREE_OUTPUTS
find $(1) -type f \( -name '*.vo' -o -name '*.glob' -o -name '*.vos' -o -name '*.vok' -o -name '.*.aux' -o -name '.lia.cache' \) -delete
endef
endif

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)
COQDEP_ARG_FILES = \
	.coqdep.core.args.tmp \
	.coqdep.core.flocq.args.tmp \
	.coqdep.core.project.args.tmp \
	.coqdep.examples.applications.args.tmp \
	.coqdep.examples.qcp_democases.args.tmp \
	.coqdep.examples.qcp_demo_feature_cases.args.tmp \
	.coqdep.examples.qcp_demo_tutorial.args.tmp \
	.coqdep.examples.llm_friendly_cases.args.tmp \
	.coqdep.examples.llm_bench.args.tmp

# Native Windows needs GNU Make to write long argument lists without passing
# them through cmd.exe.  POSIX systems use printf, which also works with the
# older GNU Make shipped by macOS and is well below their ARG_MAX limit.
ifeq ($(USE_WINDOWS_COMMANDS),yes)
define RUN_COQDEP
$(file >$(1),$(DEP_FLAG) $(2))( $(COQDEP) -f $(1) > $(3) || (echo Retrying coqdep for $(3) 1>&2 && $(COQDEP) -f $(1) > $(3)) || (echo Retrying coqdep for $(3) again 1>&2 && $(COQDEP) -f $(1) > $(3)) ) && $(call REMOVE_FILES,$(1))
endef
else
define RUN_COQDEP
printf '%s\n' '$(DEP_FLAG) $(2)' > $(1) && ( $(COQDEP) -f $(1) > $(3) || (echo 'Retrying coqdep for $(3)' >&2 && $(COQDEP) -f $(1) > $(3)) || (echo 'Retrying coqdep for $(3) again' >&2 && $(COQDEP) -f $(1) > $(3)) ) && $(call REMOVE_FILES,$(1))
endef
endif

DIRS = \
	Common auxlibs compcert_lib SeparationLogic sets unifysl StrategyLib fixedpoints MonadLib examples MaxMinLib GraphLib listlib tracelib algorithms coq-record-update
 
COQ_FLAG = -R flocq/src Flocq -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R stdlib SimpleC.StdLib -R StrategyLib SimpleC.StrategyLib -R Common SimpleC.Common -R fixedpoints FP -R MonadLib MonadLib -R listlib ListLib -R MaxMinLib MaxMinLib -R GraphLib GraphLib -R SumLib SumLib -R tracelib TraceLib -R coq-record-update/src RecordUpdate -Q algorithms Algorithms

DEP_FLAG = -R flocq/src Flocq -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R stdlib SimpleC.StdLib -R StrategyLib SimpleC.StrategyLib -R Common SimpleC.Common -R fixedpoints FP -R MonadLib MonadLib -R listlib ListLib -R MaxMinLib MaxMinLib -R GraphLib GraphLib -R SumLib SumLib -R tracelib TraceLib -R coq-record-update/src RecordUpdate -Q algorithms Algorithms

Common_FILES = \
  CTypes.v COps.v Notations.v

Compcertlib_FILES = \
  Coqlib.v Integers.v Zbits.v

ListLib_FILES = \
	Base/Positional.v Base/Inductive.v \
	General/Length.v General/Presuffix.v General/Forall.v General/IndexedElements.v General/NoDup.v 

MaxMinLib_FILES = \
	MaxMin.v Interface.v 

GraphLib_BASE_FILES = graph_basic.v Syntax.v GraphLib.v

GraphLib_REACHABLE_FILES = \
	reachable/reachable_basic.v reachable/reachable_restricted.v \
	reachable/bfs_dist.v \
	reachable/path_basic.v reachable/path.v \
	reachable/vpath.v reachable/epath.v \
	reachable/Zweight.v

GraphLib_DIRECTED_FILES = directed/rootedtree.v directed/dfstree.v

GraphLib_SUBGRAPH_FILES = subgraph/subgraph.v

GraphLib_UNDIRECTED_FILES = undirected/undirected_basic.v undirected/tree.v

GraphLib_EXAMPLES_FILES = examples/floyd.v examples/dijkstra.v examples/prim.v examples/kruskal.v examples/tarjan.v 

GraphLib_FILES = \
	$(GraphLib_BASE_FILES) \
 	$(GraphLib_REACHABLE_FILES) \
 	$(GraphLib_DIRECTED_FILES) \
 	$(GraphLib_SUBGRAPH_FILES) \
 	$(GraphLib_UNDIRECTED_FILES) \
 	$(GraphLib_EXAMPLES_FILES)

RecordUpdate_FILES = \
	src/RecordEta.v src/RecordSet.v src/Lens.v src/RecordUpdate.v

TraceLib_BASE_FILES = \
	CommonTactics.v TraceBasic.v TraceRecur.v TraceLogic.v GhostCode.v TraceLoop.v MapLib.v TraceLib.v

TraceLib_STATEREL_FILES = \
	StateRel/StateRelCommonTactics.v \
	StateRel/StateRelGhostCode.v \
	StateRel/StateRelTraceBasic.v \
	StateRel/StateRelTraceRecur.v \
	StateRel/StateRelTraceLoop.v \
	StateRel/StateRelTraceLib.v

TraceLib_MONADERR_FILES = \
	MonadErr/CommonTacticsErr.v \
	MonadErr/GhostCodeErr.v \
	MonadErr/TraceBasicErr.v \
	MonadErr/TraceRecurErr.v \
	MonadErr/TraceLoopErr.v \
	MonadErr/TraceLibErr.v

TraceLib_FILES = \
	$(TraceLib_BASE_FILES) \
	$(TraceLib_STATEREL_FILES) \
	$(TraceLib_MONADERR_FILES)

Algorithms_FILES = \
	MapLib.v Tactics.v \
	Floyd/Floyd.v \
	Dijkstra/Dijkstra.v Dijkstra/Dijkstra_trace.v \
	Prim/Prim.v \
	Kruskal/Kruskal.v \
	DFS/DFS.v DFS/DFS_traditional.v DFS/C10909_MonadProg_DFS.v \
	BFS/BFS.v BFS/BFS_path.v BFS/Go.v \
	Tarjan/Tarjan.v Tarjan/Tarjan_tactics.v Tarjan/Tarjan_set_tree.v \
	Tarjan/Tarjan_basics.v Tarjan/Tarjan_basics_ex.v \
	Tarjan/Tarjan_is_dfn.v Tarjan/Tarjan_no_cross_edge.v Tarjan/Tarjan_is_low.v \
	Tarjan/Tarjan_bridge_iff.v Tarjan/Tarjan_tarjan.v \

SumLib_FILES = \
	Sum.v \
	ZRange.v \
	ZRect.v \
	ListMember.v \
	GraphSum.v \
	FiniteExtra.v \
	SumLib.v

Flocq_FILES = \
	Version.v \
	Core/Raux.v \
	Core/Zaux.v \
	Core/Defs.v \
	Core/Digits.v \
	Core/Float_prop.v \
	Core/FIX.v \
	Core/FLT.v \
	Core/FLX.v \
	Core/FTZ.v \
	Core/Generic_fmt.v \
	Core/Round_pred.v \
	Core/Round_NE.v \
	Core/Ulp.v \
	Core/Core.v \
	Calc/Bracket.v \
	Calc/Div.v \
	Calc/Operations.v \
	Calc/Plus.v \
	Calc/Round.v \
	Calc/Sqrt.v \
	Prop/Div_sqrt_error.v \
	Prop/Mult_error.v \
	Prop/Plus_error.v \
	Prop/Relative.v \
	Prop/Sterbenz.v \
	Prop/Round_odd.v \
	Prop/Double_rounding.v \
	IEEE754/BinarySingleNaN.v \
	IEEE754/Binary.v \
	IEEE754/Bits.v \
	IEEE754/PrimFloat.v \
	Pff/Pff.v \
	Pff/Pff2FlocqAux.v \
	Pff/Pff2Flocq.v

StdLib_FILES = \
  string_lib.v \
  string_strategy_goal.v \
  string_strategy_proof.v \
  string_strategy_goal_check.v

Auxlibs_FILES = \
  int_auto.v Idents.v Feq.v Axioms.v VMap.v relations.v ListLib.v \
  OrdersDecFact.v BinaryTree.v EqDec.v Bool.v Tactics.v Vec.v MonotonicList.v

Sets_FILES = \
  SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v

Unify_FILES = \
   Interface.v 

FIXPOINT_FILES = \
  Coqlib.v LiftConstructors.v  PartialOrder_Setoid.v  KnasterTarski.v  BourbakiWitt.v AllFramework.v SetsFixedpoints.v

ListMonad_Files = \
	 ListMonad.v ListBasic.v

OptionMonad_Files = \
	 OptionMonad.v OptionBasic.v

SetMonad_Files = \
	SetBasic.v SetHoare.v FixpointLib.v SetMonad.v

StateRelMonad_Files = \
	StateRelBasic.v StateRelHoare.v FixpointLib.v safeexec_lib.v StateRelMonad.v

MonadErr_Files = \
	MonadErrBasic.v MonadErrLoop.v MonadErrHoare.v MonadErrHoarePartial.v monadesafe_lib.v StateRelMonadErr.v

MonadExample_FILES = \
	kmp.v mergesort.v union_find_err.v 
  
MONAD_FILES = \
	MonadLib/MonadLib.v \
	MonadLib/Monad.v \
	$(ListMonad_Files:%.v=MonadLib/ListMonad/%.v) \
	$(OptionMonad_Files:%.v=MonadLib/OptionMonad/%.v) \
	$(SetMonad_Files:%.v=MonadLib/SetMonad/%.v) \
	$(StateRelMonad_Files:%.v=MonadLib/StateRelMonad/%.v) \
	$(MonadErr_Files:%.v=MonadLib/MonadErr/%.v) \
	$(MonadExample_FILES:%.v=MonadLib/Examples/%.v) \

SL_FILES = \
  CommonAssertion.v Assertion.v Mem.v ConAssertion.v \
  NestedCriticalSTS.v CriticalSTS.v FloatLib.v \
  IntLib.v StoreAux.v pocv02.v SeparationLogic.v CNotation.v MapLib.v StringLib.v \
  ArrayLib.v ArrayLibCore.v Array2Lib.v Array2LibCore.v PtrArray2Lib.v PtrArray2LibCore.v \

StrategyLib_FILES = \
  DepList.v Mapping.v

QCP_DEMO_Example_Lib_FILES = \
	poly_sll_lib.v sll_lib.v sll_insert_sort_lib.v functional_queue_lib.v dll_queue_lib.v sll_queue_lib.v simple_arith/Apos_lib.v simple_arith/PDiv_lib.v bst_lib.v bst_fp_lib.v swap_lib.v eval_lib.v avl_shape.v sll_shape_lib.v dll_shape_lib.v \
	sll_merge_rel_lib.v kmp_lib.v kmp_rel_lib.v int_array_merge_rel_lib.v majorityElement_lib.v \

QCP_DEMO_TUTORIAL_FEATURE_Lib_FILES = \
	branch_join_private_condition_lib.v

QCP_DEMO_TUTORIAL_Lib_FILES = \
	swap_simple1_lib.v \
	$(QCP_DEMO_TUTORIAL_FEATURE_Lib_FILES)

LLM_FRIENDLY_CASES_Lib_FILES = \
	poly_sll_lib.v sll_lib.v sll_insert_sort_lib.v functional_queue_lib.v dll_queue_lib.v sll_queue_lib.v simple_arith/Apos_lib.v simple_arith/PDiv_lib.v bst_lib.v bst_fp_lib.v swap_lib.v eval_lib.v avl_shape.v sll_shape_lib.v dll_shape_lib.v \
	sll_merge_rel_lib.v kmp_lib.v kmp_rel_lib.v int_array_merge_rel_lib.v \
	majorityElement_lib.v bubble_sort_lib.v sortArray_lib.v zephyr_slist_lib.v union_find_err_rel_lib.v simple_arith/test_prime_lib.v \

LLM_BENCH_Lib_FILES = \
	Algorithms/coin_change/coin_change_lib.v \
	Algorithms/dual_loop_quicksort/dual_loop_quicksort_lib.v \
	Algorithms/energy_necklace/energy_necklace_lib.v \
	Algorithms/house_robber/house_robber_lib.v \
	Algorithms/longest_increasing_subsequence/longest_increasing_subsequence_lib.v \
	Algorithms/longest_nondecreasing_subsequence/longest_nondecreasing_subsequence_lib.v \
	Algorithms/maximum_subarray/maximum_subarray_lib.v \
	Algorithms/multiple_knapsack/multiple_knapsack_lib.v \
	Algorithms/quicksort/int_array_quicksort_lib.v \
	Algorithms/rmq/rmq_lib.v \
	Algorithms/sliding_window_maximum/sliding_window_maximum_lib.v \
	Algorithms/sort_point/sort_point_lib.v \
	Algorithms/split_array_largest_sum/split_array_largest_sum_lib.v \
	Algorithms/super_piano/super_piano_lib.v \
	Algorithms/zero_one_knapsack/zero_one_knapsack_lib.v \
	Data_structures/priority_queue/priority_queue_lib.v \
	Algorithms/manacher/manacher_lib.v \
	Engineering/string/string_lib.v \
	Engineering/string/memchr_lib.v \
	Engineering/string/search_lib.v \
	Engineering/string/strcat_lib.v \
	Engineering/string/strcmp_lib.v \
	Engineering/string/strcpy_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/list_tail_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/list_append_raw_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_app_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_copy_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_free_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_iter_back_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_iter_back_2_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_iter_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_iter_twice_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_merge_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_multi_append_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_multi_merge_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_multi_rev_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_rev_append_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_rev_append_twice_rel_lib.v \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_rev_rel_lib.v \
	Codeforces/SpecHelpers.v \
	Codeforces/GraphInstances.v \
	Codeforces/GridGraphInstances.v

APPLICATION_Lib_FILES = \
	fme/algorithm.v fme/implement.v fme/implement_lemma.v fme/fme_lib.v typeinfer/repr_subst_prop.v typeinfer/sol_prop.v typeinfer/sound_pv.v typeinfer/type_infer_lib.v typeinfer/typeinfer_lib.v \
	minigmp/GmpAux.v minigmp/GmpNumber.v minigmp/GmpMulAux.v minigmp_sumlib/GmpAux.v minigmp_sumlib/GmpNumber.v minigmp_sumlib/GmpMulAux.v cnf_trans/cnf_trans_lib.v cnf_trans/smt_lang_lib.v alpha_equiv/ast_lib.v \
	malloc.v super_poly_sll2.v mergeablelist/sll_project_lib.v

APPLICATION_Lib_FILES += \
	convex_hull/Geo_Vec.v convex_hull/Geo_Point_Primitives.v convex_hull/Convexity.v convex_hull/Maximality.v convex_hull/Geo_Point.v convex_hull/Geo_Predicates.v convex_hull/Point_Order.v convex_hull/Point_Array_Specs.v \
	convex_hull/Graham_Scan.v convex_hull/Graham_Scan_M.v convex_hull/Andrew_Monotone_Chain.v \
	convex_hull/Andrew_Monotone_Chain_M.v convex_hull/Reversal.v convex_hull/ConvexHull.v convex_hull/convex_hull_lib.v

QCP_DEMO_EXAMPLE_FILE_NAME = \
	poly_sll sll sll_insert_sort functional_queue dll_queue sll_queue simple_arith/abs simple_arith/add simple_arith/max3 simple_arith/gcd simple_arith/Always_pos simple_arith/div_test simple_arith/exgcd \
	sum bst_insert bst_insert_rec bst_fp_insert bst_fp_delete swap eval bst_delete_rec bst_delete_rec2 avl_insert sll_auto dll_auto array_auto chars \
	kmp_rel int_array_merge_rel sll_merge_rel sll_split_while majorityElement

QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_FILE_NAME = \
	branch_destruct branch_join_private_condition multiinv_examples

QCP_DEMO_TUTORIAL_EXAMPLE_FILE_NAME = \
	swap_simple1 swap_simple2 swap_simple3 given_mark float \
	$(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_FILE_NAME)

LLM_FRIENDLY_CASES_EXAMPLE_FILE_NAME = \
	poly_sll sll sll_insert_sort functional_queue dll_queue sll_queue simple_arith/abs simple_arith/add simple_arith/max3 simple_arith/gcd simple_arith/Always_pos simple_arith/div_test simple_arith/exgcd simple_arith/delta simple_arith/test_prime \
	sum bst_insert bst_insert_rec bst_fp_insert bst_fp_delete swap eval bst_delete_rec bst_delete_rec2 avl_insert sll_auto dll_auto array_auto chars \
	kmp_rel int_array_merge_rel sll_merge_rel sll_split_while majorityElement bubble_sort sortArray sortArray2 sortArray3 array_cases union_find_err_rel \
	two_d_int_array two_d_int_ptr_array two_d_char_ptr_array

LLM_BENCH_EXAMPLE_FILE_NAME = \
	Algorithms/coin_change/coin_change \
	Algorithms/dual_loop_quicksort/dual_loop_quicksort \
	Algorithms/energy_necklace/energy_necklace \
	Algorithms/house_robber/house_robber \
	Algorithms/longest_increasing_subsequence/longest_increasing_subsequence \
	Algorithms/longest_nondecreasing_subsequence/longest_nondecreasing_subsequence \
	Algorithms/maximum_subarray/maximum_subarray \
	Algorithms/multiple_knapsack/multiple_knapsack \
	Algorithms/quicksort/int_array_quicksort \
	Algorithms/rmq/rmq \
	Algorithms/sliding_window_maximum/sliding_window_maximum \
	Algorithms/sort_point/sort_point \
	Algorithms/split_array_largest_sum/split_array_largest_sum \
	Algorithms/super_piano/super_piano \
	Algorithms/zero_one_knapsack/zero_one_knapsack \
	Data_structures/priority_queue/priority_queue \
	Algorithms/manacher/manacher \
	Engineering/string/memchr \
	Engineering/string/memory \
	Engineering/string/search \
	Engineering/string/strcat \
	Engineering/string/strcmp \
	Engineering/string/strcpy \
	Engineering/string/strlen \
	Engineering/glibc_slist/glibc_slist_rel/list_tail_rel \
	Engineering/glibc_slist/glibc_slist_rel/list_append_raw_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_app_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_copy_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_free_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_iter_back_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_iter_back_2_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_iter_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_iter_twice_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_merge_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_multi_append_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_multi_merge_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_multi_rev_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_rev_append_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_rev_append_twice_rel \
	Engineering/glibc_slist/glibc_slist_rel/glibc_slist_rev_rel

LLM_BENCH_STRATEGY_FILE_NAME = \
	Engineering/string/string

APPLICATION_FILE_NAME = \
	LiteOS/Get_Set_Value LiteOS/GetSortLinkNextExpireTime LiteOS/List_Add LiteOS/LOS_ListDelete LiteOS/LOS_ListDelInit LiteOS/LOS_ListEmpty LiteOS/LOS_ListInit LiteOS/OsAdd2SortLink LiteOS/OsDeleteNodeSortLink \
	LiteOS/OsDeleteSortLink LiteOS/OsGetNextExpireTime LiteOS/OsGetSortLinkAttribute LiteOS/OsSortLinkGetNextExpireTime LiteOS/OsSortLinkGetRemainTime LiteOS/OsSortLinkGetTargetExpireTime \
	LiteOS/OsSortLinkInit LiteOS/OsSortLinkResponseTimeConvertFreq \
	typeinfer/typeinfer alpha_equiv/alpha_equiv alpha_equiv/subst alpha_equiv/thm_apply cnf_trans/cnf_trans fme/fme minigmp/gmp minigmp_sumlib/gmp mergeablelist/sll_project

APPLICATION_FILE_NAME += \
	convex_hull/graham_scan convex_hull/graham_scan_dedup convex_hull/andrew_monotone_chain

APPLICATION_PROOF_SPLIT_FILES = \
	minigmp/gmp_proof_manual_part1.v \
	minigmp/gmp_proof_manual_part2.v \
	minigmp/gmp_proof_manual_part3.v \
	minigmp/gmp_proof_manual_part4.v \
	minigmp/gmp_proof_manual_part5.v \
	minigmp/gmp_proof_manual_part6.v \
	minigmp_sumlib/gmp_proof_manual_part1.v \
	minigmp_sumlib/gmp_proof_manual_part2.v \
	minigmp_sumlib/gmp_proof_manual_part3.v \
	minigmp_sumlib/gmp_proof_manual_part4.v \
	minigmp_sumlib/gmp_proof_manual_part5.v \
	minigmp_sumlib/gmp_proof_manual_part6.v \
	cnf_trans/cnf_trans_proof_manual1.v \
	cnf_trans/cnf_trans_proof_manual2.v \
	cnf_trans/cnf_trans_proof_manual3.v

QCP_DEMO_Examples_FILES = \
	$(addsuffix _goal.v, $(QCP_DEMO_EXAMPLE_FILE_NAME:%=QCP_demos_human/%)) \
	$(addsuffix _goal_check.v, $(QCP_DEMO_EXAMPLE_FILE_NAME:%=QCP_demos_human/%)) \
	$(addsuffix _proof_auto.v, $(QCP_DEMO_EXAMPLE_FILE_NAME:%=QCP_demos_human/%)) \
	$(addsuffix _proof_manual.v, $(QCP_DEMO_EXAMPLE_FILE_NAME:%=QCP_demos_human/%)) \
	$(QCP_DEMO_Example_Lib_FILES:%=QCP_demos_human/%)

QCP_DEMO_TUTORIAL_FEATURE_Examples_FILES = \
	$(addsuffix _goal.v, $(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(addsuffix _goal_check.v, $(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(addsuffix _proof_auto.v, $(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(addsuffix _proof_manual.v, $(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(QCP_DEMO_TUTORIAL_FEATURE_Lib_FILES:%=QCP_demos_tutorial/%)

QCP_DEMO_TUTORIAL_Examples_FILES = \
	$(addsuffix _goal.v, $(QCP_DEMO_TUTORIAL_EXAMPLE_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(addsuffix _goal_check.v, $(QCP_DEMO_TUTORIAL_EXAMPLE_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(addsuffix _proof_auto.v, $(QCP_DEMO_TUTORIAL_EXAMPLE_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(addsuffix _proof_manual.v, $(QCP_DEMO_TUTORIAL_EXAMPLE_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(QCP_DEMO_TUTORIAL_Lib_FILES:%=QCP_demos_tutorial/%)

APPLICATION_Examples_FILES = \
	$(addsuffix _goal.v, $(APPLICATION_FILE_NAME:%=Applications_human/%)) \
	$(addsuffix _goal_check.v, $(APPLICATION_FILE_NAME:%=Applications_human/%)) \
	$(addsuffix _proof_auto.v, $(APPLICATION_FILE_NAME:%=Applications_human/%)) \
	$(addsuffix _proof_manual.v, $(APPLICATION_FILE_NAME:%=Applications_human/%)) \
	$(APPLICATION_Lib_FILES:%=Applications_human/%) \
	$(APPLICATION_PROOF_SPLIT_FILES:%=Applications_human/%)

LLM_FRIENDLY_CASES_Examples_FILES = \
	$(addsuffix _goal.v, $(LLM_FRIENDLY_CASES_EXAMPLE_FILE_NAME:%=QCP_demos_LLM/%)) \
	$(addsuffix _goal_check.v, $(LLM_FRIENDLY_CASES_EXAMPLE_FILE_NAME:%=QCP_demos_LLM/%)) \
	$(addsuffix _proof_auto.v, $(LLM_FRIENDLY_CASES_EXAMPLE_FILE_NAME:%=QCP_demos_LLM/%)) \
	$(addsuffix _proof_manual.v, $(LLM_FRIENDLY_CASES_EXAMPLE_FILE_NAME:%=QCP_demos_LLM/%)) \
	$(LLM_FRIENDLY_CASES_Lib_FILES:%=QCP_demos_LLM/%)

LLM_BENCH_Examples_FILES = \
	$(LLM_BENCH_Lib_FILES:%=LLM_bench/%) \
	$(addsuffix _strategy_goal.v, $(LLM_BENCH_STRATEGY_FILE_NAME:%=LLM_bench/%)) \
	$(addsuffix _strategy_goal_check.v, $(LLM_BENCH_STRATEGY_FILE_NAME:%=LLM_bench/%)) \
	$(addsuffix _strategy_proof.v, $(LLM_BENCH_STRATEGY_FILE_NAME:%=LLM_bench/%)) \
	$(addsuffix _goal.v, $(LLM_BENCH_EXAMPLE_FILE_NAME:%=LLM_bench/%)) \
	$(addsuffix _proof_auto.v, $(LLM_BENCH_EXAMPLE_FILE_NAME:%=LLM_bench/%)) \
	$(addsuffix _proof_manual.v, $(LLM_BENCH_EXAMPLE_FILE_NAME:%=LLM_bench/%)) \
	$(addsuffix _goal_check.v, $(LLM_BENCH_EXAMPLE_FILE_NAME:%=LLM_bench/%))

QCP_DEMO_EXAMPLE_ONLY = \
	$(QCP_DEMO_Examples_FILES:%.v=examples/%.v) \
	$(QCP_DEMO_StrategyProof_FILES:%.v=examples/%.v) \

QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_ONLY = \
	$(QCP_DEMO_TUTORIAL_FEATURE_Examples_FILES:%.v=examples/%.v) \

QCP_DEMO_TUTORIAL_EXAMPLE_ONLY = \
	$(QCP_DEMO_TUTORIAL_Examples_FILES:%.v=examples/%.v) \
	$(QCP_DEMO_TUTORIAL_StrategyProof_FILES:%.v=examples/%.v) \

APPLICATION_EXAMPLE_ONLY = \
	$(APPLICATION_Examples_FILES:%.v=examples/%.v) \
	$(APPLICATION_StrategyProof_FILES:%.v=examples/%.v) \
	$(LiteOS_FILE:%.v=examples/%.v) \

LLM_FRIENDLY_CASES_EXAMPLE_ONLY = \
	$(LLM_FRIENDLY_CASES_Examples_FILES:%.v=examples/%.v) \
	$(LLM_FRIENDLY_CASES_StrategyProof_FILES:%.v=examples/%.v) \

LLM_BENCH_EXAMPLE_ONLY = \
	$(LLM_BENCH_Examples_FILES:%.v=examples/%.v) \

Examples_FILES = \
	$(QCP_DEMO_Examples_FILES) \
	$(QCP_DEMO_TUTORIAL_Examples_FILES) \
	$(APPLICATION_Examples_FILES) \
	$(LLM_FRIENDLY_CASES_Examples_FILES) \
	$(LLM_BENCH_Examples_FILES)

QCP_DEMO_STRATEGY_FILE_NAME = \
	common poly_sll sll_shape sll dll_queue functional_queue sll_queue int_array undef_uint_array uint_array array_shape bst bst_fp eval char_array avl dll_shape safeexec safeexecE

QCP_DEMO_TUTORIAL_STRATEGY_FILE_NAME = \
	swap_simple2 swap_simple3

LLM_FRIENDLY_CASES_STRATEGY_FILE_NAME = \
	common poly_sll sll_shape sll dll_queue functional_queue sll_queue int_array undef_uint_array uint_array array_shape bst bst_fp eval char_array avl dll_shape safeexec safeexecE \
	array2 int_ptr_array2 ptr_array2

APPLICATION_STRATEGY_FILE_NAME = \
	fme/fme typeinfer/typeinfer minigmp/gmp mergeablelist/sll_project convex_hull/point_array convex_hull/safeexec
  
QCP_DEMO_StrategyProof_FILES = \
	$(addsuffix _strategy_goal.v, $(QCP_DEMO_STRATEGY_FILE_NAME:%=QCP_demos_human/%)) \
	$(addsuffix _strategy_goal_check.v, $(QCP_DEMO_STRATEGY_FILE_NAME:%=QCP_demos_human/%)) \
	$(addsuffix _strategy_proof.v, $(QCP_DEMO_STRATEGY_FILE_NAME:%=QCP_demos_human/%))

QCP_DEMO_TUTORIAL_StrategyProof_FILES = \
	$(addsuffix _strategy_goal.v, $(QCP_DEMO_TUTORIAL_STRATEGY_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(addsuffix _strategy_goal_check.v, $(QCP_DEMO_TUTORIAL_STRATEGY_FILE_NAME:%=QCP_demos_tutorial/%)) \
	$(addsuffix _strategy_proof.v, $(QCP_DEMO_TUTORIAL_STRATEGY_FILE_NAME:%=QCP_demos_tutorial/%))

APPLICATION_StrategyProof_FILES = \
	$(addsuffix _strategy_goal.v, $(APPLICATION_STRATEGY_FILE_NAME:%=Applications_human/%)) \
	$(addsuffix _strategy_goal_check.v, $(APPLICATION_STRATEGY_FILE_NAME:%=Applications_human/%)) \
	$(addsuffix _strategy_proof.v, $(APPLICATION_STRATEGY_FILE_NAME:%=Applications_human/%))

LLM_FRIENDLY_CASES_StrategyProof_FILES = \
	$(addsuffix _strategy_goal.v, $(LLM_FRIENDLY_CASES_STRATEGY_FILE_NAME:%=QCP_demos_LLM/%)) \
	$(addsuffix _strategy_goal_check.v, $(LLM_FRIENDLY_CASES_STRATEGY_FILE_NAME:%=QCP_demos_LLM/%)) \
	$(addsuffix _strategy_proof.v, $(LLM_FRIENDLY_CASES_STRATEGY_FILE_NAME:%=QCP_demos_LLM/%))

StrategyProof_FILES = \
	$(QCP_DEMO_StrategyProof_FILES) \
	$(QCP_DEMO_TUTORIAL_StrategyProof_FILES) \
	$(APPLICATION_StrategyProof_FILES) \
	$(LLM_FRIENDLY_CASES_StrategyProof_FILES) \

LiteOS_Lib_FILES = \
	dll sortlink tick_backup glob_vars_and_defs tick Los_Verify_State_def

LiteOS_Strategy_FILE_NAME = \
	los_sortlink


LiteOS_FILE = \
	$(LiteOS_Lib_FILES:%=Applications_human/LiteOS/lib/%.v) \
	$(LiteOS_Strategy_FILE_NAME:%=Applications_human/%_strategy_goal.v) \
	$(LiteOS_Strategy_FILE_NAME:%=Applications_human/%_strategy_goal_check.v) \
	$(LiteOS_Strategy_FILE_NAME:%=Applications_human/%_strategy_proof.v) \

EXAMPLE = \
	$(Flocq_FILES:%.v=flocq/src/%.v) \
	$(SL_FILES:%.v=SeparationLogic/%.v) \
	$(FIXPOINT_FILES:%.v=fixedpoints/%.v) \
	$(Common_FILES:%.v=Common/%.v) \
	$(MONAD_FILES:%.v=%.v) \
	$(ListLib_FILES:%.v=listlib/%.v) \
	$(MaxMinLib_FILES:%.v=MaxMinLib/%.v) \
	$(GraphLib_FILES:%.v=GraphLib/%.v) \
	$(RecordUpdate_FILES:%.v=coq-record-update/%.v) \
	$(TraceLib_FILES:%.v=tracelib/%.v) \
	$(Algorithms_FILES:%.v=algorithms/%.v) \
	$(SumLib_FILES:%.v=SumLib/%.v) \
	$(StdLib_FILES:%.v=stdlib/%.v) \
	$(Sets_FILES:%.v=sets/%.v) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.v) \
	$(Examples_FILES:%.v=examples/%.v) \
	$(StrategyProof_FILES:%.v=examples/%.v) \
	$(Compcertlib_FILES:%.v=compcert_lib/%.v) \
	$(Auxlibs_FILES:%.v=auxlibs/%.v) \
	$(LiteOS_FILE:%.v=examples/%.v) \

FLOCQ_EXAMPLE = \
	$(Flocq_FILES:%.v=flocq/src/%.v)

CORE_PROJECT_EXAMPLE = \
	$(SL_FILES:%.v=SeparationLogic/%.v) \
	$(FIXPOINT_FILES:%.v=fixedpoints/%.v) \
	$(Common_FILES:%.v=Common/%.v) \
	$(MONAD_FILES:%.v=%.v) \
	$(ListLib_FILES:%.v=listlib/%.v) \
	$(MaxMinLib_FILES:%.v=MaxMinLib/%.v) \
	$(GraphLib_FILES:%.v=GraphLib/%.v) \
	$(RecordUpdate_FILES:%.v=coq-record-update/%.v) \
	$(TraceLib_FILES:%.v=tracelib/%.v) \
	$(Algorithms_FILES:%.v=algorithms/%.v) \
	$(SumLib_FILES:%.v=SumLib/%.v) \
	$(StdLib_FILES:%.v=stdlib/%.v) \
	$(Sets_FILES:%.v=sets/%.v) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.v) \
	$(Compcertlib_FILES:%.v=compcert_lib/%.v) \
	$(Auxlibs_FILES:%.v=auxlibs/%.v) \

CORE_EXAMPLE = \
	$(FLOCQ_EXAMPLE) \
	$(CORE_PROJECT_EXAMPLE)

EXAMPLE_ONLY = \
	$(APPLICATION_EXAMPLE_ONLY) \
	$(QCP_DEMO_EXAMPLE_ONLY) \
	$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY) \
	$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY) \
	$(LLM_BENCH_EXAMPLE_ONLY) \

CORE_OUTPUTS = \
	$(CORE_EXAMPLE:%.v=%.glob) \
	$(CORE_EXAMPLE:%.v=%.vo) \
	$(CORE_EXAMPLE:%.v=%.vok) \
	$(CORE_EXAMPLE:%.v=%.vos) \

UNIFY_OUTPUTS = \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.glob) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.vo) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.vok) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.vos) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/.*.aux) \

APPLICATION_OUTPUTS = \
	$(APPLICATION_EXAMPLE_ONLY:%.v=%.glob) \
	$(APPLICATION_EXAMPLE_ONLY:%.v=%.vo) \
	$(APPLICATION_EXAMPLE_ONLY:%.v=%.vok) \
	$(APPLICATION_EXAMPLE_ONLY:%.v=%.vos) \

QCP_DEMO_OUTPUTS = \
	$(QCP_DEMO_EXAMPLE_ONLY:%.v=%.glob) \
	$(QCP_DEMO_EXAMPLE_ONLY:%.v=%.vo) \
	$(QCP_DEMO_EXAMPLE_ONLY:%.v=%.vok) \
	$(QCP_DEMO_EXAMPLE_ONLY:%.v=%.vos) \

QCP_DEMO_TUTORIAL_FEATURE_OUTPUTS = \
	$(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_ONLY:%.v=%.glob) \
	$(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_ONLY:%.v=%.vo) \
	$(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_ONLY:%.v=%.vok) \
	$(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_ONLY:%.v=%.vos) \

QCP_DEMO_TUTORIAL_OUTPUTS = \
	$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY:%.v=%.glob) \
	$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY:%.v=%.vo) \
	$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY:%.v=%.vok) \
	$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY:%.v=%.vos) \

LLM_FRIENDLY_CASES_OUTPUTS = \
	$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY:%.v=%.glob) \
	$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY:%.v=%.vo) \
	$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY:%.v=%.vok) \
	$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY:%.v=%.vos) \

LLM_BENCH_OUTPUTS = \
	$(LLM_BENCH_EXAMPLE_ONLY:%.v=%.glob) \
	$(LLM_BENCH_EXAMPLE_ONLY:%.v=%.vo) \
	$(LLM_BENCH_EXAMPLE_ONLY:%.v=%.vok) \
	$(LLM_BENCH_EXAMPLE_ONLY:%.v=%.vos) \

EXAMPLE_OUTPUTS = \
	$(EXAMPLE_ONLY:%.v=%.glob) \
	$(EXAMPLE_ONLY:%.v=%.vo) \
	$(EXAMPLE_ONLY:%.v=%.vok) \
	$(EXAMPLE_ONLY:%.v=%.vos) \

CONVEX_HULL_EXAMPLE_FILES = \
	examples/Applications_human/convex_hull/Geo_Vec.v \
	examples/Applications_human/convex_hull/Geo_Point_Primitives.v \
	examples/Applications_human/convex_hull/Convexity.v \
	examples/Applications_human/convex_hull/Maximality.v \
	examples/Applications_human/convex_hull/Geo_Point.v \
	examples/Applications_human/convex_hull/Geo_Predicates.v \
	examples/Applications_human/convex_hull/Point_Order.v \
	examples/Applications_human/convex_hull/Point_Array_Specs.v \
	examples/Applications_human/convex_hull/Graham_Scan.v \
	examples/Applications_human/convex_hull/Graham_Scan_M.v \
	examples/Applications_human/convex_hull/Andrew_Monotone_Chain.v \
	examples/Applications_human/convex_hull/Andrew_Monotone_Chain_M.v \
	examples/Applications_human/convex_hull/Reversal.v \
	examples/Applications_human/convex_hull/ConvexHull.v \
	examples/Applications_human/convex_hull/convex_hull_lib.v \
	examples/Applications_human/convex_hull/point_array_strategy_goal.v \
	examples/Applications_human/convex_hull/point_array_strategy_proof.v \
	examples/Applications_human/convex_hull/safeexec_strategy_goal.v \
	examples/Applications_human/convex_hull/safeexec_strategy_proof.v \
	examples/Applications_human/convex_hull/graham_scan_goal.v \
	examples/Applications_human/convex_hull/graham_scan_proof_auto.v \
	examples/Applications_human/convex_hull/graham_scan_proof_manual.v \
	examples/Applications_human/convex_hull/graham_scan_goal_check.v \
	examples/Applications_human/convex_hull/graham_scan_dedup_goal.v \
	examples/Applications_human/convex_hull/graham_scan_dedup_proof_auto.v \
	examples/Applications_human/convex_hull/graham_scan_dedup_proof_manual.v \
	examples/Applications_human/convex_hull/graham_scan_dedup_goal_check.v \
	examples/Applications_human/convex_hull/andrew_monotone_chain_goal.v \
	examples/Applications_human/convex_hull/andrew_monotone_chain_proof_auto.v \
	examples/Applications_human/convex_hull/andrew_monotone_chain_proof_manual.v \
	examples/Applications_human/convex_hull/andrew_monotone_chain_goal_check.v

DEPEND_TARGETS := depend depend-core depend-examples depend-examples-applications depend-examples-qcp-democases depend-examples-qcp-demo-feature-cases depend-examples-qcp-demo-tutorial depend-examples-llm-friendly-cases depend-examples-llm-bench clean clean-core clean-examples clean-examples-applications clean-examples-qcp-democases clean-examples-qcp-demo-feature-cases clean-examples-qcp-demo-tutorial clean-examples-llm-friendly-cases clean-examples-llm-bench clean-deps

$(EXAMPLE:%.v=%.vo): %.vo: %.v
ifeq ($(TIMING),)
	$(call print_line,COQC $*.v)
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v
else
	$(call timeit,COQC $*.v,$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v)
endif

	

all: \
	$(EXAMPLE:%.v=%.vo) \

convex-hull: \
	examples/Applications_human/convex_hull/graham_scan_goal_check.vo \
	examples/Applications_human/convex_hull/graham_scan_dedup_goal_check.vo \
	examples/Applications_human/convex_hull/andrew_monotone_chain_goal_check.vo

core: \
	$(CORE_EXAMPLE:%.v=%.vo) \

coq-record-update: \
	$(RecordUpdate_FILES:%.v=coq-record-update/%.vo)

tracelib: \
	$(TraceLib_FILES:%.v=tracelib/%.vo)

algorithms: \
	$(Algorithms_FILES:%.v=algorithms/%.vo)

examples : \
	$(EXAMPLE:%.v=%.vo) 

examples-applications: \
	$(APPLICATION_EXAMPLE_ONLY:%.v=%.vo) \

examples-qcp-democases: \
	$(QCP_DEMO_EXAMPLE_ONLY:%.v=%.vo) \

examples-qcp-demo-feature-cases: \
	$(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_ONLY:%.v=%.vo) \

examples-qcp-demo-tutorial: \
	$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY:%.v=%.vo) \

examples-llm-friendly-cases: \
	$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY:%.v=%.vo) \

examples-llm-bench: \
	$(LLM_BENCH_EXAMPLE_ONLY:%.v=%.vo) \

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

.depend.convex_hull: Makefile $(CONVEX_HULL_EXAMPLE_FILES)
	@$(COQDEP) $(DEP_FLAG) $(CONVEX_HULL_EXAMPLE_FILES) > .depend.convex_hull.tmp
	@$(call MOVE_FILE,.depend.convex_hull.tmp,.depend.convex_hull)

depend:
	@$(call RUN_COQDEP,.coqdep.core.flocq.args.tmp,$(FLOCQ_EXAMPLE),.depend.core.flocq.tmp)
	@$(call MOVE_FILE,.depend.core.flocq.tmp,.depend.core.flocq)
	@$(call RUN_COQDEP,.coqdep.core.project.args.tmp,$(CORE_PROJECT_EXAMPLE),.depend.core.project.tmp)
	@$(call MOVE_FILE,.depend.core.project.tmp,.depend.core.project)
	@$(call CONCAT_FILES,.depend.core.flocq .depend.core.project,.depend.core.tmp)
	@$(call MOVE_FILE,.depend.core.tmp,.depend.core)
	@$(call RUN_COQDEP,.coqdep.examples.applications.args.tmp,$(APPLICATION_EXAMPLE_ONLY),.depend.examples.applications.tmp)
	@$(call MOVE_FILE,.depend.examples.applications.tmp,.depend.examples.applications)
	@$(call RUN_COQDEP,.coqdep.examples.qcp_democases.args.tmp,$(QCP_DEMO_EXAMPLE_ONLY),.depend.examples.qcp_democases.tmp)
	@$(call MOVE_FILE,.depend.examples.qcp_democases.tmp,.depend.examples.qcp_democases)
	@$(call RUN_COQDEP,.coqdep.examples.qcp_demo_tutorial.args.tmp,$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY),.depend.examples.qcp_demo_tutorial.tmp)
	@$(call MOVE_FILE,.depend.examples.qcp_demo_tutorial.tmp,.depend.examples.qcp_demo_tutorial)
	@$(call RUN_COQDEP,.coqdep.examples.llm_friendly_cases.args.tmp,$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY),.depend.examples.llm_friendly_cases.tmp)
	@$(call MOVE_FILE,.depend.examples.llm_friendly_cases.tmp,.depend.examples.llm_friendly_cases)
	@$(call RUN_COQDEP,.coqdep.examples.llm_bench.args.tmp,$(LLM_BENCH_EXAMPLE_ONLY),.depend.examples.llm_bench.tmp)
	@$(call MOVE_FILE,.depend.examples.llm_bench.tmp,.depend.examples.llm_bench)
	@$(call CONCAT_FILES,.depend.examples.applications .depend.examples.qcp_democases .depend.examples.qcp_demo_tutorial .depend.examples.llm_friendly_cases .depend.examples.llm_bench,.depend.examples.tmp)
	@$(call MOVE_FILE,.depend.examples.tmp,.depend.examples)
	@$(call CONCAT_FILES,.depend.core .depend.examples,.depend.tmp)
	@$(call MOVE_FILE,.depend.tmp,.depend)

depend-core:
	@$(call RUN_COQDEP,.coqdep.core.flocq.args.tmp,$(FLOCQ_EXAMPLE),.depend.core.flocq.tmp)
	@$(call MOVE_FILE,.depend.core.flocq.tmp,.depend.core.flocq)
	@$(call RUN_COQDEP,.coqdep.core.project.args.tmp,$(CORE_PROJECT_EXAMPLE),.depend.core.project.tmp)
	@$(call MOVE_FILE,.depend.core.project.tmp,.depend.core.project)
	@$(call CONCAT_FILES,.depend.core.flocq .depend.core.project,.depend.core.tmp)
	@$(call MOVE_FILE,.depend.core.tmp,.depend.core)

depend-examples:
	@$(call RUN_COQDEP,.coqdep.examples.applications.args.tmp,$(APPLICATION_EXAMPLE_ONLY),.depend.examples.applications.tmp)
	@$(call MOVE_FILE,.depend.examples.applications.tmp,.depend.examples.applications)
	@$(call RUN_COQDEP,.coqdep.examples.qcp_democases.args.tmp,$(QCP_DEMO_EXAMPLE_ONLY),.depend.examples.qcp_democases.tmp)
	@$(call MOVE_FILE,.depend.examples.qcp_democases.tmp,.depend.examples.qcp_democases)
	@$(call RUN_COQDEP,.coqdep.examples.qcp_demo_tutorial.args.tmp,$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY),.depend.examples.qcp_demo_tutorial.tmp)
	@$(call MOVE_FILE,.depend.examples.qcp_demo_tutorial.tmp,.depend.examples.qcp_demo_tutorial)
	@$(call RUN_COQDEP,.coqdep.examples.llm_friendly_cases.args.tmp,$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY),.depend.examples.llm_friendly_cases.tmp)
	@$(call MOVE_FILE,.depend.examples.llm_friendly_cases.tmp,.depend.examples.llm_friendly_cases)
	@$(call RUN_COQDEP,.coqdep.examples.llm_bench.args.tmp,$(LLM_BENCH_EXAMPLE_ONLY),.depend.examples.llm_bench.tmp)
	@$(call MOVE_FILE,.depend.examples.llm_bench.tmp,.depend.examples.llm_bench)
	@$(call CONCAT_FILES,.depend.examples.applications .depend.examples.qcp_democases .depend.examples.qcp_demo_tutorial .depend.examples.llm_friendly_cases .depend.examples.llm_bench,.depend.examples.tmp)
	@$(call MOVE_FILE,.depend.examples.tmp,.depend.examples)

depend-examples-applications:
	@$(call RUN_COQDEP,.coqdep.examples.applications.args.tmp,$(APPLICATION_EXAMPLE_ONLY),.depend.examples.applications.tmp)
	@$(call MOVE_FILE,.depend.examples.applications.tmp,.depend.examples.applications)

depend-examples-qcp-democases:
	@$(call RUN_COQDEP,.coqdep.examples.qcp_democases.args.tmp,$(QCP_DEMO_EXAMPLE_ONLY),.depend.examples.qcp_democases.tmp)
	@$(call MOVE_FILE,.depend.examples.qcp_democases.tmp,.depend.examples.qcp_democases)

depend-examples-qcp-demo-feature-cases:
	@$(call RUN_COQDEP,.coqdep.examples.qcp_demo_feature_cases.args.tmp,$(QCP_DEMO_TUTORIAL_FEATURE_EXAMPLE_ONLY),.depend.examples.qcp_demo_feature_cases.tmp)
	@$(call MOVE_FILE,.depend.examples.qcp_demo_feature_cases.tmp,.depend.examples.qcp_demo_feature_cases)

depend-examples-qcp-demo-tutorial:
	@$(call RUN_COQDEP,.coqdep.examples.qcp_demo_tutorial.args.tmp,$(QCP_DEMO_TUTORIAL_EXAMPLE_ONLY),.depend.examples.qcp_demo_tutorial.tmp)
	@$(call MOVE_FILE,.depend.examples.qcp_demo_tutorial.tmp,.depend.examples.qcp_demo_tutorial)

depend-examples-llm-friendly-cases:
	@$(call RUN_COQDEP,.coqdep.examples.llm_friendly_cases.args.tmp,$(LLM_FRIENDLY_CASES_EXAMPLE_ONLY),.depend.examples.llm_friendly_cases.tmp)
	@$(call MOVE_FILE,.depend.examples.llm_friendly_cases.tmp,.depend.examples.llm_friendly_cases)

depend-examples-llm-bench:
	@$(call RUN_COQDEP,.coqdep.examples.llm_bench.args.tmp,$(LLM_BENCH_EXAMPLE_ONLY),.depend.examples.llm_bench.tmp)
	@$(call MOVE_FILE,.depend.examples.llm_bench.tmp,.depend.examples.llm_bench)

.depend:
	@$(MAKE) depend

clean:
	@$(MAKE) clean-core
	@$(MAKE) clean-examples
	@$(MAKE) clean-deps

clean-core:
	@$(call REMOVE_TREE_OUTPUTS,flocq/src Common auxlibs compcert_lib SeparationLogic sets StrategyLib fixedpoints MonadLib MaxMinLib GraphLib SumLib listlib coq-record-update tracelib algorithms)
	@$(call REMOVE_FILES,$(UNIFY_OUTPUTS))
	@$(call REMOVE_FILES,coq-record-update/.depend coq-record-update/.Makefile.coq.d tracelib/.depend algorithms/.depend)
	@$(call REMOVE_FILES,.depend.core.flocq .depend.core.flocq.tmp .depend.core.project .depend.core.project.tmp .depend.core .depend.core.tmp .depend.tmp .depend)

clean-examples:
	@$(call REMOVE_TREE_OUTPUTS,examples)
	@$(call REMOVE_FILES,.depend.examples.applications .depend.examples.applications.tmp .depend.examples.qcp_democases .depend.examples.qcp_democases.tmp .depend.examples.qcp_demo_feature_cases .depend.examples.qcp_demo_feature_cases.tmp .depend.examples.qcp_demo_tutorial .depend.examples.qcp_demo_tutorial.tmp .depend.examples.llm_friendly_cases .depend.examples.llm_friendly_cases.tmp .depend.examples.llm_bench .depend.examples.llm_bench.tmp .depend.examples .depend.examples.tmp .depend.tmp .depend)

clean-examples-applications:
	@$(call REMOVE_TREE_OUTPUTS,examples/Applications_human)
	@$(call REMOVE_FILES,.depend.examples.applications .depend.examples.applications.tmp .depend.examples .depend.examples.tmp .depend.tmp .depend)

clean-examples-qcp-democases:
	@$(call REMOVE_TREE_OUTPUTS,examples/QCP_demos_human)
	@$(call REMOVE_FILES,.depend.examples.qcp_democases .depend.examples.qcp_democases.tmp .depend.examples .depend.examples.tmp .depend.tmp .depend)

clean-examples-qcp-demo-feature-cases:
	@$(call REMOVE_FILES,$(QCP_DEMO_TUTORIAL_FEATURE_OUTPUTS))
	@$(call REMOVE_FILES,.depend.examples.qcp_demo_feature_cases .depend.examples.qcp_demo_feature_cases.tmp .depend.examples .depend.examples.tmp .depend.tmp .depend)

clean-examples-qcp-demo-tutorial:
	@$(call REMOVE_TREE_OUTPUTS,examples/QCP_demos_tutorial)
	@$(call REMOVE_FILES,.depend.examples.qcp_demo_tutorial .depend.examples.qcp_demo_tutorial.tmp .depend.examples .depend.examples.tmp .depend.tmp .depend)

clean-examples-llm-friendly-cases:
	@$(call REMOVE_TREE_OUTPUTS,examples/QCP_demos_LLM)
	@$(call REMOVE_FILES,.depend.examples.llm_friendly_cases .depend.examples.llm_friendly_cases.tmp .depend.examples .depend.examples.tmp .depend.tmp .depend)

clean-examples-llm-bench:
	@$(call REMOVE_TREE_OUTPUTS,examples/LLM_bench)
	@$(call REMOVE_FILES,.depend.examples.llm_bench .depend.examples.llm_bench.tmp .depend.examples .depend.examples.tmp .depend.tmp .depend)

clean-deps:
	@$(call REMOVE_FILES,$(COQDEP_ARG_FILES))
	@$(call REMOVE_FILES,.depend.convex_hull .depend.convex_hull.tmp .depend.core.flocq .depend.core.flocq.tmp .depend.core.project .depend.core.project.tmp .depend.core .depend.core.tmp .depend.examples.applications .depend.examples.applications.tmp .depend.examples.qcp_democases .depend.examples.qcp_democases.tmp .depend.examples.qcp_demo_feature_cases .depend.examples.qcp_demo_feature_cases.tmp .depend.examples.qcp_demo_tutorial .depend.examples.qcp_demo_tutorial.tmp .depend.examples.llm_friendly_cases .depend.examples.llm_friendly_cases.tmp .depend.examples.llm_bench .depend.examples.llm_bench.tmp .depend.examples .depend.examples.tmp .depend.tmp .depend)

.PHONY: clean clean-core clean-examples clean-examples-applications clean-examples-qcp-democases clean-examples-qcp-demo-feature-cases clean-examples-qcp-demo-tutorial clean-examples-llm-friendly-cases clean-examples-llm-bench clean-deps depend depend-core depend-examples depend-examples-applications depend-examples-qcp-democases depend-examples-qcp-demo-feature-cases depend-examples-qcp-demo-tutorial depend-examples-llm-friendly-cases depend-examples-llm-bench core coq-record-update tracelib algorithms convex-hull examples-applications examples-qcp-democases examples-qcp-demo-feature-cases examples-qcp-demo-tutorial examples-llm-friendly-cases examples-llm-bench
.DEFAULT_GOAL := all

ifeq ($(strip $(MAKECMDGOALS)),)
-include .depend
else ifneq ($(filter convex-hull,$(MAKECMDGOALS)),)
-include .depend
-include .depend.convex_hull
else ifeq ($(filter $(DEPEND_TARGETS),$(MAKECMDGOALS)),)
-include .depend.core
-include .depend.examples.applications
-include .depend.examples.qcp_democases
-include .depend.examples.qcp_demo_feature_cases
-include .depend.examples.qcp_demo_tutorial
-include .depend.examples.llm_friendly_cases
-include .depend.examples.llm_bench
-include .depend.examples
-include .depend
endif
