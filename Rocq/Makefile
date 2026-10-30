# GNU Make >= 4.0 (the file function keeps long lists out of cmd.exe).
.DEFAULT_GOAL := core
.DELETE_ON_ERROR:
.SUFFIXES:
ifneq ($(filter 0.% 1.% 2.% 3.%,$(MAKE_VERSION)),)
$(error GNU Make 4.0 or newer is required)
endif

COQBIN ?=
CURRENT_DIR = .
-include CONFIGURE
COQC = $(COQBIN)coqc
COQDEP = $(COQBIN)coqdep
COQ_FLAG = -R flocq/src Flocq -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R stdlib SimpleC.StdLib -R Verification SimpleC.Verification -R StrategyLib SimpleC.StrategyLib -R Common SimpleC.Common -R CoreLang SimpleC.CoreLang -R cdcllib CDCLLib -R fixedpoints FP -R MonadLib MonadLib -R listlib ListLib -R MaxMinLib MaxMinLib -R GraphLib GraphLib -R SumLib SumLib -R tracelib TraceLib -R coq-record-update/src RecordUpdate -Q algorithms Algorithms
DEP_FLAG = $(COQ_FLAG)

# Mirror the coq.theory roots and include_subdirs settings in dune.
RECURSIVE_ROOTS = Common cdcllib auxlibs compcert_lib sets unifysl \
  StrategyLib fixedpoints MonadLib MaxMinLib GraphLib SumLib listlib stdlib Verification \
  tracelib algorithms
FLAT_ROOTS = CoreLang SeparationLogic coq-record-update/src
EXAMPLE_ROOTS = examples/Applications_human examples/LLM_bench \
  examples/QCP_demos_LLM examples/QCP_demos_human examples/QCP_demos_tutorial
CORE_ROOTS = $(RECURSIVE_ROOTS) $(FLAT_ROOTS) flocq/src

# Keep these exclusions in sync with (dirs ...) and (modules ...) in dune.
# Do not descend into disabled directories, hidden directories or _build.
EXCLUDED_DIRS = unifysl/Examples/ \
  unifysl/ExportSolvers/SepApply/ unifysl/ExportSolvers/SepCancel/ \
  $(addprefix unifysl/LogicGenerator/,demo/ demo424/ demo6/ demo7/ demo931/ demo933/ demo_osa/ demoq/) \
  examples/QCP_demos_LLM/uint256/
EXCLUDED_FILES = \
  GraphLib/directed/dfstree_dfn.v \
  GraphLib/undirected/bigraph.v \
  MonadLib/MonadTest.v \
  sets/Test.v \
  unifysl/HoareLogic/UnusedProofs.v \
  unifysl/LogicGenerator/Generate.v \
  unifysl/LogicGenerator/GenerateBeta.v \
  unifysl/LogicGenerator/GenerateGenerate.v \
  unifysl/QuantifierLogic/ProofTheory/IntuitionisticDerivedRules.v \
  unifysl/PropositionalLogic/DeepEmbedded/Deep.v \
  unifysl/PropositionalLogic/DeepEmbedded/Solver.v \
  unifysl/PropositionalLogic/DeepEmbedded/configuration_Mendelson.v \
  unifysl/PropositionalLogic/DeepEmbedded/implementation_Mendelson.v \
  unifysl/SeparationLogic/DeepEmbedded/MinimumSeparationLogic.v \
  unifysl/SeparationLogic/DeepEmbedded/MinimumSeparationLogic_Config.v \
  unifysl/ModalLogic/ProofTheory/ClassicalDerivedRules.v \
  unifysl/ModalLogic/ShallowEmbedded/MonoPredicateModalLogic.v \
  unifysl/ModalLogic/Sound/Sound_Flat.v \
  unifysl/Extensions/Semantics/ModalSeparation.v \
  unifysl/Extensions/ShallowEmbedded/MonoPredicateStable.v \
  unifysl/Extensions/Sound/StableSound.v \
  unifysl/temp.v \
  examples/QCP_demos_LLM/sll_data_strategy_goal.v \
  examples/QCP_demos_LLM/sll_data_strategy_goal_check.v \
  examples/QCP_demos_LLM/sll_data_strategy_proof.v \
  examples/QCP_demos_LLM/dll_data_strategy_goal.v \
  examples/QCP_demos_LLM/dll_data_strategy_goal_check.v \
  examples/QCP_demos_LLM/dll_data_strategy_proof.v

# Flocq's dune file uses an explicit module whitelist.
FLOCQ_FILES = \
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

# Built-in functions only; use / separators and relative paths without spaces.
# Native Windows wildcard may also return files for */; keep only entries
# ending in /, otherwise recursion can repeatedly visit the same file.
source_dirs = $(filter-out $(EXCLUDED_DIRS),$(filter-out $(1)_%/,$(filter %/,$(wildcard $(1)*/))))
find_coq = $(wildcard $(1)*.v) $(foreach d,$(call source_dirs,$(1)),$(call find_coq,$(d)))
CORE_FILES := $(sort $(filter-out $(EXCLUDED_FILES),\
  $(foreach d,$(RECURSIVE_ROOTS),$(call find_coq,$(d)/)) \
  $(foreach d,$(FLAT_ROOTS),$(wildcard $(d)/*.v)) \
  $(addprefix flocq/src/,$(FLOCQ_FILES))))
EXAMPLE_FILES := $(sort $(filter-out $(EXCLUDED_FILES),\
  $(foreach d,$(EXAMPLE_ROOTS),$(call find_coq,$(d)/))))
ALL_FILES := $(CORE_FILES) $(EXAMPLE_FILES)

# Public build groups. coqdep supplies all transitive and cross-group edges.
GROUPS = core examples examples-applications examples-qcp-democases \
  examples-qcp-demo-tutorial examples-qcp-demo-feature-cases \
  examples-llm-friendly-cases examples-llm-bench coq-record-update tracelib algorithms convex-hull
core_FILES := $(CORE_FILES)
examples_FILES := $(EXAMPLE_FILES)
examples-applications_FILES := $(filter examples/Applications_human/%,$(EXAMPLE_FILES))
examples-qcp-democases_FILES := $(filter examples/QCP_demos_human/%,$(EXAMPLE_FILES))
examples-qcp-demo-tutorial_FILES := $(filter examples/QCP_demos_tutorial/%,$(EXAMPLE_FILES))
examples-qcp-demo-feature-cases_FILES := $(filter $(addprefix examples/QCP_demos_tutorial/,branch_destruct% branch_join_private_condition% multiinv_examples%),$(EXAMPLE_FILES))
examples-llm-friendly-cases_FILES := $(filter examples/QCP_demos_LLM/%,$(EXAMPLE_FILES))
examples-llm-bench_FILES := $(filter examples/LLM_bench/%,$(EXAMPLE_FILES))
coq-record-update_FILES := $(filter coq-record-update/src/%,$(CORE_FILES))
tracelib_FILES := $(filter tracelib/%,$(CORE_FILES))
algorithms_FILES := $(filter algorithms/%,$(CORE_FILES))
convex-hull_FILES := $(filter examples/Applications_human/convex_hull/%,$(EXAMPLE_FILES))

.PHONY: all $(GROUPS) list-sources
all: $(ALL_FILES:.v=.vo)
$(foreach group,$(GROUPS),$(eval $(group): $($(group)_FILES:.v=.vo)))
list-sources:
	$(foreach source,$(ALL_FILES),$(info $(source)))

# Select recipes by the Make binary, not OS (also Windows_NT on Cygwin/MSYS).
USE_WINDOWS_COMMANDS := $(if $(or $(filter Windows32,$(MAKE_HOST)),$(findstring mingw,$(MAKE_HOST))),yes)
empty :=
space := $(empty) $(empty)
comma := ,
powershell_list = $(subst $(space),$(comma),$(strip $(foreach item,$(1),'$(item)')))
ifeq ($(USE_WINDOWS_COMMANDS),yes)
SHELL := cmd.exe
.SHELLFLAGS := /d /s /c
print_line = @echo $(1)
# Keep PowerShell logic in a script; only serialize the path array here.
clean_windows = powershell -NoProfile -ExecutionPolicy Bypass -Command "& 'scripts/clean.ps1' $(2) -Paths $(call powershell_list,$(1))"
REMOVE_FILES = $(call clean_windows,$(1))
REMOVE_TREE_OUTPUTS = $(call clean_windows,$(1),-Recurse)
define RUN_COQDEP
"$(COQDEP)" -f .coqdep.args.tmp >> .depend.tmp && move /y .depend.tmp .depend >nul
endef
else
print_line = @printf '%s\n' '$(1)'
REMOVE_FILES = rm -f $(1)
REMOVE_TREE_OUTPUTS = find $(1) -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '.*.aux' -o -name '.lia.cache' -o -name '.nia.cache' -o -name '.nra.cache' -o -name '.csdp.cache' \) -delete
RUN_COQDEP = "$(COQDEP)" -f .coqdep.args.tmp >> .depend.tmp && mv -f .depend.tmp .depend
endif

# Match the local warning override in coq-record-update/src/dune.
$(filter coq-record-update/src/%,$(CORE_FILES:.v=.vo)): private EXTRA_COQ_FLAGS = -w -undeclared-scope
$(ALL_FILES:.v=.vo): %.vo: %.v
	$(call print_line,COQC $<)
ifeq ($(TIMING),)
	@"$(COQC)" -q $(COQ_FLAG) $(EXTRA_COQ_FLAGS) $(CURRENT_DIR)/$<
else ifeq ($(USE_WINDOWS_COMMANDS),yes)
	@"$(COQC)" -q -time $(COQ_FLAG) $(EXTRA_COQ_FLAGS) $(CURRENT_DIR)/$<
else
	@t0=`date +%s`; "$(COQC)" -q $(COQ_FLAG) $(EXTRA_COQ_FLAGS) $(CURRENT_DIR)/$<; status=$$?; t1=`date +%s`; echo "$$((t1 - t0)) s"; exit $$status
endif

# One dependency graph avoids stale or overlapping per-group caches.
# Snapshot the source list AND flags in the atomic .depend output: additions,
# deletions and load-path changes invalidate it without scanning timestamps of
# artifact-containing directories. Source edits are ordinary prerequisites.
DEPEND_INPUTS := $(strip $(DEP_FLAG) $(ALL_FILES))
DEPEND_TARGETS := depend $(addprefix depend-,$(GROUPS))
CLEAN_TARGETS := clean clean-deps clean-tmp $(addprefix clean-,$(GROUPS))
.PHONY: $(DEPEND_TARGETS) $(CLEAN_TARGETS) FORCE
FORCE:

# Never regenerate dependencies just to clean or list sources. For mixed
# maintenance/build requests the graph is still required.
BUILD_GOALS := $(filter-out $(CLEAN_TARGETS) list-sources,$(or $(MAKECMDGOALS),core))
ifneq ($(strip $(BUILD_GOALS)),)
include .depend
ifneq ($(DEPEND_INPUTS),$(SAVED_DEPEND_INPUTS))
.depend: FORCE
endif
endif

.depend: Makefile $(wildcard CONFIGURE) $(ALL_FILES)
	$(file >.coqdep.args.tmp,$(DEPEND_INPUTS))
	$(file >.depend.tmp,SAVED_DEPEND_INPUTS := $(DEPEND_INPUTS))
	$(call print_line,COQDEP)
	@$(RUN_COQDEP)
	@$(call REMOVE_FILES,.coqdep.args.tmp)

# Compatibility aliases; explicit depend requests force a refresh once.
ifeq ($(MAKE_RESTARTS),)
ifneq ($(filter $(DEPEND_TARGETS),$(MAKECMDGOALS)),)
.depend: FORCE
endif
endif
$(DEPEND_TARGETS): .depend

# Clean only Make outputs; dune's _build tree is untouched.
clean: clean-core clean-examples clean-deps
clean-core:
	@$(call REMOVE_TREE_OUTPUTS,$(CORE_ROOTS))
clean-examples:
	@$(call REMOVE_TREE_OUTPUTS,examples)

# Use directories for normal groups, so deleted sources leave no stale output.
examples-applications_DIR = examples/Applications_human
examples-qcp-democases_DIR = examples/QCP_demos_human
examples-qcp-demo-tutorial_DIR = examples/QCP_demos_tutorial
examples-llm-friendly-cases_DIR = examples/QCP_demos_LLM
examples-llm-bench_DIR = examples/LLM_bench
coq-record-update_DIR = coq-record-update/src
tracelib_DIR = tracelib
algorithms_DIR = algorithms
convex-hull_DIR = examples/Applications_human/convex_hull
TREE_GROUPS = $(filter-out core examples examples-qcp-demo-feature-cases,$(GROUPS))
$(addprefix clean-,$(TREE_GROUPS)):
	@$(call REMOVE_TREE_OUTPUTS,$($(patsubst clean-%,%,$@)_DIR))
clean-examples-qcp-demo-feature-cases:
	@$(call REMOVE_FILES,$(foreach f,$(examples-qcp-demo-feature-cases_FILES),$(f:.v=.vo) $(f:.v=.vos) $(f:.v=.vok) $(f:.v=.glob) $(dir $(f)).$(notdir $(f:.v=.aux))))
clean-deps:
	@$(call REMOVE_FILES,$(sort .depend $(wildcard .depend.* .coqdep.*.tmp)))
clean-tmp:
	@$(call REMOVE_FILES,$(sort .depend.tmp .coqdep.args.tmp $(wildcard .depend.*.tmp .coqdep.*.tmp)))
