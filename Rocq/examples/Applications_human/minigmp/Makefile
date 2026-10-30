# Independent non-SumLib MiniGMP. Run make from this directory.
REPO_ROOT := ../../../..
PROJECT := Rocq/examples/Applications_human/minigmp
JOBS ?= 1
ifeq ($(OS),Windows_NT)
SPEC_CHECK ?= bin/windows/spec-check.exe
DUNE := dune.cmd
SYMEXEC := win-binary/symexec.exe
STRATEGY_CHECK := win-binary/StrategyCheck.exe
else
SPEC_CHECK ?= $(if $(filter Darwin,$(shell uname -s)),bin/macos-$(shell uname -m),bin/linux)/spec-check
DUNE := dune
SYMEXEC := linux-binary/symexec
STRATEGY_CHECK := linux-binary/StrategyCheck
endif
SOURCE := QCP_examples/Applications_human/minigmp
LOGIC := SimpleC.EE.Applications_human.minigmp
COMMON := -I$(SOURCE)/ -IQCP_examples/Applications_human/ -IQCP_examples/QCP_demos_human/ -slp $(SOURCE)/ $(LOGIC) -slp QCP_examples/Applications_human/ SimpleC.EE.Applications_human -slp QCP_examples/QCP_demos_human/ SimpleC.EE.QCP_demos_human
TARGETS := $(addprefix $(PROJECT)/,$(notdir $(wildcard *.v)))

.PHONY: all check generate generate-strategies generate-cases
all:
	cd $(REPO_ROOT) && $(DUNE) build -j$(JOBS) $(TARGETS:.v=.vo)

check:
	cd $(REPO_ROOT) && "$(SPEC_CHECK)" $(SOURCE) -I QCP_examples/Applications_human --given-contracts $(SOURCE)/given-contracts.tsv
	$(MAKE) all

# Regeneration replaces generated manuals; normal builds only compile them.
generate: generate-strategies generate-cases

generate-strategies:
	cd $(REPO_ROOT) && $(STRATEGY_CHECK) --coq-output-dir=$(PROJECT)/ --coq-logic-path=$(LOGIC) $(COMMON) --input-file=$(SOURCE)/gmp.strategies --no-exec-info

generate-cases: generate-gmp generate-mpz_neg

generate-%:
	cd $(REPO_ROOT) && $(SYMEXEC) --goal-file=$(PROJECT)/$*_goal.v --proof-auto-file=$(PROJECT)/$*_proof_auto.v --proof-manual-file=$(PROJECT)/$*_proof_manual.v --coq-logic-path=$(LOGIC) $(COMMON) --input-file=$(SOURCE)/$*.c --no-exec-info
