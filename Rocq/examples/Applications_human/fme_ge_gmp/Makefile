CURRENT_DIR=.
SL_DIR=../../..
REPO_ROOT=../../../..
CASE_DIR=examples/Applications_human/fme_ge_gmp
C_CASE_DIR=QCP_examples/Applications_human/fme_ge_gmp
FORMAL_REPO_DIR=Rocq/$(CASE_DIR)
LOGIC_ROOT=SimpleC.EE.Applications_human.fme_ge_gmp
COQBIN ?=
SUF ?=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)
SYMEXEC=linux-binary/symexec
STRATEGY_CHECK=linux-binary/StrategyCheck

COQ_FLAG = \
	-R flocq/src Flocq \
	-R SeparationLogic SimpleC.SL \
	-R unifysl Logic \
	-R sets SetsClass \
	-R compcert_lib compcert.lib \
	-R auxlibs AUXLib \
	-R examples SimpleC.EE \
	-R stdlib SimpleC.StdLib \
	-R StrategyLib SimpleC.StrategyLib \
	-R Common SimpleC.Common \
	-R fixedpoints FP \
	-R MonadLib MonadLib \
	-R listlib ListLib \
	-R MaxMinLib MaxMinLib \
	-R GraphLib GraphLib \
	-R SumLib SumLib \
	-R tracelib TraceLib \
	-R coq-record-update/src RecordUpdate \
	-Q algorithms Algorithms

DEP_FLAG = $(COQ_FLAG)

QCP_COMMON_ARGS = \
	-IQCP_examples/Applications_human/ \
	-slp QCP_examples/Applications_human/ SimpleC.EE.Applications_human

QCP_GMP_SLP = \
	-slp $(C_CASE_DIR)/gmp/ $(LOGIC_ROOT).gmp

QCP_FME_SLP = \
	$(QCP_GMP_SLP) \
	-slp $(C_CASE_DIR)/fme/ $(LOGIC_ROOT).fme

QCP_GE_SLP = \
	$(QCP_GMP_SLP) \
	-slp $(C_CASE_DIR)/ge/ $(LOGIC_ROOT).ge

FME_REL_FILE = $(SL_DIR)/MonadLib/Examples/fme_rel.v
SL_FME_REL_FILE = MonadLib/Examples/fme_rel.v
FME_REL_VO = $(FME_REL_FILE:%.v=%.vo)

GMP_LIB_FILES = \
	gmp/GmpAux.v \
	gmp/GmpNumber.v \
	gmp/GmpMul.v \
	gmp/GmpDiv.v \
	gmp/GmpGcd.v \
	gmp/gmp_lib.v

FME_LIB_FILES = \
	fme/fme_gmp_lib.v

GE_LIB_FILES = \
	ge/GeGmpMatrix.v \
	ge/GeGmpMod.v \
	ge/GeGmpRank.v \
	ge/GeGmpInverse.v \
	ge/GeGmpArray.v \
	ge/ge_gmp_lib.v

LIB_FILES = $(GMP_LIB_FILES) $(FME_LIB_FILES) $(GE_LIB_FILES)

GMP_STRATEGY_NAMES = \
	gmp/gmp_strategy \
	gmp/gmp_optional_strategy \
	gmp/mpz_div_qr_strategy \
	gmp/mpz_tdiv_r_read0_strategy

FME_STRATEGY_NAMES = \
	fme/fme_gmp_strategy \
	fme/safeexec_fme_gmp_strategy

GE_STRATEGY_NAMES = \
	ge/ge_gmp_array_strategy

GMP_STRATEGY_SOURCES = gmp gmp_optional mpz_div_qr mpz_tdiv_r_read0
FME_STRATEGY_SOURCES = fme_gmp safeexec_fme_gmp
GE_STRATEGY_SOURCES = ge_gmp_array

GMP_C_CASE_NAMES = $(sort $(basename $(notdir $(wildcard $(REPO_ROOT)/$(C_CASE_DIR)/gmp/*.c))))
FME_C_CASE_NAMES = $(sort $(basename $(notdir $(wildcard $(REPO_ROOT)/$(C_CASE_DIR)/fme/*.c))))
GE_C_CASE_NAMES = $(sort $(basename $(notdir $(wildcard $(REPO_ROOT)/$(C_CASE_DIR)/ge/*.c))))

STRATEGY_NAMES = $(GMP_STRATEGY_NAMES) $(FME_STRATEGY_NAMES) $(GE_STRATEGY_NAMES)
STRATEGY_FILES = \
	$(foreach s,$(STRATEGY_NAMES),$(s)_goal.v $(s)_proof.v $(s)_goal_check.v)

GMP_CASE_GOALS = $(filter-out $(GMP_STRATEGY_NAMES:%=%_goal.v),$(wildcard gmp/*_goal.v))
FME_CASE_GOALS = $(filter-out $(FME_STRATEGY_NAMES:%=%_goal.v),$(wildcard fme/*_goal.v))
GE_CASE_GOALS = $(filter-out $(GE_STRATEGY_NAMES:%=%_goal.v),$(wildcard ge/*_goal.v))

GMP_CASE_NAMES = $(sort $(patsubst gmp/%_goal.v,%,$(GMP_CASE_GOALS)))
FME_CASE_NAMES = $(sort $(patsubst fme/%_goal.v,%,$(FME_CASE_GOALS)))
GE_CASE_NAMES = $(sort $(patsubst ge/%_goal.v,%,$(GE_CASE_GOALS)))

GMP_CASE_FILES = \
	$(foreach c,$(GMP_CASE_NAMES),gmp/$(c)_goal.v gmp/$(c)_proof_auto.v gmp/$(c)_proof_manual.v gmp/$(c)_goal_check.v)
FME_CASE_FILES = \
	$(foreach c,$(FME_CASE_NAMES),fme/$(c)_goal.v fme/$(c)_proof_auto.v fme/$(c)_proof_manual.v fme/$(c)_goal_check.v)
GE_CASE_FILES = \
	$(foreach c,$(GE_CASE_NAMES),ge/$(c)_goal.v ge/$(c)_proof_auto.v ge/$(c)_proof_manual.v ge/$(c)_goal_check.v)

CASE_FILES = $(GMP_CASE_FILES) $(FME_CASE_FILES) $(GE_CASE_FILES)
FILES = $(FME_REL_FILE) $(LIB_FILES) $(STRATEGY_FILES) $(CASE_FILES)
SL_FILES = $(SL_FME_REL_FILE) $(addprefix $(CASE_DIR)/,$(LIB_FILES) $(STRATEGY_FILES) $(CASE_FILES))

GMP_STRATEGY_VOS = $(foreach s,$(GMP_STRATEGY_NAMES),$(s)_goal.vo $(s)_proof.vo $(s)_goal_check.vo)
FME_STRATEGY_VOS = $(foreach s,$(FME_STRATEGY_NAMES),$(s)_goal.vo $(s)_proof.vo $(s)_goal_check.vo)
GE_STRATEGY_VOS = $(foreach s,$(GE_STRATEGY_NAMES),$(s)_goal.vo $(s)_proof.vo $(s)_goal_check.vo)

.PHONY: \
	all world libs strategies artifacts \
	generate generate-strategies generate-cases \
	generate-gmp generate-fme generate-ge \
	generate-gmp-strategies generate-fme-strategies generate-ge-strategies \
	generate-gmp-cases generate-fme-cases generate-ge-cases \
	gmp-libs fme-libs ge-libs \
	gmp-strategies fme-strategies ge-strategies \
	gmp-artifacts fme-artifacts ge-artifacts \
	case-gmp-% case-fme-% case-ge-% \
	list depend clean

all: world

world: libs strategies artifacts

generate: generate-strategies generate-cases

generate-strategies: generate-gmp-strategies generate-fme-strategies generate-ge-strategies

generate-cases: generate-gmp-cases generate-fme-cases generate-ge-cases

generate-gmp: generate-gmp-strategies generate-gmp-cases

generate-fme: generate-gmp-strategies generate-fme-strategies generate-fme-cases

generate-ge: generate-gmp-strategies generate-ge-strategies generate-ge-cases

generate-gmp-strategies: $(GMP_STRATEGY_SOURCES:%=qcp-strategy-gmp-%)

generate-fme-strategies: $(FME_STRATEGY_SOURCES:%=qcp-strategy-fme-%)

generate-ge-strategies: $(GE_STRATEGY_SOURCES:%=qcp-strategy-ge-%)

generate-gmp-cases: $(GMP_C_CASE_NAMES:%=qcp-case-gmp-%)

generate-fme-cases: $(FME_C_CASE_NAMES:%=qcp-case-fme-%)

generate-ge-cases: $(GE_C_CASE_NAMES:%=qcp-case-ge-%)

qcp-strategy-gmp-%:
	@cd $(REPO_ROOT) && $(STRATEGY_CHECK) \
		--strategy-folder-path=$(FORMAL_REPO_DIR)/gmp/ \
		--coq-logic-path=$(LOGIC_ROOT).gmp \
		$(QCP_GMP_SLP) $(QCP_COMMON_ARGS) \
		--input-file=$(C_CASE_DIR)/gmp/$*.strategies \
		--no-exec-info

qcp-strategy-fme-%:
	@cd $(REPO_ROOT) && $(STRATEGY_CHECK) \
		--strategy-folder-path=$(FORMAL_REPO_DIR)/fme/ \
		--coq-logic-path=$(LOGIC_ROOT).fme \
		$(QCP_FME_SLP) $(QCP_COMMON_ARGS) \
		--input-file=$(C_CASE_DIR)/fme/$*.strategies \
		--no-exec-info

qcp-strategy-ge-%:
	@cd $(REPO_ROOT) && $(STRATEGY_CHECK) \
		--strategy-folder-path=$(FORMAL_REPO_DIR)/ge/ \
		--coq-logic-path=$(LOGIC_ROOT).ge \
		$(QCP_GE_SLP) $(QCP_COMMON_ARGS) \
		--input-file=$(C_CASE_DIR)/ge/$*.strategies \
		--no-exec-info

qcp-case-gmp-%:
	@cd $(REPO_ROOT) && $(SYMEXEC) \
		--goal-file=$(FORMAL_REPO_DIR)/gmp/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/gmp/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/gmp/$*_proof_manual.v \
		--coq-logic-path=$(LOGIC_ROOT).gmp \
		$(QCP_GMP_SLP) $(QCP_COMMON_ARGS) \
		--input-file=$(C_CASE_DIR)/gmp/$*.c \
		--no-exec-info

qcp-case-fme-%:
	@cd $(REPO_ROOT) && $(SYMEXEC) \
		--goal-file=$(FORMAL_REPO_DIR)/fme/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/fme/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/fme/$*_proof_manual.v \
		--coq-logic-path=$(LOGIC_ROOT).fme \
		$(QCP_FME_SLP) $(QCP_COMMON_ARGS) \
		--input-file=$(C_CASE_DIR)/fme/$*.c \
		--no-exec-info

qcp-case-ge-%:
	@cd $(REPO_ROOT) && $(SYMEXEC) \
		--goal-file=$(FORMAL_REPO_DIR)/ge/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/ge/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/ge/$*_proof_manual.v \
		--coq-logic-path=$(LOGIC_ROOT).ge \
		$(QCP_GE_SLP) $(QCP_COMMON_ARGS) \
		--input-file=$(C_CASE_DIR)/ge/$*.c \
		--no-exec-info

libs: gmp-libs fme-libs ge-libs

strategies: gmp-strategies fme-strategies ge-strategies

artifacts: gmp-artifacts fme-artifacts ge-artifacts

gmp-libs: $(GMP_LIB_FILES:%.v=%.vo)

fme-libs: gmp-libs $(FME_REL_VO) $(FME_LIB_FILES:%.v=%.vo)

ge-libs: gmp-libs $(GE_LIB_FILES:%.v=%.vo)

gmp-strategies: gmp-libs $(GMP_STRATEGY_VOS)

fme-strategies: fme-libs $(FME_STRATEGY_VOS)

ge-strategies: ge-libs $(GE_STRATEGY_VOS)

gmp-artifacts: gmp-libs gmp-strategies $(GMP_CASE_FILES:%.v=%.vo)

fme-artifacts: fme-libs gmp-strategies fme-strategies $(FME_CASE_FILES:%.v=%.vo)

ge-artifacts: ge-libs gmp-strategies ge-strategies $(GE_CASE_FILES:%.v=%.vo)

case-gmp-%: gmp-libs gmp-strategies gmp/%_goal_check.vo
	@true

case-fme-%: fme-libs gmp-strategies fme-strategies fme/%_goal_check.vo
	@true

case-ge-%: ge-libs gmp-strategies ge-strategies ge/%_goal_check.vo
	@true

list:
	@printf 'gmp:\n'; printf '  %s\n' $(GMP_CASE_NAMES)
	@printf 'fme:\n'; printf '  %s\n' $(FME_CASE_NAMES)
	@printf 'ge:\n'; printf '  %s\n' $(GE_CASE_NAMES)

gmp/GmpAux.vo: gmp/GmpAux.v
gmp/GmpNumber.vo: gmp/GmpNumber.v gmp/GmpAux.vo
gmp/GmpMul.vo: gmp/GmpMul.v gmp/GmpNumber.vo
gmp/GmpDiv.vo: gmp/GmpDiv.v gmp/GmpNumber.vo
gmp/GmpGcd.vo: gmp/GmpGcd.v gmp/GmpNumber.vo
gmp/gmp_lib.vo: gmp/gmp_lib.v gmp/GmpMul.vo gmp/GmpDiv.vo gmp/GmpGcd.vo

$(FME_REL_VO): $(FME_REL_FILE)
	@echo COQC $(SL_FME_REL_FILE)
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(SL_FME_REL_FILE)

fme/fme_gmp_lib.vo: fme/fme_gmp_lib.v gmp/gmp_lib.vo $(FME_REL_VO)

ge/GeGmpMatrix.vo: ge/GeGmpMatrix.v gmp/gmp_lib.vo
ge/GeGmpMod.vo: ge/GeGmpMod.v ge/GeGmpMatrix.vo gmp/GmpMul.vo
ge/GeGmpRank.vo: ge/GeGmpRank.v ge/GeGmpMod.vo
ge/GeGmpInverse.vo: ge/GeGmpInverse.v ge/GeGmpMod.vo
ge/GeGmpArray.vo: ge/GeGmpArray.v ge/GeGmpMod.vo gmp/GmpNumber.vo gmp/GmpMul.vo
ge/ge_gmp_lib.vo: ge/ge_gmp_lib.v ge/GeGmpRank.vo ge/GeGmpInverse.vo ge/GeGmpArray.vo

gmp/%_strategy_goal.vo: gmp/%_strategy_goal.v gmp/gmp_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

fme/%_strategy_goal.vo: fme/%_strategy_goal.v fme/fme_gmp_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

ge/%_strategy_goal.vo: ge/%_strategy_goal.v ge/ge_gmp_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

%_strategy_proof.vo: %_strategy_proof.v %_strategy_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

%_strategy_goal_check.vo: %_strategy_goal_check.v %_strategy_proof.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

gmp/%_goal.vo: gmp/%_goal.v gmp/gmp_lib.vo $(GMP_STRATEGY_VOS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

fme/%_goal.vo: fme/%_goal.v fme/fme_gmp_lib.vo $(GMP_STRATEGY_VOS) $(FME_STRATEGY_VOS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

ge/%_goal.vo: ge/%_goal.v ge/ge_gmp_lib.vo $(GMP_STRATEGY_VOS) $(GE_STRATEGY_VOS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

%_proof_auto.vo: %_proof_auto.v %_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

%_proof_manual.vo: %_proof_manual.v %_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

gmp/mpz_tdiv_r_read0_proof_manual.vo: \
	gmp/mpz_tdiv_r_read0_proof_manual_part1.vo \
	gmp/mpz_tdiv_r_read0_proof_manual_part2.vo \
	gmp/mpz_tdiv_r_read0_proof_manual_part3.vo \
	gmp/mpz_tdiv_r_read0_proof_manual_part4.vo

%_goal_check.vo: %_goal_check.v %_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

%.vo: %.v
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	@cd $(SL_DIR) && $(COQDEP) $(DEP_FLAG) $(SL_FILES) > $(CASE_DIR)/.depend

.depend: $(FILES)
	@cd $(SL_DIR) && $(COQDEP) $(DEP_FLAG) $(SL_FILES) > $(CASE_DIR)/.depend

clean:
	@find gmp fme ge -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '.*.aux' \) -delete
	@rm -f gmp/.lia.cache gmp/.nia.cache fme/.lia.cache fme/.nia.cache ge/.lia.cache ge/.nia.cache .depend

.DEFAULT_GOAL := all

-include .depend
