CURRENT_DIR=.
COQBIN ?=
SUF ?=
empty :=
space := $(empty) $(empty)
comma := ,
powershell_list = $(subst $(space),$(comma) ,$(strip $(foreach item,$(1),'$(item)')))

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

ifeq ($(OS),Windows_NT)
SHELL := cmd

define BACKUP_FILES
powershell -NoProfile -Command "$$files = @($(call powershell_list,$(1))); foreach ($$name in $$files) { if (Test-Path -LiteralPath $$name) { Move-Item -Force -LiteralPath $$name -Destination ($$name + '_BACKUP') } }"
endef

define TOUCH_FILES
powershell -NoProfile -Command "$$files = @($(call powershell_list,$(1))); foreach ($$name in $$files) { New-Item -ItemType File -Force -Path $$name | Out-Null }"
endef

define REMOVE_FILES
powershell -NoProfile -Command "$$files = @($(call powershell_list,$(1))); if ($$files.Length -gt 0) { Remove-Item -Force -LiteralPath $$files -ErrorAction SilentlyContinue }; exit 0"
endef

define RESTORE_FILES
powershell -NoProfile -Command "$$files = @($(call powershell_list,$(1))); foreach ($$name in $$files) { $$backup = $$name + '_BACKUP'; if (Test-Path -LiteralPath $$backup) { Move-Item -Force -LiteralPath $$backup -Destination $$name } }"
endef

define REMOVE_TREE_OUTPUTS
powershell -NoProfile -Command "Get-ChildItem -Path $(call powershell_list,$(1)) -Recurse -Force -Include *.vo,*.glob,*.vos,*.vok,.*.aux -ErrorAction SilentlyContinue | Remove-Item -Force -ErrorAction SilentlyContinue; exit 0"
endef
else
define BACKUP_FILES
for name in $(1); do \
  if [ -f "$$name" ]; then mv -f "$$name" "$$name"_BACKUP; fi; \
done
endef

define TOUCH_FILES
for name in $(1); do \
  : > "$$name"; \
done
endef

define REMOVE_FILES
rm -f $(1)
endef

define RESTORE_FILES
for name in $(1); do \
  if [ -f "$$name"_BACKUP ]; then mv -f "$$name"_BACKUP "$$name"; fi; \
done
endef

define REMOVE_TREE_OUTPUTS
find $(1) -type f \( -name '*.vo' -o -name '*.glob' -o -name '*.vos' -o -name '*.vok' -o -name '.*.aux' \) -delete
endef
endif

DIRS = \
  lib GeneralLogic MinimumLogic PropositionalLogic MetaLogicInj ModalLogic SeparationLogic \
  QuantifierLogic Extensions HoareLogic ExportSolvers LogicGenerator ShallowQuantifierLogic

COQ_FLAG = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Logic.$(d))
DEP_FLAG = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Logic.$(d))

lib_FILES = \
  Coqlib.v Ensembles_ext.v EnsemblesProperties.v Relation_ext.v Equivalence_ext.v List_Func_ext.v \
  Bijection.v Countable.v NatChoice.v StrongInduction.v \
  Bisimulation.v RelationPairs_ext.v \
  register_typeclass.v SublistT.v \
  Stream/SigStream.v Stream/StreamFunctions.v Stream/StreamSplit.v \
  PTree.v CancelFoundation.v

GeneralLogic_ProofTheory_FILES = \
  BasicSequentCalculus.v BasicDeduction.v BasicLogicEquiv.v \
  TheoryOfSequentCalculus.v ProofTheoryPatternsD1.v

GeneralLogic_Semantics_FILES = \
  Kripke.v

GeneralLogic_Complete_FILES = \
  ContextProperty_Trivial.v ContextProperty_Kripke.v ContextProperty.v \
  Canonical_Kripke.v \
  Lindenbaum.v Lindenbaum_Kripke.v \
  Complete_Kripke.v 

GeneralLogic_ShallowEmbedded_FILES = \
  PredicateAsLang.v MonoPredicateAsLang.v ModelLanguage.v

GeneralLogic_FILES = \
  Base.v HenkinCompleteness.v \
  KripkeModel.v  ModelClass.v \
  $(GeneralLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(GeneralLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(GeneralLogic_Complete_FILES:%.v=Complete/%.v) \
  $(GeneralLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

MinimumLogic_ProofTheory_FILES = \
  Minimum.v ProofTheoryPatternsP.v ProofTheoryPatterns.v \
  RewriteClass.v TheoryOfSequentCalculus.v ExtensionTactic.v TheoryOfJudgement.v

MinimumLogic_Semantics_FILES = \
  Kripke.v Trivial.v SemanticEquiv.v

MinimumLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Classical_Trivial.v

MinimumLogic_Complete_FILES = \
  Complete.v ContextProperty_Kripke.v Lindenbaum_Kripke.v Truth_Kripke.v

MinimumLogic_ShallowEmbedded_FILES = \
  ModelLanguageMinimumLogic.v

MinimumLogic_DeepEmbedded_FILES = \
  MinimumLanguage.v KripkeSemantics.v MinimumLogic.v \
  Complete_Kripke.v Soundness.v

MinimumLogic_FILES = \
  Syntax.v \
  $(MinimumLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(MinimumLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(MinimumLogic_Sound_FILES:%.v=Sound/%.v) \
  $(MinimumLogic_Complete_FILES:%.v=Complete/%.v) \
  $(MinimumLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v) \
  $(MinimumLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v)

PropositionalLogic_ProofTheory_FILES = \
  Intuitionistic.v DeMorgan.v \
  GodelDummett.v Classical.v \
  RewriteClass.v ProofTheoryPatterns.v \
  TheoryOfIteratedConnectives.v \
  TheoryOfPropositionalConnectives.v \
  TheoryOfClassicalAxioms.v

PropositionalLogic_Semantics_FILES = \
  Kripke.v Trivial.v

PropositionalLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Classical_Trivial.v

PropositionalLogic_Complete_FILES = \
  ContextProperty_Kripke.v \
  Lindenbaum_Kripke.v Canonical_Kripke.v Truth_Kripke.v \
  ContextProperty_Trivial.v \
  Lindenbaum_Trivial.v Truth_Trivial.v Complete_Trivial.v

PropositionalLogic_DeepEmbedded_FILES = \
  PropositionalLanguage.v ProofTheories.v \
  KripkeSemantics.v TrivialSemantics.v \
  Soundness.v Complete_Kripke.v Complete_Classical_Trivial.v \
  # configuration_Mendelson.v interface_Mendelson.v implementation_Mendelson.v \
  Deep.v Solver.v

PropositionalLogic_ShallowEmbedded_FILES = \
  PredicatePropositionalLogic.v \
  MonoPredicatePropositionalLogic.v \
  ModelLanguagePropositionalLogic.v

PropositionalLogic_FILES = \
  Syntax.v\
  $(PropositionalLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(PropositionalLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(PropositionalLogic_Sound_FILES:%.v=Sound/%.v) \
  $(PropositionalLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(PropositionalLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v) \
  $(PropositionalLogic_Complete_FILES:%.v=Complete/%.v)

MetaLogicInj_ProofTheory_FILES = \
  ProofRules.v

MetaLogicInj_Semantics_FILES = \
  Kripke.v

MetaLogicInj_Sound_FILES = \
  Sound_Kripke.v

MetaLogicInj_ShallowEmbedded_FILES = \
  ModelLanguageMetaLogic.v

MetaLogicInj_FILES = \
  Syntax.v \
  $(MetaLogicInj_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(MetaLogicInj_Semantics_FILES:%.v=Semantics/%.v) \
  $(MetaLogicInj_Sound_FILES:%.v=Sound/%.v) \
  $(MetaLogicInj_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

ModalLogic_ProofTheory_FILES = \
  ModalLogic.v RewriteClass.v \
  ClassicalDerivedRules.v IntuitionisticDerivedRules.v

ModalLogic_Model_FILES = \
  KripkeModel.v OrderedKripkeModel.v

ModalLogic_Semantics_FILES = \
  Kripke.v Flat.v

ModalLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Flat.v

ModalLogic_ShallowEmbedded_FILES = \
  PredicateModalLogic.v \
  MonoPredicateModalLogic.v

ModalLogic_FILES = \
  Syntax.v \
  $(ModalLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(ModalLogic_Model_FILES:%.v=Model/%.v) \
  $(ModalLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(ModalLogic_Sound_FILES:%.v=Sound/%.v) \
  $(ModalLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

QuantifierLogic_ProofTheory_FILES = \
  QuantifierLogic.v

QuantifierLogic_DeepEmbedded_FILES = \
  FirstOrderLanguage.v FirstOrderLogic.v

QuantifierLogic_ShallowEmbedded_FILES = \
  PredicateAsBLang.v PredicateQuantifierLogic.v

QuantifierLogic_FILES = \
  Syntax.v \
  $(QuantifierLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(QuantifierLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(QuantifierLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

SeparationLogic_ProofTheory_FILES = \
  SeparationLogic.v SeparationLogicExtension.v TheoryOfSeparationAxioms.v TheoryOfCancel.v \
  RewriteClass.v DerivedRules.v IterSepcon.v WandFrame.v Corable.v Deduction.v

SeparationLogic_Model_FILES = \
  SeparationAlgebra.v OrderedSA.v \
  UpwardsClosure.v DownwardsClosure.v \
  OSAGenerators.v OSAExamples.v

SeparationLogic_Semantics_FILES = \
  WeakSemantics.v StrongSemantics.v  EmpSemantics.v\
  UpwardsSemantics.v DownwardsSemantics.v FlatSemantics.v \
  DownUpSemantics_Fail.v \
  Down2Flat.v Up2Flat.v \
  SemanticsExtension.v \


SeparationLogic_Sound_FILES = \
  Sound_Downwards.v Sound_Upwards.v Sound_Flat.v \
  Sound_DownUp_Fail.v Sound_Flat_Corable.v

SeparationLogic_Complete_FILES = \
  ContextProperty_Flat.v \
  Lindenbaum_Flat.v Truth_Flat.v Canonical_Flat.v

SeparationLogic_DeepEmbedded_FILES = \
  SeparationLanguage.v SeparationEmpLanguage.v \
  Parameter.v \
  ParametricSeparationLogic.v SeparationLogicsInLiteratures.v \
  FlatSemantics.v ParametricCompleteness.v \
  # MinimumSeparationLogic_Config.v MinimumSeparationLogic_LibSupport.v MinimumSeparationLogic.v

SeparationLogic_ShallowEmbedded_FILES = \
  PredicateSeparationLogic.v MonoPredicateSeparationLogic.v \
  Join2Sepcon.v \
  Model2CoqPropEmp.v\
  ModelLanguageSeparationLogic.v

SeparationLogic_FILES = \
  Syntax.v \
  $(SeparationLogic_Model_FILES:%.v=Model/%.v) \
  $(SeparationLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(SeparationLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(SeparationLogic_Sound_FILES:%.v=Sound/%.v) \
  $(SeparationLogic_Complete_FILES:%.v=Complete/%.v) \
  $(SeparationLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(SeparationLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

ExportSolvers_FILES = \
  Normalize.v Normalize_Para.v #SepApply/SepApply.v SepApply/export_lib.v

Extensions_ProofTheory_FILES = \
  Stable.v ModalSeparation.v Corable.v CoreTransit.v

Extensions_Semantics_FILES = \
  SemanticStable.v ModalSeparation.v

Extensions_Sound_FILES = \
  StableSound.v

Extensions_ShallowEmbedded_FILES = \
  MonoPredicateStable.v

Extensions_FILES = \
  Syntax_CoreTransit.v \
  $(Extensions_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(Extensions_Semantics_FILES:%.v=Semantics/%.v) \
  $(Extensions_Sound_FILES:%.v=Sound/%.v) \
  $(Extensions_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

HoareLogic_FILES = \
  ImperativeLanguage.v ProgramState.v Trace.v \
  SimpleSmallStepSemantics.v SmallStepSemantics.v \
  BigStepSemantics.v ConcurrentSemantics_Angelic.v \
  TraceSemantics.v \
  OperationalSemanticsGenerator.v \
  HoareLogic.v GuardedHoareLogic.v \
  HoareTriple_BigStepSemantics.v GuardedHoareTriple_Angelic.v GuardedHoareTriple_TraceSemantics.v \
  Sound_Basic.v Sound_Imp.v Sound_Frame.v \
  Sound_Resource_Angelic.v Sound_Resource_TraceSemantics.v

ShallowQuantifierLogic_FILES = \
  Syntax.v ProofTheory.v ModelConstrEX.v ModelConstrALL.v

LogicGenerator_FILES = \
  ConfigLang.v ConfigDenot.v ConfigCompute.v Utils.v #Generate.v 

Example_Files = \
  Pub_Problem.v

FILES = \
  $(lib_FILES:%.v=lib/%.v) \
  $(GeneralLogic_FILES:%.v=GeneralLogic/%.v) \
  $(MinimumLogic_FILES:%.v=MinimumLogic/%.v) \
  $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.v) \
  $(MetaLogicInj_FILES:%.v=MetaLogicInj/%.v) \
  $(QuantifierLogic_FILES:%.v=QuantifierLogic/%.v) \
  $(SeparationLogic_FILES:%.v=SeparationLogic/%.v) \
  $(ExportSolvers_FILES:%.v=ExportSolvers/%.v) \
  $(HoareLogic_FILES:%.v=HoareLogic/%.v) \
  $(ShallowQuantifierLogic_FILES:%.v=ShallowQuantifierLogic/%.v) \
  $(LogicGenerator_FILES:%.v=LogicGenerator/%.v) 
#  $(ModalLogic_FILES:%.v=ModalLogic/%.v) \
#  $(Extensions_FILES:%.v=Extensions/%.v) \
#  $(Example_Files:%.v=Examples/%.v) \

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

lib: \
  .depend $(lib_FILES:%.v=lib/%.vo)

GeneralLogic: \
  .depend $(GeneralLogic_FILES:%.v=GeneralLogic/%.vo)

MinimumLogic: \
  .depend $(MinimumLogic_FILES:%.v=MinimumLogic/%.vo)

PropositionalLogic: \
  .depend $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.vo)

MetaLogicInj: \
  .depend $(MetaLogicInj_FILES:%.v=MetaLogicInj/%.vo)

ModalLogic: \
  .depend $(ModalLogic_FILES:%.v=ModalLogic/%.vo)

QuantifierLogic: \
  .depend $(QuantifierLogic_FILES:%.v=QuantifierLogic/%.vo)

SeparationLogic: \
  .depend $(SeparationLogic_FILES:%.v=SeparationLogic/%.vo)

ShallowQuantifierLogic: \
  .depend $(ShallowQuantifierLogic:%.v=ShallowQuantifierLogic/%.vo)

LogicGenerator: \
  .depend $(LogicGenerator_FILES:%.v=LogicGenerator/%.vo)

all: \
  $(FILES:%.v=%.vo)

# PropositionalLogic/DeepEmbedded/interface_Mendelson.v: PropositionalLogic/DeepEmbedded/configuration_Mendelson.v LogicGenerator/ConfigCompute.vo PropositionalLogic/DeepEmbedded/Solver.vo
# 	./logic_gen.sh PropositionalLogic/DeepEmbedded/configuration_Mendelson.v PropositionalLogic/DeepEmbedded/interface_Mendelson.v

# SeparationLogic/DeepEmbedded/MinimumSeparationLogic_LibSupport.v: SeparationLogic/DeepEmbedded/MinimumSeparationLogic_Config.v LogicGenerator/ConfigCompute.vo PropositionalLogic/DeepEmbedded/Solver.vo
# 	./logic_gen.sh SeparationLogic/DeepEmbedded/MinimumSeparationLogic_Config.v SeparationLogic/DeepEmbedded/MinimumSeparationLogic_LibSupport.v

lgen_demo_1:
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/HypotheticalExternLib.v
	./logic_gen.sh LogicGenerator/demo/configuration_1.v LogicGenerator/demo/interface_1.v LogicGenerator/demo/export_lib_1.v
	@echo COQC LogicGenerator/demo/interface_1.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/interface_1.v
	@echo COQC LogicGenerator/demo/implementation_1.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_1.v
	@echo COQC LogicGenerator/demo/export_lib_1.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/export_lib_1.v

lgen_demo_2:
	./logic_gen.sh LogicGenerator/demo/configuration_2.v LogicGenerator/demo/interface_2.v
	@echo COQC LogicGenerator/demo/interface_2.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/interface_2.v
	@echo COQC LogicGenerator/demo/implementation_2a.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_2a.v
	@echo COQC LogicGenerator/demo/implementation_2b.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_2b.v

lgen_demo_3:
	./logic_gen.sh LogicGenerator/demo/configuration_3.v LogicGenerator/demo/interface_3.v
	@echo COQC LogicGenerator/demo/interface_3.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/interface_3.v
	@echo COQC LogicGenerator/demo/implementation_3.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_3.v

lgen_demo_4:
	./logic_gen.sh LogicGenerator/demo/configuration_4.v LogicGenerator/demo/interface_4.v
	@echo COQC LogicGenerator/demo/interface_4.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/interface_4.v
	@echo COQC LogicGenerator/demo/implementation_4.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_4.v

lgen_demo_5:
	./logic_gen.sh LogicGenerator/demo/configuration_5.v LogicGenerator/demo/interface_5.v
	@echo COQC LogicGenerator/demo/interface_5.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/interface_5.v
	@echo COQC LogicGenerator/demo/implementation_5.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_5.v

lgen_demo_6:
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo6/HypotheticalExternLib.v
	./logic_gen.sh LogicGenerator/demo6/configuration_6.v LogicGenerator/demo6/interface_6.v LogicGenerator/demo6/export_lib_6.v
	@echo COQC LogicGenerator/demo6/interface_6.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo6/interface_6.v
	@echo COQC LogicGenerator/demo6/implementation_6.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo6/implementation_6.v
	@echo COQC LogicGenerator/demo6/export_lib_6.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo6/export_lib_6.v
	@cp ExportSolvers/SepApply/SepApply.v LogicGenerator/demo6/SepApply_6.v
	@sed -i 's/export_lib/export_lib_6/g' LogicGenerator/demo6/SepApply_6.v
	@echo COQC LogicGenerator/demo6/SepApply_6.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo6/SepApply_6.v
	@cp ExportSolvers/SepCancel/SepCancel.v LogicGenerator/demo6/SepCancel_6.v
	@sed -i 's/export_lib/export_lib_6/g' LogicGenerator/demo6/SepCancel_6.v
	@echo COQC LogicGenerator/demo6/SepCancel_6.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo6/SepCancel_6.v
	@echo COQC LogicGenerator/demo6/test_6.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo6/test_6.v

demo931:
	@echo COQC LogicGenerator/demo931/Config.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo931/Config.v
	./logic_gen.sh LogicGenerator/demo931/Config.v LogicGenerator/demo931/Interface.v
	@echo COQC LogicGenerator/demo931/Interface.v 
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo931/Interface.v
  # cd ./LogicGenerator/demo931 
  # python subst.py

demo932:
	@echo COQC LogicGenerator/demo932/Config.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo932/Config.v
	./logic_gen.sh LogicGenerator/demo932/Config.v LogicGenerator/demo932/Interface.v
	@echo COQC LogicGenerator/demo932/Interface.v 
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo932/Interface.v

demo933:
	@echo COQC LogicGenerator/demo933/Config.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo933/Config.v
	./logic_gen.sh LogicGenerator/demo933/Config.v LogicGenerator/demo933/Interface.v
	@echo COQC LogicGenerator/demo933/Interface.v 
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo933/Interface.v

demoq:
	@echo COQC LogicGenerator/demoq/Config.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demoq/Config.v
	./logic_gen.sh LogicGenerator/demoq/Config.v LogicGenerator/demoq/Interface.v

demo424:
	@echo COQC LogicGenerator/demoq424/Config.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo424/Config.v
	./logic_gen.sh LogicGenerator/demo424/Config.v LogicGenerator/demo424/Interface.v

# sprop:
#	@echo COQC LogicGenerator/demo/sprop_config.v 
#	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/sprop_config.v 
#	./logic_gen.sh LogicGenerator/demo/sprop_config.v LogicGenerator/demo/sprop_interface.v
#	@echo COQC LogicGenerator/demo/sprop_interface.v 
#	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/sprop_interface.v
#	cp LogicGenerator/demo/sprop_interface.v ../foundationalverifier/sprop_interface.v 
#	@echo COQC ../foundationalverifier/sprop_interface.v 
#	@$(COQC) $(COQ_FLAG) ../foundationalverifier/sprop_interface.v 
#	@echo COQC ../foundationalverifier/sprop_implement.v
#	@$(COQC) $(COQ_FLAG) ../foundationalverifier/sprop_implement.v

# demo932:
# 	@echo COQC LogicGenerator/demo932/Config.v
# 	@$(COQC) $(COQ_FLAG) LogicGenerator/demo932/Config.v
# 	./logic_gen.sh LogicGenerator/demo932/Config.v LogicGenerator/demo932/Interface.v


# @echo COQC LogicGenerator/demo/Interface.v
# @$(COQC) $(COQ_FLAG) LogicGenerator/demo/Interface.v

# lgen_demo_7:
# 	./logic_gen.sh LogicGenerator/demo7/configuration_7.v LogicGenerator/demo7/interface_7.v LogicGenerator/demo7/export_lib_7.v
# 	@echo COQC LogicGenerator/demo7/interface_7.v
# 	@$(COQC) $(COQ_FLAG) LogicGenerator/demo7/interface_7.v
# 	@echo COQC LogicGenerator/demo7/implementation_7.v
# 	@$(COQC) $(COQ_FLAG) LogicGenerator/demo7/implementation_7.v
# 	@echo COQC LogicGenerator/demo7/export_lib_7.v
# 	@$(COQC) $(COQ_FLAG) LogicGenerator/demo7/export_lib_7.v
# 	@cp ExportSolvers/SepApply/SepApply.v LogicGenerator/demo7/SepApply_7.v
# 	@sed -i 's/export_lib/export_lib_7/g' LogicGenerator/demo7/SepApply_7.v
# 	@echo COQC LogicGenerator/demo7/SepApply_7.v
# 	@$(COQC) $(COQ_FLAG) LogicGenerator/demo7/SepApply_7.v
# 	@cp ExportSolvers/SepCancel/SepCancel.v LogicGenerator/demo7/SepCancel_7.v
# 	@sed -i 's/export_lib/export_lib_7/g' LogicGenerator/demo7/SepCancel_7.v
# 	@echo COQC LogicGenerator/demo7/SepCancel_7.v
# 	@$(COQC) $(COQ_FLAG) LogicGenerator/demo7/SepCancel_7.v
# 	@echo COQC LogicGenerator/demo7/test_7.v
# 	@$(COQC) $(COQ_FLAG) LogicGenerator/demo7/test_7.v

# lgen_demo_bedrock2:
# 	./logic_gen.sh LogicGenerator/demo/configuration_bedrock2.v ../bedrock2/bedrock2/src/exportLogic/interface.v ../bedrock2/bedrock2/src/exportLogic/export_lib.v
# 	@echo COQC interface.v [in-bedrock2-folder]
# 	@$(COQC) $(COQ_FLAG) -R ../bedrock2/bedrock2/src/bedrock2 bedrock2 -R ../bedrock2/bedrock2/src/exportLogic exportLogic -R ../bedrock2/deps/coqutil/src/coqutil coqutil ../bedrock2/bedrock2/src/exportLogic/interface.v
# 	@echo COQC implementation.v [in-bedrock2-folder]
# 	@cp LogicGenerator/demo/implementation_bedrock2.v ../bedrock2/bedrock2/src/exportLogic/implementation.v
# 	@$(COQC) $(COQ_FLAG) -R ../bedrock2/bedrock2/src/bedrock2 bedrock2 -R ../bedrock2/bedrock2/src/exportLogic exportLogic -R ../bedrock2/deps/coqutil/src/coqutil coqutil ../bedrock2/bedrock2/src/exportLogic/implementation.v
# 	@echo COQC export_lib.v [in-bedrock2-folder]
# 	@$(COQC) $(COQ_FLAG) -R ../bedrock2/bedrock2/src/bedrock2 bedrock2 -R ../bedrock2/bedrock2/src/exportLogic exportLogic -R ../bedrock2/deps/coqutil/src/coqutil coqutil ../bedrock2/bedrock2/src/exportLogic/export_lib.v
# 	@cp ExportSolvers/SepApply/SepApply.v ../bedrock2/bedrock2/src/exportLogic/
# 	@echo COQC SepApply.v [in-bedrock2-folder]
# 	@$(COQC) $(COQ_FLAG) -R ../bedrock2/bedrock2/src/bedrock2 bedrock2 -R ../bedrock2/bedrock2/src/exportLogic exportLogic -R ../bedrock2/deps/coqutil/src/coqutil coqutil ../bedrock2/bedrock2/src/exportLogic/SepApply.v

# DF=PropositionalLogic/DeepEmbedded/interface_Mendelson.v SeparationLogic/DeepEmbedded/MinimumSeparationLogic_LibSupport.v

depend:

ifeq ($(strip $(DF)),)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend
else
	@$(call BACKUP_FILES,$(DF))
	@$(call TOUCH_FILES,$(DF))
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend
	@$(call REMOVE_FILES,$(DF))
	@$(call RESTORE_FILES,$(DF))
endif

.depend:

ifeq ($(strip $(DF)),)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend
else
	@$(call BACKUP_FILES,$(DF))
	@$(call TOUCH_FILES,$(DF))
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend
	@$(call REMOVE_FILES,$(DF))
	@$(call RESTORE_FILES,$(DF))
endif

clean:
	-@$(call REMOVE_TREE_OUTPUTS,.)
	-@$(call REMOVE_FILES,.depend)

.DEFAULT_GOAL := all

-include .depend
