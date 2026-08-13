CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

MONAD_FLAG = -R $(SETS_DIR) SetsClass -R $(FIXPOINT_DIR) FP -R $(LISTLIB_DIR) ListLib -R . MonadLib 

DEP_FLAG = -R $(SETS_DIR) SetsClass -R $(FIXPOINT_DIR) FP -R $(LISTLIB_DIR) ListLib -R . MonadLib 

SetMonad_Files = \
	SetBasic.v SetHoare.v FixpointLib.v SetMonad.v

StateRelMonad_Files = \
	StateRelBasic.v StateRelHoare.v FixpointLib.v safeexec_lib.v StateRelMonad.v

MonadErr_Files = \
	MonadErrBasic.v MonadErrLoop.v MonadErrHoare.v monadesafe_lib.v StateRelMonadErr.v MonadErrHoarePartial.v

OptionMonad_Files = \
	OptionBasic.v OptionMonad.v

ListMonad_Files = \
	ListBasic.v ListMonad.v

Rec_Interface_Test_Files = \
	test/RecInterface_Set.v \
	test/RecInterface_StateRel.v \
	test/RecInterface_MonadErr.v

Notation_Test_Files = \
	test/NotationTest_Set.v \
	test/NotationTest_StateRel.v \
	test/NotationTest_MonadErr.v \
	test/NotationTest_Option.v \
	test/NotationTest_List.v
MonadExample_FILES = \
	kmp.v mergesort.v 


MONAD_FILES = \
	Monad.v MonadLib.v \
	$(SetMonad_Files:%.v=SetMonad/%.v) \
	$(StateRelMonad_Files:%.v=StateRelMonad/%.v) \
	$(MonadErr_Files:%.v=MonadErr/%.v) \
	$(OptionMonad_Files:%.v=OptionMonad/%.v) \
	$(ListMonad_Files:%.v=ListMonad/%.v) \
	$(MonadExample_FILES:%.v=Examples/%.v) \

FILES = $(MONAD_FILES) $(Rec_Interface_Test_Files) $(Notation_Test_Files)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(MONAD_FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f */*.vo */*.glob */*.vos */*.vok */.*.aux

.DEFAULT_GOAL := all

-include .depend
