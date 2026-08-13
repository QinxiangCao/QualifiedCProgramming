Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.

Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigDenot.
Require Import Logic.LogicGenerator.ConfigCompute.
Require Logic.LogicGenerator.ConfigLang.

Require Import GeneratedGenerate.
Require Config.

Module PARA_OPEN.

Definition instance_para_open := false.

Import Config.

Definition PARA_OPEN: bool :=
  ltac:(first [ let XXX := eval compute in instance_para_open in exact XXX
              | exact false]).

End PARA_OPEN.

Definition instance_para_open := PARA_OPEN.PARA_OPEN.

Section Generate.
Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {truepL: TrueLanguage L}
        {iffpL: IffLanguage L}
        {negpL: NegLanguage L}
        {iter_andp_L: IterAndLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {sepconL : SepconLanguage L}
        {wandL : WandLanguage L}
        {empL: EmpLanguage L}
        {iter_sepcon_L: IterSepconLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {Cor: Corable L}
        {iffpDef: IffDefinition_And_Imp L}
        {truepDef: TrueDefinition_False_Imp L}
        {negpDef: NegDefinition_False_Imp L}
        {orpDef_impp_negp: OrDefinition_Imp_Neg L}
        {truepDef_impp_self: TrueDefinition_Imp_Self L}
        {truepDef_negp_falsep: TrueDefinition_Neg_False L}
        {falsepDef_negp_truep: FalseDefinition_Neg_True L}
        {iter_andp_DL: IterAndDefinition_left L}
        {iter_andp_DR: IterAndDefinition_right L}
        {iter_sepcon_DL: IterSepconDefinition_left L}
        {iter_sepcon_DR: IterSepconDefinition_right L}
        {GammaDP: DerivableFromProvable L GammaP GammaD}
        {GammaPD : ProvableFromDerivable L GammaP GammaD}
        {GammaD1P: Derivable1FromProvable L GammaP GammaD1}
        {GammaEP: EquivProvable L GammaP GammaE}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iter_andp_AXL: IterAndAxiomatization_left L GammaP}
        {cpAX: ClassicalAxiomatization L GammaP}
        {dmpAX: DeMorganAxiomatization L GammaP}
        {gdpAX: GodelDummettAxiomatization L GammaP}
        {plAX: PeirceLaw L GammaP}
        {bcAX: ByContradiction L GammaP}
        {dneAX: DoubleNegElimination L GammaP}
        {caAX: ClassicAnalysis L GammaP}
        {emAX: ExcludedMiddle L GammaP}
        {provable_negp_orpAX: ImplyToOr L GammaP}
        {coq_prop_AX: CoqPropAxiomatization L GammaP}
        {coq_prop_impp_AX: CoqPropImpAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}
        {wandAX: WandAxiomatization L GammaP}
        {empAX: EmpAxiomatization L GammaP}
        {iter_sepcon_AXL: IterSepconAxiomatization_left L GammaP}
        {sepcon_orp_AX: SepconOrAxiomatization L GammaP}
        {sepcon_falsep_AX: SepconFalseAxiomatization L GammaP}
        {sepcon_coq_prop_AX: SepconCoqPropAxiomatization L GammaP}
        {sepconAX_weak: SepconAxiomatization_weak L GammaP}
        {sepconAX_weak_iffp: SepconAxiomatization_weak_iffp L GammaP}
        {provable_sepcon_mono_AX: SepconMonoAxiomatization L GammaP}
        {empAX_iffp: EmpAxiomatization_iffp L GammaP}
        {extAX: ExtSeparationLogic L GammaP}
        {nseAX: NonsplitEmpSeparationLogic L GammaP}
        {deAX: DupEmpSeparationLogic L GammaP}
        {mfAX: MallocFreeSeparationLogic L GammaP}
        {gcAX: GarbageCollectSeparationLogic L GammaP}
        {bSC : BasicSequentCalculus L GammaD}
        {fwSC : FiniteWitnessedSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC : AndSequentCalculus L GammaD}
        {orpSC : OrSequentCalculus L GammaD}
        {falsepSC : FalseSequentCalculus L GammaD}
        {truepSC : TrueSequentCalculus L GammaD}
        {iffpSC : IffSequentCalculus L GammaD}
        {inegpSC : IntuitionisticNegSequentCalculus L GammaD}
        {cpSC: ClassicalSequentCalculus L GammaD}
        {bD : BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD : AndDeduction L GammaD1}
        {orpD : OrDeduction L GammaD1}
        {falsepD : FalseDeduction L GammaD1}
        {truepD : TrueDeduction L GammaD1}
        {iffpD : IffDeduction L GammaD1}
        {inegpD : IntuitionisticNegDeduction L GammaD1}
        {impp_negp_D : ImpNegDeduction L GammaD1}
        {sepconD : SepconDeduction L GammaD1}
        {wandD : WandDeduction L GammaD1}
        {empD : EmpDeduction L GammaD1}
        {sepcon_orp_D : SepconOrDeduction L GammaD1}
        {sepcon_falsep_D : SepconFalseDeduction L GammaD1}
        {bE: BasicLogicEquiv L GammaE}
        {imppE: ImpLogicEquiv L GammaE}
        {CorAX: Corable_withAxiomatization L GammaP Cor}
        {coq_prop_Cor: CoqPropCorable L Cor}
        .

Import NameListNotations.

Definition foo :=
  ltac:(
    let res := eval compute in
    (ConfigCompute.result
       Config.how_connectives
       Config.how_judgements
       Config.transparent_names
       Config.primitive_rule_classes)
    in exact res).

Definition primitive_types: list Name :=
  map_with_hint
    (ConfigDenot.D.types, ConfigDenot.S.types)
    (ConfigLang.Output.primitive_types foo).

Definition transparent_types: list Name :=
  map_with_hint
    (ConfigDenot.D.types, ConfigDenot.S.types)
    (ConfigLang.Output.transparent_types foo).
  
Definition derived_types: list Name :=
  map_with_hint
    (ConfigDenot.D.how_types, ConfigDenot.S.how_types)
    (ConfigLang.Output.derived_types foo).
  
Definition primitive_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.connectives, ConfigDenot.S.connectives)
    (ConfigLang.Output.primitive_connectives foo).

Definition transparent_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.connectives, ConfigDenot.S.connectives)
    (ConfigLang.Output.transparent_connectives foo).

Definition derived_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.how_connectives, ConfigDenot.S.how_connectives)
    (ConfigLang.Output.derived_connectives foo).

Definition primitive_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.judgements, ConfigDenot.S.judgements)
    (ConfigLang.Output.primitive_judgements foo).

Definition transparent_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.judgements, ConfigDenot.S.judgements)
    (ConfigLang.Output.transparent_judgements foo).

Definition derived_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.how_judgements, ConfigDenot.S.how_judgements)
    (ConfigLang.Output.derived_judgements foo).

Definition aux_primitive_instances: list Name :=
  map_with_hint
    (ConfigDenot.D.classes, ConfigDenot.S.instances_build)
    (ConfigLang.Output.primitive_classes foo).

Definition aux_refl_instances_for_derivation: list Name :=
  map_with_hint
    (ConfigDenot.D.refl_classes, ConfigDenot.S.refl_instances)
    (ConfigLang.Output.refl_classes_for_derivation foo).

Definition aux_derived_instances: list Name :=
  map_with_hint
    (ConfigDenot.S.D_instance_transitions, ConfigDenot.S.instance_transitions)
    (ConfigLang.Output.how_derive_classes foo).

Definition primary_rules: list Name :=
  map_with_hint
    (ConfigDenot.S.D_primary_rules, ConfigDenot.S.primary_rules)
    (ConfigLang.Output.primary_rules foo).

Let derived_rules': list Name :=
  (map_with_hint
    (ConfigDenot.S.D_primary_rules, ConfigDenot.S.primary_rules)
    (ConfigLang.Output.derived_primary_rules foo)) ++
  map_with_hint
    (ConfigDenot.S.D_derived_rules, ConfigDenot.S.derived_rules)
    (ConfigLang.Output.derived_derived_rules foo).

Definition derived_rules : list Name :=
  ltac:(let res0 := eval unfold derived_rules' in derived_rules' in
        let res1 := eval unfold app at 1 in res0 in
            exact res1).

Definition derived_rules_as_instance :=
  map_with_hint
    (ConfigDenot.S.D_derived_rules, ConfigDenot.S.derived_rules)
    (ConfigLang.Output.derived_rules_as_instance foo).

Import ListNotations.

Ltac print_notation name :=
  match name with
  | expr => idtac "  ""'expr'"""
  | Base.context => idtac "  ""'context'"""
  | impp => idtac "  ""'impp'"""
  | andp => idtac "  ""'andp'"""
  | orp => idtac "  ""'orp'"""
  | falsep => idtac "  ""'falsep'"""
  | truep => idtac "  ""'truep'"""
  | iffp => idtac "  ""'iffp'"""
  | negp => idtac "  ""'negp'"""
  | coq_prop => idtac "  ""'coq_prop'"""
  | sepcon => idtac "  ""'sepcon'"""
  | wand => idtac "  ""'wand'"""
  | emp => idtac "  ""'emp'"""
  | multi_imp => idtac "  ""'multi_imp'"""
  | iter_andp => idtac "  ""'iter_andp'"""
  | iter_sepcon => idtac "  ""'iter_sepcon'"""
  | empty_context => idtac "  ""'empty_context'"""
  | provable => idtac "  ""'provable'"""
  | derivable => idtac "  ""'derivable'"""
  | derivable1 => idtac "  ""'derivable1'"""
  | logic_equiv => idtac "  ""'logic_equiv'"""
  | corable => idtac "  ""'corable'"""
  end.

Inductive PrintType := NT_IPar (Inline_list: list Name) | IPar (Inline_list: list Name) | Prt | Der | Der2 | Def | Def2 | DIns | NT.

Ltac print prt name :=
  match name with
  | BuildName ?n =>
    match type of n with
    | ?T =>
      match prt with
      | NT_IPar ?l =>
        let l := eval hnf in l in
        let should_inline := in_name_list n l in
        match should_inline with
        | true => idtac "  Definition" n ":" T ":= ltac:(let x0 := eval unfold" n "in" n "in exact x0)."
        | false => idtac "  Definition" n ":" T ":=" n "."
        end
      | IPar ?l =>
        let l := eval hnf in l in
        let should_inline := in_name_list n l in
        match should_inline with
        | true => idtac "  Definition" n ": UNFOLD" T ":= ltac:(let x0 := eval unfold" n "in" n "in exact x0)."
        | false => idtac "  Definition" n ": UNFOLD" T ":=" n "."
        end
      | Prt => idtac "      " n
      | Der => match n with
                  | (?n0, ?n1) => idtac "  Definition" n0 ":= UNFOLD" n1 "."
                  end
      | Der2 => match n with
                  | (?n0, ?n1) => idtac "  Definition" n0 ":= UNFOLD2" n1 "."
                  end
      | Def => idtac "  Definition" n ": UNFOLD" T ":=" n "."
      | Def2 => idtac "  Definition" n ": UNFOLD2" T ":=" n "."
      | DIns => idtac "  Existing Instance" n "."
      | NT => idtac "Notation";
              print_notation n;
              idtac "    := (ltac:(let x0 := eval unfold" n "in" n "in exact x0)) (only parsing, at level 99): expo_transparent_scope."

      end
    end
  end.

Ltac newline := idtac "".

Set Printing Width 1000.

Ltac beta_print :=
  import_local_lib_tac;
  import_implementation_tac;
  idtac "Require Import Coq.Numbers.BinNums.";
  idtac "Require Import Coq.PArith.BinPosDef.";
  idtac "Require Import Logic.lib.PTree.";
  idtac "Require Import Coq.Sets.Ensembles.";
  idtac "Require Import Coq.Lists.List.";
  idtac "Import ListNotations.";

  newline;

  set_up_module_name_tac;
  idtac "Module EXPO.";
  idtac "Import ___LogicTheorem___.";
  idtac "  Section EXPO_SECTION.";
  context_expr_tac;
  newline;

  idtac "  Declare Scope EXPO_scope.";
  idtac "  Local Open Scope EXPO_scope.";

  newline;

  dolist (print (NT_IPar transparent_types)) primitive_types;

  idtac "  Ltac unfold_tac x :=";
  idtac "    let x0 :=";
  idtac "    eval cbv beta delta [";
  dolist (print Prt) transparent_types;
  idtac "      ] in x";
  idtac "      in exact x0.";
  newline;
  idtac "  Local Notation ""'UNFOLD' x"" := ltac:(unfold_tac x) (only parsing, at level 99): EXPO_scope.";

  newline;

  dolist (print Der) derived_types;
  dolist (print (IPar transparent_judgements)) primitive_judgements;
  dolist (print (IPar transparent_connectives)) primitive_connectives;

  newline;

  idtac "  Ltac unfold2_tac x :=";
  idtac "    let x0 :=";
  idtac "    eval cbv beta delta [";
  dolist (print Prt) transparent_types;
  dolist (print Prt) transparent_judgements;
  dolist (print Prt) transparent_connectives;
  idtac "    ] in x";
  idtac "    in exact x0.";
  
  idtac "  Local Notation ""'UNFOLD2' x"" := ltac:(unfold2_tac x) (only parsing, at level 99): EXPO_scope.";
  
  newline;

  dolist (print Der2) derived_judgements;
  dolist (print Der2) derived_connectives;
  dolist (print Def2) primary_rules;
  idtac "Definition tree_pos : Type := tree_pos.";
  dolist (print Def2) derived_rules;

  newline;

  idtac "  End EXPO_SECTION.";

  newline;

  dolist (print DIns) derived_rules_as_instance;

  newline;

  idtac "End EXPO.";

  newline;

  idtac "Module EXPO_TRANSPARENTS.";
  idtac "Import EXPO.";
  idtac "Declare Scope expo_transparent_scope.";
  dolist (print NT) transparent_types;
  dolist (print NT) transparent_judgements;
  dolist (print NT) transparent_connectives;
  idtac "End EXPO_TRANSPARENTS.";
  idtac.

  
Goal False.
  beta_print.
Abort.

End Generate.
