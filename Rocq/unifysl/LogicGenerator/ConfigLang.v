Require Import Coq.Lists.List.
Import ListNotations.

(** * What users need to know **)
(** ** Parameters *)

Inductive connective :=
| impp
| andp
| orp
| falsep
| truep
| negp
| iffp
| coq_prop
| sepcon
| wand
| emp
| multi_imp
| iter_andp
| iter_sepcon
| empty_context
| join
| is_unit
| Krelation
| exp
| allp.

Inductive judgement :=
| provable
| derivable
| derivable1
| logic_equiv
| corable.

Inductive type :=
| model
| expr
| context.

Inductive parameter :=
| CP (c: connective)
| JP (j: judgement)
| TP (t: type).

Coercion CP: connective >-> parameter.
Coercion JP: judgement >-> parameter.
Coercion TP: type >-> parameter.

Inductive how_connective :=
| primitive_connective (c: connective)
| ___predicate_over_states (mono: bool) (c: connective)
| FROM_andp_impp_TO_iffp
| FROM_falsep_impp_TO_negp
| FROM_falsep_impp_TO_truep
| FROM_impp_negp_TO_orp
| FROM_negp_falsep_TO_truep
| FROM_negp_truep_TO_falsep
| FROM_impp_TO_multi_imp
| FROM_andp_TO_iter_andp
| FROM_sepcon_TO_iter_sepcon
| FROM_empty_set_TO_empty_context
| FROM_join_TO_sepcon
| FROM_model_TO_impp 
| FROM_model_TO_andp
| FROM_model_TO_orp
| FROM_model_TO_coq_prop
| FROM_unit_TO_emp
| FROM_model_TO_truep
| FROM_join_TO_wand
| FROM_model_TO_exp
| FROM_model_TO_allp
.

Definition primitive_connectives := map primitive_connective.
Definition predicate_over_states := ___predicate_over_states false.
Definition mpredicate_over_states := ___predicate_over_states true.
Definition predicates_over_states := map predicate_over_states.
Definition mpredicates_over_states := map mpredicate_over_states.

Inductive how_judgement :=
| primitive_judgement (j: judgement)
| ___USE_valid_FOR_provable (mono: bool)
| ___USE_consequence_FOR_derivable (mono fin: bool)
| FROM_provable_TO_derivable
| FROM_derivable_TO_provable
| FROM_provable_TO_derivable1
| FROM_provable_TO_logic_equiv
| FROM_derivable1_TO_logic_equiv
| FROM_derivable1_TO_provable
| FROM_model_TO_provable
| FROM_model_TO_derivable1
.

Definition USE_valid_FOR_provable := ___USE_valid_FOR_provable false.
Definition USE_mono_valid_FOR_provable := ___USE_valid_FOR_provable true.
Definition USE_conseq_FOR_derivable :=
  ___USE_consequence_FOR_derivable false false.
Definition USE_mono_conseq_FOR_derivable :=
  ___USE_consequence_FOR_derivable true false.
Definition USE_fin_conseq_FOR_derivable :=
  ___USE_consequence_FOR_derivable false true.
Definition USE_mono_fin_conseq_FOR_derivable :=
  ___USE_consequence_FOR_derivable true true.

Inductive rule_class :=
| provability_OF_impp
| provability_OF_andp
| provability_OF_orp
| provability_OF_falsep
| provability_OF_truep
| provability_OF_iffp
| provability_OF_negp
| provability_OF_iter_andp
| provability_OF_de_morgan
| provability_OF_godel_dummett
| provability_OF_classical_logic
| provability_OF_classical_logic_peirce
| provability_OF_classical_logic_by_contra
| provability_OF_classical_logic_double_negp
| provability_OF_classical_logic_canalysis
| provability_OF_classical_logic_EM
| provability_OF_classical_logic_impp_orp
| provability_OF_coq_prop
| provability_OF_coq_prop_impp
| provability_OF_sepcon_rule
| provability_OF_wand_rule
| provability_OF_emp_rule
| provability_OF_iter_sepcon
| provability_OF_sepcon_orp_rule
| provability_OF_sepcon_falsep_rule
| provability_OF_sepcon_coq_prop
| provability_OF_sepcon_rule_AS_weak
| provability_OF_sepcon_rule_AS_weak_iffp
| provability_OF_sepcon_rule_AS_mono
| provability_OF_emp_rule_AS_iffp
| provability_OF_garbage_collected_sl
| derivitive_OF_basic_setting
| derivitive_OF_finite_derivation
| derivitive_OF_impp
| derivitive_OF_andp
| derivitive_OF_orp
| derivitive_OF_falsep
| derivitive_OF_truep
| derivitive_OF_iffp
| derivitive_OF_negp
| derivitive_OF_de_morgan
| derivitive_OF_godel_dummett
| derivitive_OF_classical_logic
| derivitive1_OF_basic_setting
| derivitive1_OF_impp
| derivitive1_OF_impp_andp_adjoint
| derivitive1_OF_andp
| derivitive1_OF_orp
| derivitive1_OF_falsep
| derivitive1_OF_truep
| derivitive1_OF_iffp
| derivitive1_OF_negp
| derivitive1_OF_impp_negp
| derivitive1_OF_sepcon
| derivitive1_OF_wand
| derivitive1_OF_emp
| derivitive1_OF_sepcon_orp_rule
| derivitive1_OF_sepcon_falsep_rule
| equivalence_OF_basic_setting
| equivalence_OF_impp
| equivalence_OF_andp
| equivalence_OF_orp
| equivalence_OF_sepcon
| equivalence_OF_truep_andp
| equivalence_OF_emp
| corability_OF_basic_setting
| corability_OF_coq_prop
| GEN_iffp_FROM_andp_impp
| GEN_truep_FROM_falsep_impp
| GEN_negp_FROM_falsep_impp
| GEN_orp_FROM_impp_negp
| GEN_truep_FROM_impp_self
| GEN_truep_FROM_negp_falsep
| GEN_falsep_FROM_negp_truep
| GEN_iter_andp_FROM_fold_left_andp
| GEN_iter_andp_FROM_fold_right_andp
| GEN_iter_sepcon_FROM_fold_left_sepcon
| GEN_iter_sepcon_FROM_fold_right_sepcon
| GEN_derivable_FROM_provable
| GEN_provable_FROM_derivable
| GEN_derivable1_FROM_provable
| GEN_logic_equiv_FROM_provable
| GEN_logic_equiv_FROM_derivable1
| GEN_sepcon_FROM_join
| join_is_SA
| GEN_impp_FROM_model
| GEN_provable_FROM_model
| GEN_andp_FROM_model
| GEN_orp_FROM_model
| GEN_coq_prop_FROM_model
| GEN_emp_FROM_unit
| GEN_truep_FROM_model
| deduction_derived_neg
| derivitive1_OF_exp
| derivitive1_OF_allp
| deduction_exp_and
| GEN_wand_FROM_model
| GEN_derivable1_FROM_model
| GEN_exp_FROM_model
| GEN_all_FROM_model
| derivitive1_OF_iter_sepcon
| deduction_exp_sepcon
| IterSepconFlatten
| unit_join_rel
| derivitive1_OF_coq_prop
| sepcon_and_inj
| sepcon_and_inj_ext
| iter_sepcon_and_inj
| derivitive_OF_basic_setting_weak
| derivitive_OF_basic_setting_subst1
| derivitive_OF_basic_setting_subst 
| derivitive_OF_basic_setting_fw
| GEN_provable_FROM_derivable1
.

(** * What users need not to know **)
(** ** Parameters *)

Inductive how_type :=
| primitive_type (t: type)
| FROM_predicate_over_states_TO_expr
| FROM_mpredicate_over_states_TO_expr
| FROM_ensemble_expr_TO_context
| FROM_model_TO_expr
.

Notation "'ht_restriction'" := (list how_type).

Inductive type_class :=
| Language
| Model
.

Inductive connective_class :=
| MinimumLanguage
| AndLanguage
| OrLanguage
| FalseLanguage
| TrueLanguage
| IffLanguage
| NegLanguage
| CoqPropLanguage
| SepconLanguage
| WandLanguage
| EmpLanguage
| IterAndLanguage
| IterSepconLanguage
| Join
| Unit
| Relation
| ShallowExistsLanguage
| ShallowForallLanguage
.

Inductive judgement_class :=
| Provable
| Derivable
| Derivable1
| LogicEquiv
| Corable
.

Inductive any_class :=
| TC (tc: type_class)
| CC (cc: connective_class)
| JC (jc: judgement_class)
| RC (rc: rule_class)
.

Definition how_instance: Type := nat.

Definition primary_rule: Type := nat.

Definition derived_rule: Type := nat.

(** ** Output *)

Module Output.
Record output: Type := {
  primitive_types: list type;
  transparent_types: list type;
  derived_types: list how_type;
  primitive_connectives: list connective;
  transparent_connectives: list connective;
  derived_connectives: list how_connective;
  primitive_judgements: list judgement;
  transparent_judgements: list judgement;
  derived_judgements: list how_judgement;
  primitive_classes: list any_class;
  refl_classes_for_derivation: list any_class;
  how_derive_classes: list how_instance;
  primary_rules: list primary_rule;
  derived_primary_rules: list primary_rule;
  derived_derived_rules: list derived_rule;
  derived_rules_as_instance: list derived_rule
}.
End Output.

(** ** Auxiliary functions *)

Definition force_val_list {T: Type} (ol: option (list T)): list T :=
  match ol with
  | Some l => l
  | None => nil
  end.

Definition is_Some {T: Type} (o: option T): bool :=
  match o with
  | Some _ => true
  | _ => false
  end.

Definition is_nil {T: Type} (l: list T): bool :=
  match l with
  | nil => true
  | _ => false
  end.

Fixpoint valid_sublist {T: Type} (ol: list (option T)): list T :=
  match ol with
  | nil => nil
  | (Some x) :: ol0 => x :: valid_sublist ol0
  | None :: ol0 => valid_sublist ol0
  end.

(* TODO Check Standard Library *)
Module Type DecTypeSig.

  Parameter Inline t: Type.

  Parameter eqb: t -> t -> bool.

  Axiom eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).

End DecTypeSig.

Module ListFunOverDecType (DTS: DecTypeSig).
Import DTS.
  
Definition shrink (l: list t): list t :=
  fold_right (fun x l => if (existsb (eqb x) l) then l else x :: l) [] l.

Definition set_minus (l1 l2: list t): list t :=
  filter (fun x => negb (existsb (eqb x) l2)) l1.

Definition set_minus1 (l: list t) (x: t): list t :=
  filter (fun x0 => negb (eqb x0 x)) l.

Definition test_element (x: t) (l: list t): bool :=
  existsb (eqb x) l.

Fixpoint test_no_dup (l: list t): bool :=
  match l with
  | nil => true
  | x :: l0 => negb (test_element x l0) && test_no_dup l0
  end.

Definition test_sublist (l1 l2: list t): bool :=
  forallb (fun x => test_element x l2) l1.

Fixpoint inv_with_hint {A: Type} (f: A -> t) (hint: list A) (x: t): option A :=
  match hint with
  | nil => None
  | a :: hint0 => if eqb x (f a) then Some a else inv_with_hint f hint0 x
  end.

Definition map_inv_with_hint {A: Type}
           (f: A -> t) (hint: list A) (l: list t): list A :=
  valid_sublist (map (inv_with_hint f hint) l).

Fixpoint inj_with_hint {A: Type} (l1: list t) (l2: list A) (x: t) :=
  match l1, l2 with
  | cons a l1', cons v l2' =>
    if eqb a x then Some v else inj_with_hint l1' l2' x
  | _, _ => None
  end.

Definition map_with_hint {A: Type} (l1: list t) (l2: list A) (l: list t) :=
  valid_sublist (map (inj_with_hint l1 l2) l).

Section topo_sort.

Fixpoint pick_one {A: Type} (cur: list (list t * t * A)): option (t * A) :=
  match cur with
  | nil => None
  | (nil, x, a) :: _ => Some (x, a)
  | _ :: cur0 => pick_one cur0
  end.

Definition reduce_one {A: Type}
           (cur: list (list t * t * A)) (x: t): list (list t * t * A) :=
  filter
    (fun d => negb (eqb x (snd (fst d))))
    (map (fun d => (set_minus1 (fst (fst d)) x, snd (fst d), snd d)) cur).

Fixpoint topo_sort_rec {A: Type}
         (cur: list (list t * t * A)) (res: list A) (n: nat): list A :=
  match n with
  | O => res
  | S n0 => let ox := pick_one cur in
            match ox with
            | None => res
            | Some (x, a) => let cur0 := reduce_one cur x in
                             topo_sort_rec cur0 (a :: res) n0
            end
  end.

Definition topo_sort {A: Type} (diag: list (list t * t * A)) :=
  let res := topo_sort_rec diag nil (length diag) in
  rev res.

End topo_sort.

End ListFunOverDecType.

Module CType <: DecTypeSig.

Definition t := type.

Definition eqb (t1 t2: type) :=
  match t1, t2 with
  | expr, expr => true
  | context, context => true
  | model, model => true
  | _, _ => false
  end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End CType.

Module CTypeList := ListFunOverDecType CType.

Module HowType <: DecTypeSig.

Definition t := how_type.

Definition eqb (ht1 ht2: how_type) :=
  match ht1, ht2 with
  | primitive_type t1, primitive_type t2 => CType.eqb t1 t2
  | FROM_predicate_over_states_TO_expr, FROM_predicate_over_states_TO_expr => true
  | FROM_mpredicate_over_states_TO_expr, FROM_mpredicate_over_states_TO_expr => true
  | FROM_ensemble_expr_TO_context, FROM_ensemble_expr_TO_context => true
  | FROM_model_TO_expr, FROM_model_TO_expr => true
  | _, _ => false
  end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
  pose proof CType.eqb_spec t0 t1.
  destruct (CType.eqb t0 t1).
  + inversion H; constructor.
    subst; auto.
  + inversion H; constructor.
    congruence.
Qed.

End HowType.

Module HowTypeList := ListFunOverDecType HowType.

Module Connective <: DecTypeSig.

Definition t := connective.

Definition eqb (c1 c2: connective) :=
match c1, c2 with
| impp, impp
| andp, andp
| orp, orp
| falsep, falsep
| truep, truep
| negp, negp
| iffp, iffp
| coq_prop, coq_prop
| sepcon, sepcon
| wand, wand
| emp, emp
| multi_imp, multi_imp
| iter_andp, iter_andp
| iter_sepcon, iter_sepcon
| empty_context, empty_context => true
| join, join => true
| is_unit, is_unit => true
| Krelation, Krelation => true
| exp, exp => true
| allp, allp => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End Connective.

Module ConnectiveList := ListFunOverDecType Connective.

Module Judgement <: DecTypeSig.

Definition t := judgement.

Definition eqb (j1 j2: judgement) :=
match j1, j2 with
| provable, provable
| derivable, derivable
| derivable1, derivable1
| logic_equiv, logic_equiv
| corable, corable => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End Judgement.

Module JudgementList := ListFunOverDecType Judgement.

Module CTypeClass.

Definition t := type_class.

Definition eqb (tc1 tc2: type_class) :=
match tc1, tc2 with
| Language, Language => true
| Model, Model => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End CTypeClass.

Module CTypeClassList := ListFunOverDecType CTypeClass.

Module ConnectiveClass.

Definition t := connective_class.

Definition eqb (cc1 cc2: connective_class) :=
match cc1, cc2 with
| MinimumLanguage, MinimumLanguage
| AndLanguage, AndLanguage
| OrLanguage, OrLanguage
| FalseLanguage, FalseLanguage
| TrueLanguage, TrueLanguage
| IffLanguage, IffLanguage
| NegLanguage, NegLanguage
| CoqPropLanguage, CoqPropLanguage
| SepconLanguage, SepconLanguage
| WandLanguage, WandLanguage
| EmpLanguage, EmpLanguage
| IterAndLanguage, IterAndLanguage
| IterSepconLanguage, IterSepconLanguage 
| Join, Join 
| Unit, Unit 
| Relation, Relation 
| ShallowExistsLanguage, ShallowExistsLanguage => true
| ShallowForallLanguage, ShallowForallLanguage => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End ConnectiveClass.

Module ConnectiveClassList := ListFunOverDecType ConnectiveClass.

Module JudgementClass.

Definition t := judgement_class.

Definition eqb (jc1 jc2: judgement_class) :=
match jc1, jc2 with
| Provable, Provable
| Derivable, Derivable
| Derivable1, Derivable1
| LogicEquiv, LogicEquiv
| Corable, Corable => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End JudgementClass.

Module JudgementClassList := ListFunOverDecType JudgementClass.

Module RuleClass.

Definition t := rule_class.

Definition eqb (rc1 rc2: rule_class) :=
match rc1, rc2 with
| provability_OF_impp, provability_OF_impp
| provability_OF_andp, provability_OF_andp
| provability_OF_orp, provability_OF_orp
| provability_OF_falsep, provability_OF_falsep
| provability_OF_truep, provability_OF_truep
| provability_OF_iffp, provability_OF_iffp
| provability_OF_negp, provability_OF_negp
| provability_OF_iter_andp, provability_OF_iter_andp
| provability_OF_de_morgan, provability_OF_de_morgan
| provability_OF_godel_dummett, provability_OF_godel_dummett
| provability_OF_classical_logic, provability_OF_classical_logic
| provability_OF_classical_logic_peirce, provability_OF_classical_logic_peirce
| provability_OF_classical_logic_by_contra, provability_OF_classical_logic_by_contra
| provability_OF_classical_logic_double_negp, provability_OF_classical_logic_double_negp
| provability_OF_classical_logic_canalysis, provability_OF_classical_logic_canalysis
| provability_OF_classical_logic_EM, provability_OF_classical_logic_EM
| provability_OF_classical_logic_impp_orp, provability_OF_classical_logic_impp_orp
| provability_OF_coq_prop, provability_OF_coq_prop
| provability_OF_coq_prop_impp, provability_OF_coq_prop_impp
| provability_OF_sepcon_rule, provability_OF_sepcon_rule
| provability_OF_wand_rule, provability_OF_wand_rule
| provability_OF_emp_rule, provability_OF_emp_rule
| provability_OF_iter_sepcon, provability_OF_iter_sepcon => true
| provability_OF_sepcon_orp_rule, provability_OF_sepcon_orp_rule => true
| provability_OF_sepcon_falsep_rule, provability_OF_sepcon_falsep_rule => true
| provability_OF_sepcon_coq_prop, provability_OF_sepcon_coq_prop => true
| provability_OF_sepcon_rule_AS_weak, provability_OF_sepcon_rule_AS_weak => true
| provability_OF_sepcon_rule_AS_weak_iffp, provability_OF_sepcon_rule_AS_weak_iffp => true
| provability_OF_sepcon_rule_AS_mono, provability_OF_sepcon_rule_AS_mono => true
| provability_OF_emp_rule_AS_iffp, provability_OF_emp_rule_AS_iffp => true
| provability_OF_garbage_collected_sl, provability_OF_garbage_collected_sl => true
| derivitive_OF_basic_setting, derivitive_OF_basic_setting
| derivitive_OF_finite_derivation, derivitive_OF_finite_derivation
| derivitive_OF_impp, derivitive_OF_impp
| derivitive_OF_andp, derivitive_OF_andp
| derivitive_OF_orp, derivitive_OF_orp
| derivitive_OF_falsep, derivitive_OF_falsep
| derivitive_OF_truep, derivitive_OF_truep
| derivitive_OF_iffp, derivitive_OF_iffp
| derivitive_OF_negp, derivitive_OF_negp
| derivitive_OF_de_morgan, derivitive_OF_de_morgan
| derivitive_OF_godel_dummett, derivitive_OF_godel_dummett
| derivitive_OF_classical_logic, derivitive_OF_classical_logic
| derivitive1_OF_basic_setting, derivitive1_OF_basic_setting
| derivitive1_OF_impp, derivitive1_OF_impp
| derivitive1_OF_impp_andp_adjoint, derivitive1_OF_impp_andp_adjoint
| derivitive1_OF_andp, derivitive1_OF_andp
| derivitive1_OF_orp, derivitive1_OF_orp
| derivitive1_OF_falsep, derivitive1_OF_falsep
| derivitive1_OF_truep, derivitive1_OF_truep
| derivitive1_OF_iffp, derivitive1_OF_iffp
| derivitive1_OF_negp, derivitive1_OF_negp
| derivitive1_OF_impp_negp, derivitive1_OF_impp_negp
| derivitive1_OF_sepcon, derivitive1_OF_sepcon
| derivitive1_OF_wand, derivitive1_OF_wand
| derivitive1_OF_emp, derivitive1_OF_emp
| derivitive1_OF_sepcon_orp_rule, derivitive1_OF_sepcon_orp_rule
| derivitive1_OF_sepcon_falsep_rule, derivitive1_OF_sepcon_falsep_rule
| equivalence_OF_basic_setting, equivalence_OF_basic_setting
| equivalence_OF_impp, equivalence_OF_impp
| equivalence_OF_andp, equivalence_OF_andp
| equivalence_OF_orp, equivalence_OF_orp
| equivalence_OF_sepcon, equivalence_OF_sepcon
| equivalence_OF_truep_andp, equivalence_OF_truep_andp
| equivalence_OF_emp, equivalence_OF_emp
| corability_OF_basic_setting, corability_OF_basic_setting
| corability_OF_coq_prop, corability_OF_coq_prop
| GEN_iffp_FROM_andp_impp, GEN_iffp_FROM_andp_impp
| GEN_truep_FROM_falsep_impp, GEN_truep_FROM_falsep_impp
| GEN_negp_FROM_falsep_impp, GEN_negp_FROM_falsep_impp
| GEN_orp_FROM_impp_negp, GEN_orp_FROM_impp_negp
| GEN_truep_FROM_impp_self, GEN_truep_FROM_impp_self
| GEN_truep_FROM_negp_falsep, GEN_truep_FROM_negp_falsep
| GEN_falsep_FROM_negp_truep, GEN_falsep_FROM_negp_truep
| GEN_iter_andp_FROM_fold_left_andp, GEN_iter_andp_FROM_fold_left_andp
| GEN_iter_andp_FROM_fold_right_andp, GEN_iter_andp_FROM_fold_right_andp
| GEN_iter_sepcon_FROM_fold_left_sepcon, GEN_iter_sepcon_FROM_fold_left_sepcon
| GEN_iter_sepcon_FROM_fold_right_sepcon, GEN_iter_sepcon_FROM_fold_right_sepcon
| GEN_derivable_FROM_provable, GEN_derivable_FROM_provable
| GEN_provable_FROM_derivable, GEN_provable_FROM_derivable
| GEN_derivable1_FROM_provable, GEN_derivable1_FROM_provable
| GEN_logic_equiv_FROM_provable, GEN_logic_equiv_FROM_provable
| GEN_logic_equiv_FROM_derivable1, GEN_logic_equiv_FROM_derivable1 => true
| GEN_sepcon_FROM_join, GEN_sepcon_FROM_join => true
| GEN_impp_FROM_model, GEN_impp_FROM_model => true
| GEN_provable_FROM_model, GEN_provable_FROM_model => true
| join_is_SA, join_is_SA => true
| GEN_andp_FROM_model, GEN_andp_FROM_model => true
| GEN_orp_FROM_model, GEN_orp_FROM_model => true
| GEN_coq_prop_FROM_model, GEN_coq_prop_FROM_model => true 
| GEN_emp_FROM_unit, GEN_emp_FROM_unit => true
| GEN_truep_FROM_model, GEN_truep_FROM_model => true
| deduction_derived_neg, deduction_derived_neg => true
| derivitive1_OF_exp, derivitive1_OF_exp => true
| derivitive1_OF_allp, derivitive1_OF_allp => true
| deduction_exp_and, deduction_exp_and => true 
| GEN_wand_FROM_model, GEN_wand_FROM_model => true
| GEN_derivable1_FROM_model, GEN_derivable1_FROM_model => true
| GEN_exp_FROM_model, GEN_exp_FROM_model => true
| GEN_all_FROM_model, GEN_all_FROM_model => true
| derivitive1_OF_iter_sepcon, derivitive1_OF_iter_sepcon => true
| deduction_exp_sepcon, deduction_exp_sepcon => true
| IterSepconFlatten, IterSepconFlatten => true 
| unit_join_rel, unit_join_rel => true
| derivitive1_OF_coq_prop, derivitive1_OF_coq_prop => true
| sepcon_and_inj, sepcon_and_inj => true 
| sepcon_and_inj_ext, sepcon_and_inj_ext => true 
| iter_sepcon_and_inj, iter_sepcon_and_inj => true
| derivitive_OF_basic_setting_weak, derivitive_OF_basic_setting_weak => true 
| derivitive_OF_basic_setting_subst1, derivitive_OF_basic_setting_subst1 => true 
| derivitive_OF_basic_setting_subst, derivitive_OF_basic_setting_subst => true 
| derivitive_OF_basic_setting_fw, derivitive_OF_basic_setting_fw => true
| GEN_provable_FROM_derivable1, GEN_provable_FROM_derivable1 => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End RuleClass.

Module RuleClassList := ListFunOverDecType RuleClass.

Module AllClass.

Definition t := any_class.

Definition eqb (ac1 ac2: any_class) :=
match ac1, ac2 with
| TC tc1, TC tc2 => CTypeClass.eqb tc1 tc2
| CC cc1, CC cc2 => ConnectiveClass.eqb cc1 cc2
| JC jc1, JC jc2 => JudgementClass.eqb jc1 jc2
| RC rc1, RC rc2 => RuleClass.eqb rc1 rc2
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
  + pose proof CTypeClass.eqb_spec tc tc0.
    destruct (CTypeClass.eqb tc tc0); inversion H; constructor; congruence.
  + pose proof ConnectiveClass.eqb_spec cc cc0.
    destruct (ConnectiveClass.eqb cc cc0); inversion H; constructor; congruence.
  + pose proof JudgementClass.eqb_spec jc jc0.
    destruct (JudgementClass.eqb jc jc0); inversion H; constructor; congruence.
  + pose proof RuleClass.eqb_spec rc rc0.
    destruct (RuleClass.eqb rc rc0); inversion H; constructor; congruence.
Qed.

End AllClass.

Module AllClassList := ListFunOverDecType AllClass.

Module NatList := ListFunOverDecType PeanoNat.Nat.
