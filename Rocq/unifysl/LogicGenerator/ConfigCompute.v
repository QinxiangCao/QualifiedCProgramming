Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.ConfigLang.
Require Import Logic.LogicGenerator.ConfigDenot.

Import ListNotations.

(** ** Attributes *)

(* infered how-type of how-connective *)
Definition ITOC (hc: how_connective): ht_restriction :=
match hc with
| primitive_connective c => []
| ___predicate_over_states false c => [FROM_predicate_over_states_TO_expr]
| ___predicate_over_states true c => [FROM_mpredicate_over_states_TO_expr]
| FROM_andp_impp_TO_iffp => []
| FROM_falsep_impp_TO_negp => []
| FROM_falsep_impp_TO_truep => []
| FROM_impp_negp_TO_orp => []
| FROM_negp_falsep_TO_truep => []
| FROM_negp_truep_TO_falsep => []
| FROM_impp_TO_multi_imp => []
| FROM_andp_TO_iter_andp => []
| FROM_sepcon_TO_iter_sepcon => []
| FROM_empty_set_TO_empty_context => [FROM_ensemble_expr_TO_context]
| FROM_join_TO_sepcon => [FROM_model_TO_expr]
| FROM_model_TO_impp => [FROM_model_TO_expr]
| FROM_model_TO_andp => [FROM_model_TO_expr]
| FROM_model_TO_orp => [FROM_model_TO_expr]
| FROM_model_TO_coq_prop => [FROM_model_TO_expr]
| FROM_unit_TO_emp => [FROM_model_TO_expr]
| FROM_model_TO_truep => [FROM_model_TO_expr]
| FROM_join_TO_wand => [FROM_model_TO_expr]
| FROM_model_TO_exp => [FROM_model_TO_expr]
| FROM_model_TO_allp => [FROM_model_TO_expr]
end.

(* infered how-type of how-judgement *)
Definition ITOJ (hj: how_judgement): ht_restriction :=
match hj with
| primitive_judgement j =>
    match j with
    | derivable => [FROM_ensemble_expr_TO_context]
    | _ => []
    end
| ___USE_valid_FOR_provable false => [FROM_predicate_over_states_TO_expr]
| ___USE_valid_FOR_provable true => [FROM_mpredicate_over_states_TO_expr]
| ___USE_consequence_FOR_derivable false _ => [FROM_predicate_over_states_TO_expr
                                              ;FROM_ensemble_expr_TO_context
                                              ]
| ___USE_consequence_FOR_derivable true _ => [FROM_mpredicate_over_states_TO_expr
                                             ;FROM_ensemble_expr_TO_context
                                             ]
| FROM_provable_TO_derivable => [FROM_ensemble_expr_TO_context]
| FROM_derivable_TO_provable => [FROM_ensemble_expr_TO_context]
| FROM_provable_TO_derivable1 => []
| FROM_provable_TO_logic_equiv => []
| FROM_derivable1_TO_logic_equiv => []
| FROM_model_TO_provable => [FROM_model_TO_expr]
| FROM_model_TO_derivable1 => [FROM_model_TO_expr]
| FROM_derivable1_TO_provable => []
end.

(* generated connective *)
Definition GenC (hc: how_connective): connective :=
match hc with
| primitive_connective c => c
| ___predicate_over_states _ c => c
| FROM_andp_impp_TO_iffp => iffp
| FROM_falsep_impp_TO_negp => negp
| FROM_falsep_impp_TO_truep => truep
| FROM_impp_negp_TO_orp => orp
| FROM_negp_falsep_TO_truep => truep
| FROM_negp_truep_TO_falsep => falsep
| FROM_impp_TO_multi_imp => multi_imp
| FROM_andp_TO_iter_andp => iter_andp
| FROM_sepcon_TO_iter_sepcon => iter_sepcon
| FROM_empty_set_TO_empty_context => empty_context
| FROM_join_TO_sepcon => sepcon
| FROM_model_TO_impp => impp
| FROM_model_TO_andp => andp
| FROM_model_TO_orp => orp
| FROM_model_TO_coq_prop => coq_prop
| FROM_unit_TO_emp => emp
| FROM_model_TO_truep => truep
| FROM_join_TO_wand => wand
| FROM_model_TO_exp => exp
| FROM_model_TO_allp => allp
end.

(* generated judgement *)
Definition GenJ (hj: how_judgement): judgement :=
match hj with
| primitive_judgement j => j
| ___USE_valid_FOR_provable _ => provable
| ___USE_consequence_FOR_derivable _ _ => derivable
| FROM_provable_TO_derivable => derivable
| FROM_derivable_TO_provable => provable
| FROM_provable_TO_derivable1 => derivable1
| FROM_provable_TO_logic_equiv => logic_equiv
| FROM_derivable1_TO_logic_equiv => logic_equiv
| FROM_model_TO_provable => provable
| FROM_model_TO_derivable1 => derivable1 
| FROM_derivable1_TO_provable => provable
end.

(* generated type *)
Definition GenT (ht: how_type): type :=
match ht with
| primitive_type t => t
| FROM_predicate_over_states_TO_expr => expr
| FROM_mpredicate_over_states_TO_expr => expr
| FROM_ensemble_expr_TO_context => context
| FROM_model_TO_expr => expr
end.

(* depended types of connectives *)
Definition DTOC (c: connective): list type :=
match c with
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
| iter_sepcon => [expr]
| join => [expr; model]
| empty_context => [context]
| is_unit => [expr; model]
| Krelation => [expr; model]
| exp => [expr]
| allp => [expr]
end.

(* depended types of judgements *)
Definition DTOJ (j: judgement): list type :=
match j with
| provable => [expr]
| derivable => [context; expr]
| derivable1 => [expr]
| logic_equiv => [expr]
| corable => [expr]
end.

(* dependent connectives of how-connective *)
Definition DCOC (hc: how_connective): list connective :=
match hc with
| primitive_connective c => []
| ___predicate_over_states _ c => []
| FROM_andp_impp_TO_iffp => [andp; impp]
| FROM_falsep_impp_TO_negp => [falsep; impp]
| FROM_falsep_impp_TO_truep => [falsep; impp]
| FROM_impp_negp_TO_orp => [impp; negp]
| FROM_negp_falsep_TO_truep => [negp; falsep]
| FROM_negp_truep_TO_falsep => [negp; truep]
| FROM_impp_TO_multi_imp => [impp]
| FROM_andp_TO_iter_andp => [andp; truep]
| FROM_sepcon_TO_iter_sepcon => [sepcon; emp]
| FROM_empty_set_TO_empty_context => []
| FROM_join_TO_sepcon => [join]
| FROM_model_TO_impp => []
| FROM_model_TO_andp => []
| FROM_model_TO_orp => []
| FROM_model_TO_coq_prop => []
| FROM_unit_TO_emp => [is_unit]
| FROM_model_TO_truep => []
| FROM_join_TO_wand => [join]
| FROM_model_TO_exp => []
| FROM_model_TO_allp => []
end.

(* dependent judgements of how-judgement *)
Definition DJOJ (hj: how_judgement): list judgement :=
match hj with
| primitive_judgement j => []
| ___USE_valid_FOR_provable _ => []
| ___USE_consequence_FOR_derivable _ _ => []
| FROM_provable_TO_derivable => [provable]
| FROM_derivable_TO_provable => [derivable]
| FROM_provable_TO_derivable1 => [provable]
| FROM_provable_TO_logic_equiv => [provable]
| FROM_derivable1_TO_logic_equiv => [derivable1]
| FROM_model_TO_provable => []
| FROM_model_TO_derivable1 => []
| FROM_derivable1_TO_provable => [derivable1]
end.

(* depended types of types *)
Definition DTOT (ht: how_type): list type :=
match ht with
| primitive_type t => []
| FROM_predicate_over_states_TO_expr => [model]
| FROM_mpredicate_over_states_TO_expr => [model]
| FROM_ensemble_expr_TO_context => [expr]
| FROM_model_TO_expr => [model]
end.

(* Automatically generated rule-instances from judgement derivation *)
Definition how_connective_class (hc: how_connective): option rule_class :=
match hc with
| primitive_connective c => None
| ___predicate_over_states _ _ => None
| FROM_andp_impp_TO_iffp => Some (GEN_iffp_FROM_andp_impp)
| FROM_falsep_impp_TO_truep => Some (GEN_truep_FROM_falsep_impp)
| FROM_falsep_impp_TO_negp => Some (GEN_negp_FROM_falsep_impp)
| FROM_impp_negp_TO_orp => Some (GEN_orp_FROM_impp_negp)
| FROM_negp_falsep_TO_truep => Some (GEN_truep_FROM_negp_falsep)
| FROM_negp_truep_TO_falsep => Some (GEN_falsep_FROM_negp_truep)
| FROM_impp_TO_multi_imp => None
| FROM_andp_TO_iter_andp => Some (GEN_iter_andp_FROM_fold_left_andp)
| FROM_sepcon_TO_iter_sepcon => Some (GEN_iter_sepcon_FROM_fold_left_sepcon)
| FROM_empty_set_TO_empty_context => None
| FROM_join_TO_sepcon => Some (GEN_sepcon_FROM_join)
| FROM_model_TO_impp => Some (GEN_impp_FROM_model)
| FROM_model_TO_andp => Some (GEN_andp_FROM_model)
| FROM_model_TO_orp => Some (GEN_orp_FROM_model)
| FROM_model_TO_coq_prop => Some (GEN_coq_prop_FROM_model)
| FROM_unit_TO_emp => Some (GEN_emp_FROM_unit)
| FROM_model_TO_truep => Some (GEN_truep_FROM_model)
| FROM_join_TO_wand => Some (GEN_wand_FROM_model)
| FROM_model_TO_exp => Some (GEN_exp_FROM_model)
| FROM_model_TO_allp => Some (GEN_all_FROM_model)
end.

(* Automatically generated rule-instances from judgement derivation *)
Definition how_judgement_class (hj: how_judgement): option rule_class :=
match hj with
| primitive_judgement _ => None
| ___USE_valid_FOR_provable _ => None
| ___USE_consequence_FOR_derivable _ _ => None
| FROM_provable_TO_derivable => Some GEN_derivable_FROM_provable
| FROM_derivable_TO_provable => Some GEN_provable_FROM_derivable
| FROM_provable_TO_derivable1 => Some GEN_derivable1_FROM_provable
| FROM_provable_TO_logic_equiv => Some GEN_logic_equiv_FROM_provable
| FROM_derivable1_TO_logic_equiv => Some GEN_logic_equiv_FROM_derivable1
| FROM_model_TO_provable => Some GEN_provable_FROM_model
| FROM_model_TO_derivable1 => Some GEN_derivable1_FROM_model
| FROM_derivable1_TO_provable => Some GEN_provable_FROM_derivable1
end.

Definition all_how_instances: list how_instance :=
  ConfigDenot.S.D_instance_transitions.

Definition DIOI (hi: how_instance): list any_class :=
  map snd
    (filter
       (fun p => Nat.eqb hi (fst p))
       (combine
          (fst ConfigDenot.S.D_instance_dependency_via_transition)
          (snd ConfigDenot.S.D_instance_dependency_via_transition))).

(* derived-instances' dependency diagram *)
Definition dis_diag: list (list any_class * any_class * option how_instance) :=
  combine
    (combine
      (map DIOI ConfigDenot.S.D_instance_transitions)
      ConfigDenot.S.D_instance_transition_results)
    (map Some ConfigDenot.S.D_instance_transitions).
(* Eval compute in dis_diag. *)
(* depended instances of primary proof rules *)
Definition DIOpR (pr: primary_rule): list rule_class :=
  map snd
    (filter
       (fun p => Nat.eqb pr (fst p))
       (combine
          (snd ConfigDenot.S.D_primary_rule_dependency_via_ins)
          (fst ConfigDenot.S.D_primary_rule_dependency_via_ins))).

(* depended instances of derived proof rules *)
Definition DIOdR (dr: derived_rule): list any_class :=
  map snd
    (filter
       (fun p => Nat.eqb dr (fst p))
       (combine
          (fst ConfigDenot.S.D_derived_rules_dependency_via_ins)
          (snd ConfigDenot.S.D_derived_rules_dependency_via_ins))).

(** ** Checking functions **)

Definition ht_restriction_merge (r1 r2: ht_restriction): ht_restriction :=
  r1 ++ r2.

Definition ht_restriction_feasible (r: ht_restriction): bool :=
  Nat.eqb (length (HowTypeList.shrink r)) (length (CTypeList.shrink (map GenT r))).

Definition parameter2type (p: parameter) :=
  match p with
  | TP t => Some t
  | _ => None
  end.

Definition parameter2connective (p: parameter) :=
  match p with
  | CP c => Some c
  | _ => None
  end.

Definition parameter2judgement (p: parameter) :=
  match p with
  | JP j => Some j
  | _ => None
  end.

Definition pick_types (p : list parameter): list type :=
  valid_sublist (map parameter2type p).

Definition pick_connectives (p : list parameter): list connective :=
  valid_sublist (map parameter2connective p).

Definition pick_judgements (p : list parameter): list judgement :=
  valid_sublist (map parameter2judgement p).

Definition is_primitive_type (ht: how_type): option type :=
  match ht with
  | primitive_type t => Some t
  | _ => None
  end.

Definition is_primitive_connective (hc: how_connective): option connective :=
  match hc with
  | primitive_connective c => Some c
  | _ => None
  end.

Definition is_primitive_judgement (hj: how_judgement): option judgement :=
  match hj with
  | primitive_judgement j => Some j
  | _ => None
  end.

Section ComputeHT.

Variable hcs : list how_connective.
Variable hjs : list how_judgement.
(* Definition hcs := [FROM_join_TO_sepcon; FROM_join_TO_wand; FROM_model_TO_exp].*)
(* Definition hjs := [FROM_model_TO_provable; FROM_provable_TO_derivable1; FROM_provable_TO_logic_equiv; FROM_derivable1_TO_logic_equiv]. *)
Let cs := map GenC hcs.
(* Eval compute in cs. *)
Let js := map GenJ hjs.

Let hcs_no_dup :=
  ConnectiveList.test_no_dup cs.

Let hjs_no_dup :=
  JudgementList.test_no_dup js.

Let inferred_hts :=
  HowTypeList.shrink (concat (map ITOC hcs ++ map ITOJ hjs)).

Let feasible :=
  ht_restriction_feasible inferred_hts.

Definition ts :=
  CTypeList.shrink (concat (map DTOC cs ++ map DTOJ js)).
(* Eval cbv in ts. *)
Let hts :=
  inferred_hts ++
  map primitive_type (CTypeList.set_minus ts (map GenT inferred_hts)).

Let ts_diag :=
  map (fun ht => (DTOT ht, GenT ht, ht)) hts.

Let cs_diag :=
  map (fun hc => (DCOC hc, GenC hc, hc)) hcs.

Let js_diag :=
  map (fun hj => (DJOJ hj, GenJ hj, hj)) hjs.

Let primitive_ts :=
  valid_sublist (map is_primitive_type hts).

Let primitive_cs :=
  valid_sublist (map is_primitive_connective hcs).

Let primitive_js :=
  valid_sublist (map is_primitive_judgement hjs).

Let ts_order :=
  CTypeList.topo_sort ts_diag.

Let cs_order :=
  ConnectiveList.topo_sort cs_diag.

Let js_order :=
  JudgementList.topo_sort js_diag.

Let derived_ts :=
  CTypeList.map_inv_with_hint GenT hts
    (CTypeList.set_minus (map GenT ts_order) primitive_ts).

Let derived_cs :=
  ConnectiveList.map_inv_with_hint GenC hcs
    (ConnectiveList.set_minus (map GenC cs_order) primitive_cs).

Let derived_js :=
  JudgementList.map_inv_with_hint GenJ hjs
    (JudgementList.set_minus (map GenJ js_order) primitive_js).

Variable transparent_names: list parameter.

Let transparent_ts :=
  pick_types transparent_names.

Let transparent_cs :=
  pick_connectives transparent_names.

Let transparent_js :=
  pick_judgements transparent_names.

Let legal_tt :=
  (CTypeList.test_sublist transparent_ts primitive_ts &&
   CTypeList.test_no_dup transparent_ts)%bool.

Let legal_tc :=
  (ConnectiveList.test_sublist transparent_cs primitive_cs &&
   ConnectiveList.test_no_dup transparent_cs)%bool.

Let legal_tj :=
  (JudgementList.test_sublist transparent_js primitive_js &&
   JudgementList.test_no_dup transparent_js)%bool.

Let primitive_classes_t :=
  CTypeClassList.shrink
    (CTypeList.map_with_hint
      (snd ConfigDenot.S.D_type_dependency_via_ins)
      (fst ConfigDenot.S.D_type_dependency_via_ins)
      ts).

Let primitive_classes_c :=
  ConnectiveClassList.shrink
    (ConnectiveList.map_with_hint
      (snd ConfigDenot.S.D_connective_dependency_via_ins)
      (fst ConfigDenot.S.D_connective_dependency_via_ins)
      cs).

Let primitive_classes_j :=
  JudgementClassList.shrink
    (JudgementList.map_with_hint
      (snd ConfigDenot.S.D_judgement_dependency_via_ins)
      (fst ConfigDenot.S.D_judgement_dependency_via_ins)
      js).

Let refl_classes_c :=
  valid_sublist (map how_connective_class hcs).

Let refl_classes_j :=
  valid_sublist (map how_judgement_class hjs).

Variable primitive_classes_r' : list rule_class.

Let primitive_classes_r :=
  RuleClassList.set_minus primitive_classes_r' (refl_classes_c ++ refl_classes_j).

Let primitive_classes :=
  map TC primitive_classes_t ++
  map CC primitive_classes_c ++
  map JC primitive_classes_j ++
  map RC primitive_classes_r.

Let refl_classes :=
  map RC (refl_classes_c ++ refl_classes_j).

Let how_derive_classes :=
  valid_sublist
    (AllClassList.topo_sort
       (map (fun ac => (nil, ac, None)) (primitive_classes ++ refl_classes) ++
        dis_diag)).

Let derived_classes :=
  NatList.map_with_hint
    S.D_instance_transitions
    S.D_instance_transition_results
    how_derive_classes.
(* Eval compute in how_derive_classes. *)
Let all_classes :=
  primitive_classes ++
  refl_classes ++
  derived_classes.

Let primary_rules :=
  filter
    (fun pr => existsb (fun rc => RuleClassList.test_element rc primitive_classes_r) (DIOpR pr))
    ConfigDenot.S.D_primary_rules.
    
Let derived_derived_rules :=
  filter
    (fun dr => AllClassList.test_sublist (DIOdR dr) all_classes)
    ConfigDenot.S.D_derived_rules.

Let derived_primary_rules :=
  ConfigLang.NatList.set_minus
    (filter
      (fun pr => existsb (fun rc => AllClassList.test_element rc derived_classes) (map RC (DIOpR pr)))
      ConfigDenot.S.D_primary_rules)
    primary_rules.

Let derived_rules_as_instance :=
  filter
    (fun dr => existsb
                 (fun dr0 => Nat.eqb dr dr0)
                 ConfigDenot.S.D_derived_rules_as_instance)
    derived_derived_rules.
(* TODO resume this checking
Let needed_connective :=
  ConnectiveList.shrink (concat (map DCOP optional_rules)).
*)
Definition test_no_dup_defs := (hcs_no_dup && hjs_no_dup)%bool.
Definition test_type_defs_consistent := feasible.
Definition how_types_define := hts.
Definition test_order_loop :=
  (Nat.eqb (length ts_order) (length hts) &&
   Nat.eqb (length cs_order) (length hcs) &&
   Nat.eqb (length js_order) (length hjs))%bool.
Definition test_legal_transp_names := (legal_tt && legal_tc && legal_tj)%bool.
(* TODO resume this checking
Definition test_legal_rules := ConnectiveList.test_sublist needed_connective cs.
*)
Definition result: Output.output :=
  Output.Build_output
    primitive_ts
    transparent_ts
    derived_ts
    primitive_cs
    transparent_cs
    derived_cs
    primitive_js
    transparent_js
    derived_js
    primitive_classes
    refl_classes
    how_derive_classes
    primary_rules
    derived_primary_rules
    derived_derived_rules
    derived_rules_as_instance
    
    .

End ComputeHT.

(*
Module test1.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective sepcon
  ;primitive_connective wand
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ;FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_propositional_connectives
  ; provability_OF_classical_logic
  ; provability_OF_sepcon_rule
  ; provability_OF_emp_rule
  ].

Eval compute in (test_no_dup_defs how_connectives how_judgements).
Eval compute in (test_type_defs_consistent how_connectives how_judgements).
Eval compute in (test_order_loop how_connectives how_judgements).
Eval compute in (how_types_define how_connectives how_judgements).
Eval compute in (result how_connectives how_judgements transparent_names primitive_rule_classes).

End test1.

Module test2.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective sepcon
  ;primitive_connective wand
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [primitive_judgement derivable
  ;FROM_derivable_TO_provable
  ].

Definition transparent_names :=
  [expr:parameter; andp:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_propositional_connectives
  ; provability_OF_classical_logic
  ; provability_OF_sepcon_rule
  ; provability_OF_wand_rule
  ; provability_OF_emp_rule
  ].

Eval compute in (test_no_dup_defs how_connectives how_judgements).
Eval compute in (test_type_defs_consistent how_connectives how_judgements).
Eval compute in (test_order_loop how_connectives how_judgements).
Eval compute in (how_types_define how_connectives how_judgements).
Eval compute in (result how_connectives how_judgements transparent_names primitive_rule_classes).

End test2.

Module test3.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective sepcon
  ;primitive_connective wand
  ;primitive_connective emp
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
  ;FROM_sepcon_TO_iter_sepcon
  ;FROM_empty_set_TO_empty_context
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ;FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_propositional_connectives
  ; provability_OF_classical_logic
  ; provability_OF_sepcon_rule_AS_weak_iffp
  ; provability_OF_sepcon_rule_AS_mono
  ; provability_OF_emp_rule
  ].

Eval compute in (test_no_dup_defs how_connectives how_judgements).
Eval compute in (test_type_defs_consistent how_connectives how_judgements).
Eval compute in (test_order_loop how_connectives how_judgements).
Eval compute in (how_types_define how_connectives how_judgements).
Eval compute in (result how_connectives how_judgements transparent_names primitive_rule_classes).

End test3.

*)

