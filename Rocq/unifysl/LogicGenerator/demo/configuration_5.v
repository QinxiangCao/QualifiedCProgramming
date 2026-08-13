Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective coq_prop
  ;primitive_connective sepcon
  ;primitive_connective wand
  ;primitive_connective emp
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
  ;FROM_empty_set_TO_empty_context
  ;FROM_andp_TO_iter_andp
  ;FROM_sepcon_TO_iter_sepcon
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ;primitive_judgement corable
  ;FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_andp
  ; provability_OF_orp
  ; provability_OF_falsep
  ; provability_OF_coq_prop
  ; provability_OF_classical_logic
  ; provability_OF_sepcon_rule_AS_weak_iffp
  ; provability_OF_wand_rule
  ; provability_OF_emp_rule_AS_iffp
  ; corability_OF_basic_setting
  ; corability_OF_coq_prop
  ].
