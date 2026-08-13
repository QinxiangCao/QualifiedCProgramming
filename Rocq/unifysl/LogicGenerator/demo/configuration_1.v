Require Import String.
Local Open Scope string.

Definition instance_para_open := true.
Definition local_lib_file := "HypotheticalExternLib".
Definition implementation_file := "implementation_1".
Definition result_module := "T".
Definition instance_para := "para".

Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
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
  ; provability_OF_andp
  ; provability_OF_orp
  ; provability_OF_falsep
  ; provability_OF_classical_logic
  ].

