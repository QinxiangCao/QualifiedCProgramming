Require Import String.
Local Open Scope string.

Definition instance_para_open := true.
Definition local_lib_file := "bedrock2.FE310CSemantics".
Definition implementation_file := "implementation".
Definition result_module := "T".
Definition instance_para := "parameters".

Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective sepcon
  ;primitive_connective emp
  ;FROM_andp_impp_TO_iffp
  ;FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ;FROM_provable_TO_derivable1
  ;FROM_provable_TO_logic_equiv
  ].

Definition transparent_names :=
  [ expr:parameter
  ; sepcon:parameter
  ; emp:parameter
  ].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_andp
  ; provability_OF_sepcon_rule_AS_weak_iffp
  ; provability_OF_sepcon_rule_AS_mono
  ; provability_OF_emp_rule_AS_iffp
  ].
