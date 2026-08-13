Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective negp
  ;primitive_connective truep
  ;FROM_impp_negp_TO_orp
  ;FROM_negp_truep_TO_falsep
  ;FROM_impp_TO_multi_imp
  ;FROM_empty_set_TO_empty_context
  ].

Definition how_judgements :=
  [ primitive_judgement provable
  ; FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter
  ;impp:parameter
  ;negp:parameter
  ;provable:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; GEN_truep_FROM_impp_self
  ; provability_OF_classical_logic_by_contra
  ].

