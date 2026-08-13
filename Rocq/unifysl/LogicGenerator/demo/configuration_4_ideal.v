Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective truep
  ;primitive_connective sepcon
  ;primitive_connective emp
  ;FROM_andp_TO_iter_andp
  ;FROM_sepcon_TO_iter_sepcon
  ].

Definition how_judgements :=
  [primitive_judgement derivable1
  ].

Definition transparent_names :=
  [expr:parameter].

Definition primitive_rule_classes :=
  [ derivitive1_OF_andp
  ; derivitive1_OF_orp
  ; derivitive1_OF_falsep
  ; derivitive1_OF_truep
  ; derivitive1_OF_sepcon
  ; derivitive1_OF_emp
  ; derivitive1_OF_sepcon_orp_rule
  ; derivitive1_OF_sepcon_falsep_rule
  ].
