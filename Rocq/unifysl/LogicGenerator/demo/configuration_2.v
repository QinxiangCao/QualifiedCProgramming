Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ].

Definition transparent_names :=
  [expr:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ].
