Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [ primitive_connective join;
    FROM_model_TO_impp;
    FROM_join_TO_sepcon].

Definition how_judgements :=
  [ FROM_model_TO_provable ].

Definition transparent_names :=
  [ provable : parameter].

Definition primitive_rule_classes :=
  [ join_is_SA ].
  
  