Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives := 
  [ primitive_connective join
  ; primitive_connective Krelation
  ; FROM_model_TO_impp
  ; FROM_model_TO_andp
  ; FROM_model_TO_orp
  ; FROM_model_TO_coq_prop
  ].

Definition how_judgements :=
  [ primitive_judgement provable ].

Definition transparent_names :=
  [ provable : parameter ].

Definition primitive_rule_classes := 
  [ join_is_SA ].