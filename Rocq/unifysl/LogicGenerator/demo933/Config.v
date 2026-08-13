Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [ primitive_connective join
  ; primitive_connective is_unit
  ; FROM_join_TO_sepcon 
  ; FROM_join_TO_wand 
  ; FROM_model_TO_orp
  ; FROM_model_TO_andp
  ; FROM_model_TO_impp
  ; FROM_model_TO_exp
  ; FROM_model_TO_allp
  ; FROM_unit_TO_emp
  ; FROM_model_TO_coq_prop
  ; FROM_model_TO_truep
  ; FROM_impp_TO_multi_imp
  ; FROM_sepcon_TO_iter_sepcon
  ; FROM_andp_impp_TO_iffp
  ].

Definition how_judgements :=
  [ FROM_model_TO_derivable1;
    FROM_derivable1_TO_provable;
    FROM_derivable1_TO_logic_equiv
  ].

Definition transparent_names :=
  [ expr : parameter ].

Definition primitive_rule_classes :=
  [ join_is_SA 
  ; unit_join_rel
  (* ; derivitive1_OF_basic_setting *)
  ].