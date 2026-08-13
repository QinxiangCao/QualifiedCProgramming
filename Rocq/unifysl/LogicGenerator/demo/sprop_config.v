Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [ primitive_connective falsep
  ; primitive_connective truep
  ; primitive_connective negp
  ; primitive_connective andp
  ; primitive_connective orp 
  ; primitive_connective impp 
  ; FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [ primitive_judgement derivable ].

Definition transparent_names :=
  [ expr : parameter ].

Definition primitive_rule_classes :=
  [ derivitive_OF_falsep
  ; derivitive_OF_truep 
  (* ; derivitive_OF_basic_setting *)
  ; derivitive_OF_basic_setting_weak
  ; derivitive_OF_basic_setting_subst1
  ; derivitive_OF_basic_setting_fw
  ; derivitive_OF_classical_logic
  ; derivitive_OF_andp 
  ; derivitive_OF_orp   
  ; derivitive_OF_impp
  ].
