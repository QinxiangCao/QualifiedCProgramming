Require Import Logic.GeneralLogic.Base.

Class SepconLanguage (L: Language): Type := {
  sepcon : expr -> expr -> expr
}.

Class WandLanguage (L: Language): Type := {
  wand : expr -> expr -> expr
}.

Class EmpLanguage (L: Language): Type := {
  emp: expr
}.

Module SeparationLogicNotation.

Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.
Notation "x -* y" := (wand x y) (at level 55, right associativity) : syntax.

End SeparationLogicNotation.

Class IterSepconLanguage (L: Language): Type := {
  iter_sepcon : list expr -> expr
}.

Class IterWandLanguage (L: Language): Type := {
  iter_wand : list expr -> expr -> expr
}.

