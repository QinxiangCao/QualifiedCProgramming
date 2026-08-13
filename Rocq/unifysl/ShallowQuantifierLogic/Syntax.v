Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.

Class ShallowExistsLanguage (L : Language) : Type := {
  exp {A : Type} : (A -> expr) -> expr 
}.

Class ShallowForallLanguage (L : Language) : Type := {
  allp {A : Type} : (A -> expr) -> expr 
}.

Module ShallowQuantifierLanguageNotation.

(* Notation "∃ x , y" := (existsp x y) (at level 30, no associativity) : syntax. *)
(* Notation "∀ x , y" := (forallp x y) (at level 30, no associativity) : syntax. *)
(* Notation "p [ t \ x ]" := (substp p t x) (at level 20, no associativity) : syntax. *)

End ShallowQuantifierLanguageNotation.

