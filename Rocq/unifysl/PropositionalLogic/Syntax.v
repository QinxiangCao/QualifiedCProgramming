Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.GeneralLogic.Base.

Class AndLanguage (L: Language):
Type := {
  andp : expr -> expr -> expr
}.

Class OrLanguage (L: Language):
Type := {
  orp : expr -> expr -> expr
}.

Class FalseLanguage (L: Language):
Type := {
  falsep : expr
}.

Class NegLanguage (L: Language):
Type := {
  negp : expr -> expr
}.

Class IffLanguage (L: Language):
Type := {
  iffp : expr -> expr -> expr
}.

Class TrueLanguage (L: Language):
Type := {
  truep : expr
}.

Class IterAndLanguage (L: Language): Type := {
  iter_andp : list expr -> expr;
}.

Class IterOrLanguage (L: Language): Type := {
  iter_orp : list expr -> expr;
}.

Module PropositionalLanguageNotation.

Notation "x && y" := (andp x y) (at level 40, left associativity) : syntax.
Notation "x || y" := (orp x y) (at level 50, left associativity) : syntax.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : syntax.
Notation "~~ x" := (negp x) (at level 35) : syntax.
Notation "'FF'" := falsep : syntax.
Notation "'TT'" := truep : syntax.

End PropositionalLanguageNotation.
