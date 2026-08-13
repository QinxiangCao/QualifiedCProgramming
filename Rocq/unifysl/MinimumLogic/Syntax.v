Require Import Logic.GeneralLogic.Base.

Class MinimumLanguage (L: Language): Type := {
  impp: expr -> expr -> expr
}.

Declare Scope syntax.

Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
