Require Import Logic.GeneralLogic.Base.

Class CoqPropLanguage (L: Language): Type := {
  coq_prop : Prop -> expr
}.

Module CoqPropInLogicNotation.

Notation "'!!' e" := (coq_prop e) (at level 25) : syntax.

End CoqPropInLogicNotation.

