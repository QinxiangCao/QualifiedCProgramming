Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import SeparationLogicNotation.

Class ImpStable
      (L: Language)
      {minL: MinimumLanguage L}
      (stable: expr -> Prop) := {
  impp_stable: forall x y, stable x -> stable y -> stable (x --> y)
}.

Class AndStable
      (L: Language)
      {andpL: AndLanguage L}
      (stable: expr -> Prop) := {
  andp_stable: forall x y, stable x -> stable y -> stable (x && y)
}.

Class OrStable
      (L: Language)
      {orpL: OrLanguage L}
      (stable: expr -> Prop) := {
  orp_stable: forall x y, stable x -> stable y -> stable (x || y)
}.

Class FalseStable
      (L: Language)
      {falsepL: FalseLanguage L}
      (stable: expr -> Prop) := {
  falsep_stable: stable FF
}.

Class StableProperIff
      (L: Language)
      {iffpL: IffLanguage L}
      (Gamma: Provable L)
      (stable: expr -> Prop) := {
  stable_proper_iffp :: Proper ((fun x y => |-- x <--> y) ==> iff) stable
}.

Class ModalStable (L: Language) {mL: ModalLanguage L} (stable: expr -> Prop) := {
  boxp_stable: forall x, stable x -> stable (boxp x)
}.

Class ModalAbsorbStable (L: Language) {minL: MinimumLanguage L} {mL: ModalLanguage L} (Gamma: Provable L) (stable: expr -> Prop) := {
  boxp_absorb_stable: forall x, stable x -> |-- x --> boxp x
}.

Class SeparationStable (L: Language) {sepconL: SepconLanguage L} {wandL: WandLanguage L} (stable: expr -> Prop) := {
  sepcon_stable: forall x y, stable x -> stable y -> stable (x * y);
  wand_stable: forall x y, stable x -> stable y -> stable (x -* y)
}.

Class SeparationAbsorbStable
      (L: Language)
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {sepconL: SepconLanguage L}
      (Gamma: Provable L)
      (stable: expr -> Prop) := {
  stable_andp_sepcon1: forall x y z, stable x -> |-- (x && y) * z <--> x && (y * z)
}.

Lemma iffp_stable
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {stable: expr -> Prop}
      {istable: ImpStable L stable}
      {astable: AndStable L stable}
      {iffp_Def_andp_impp: IffDefinition_And_Imp L}:
  forall x y, stable x -> stable y -> stable (x <--> y).
Proof.
  intros.
  rewrite andp_impp2iffp.
  apply andp_stable; apply impp_stable; auto.
Qed.

Lemma truep_stable
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {truepL: TrueLanguage L}
      {stable: expr -> Prop}
      {istable: ImpStable L stable}
      {fstable: FalseStable L stable}
      {truep_Def_falsep_impp: TrueDefinition_False_Imp L}:
  stable TT.
Proof.
  rewrite falsep_impp2truep.
  apply impp_stable; apply falsep_stable.
Qed.
