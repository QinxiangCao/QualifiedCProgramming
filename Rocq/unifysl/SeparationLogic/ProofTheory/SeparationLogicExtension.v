Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class SeparationLogic_Precise
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  precise: expr -> Prop;
  precise_sepcon: forall x y, precise x -> precise y -> precise (x * y)
}.

(*
This rule is not sound for garbage collect SL
precise_impp: forall x y, |-- x --> y -> precise y -> precise x

The following is not sound e.g. when x := a = 0 && emp, y := a = 1, z := a = 0
sepcon_cancel: forall x y z, |-- (x * z) --> (y * z) -> precise z -> |-- (x --> y)
*)
