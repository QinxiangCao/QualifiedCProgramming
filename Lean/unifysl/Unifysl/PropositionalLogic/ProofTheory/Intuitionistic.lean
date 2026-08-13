import Unifysl.MinimumLogic.ProofTheory.ExtensionTactic
import Unifysl.MinimumLogic.ProofTheory.ProofTheoryPatterns
import Unifysl.MinimumLogic.ProofTheory.RewriteClass
import Unifysl.PropositionalLogic.Syntax

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory shard from `PropositionalLogic/ProofTheory/Intuitionistic.v`:
- Class definitions:
  `AndAxiomatization`, `OrAxiomatization`, `FalseAxiomatization`,
  `IntuitionisticNegAxiomatization`, `IffAxiomatization`,
  `TrueAxiomatization`, `IterAndAxiomatization_left`,
  `AndSequentCalculus`, `OrSequentCalculus`, `FalseSequentCalculus`,
  `IntuitionisticNegSequentCalculus`, `IffSequentCalculus`,
  `TrueSequentCalculus`, `AndDeduction`, `ImpAndAdjointDeduction`,
  `OrDeduction`, `FalseDeduction`, `IntuitionisticNegDeduction`,
  `ImpNegDeduction`, `TrueDeduction`, `IffDeduction`,
  `ImpLogicEquiv`, `AndLogicEquiv`, `OrLogicEquiv`,
  `DistrLogicEquiv`, `DeMorgenLogicEquiv`, `FalseAndLogicEquiv`,
  `FalseOrLogicEquiv`, `TrueAndLogicEquiv`, `TrueOrEquiv`,
  `IffLogicEquiv`, `NegLogicEquiv`.
- Derivable rules from deduction:
  `derivable1_andp_comm`, `derivable1_andp_assoc`,
  `derivable1_andp_modus_ponens`, `derivable1_impp_mono`,
  `derivable1_base`, `derivable1_orp_elim'`,
  `derivable1_negp_l`, `derivable1_negp_r`.
- Deduction-to-axiomatization lemmas:
  `Deduction2Axiomatization_GammaD1P`,
  `Deduction2Axiomatization_minAX`,
  `Deduction2Axiomatization_andpAX`,
  `Deduction2Axiomatization_orpAX`,
  `Deduction2Axiomatization_falsepAX`,
  `Deduction2Axiomatization_truepAX`,
  `Deduction2Axiomatization_inegpAX`,
  `Deduction2Axiomatization_iffpAX`.
- Register instances:
  `reg_Deduction2Axiomatization_GammaD1P`,
  `reg_Deduction2Axiomatization_minAX`,
  `reg_Deduction2Axiomatization_andpAX`,
  `reg_Deduction2Axiomatization_orpAX`,
  `reg_Deduction2Axiomatization_falsepAX`,
  `reg_Deduction2Axiomatization_truepAX`,
  `reg_Deduction2Axiomatization_negpAX`,
  `reg_Deduction2Axiomatization_iffpAX`.
- Sequent/Axiomatization conversion:
  `SequentCalculus2Axiomatization_*`,
  `Axiomatization2SequentCalculus_*`,
  `Deduction2Axiomatization_*`, plus the corresponding register instances.
- Axiomatization-derived propositional rules:
  `solve_*`, `negp_*`, `contrapositive*`, `provable_impp_curry`,
  `provable_impp_uncurry`, `andp_*`, `demorgan_*`, `orp_*`, `provable_falsep_orp*`,
  `provable_truep_impp`, `provable_andp_dup`, `provable_orp_dup*`, `provable_iffp`,
  `provable_neqp_orp_derives`.
- Deduction-derived or rules:
  `derivable1_orp_comm`, `derivable1_orp_assoc1`,
  `derivable1_orp_mono`, `derivable1_orp_Comm`,
  `derivable1_orp_Mono`.
- Logic-equivalence bridge:
  `logic_equiv_iffp`, `provable_derivable1_true`,
  `Axiomatization2LogicEquiv_imppE` and its register instance.
-/

universe u

namespace Unifysl

open PropositionalLanguageNotation

class AndAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [AndLanguage L] (Gamma : Provable L) : Prop where
  provable_andp_intros :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y ⟶ (x && y))
  provable_andp_elim1 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x && y) ⟶ x)
  provable_andp_elim2 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x && y) ⟶ y)

class OrAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [OrLanguage L] (Gamma : Provable L) : Prop where
  provable_orp_intros1 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (x || y))
  provable_orp_intros2 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (y ⟶ (x || y))
  provable_orp_elim :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma
        ((x ⟶ z) ⟶ (y ⟶ z) ⟶ ((x || y) ⟶ z))

class FalseAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [FalseLanguage L] (Gamma : Provable L) : Prop where
  provable_falsep_elim :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (FF ⟶ x)

class IntuitionisticNegAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [NegLanguage L] (Gamma : Provable L) : Prop where
  provable_contrapositivePP :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((y ⟶ x) ⟶ ((~~ x) ⟶ (~~ y)))
  provable_contradiction_elim1 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((~~ x) ⟶ (x ⟶ y))
  provable_double_negp_intros :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (~~ (~~ x)))

class IffAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [IffLanguage L] (Gamma : Provable L) : Prop where
  provable_iffp_intros :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma
        ((x ⟶ y) ⟶ (y ⟶ x) ⟶ (x ⟷ y))
  provable_iffp_elim1 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟷ y) ⟶ (x ⟶ y))
  provable_iffp_elim2 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟷ y) ⟶ (y ⟶ x))

class TrueAxiomatization (L : Language.{u}) [TrueLanguage L]
    (Gamma : Provable L) : Prop where
  provable_truep_intros : @Provable.provable L Gamma TT

class IterAndAxiomatization_left (L : Language.{u}) [TrueLanguage L]
    [AndLanguage L] [IffLanguage L] [semiOutParam (IterAndLanguage L)]
    (Gamma : Provable L) : Prop where
  provable_iter_andp_spec_left :
    forall xs : List (@Language.expr L),
      @Provable.provable L Gamma
        (iter_andp xs ⟷ xs.foldl (fun acc x => acc && x) TT)

class AndSequentCalculus (L : Language.{u}) [AndLanguage L]
    (Gamma : Derivable L) : Prop where
  derivables_andp_intros :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi y ->
      @Derivable.derivable L Gamma Phi (x && y)
  derivables_andp_elim1 :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi (x && y) ->
      @Derivable.derivable L Gamma Phi x
  derivables_andp_elim2 :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi (x && y) ->
      @Derivable.derivable L Gamma Phi y

class OrSequentCalculus (L : Language.{u}) [OrLanguage L]
    (Gamma : Derivable L) : Prop where
  derivables_orp_intros1 :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi (x || y)
  derivables_orp_intros2 :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi y ->
      @Derivable.derivable L Gamma Phi (x || y)
  derivables_orp_elim :
    forall Phi : context (L := L), forall x y z : @Language.expr L,
      @Derivable.derivable L Gamma (Phi ;; x) z ->
      @Derivable.derivable L Gamma (Phi ;; y) z ->
      @Derivable.derivable L Gamma (Phi ;; (x || y)) z

class FalseSequentCalculus (L : Language.{u}) [FalseLanguage L]
    (Gamma : Derivable L) : Prop where
  derivables_falsep_elim :
    forall Phi : context (L := L), forall x : @Language.expr L,
      @Derivable.derivable L Gamma Phi FF ->
      @Derivable.derivable L Gamma Phi x

class IntuitionisticNegSequentCalculus (L : Language.{u}) [NegLanguage L]
    (Gamma : Derivable L) : Prop where
  derivables_contrapositivePP :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma (Phi ;; y) x ->
      @Derivable.derivable L Gamma (Phi ;; ~~ x) (~~ y)
  derivables_contradiction_elim :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi (~~ x) ->
      @Derivable.derivable L Gamma Phi y
  derivables_double_negp_intros :
    forall Phi : context (L := L), forall x : @Language.expr L,
      @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi (~~ (~~ x))

class IffSequentCalculus (L : Language.{u}) [IffLanguage L]
    (Gamma : Derivable L) : Prop where
  derivables_iffp_intros :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma (Phi ;; x) y ->
      @Derivable.derivable L Gamma (Phi ;; y) x ->
      @Derivable.derivable L Gamma Phi (x ⟷ y)
  derivables_iffp_elim1 :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi (x ⟷ y) ->
      @Derivable.derivable L Gamma (Phi ;; x) y
  derivables_iffp_elim2 :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi (x ⟷ y) ->
      @Derivable.derivable L Gamma (Phi ;; y) x

class TrueSequentCalculus (L : Language.{u}) [TrueLanguage L]
    (Gamma : Derivable L) : Prop where
  derivables_truep_intros :
    forall Phi : context (L := L),
      @Derivable.derivable L Gamma Phi TT

class AndDeduction (L : Language.{u}) [AndLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1s_truep_intros :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x y ->
      @Derivable1.derivable1 L GammaD1 x z ->
      @Derivable1.derivable1 L GammaD1 x (y && z)
  derivable1_andp_elim1 :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x && y) x
  derivable1_andp_elim2 :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x && y) y

class ImpAndAdjointDeduction (L : Language.{u}) [MinimumLanguage L]
    [AndLanguage L] (GammaD1 : Derivable1 L) : Prop where
  derivable1s_impp_andp_adjoint :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (y ⟶ z) <->
        @Derivable1.derivable1 L GammaD1 (x && y) z

class OrDeduction (L : Language.{u}) [OrLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_orp_intros1 :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (x || y)
  derivable1_orp_intros2 :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 y (x || y)
  derivable1_orp_elim :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x z ->
      @Derivable1.derivable1 L GammaD1 y z ->
      @Derivable1.derivable1 L GammaD1 (x || y) z

class FalseDeduction (L : Language.{u}) [FalseLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_falsep_elim :
    forall x : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 FF x

class IntuitionisticNegDeduction (L : Language.{u}) [NegLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1s_contrapositivePP :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 y x ->
      @Derivable1.derivable1 L GammaD1 (~~ x) (~~ y)
  derivable1s_contradiction_elim :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 z x ->
      @Derivable1.derivable1 L GammaD1 z (~~ x) ->
      @Derivable1.derivable1 L GammaD1 z y
  derivable1_double_negp_intros :
    forall x : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (~~ (~~ x))

class ImpNegDeduction (L : Language.{u}) [MinimumLanguage L]
    [NegLanguage L] (GammaD1 : Derivable1 L) : Prop where
  derivable1_contrapositivePP :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (y ⟶ x) ((~~ x) ⟶ (~~ y))
  derivable1_contradiction_elim :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (~~ x) (x ⟶ y)

class TrueDeduction (L : Language.{u}) [TrueLanguage L]
    (GammaD1 : Derivable1 L) : Prop where
  derivable1_truep_intros :
    forall x : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x TT

class IffDeduction (L : Language.{u}) [MinimumLanguage L]
    [IffLanguage L] (GammaD1 : Derivable1 L) : Prop where
  derivable1_iffp_intros :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))
  derivable1_iffp_elim1 :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x ⟷ y) (x ⟶ y)
  derivable1_iffp_elim2 :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x ⟷ y) (y ⟶ x)

class ImpLogicEquiv (L : Language.{u}) [MinimumLanguage L]
    (Gamma : LogicEquiv L) : Prop where
  logic_equiv_impp :
    forall x1 x2 y1 y2 : @Language.expr L,
      @LogicEquiv.logic_equiv L Gamma x1 x2 ->
      @LogicEquiv.logic_equiv L Gamma y1 y2 ->
      @LogicEquiv.logic_equiv L Gamma (x1 ⟶ y1) (x2 ⟶ y2)

class AndLogicEquiv (L : Language.{u}) [AndLanguage L]
    (GammaE : LogicEquiv L) : Prop where
  logic_equiv_andp_congr :
    forall x1 x2 y1 y2 : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE x1 x2 ->
      @LogicEquiv.logic_equiv L GammaE y1 y2 ->
      @LogicEquiv.logic_equiv L GammaE (x1 && y1) (x2 && y2)
  logic_equiv_andp_comm :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (x && y) (y && x)
  logic_equiv_andp_assoc :
    forall x y z : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE ((x && y) && z) (x && (y && z))

class OrLogicEquiv (L : Language.{u}) [OrLanguage L]
    (GammaE : LogicEquiv L) : Prop where
  logic_equiv_orp_congr :
    forall x1 x2 y1 y2 : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE x1 x2 ->
      @LogicEquiv.logic_equiv L GammaE y1 y2 ->
      @LogicEquiv.logic_equiv L GammaE (x1 || y1) (x2 || y2)
  logic_equiv_orp_comm :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (x || y) (y || x)
  logic_equiv_orp_assoc :
    forall x y z : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE ((x || y) || z) (x || (y || z))

class DistrLogicEquiv (L : Language.{u}) [AndLanguage L] [OrLanguage L]
    (GammaE : LogicEquiv L) : Prop where
  logic_equiv_andp_distr :
    forall x y z : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE
        (x && (y || z)) ((x && y) || (x && z))
  logic_equiv_orp_distr :
    forall x y z : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE
        (x || (y && z)) ((x || y) && (x || z))

class DeMorgenLogicEquiv (L : Language.{u}) [AndLanguage L]
    [OrLanguage L] [NegLanguage L] (GammaE : LogicEquiv L) : Prop where
  logic_equiv_DeMorgen :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (~~ (x || y)) ((~~ x) && (~~ y))

class FalseAndLogicEquiv (L : Language.{u}) [AndLanguage L]
    [FalseLanguage L] (GammaE : LogicEquiv L) : Prop where
  logic_equiv_false_andp :
    forall x : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (x && FF) FF

class FalseOrLogicEquiv (L : Language.{u}) [OrLanguage L]
    [FalseLanguage L] (GammaE : LogicEquiv L) : Prop where
  logic_equiv_falsep_orp :
    forall x : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (x || FF) x

class TrueAndLogicEquiv (L : Language.{u}) [AndLanguage L]
    [TrueLanguage L] (GammaE : LogicEquiv L) : Prop where
  logic_equiv_andp_truep :
    forall x : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (x && TT) x
  logic_equiv_truep_andp :
    forall x : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (TT && x) x

class TrueOrEquiv (L : Language.{u}) [OrLanguage L]
    [TrueLanguage L] (GammaE : LogicEquiv L) : Prop where
  logic_equiv_truep_orp :
    forall x : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (x || TT) TT

class IffLogicEquiv (L : Language.{u}) [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] (GammaE : LogicEquiv L) : Prop where
  logic_equiv_provable_iffp_intros :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE ((x ⟶ y) && (y ⟶ x)) (x ⟷ y)

class NegLogicEquiv (L : Language.{u}) [NegLanguage L]
    (GammaE : LogicEquiv L) : Prop where
  logic_equiv_negp_intros :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE x y ->
      @LogicEquiv.logic_equiv L GammaE (~~ x) (~~ y)

/- Root wrappers for Coq-style projection names. Lean structure projections are
qualified by their class name, so these theorems keep the 8.20 names available
at the `Unifysl` root while the class fields use the same 8.20 names. -/

theorem provable_andp_intros {L : Language.{u}} [MinimumLanguage L] [AndLanguage L]
    [Gamma : Provable L] [AndAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y ⟶ (x && y)) :=
  AndAxiomatization.provable_andp_intros (Gamma := Gamma)

theorem provable_andp_elim1 {L : Language.{u}} [MinimumLanguage L] [AndLanguage L]
    [Gamma : Provable L] [AndAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x && y) ⟶ x) :=
  AndAxiomatization.provable_andp_elim1 (Gamma := Gamma)

theorem provable_andp_elim2 {L : Language.{u}} [MinimumLanguage L] [AndLanguage L]
    [Gamma : Provable L] [AndAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x && y) ⟶ y) :=
  AndAxiomatization.provable_andp_elim2 (Gamma := Gamma)

theorem provable_orp_intros1 {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [Gamma : Provable L] [OrAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (x || y)) :=
  OrAxiomatization.provable_orp_intros1 (Gamma := Gamma)

theorem provable_orp_intros2 {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [Gamma : Provable L] [OrAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (y ⟶ (x || y)) :=
  OrAxiomatization.provable_orp_intros2 (Gamma := Gamma)

theorem provable_orp_elim {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [Gamma : Provable L] [OrAxiomatization L Gamma] :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma
        ((x ⟶ z) ⟶ (y ⟶ z) ⟶ ((x || y) ⟶ z)) :=
  OrAxiomatization.provable_orp_elim (Gamma := Gamma)

theorem provable_falsep_elim {L : Language.{u}} [MinimumLanguage L] [FalseLanguage L]
    [Gamma : Provable L] [FalseAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (FF ⟶ x) :=
  FalseAxiomatization.provable_falsep_elim (Gamma := Gamma)

theorem provable_contrapositivePP {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [Gamma : Provable L] [IntuitionisticNegAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((y ⟶ x) ⟶ ((~~ x) ⟶ (~~ y))) :=
  IntuitionisticNegAxiomatization.provable_contrapositivePP (Gamma := Gamma)

theorem provable_contradiction_elim1 {L : Language.{u}} [MinimumLanguage L]
    [NegLanguage L] [Gamma : Provable L] [IntuitionisticNegAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((~~ x) ⟶ (x ⟶ y)) :=
  IntuitionisticNegAxiomatization.provable_contradiction_elim1 (Gamma := Gamma)

theorem provable_double_negp_intros {L : Language.{u}} [MinimumLanguage L]
    [NegLanguage L] [Gamma : Provable L] [IntuitionisticNegAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (~~ (~~ x))) :=
  IntuitionisticNegAxiomatization.provable_double_negp_intros (Gamma := Gamma)

theorem provable_iffp_intros {L : Language.{u}} [MinimumLanguage L] [IffLanguage L]
    [Gamma : Provable L] [IffAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟶ (y ⟶ x) ⟶ (x ⟷ y)) :=
  IffAxiomatization.provable_iffp_intros (Gamma := Gamma)

theorem provable_iffp_elim1 {L : Language.{u}} [MinimumLanguage L] [IffLanguage L]
    [Gamma : Provable L] [IffAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟷ y) ⟶ (x ⟶ y)) :=
  IffAxiomatization.provable_iffp_elim1 (Gamma := Gamma)

theorem provable_iffp_elim2 {L : Language.{u}} [MinimumLanguage L] [IffLanguage L]
    [Gamma : Provable L] [IffAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟷ y) ⟶ (y ⟶ x)) :=
  IffAxiomatization.provable_iffp_elim2 (Gamma := Gamma)

theorem provable_truep_intros {L : Language.{u}} [TrueLanguage L]
    [Gamma : Provable L] [TrueAxiomatization L Gamma] :
    @Provable.provable L Gamma TT :=
  TrueAxiomatization.provable_truep_intros (Gamma := Gamma)

theorem provable_iter_andp_spec_left {L : Language.{u}} [TrueLanguage L]
    [AndLanguage L] [IffLanguage L] [IterAndLanguage L] [Gamma : Provable L]
    [IterAndAxiomatization_left L Gamma] :
    forall xs : List (@Language.expr L),
      @Provable.provable L Gamma
        (iter_andp xs ⟷ xs.foldl (fun acc x => acc && x) TT) :=
  IterAndAxiomatization_left.provable_iter_andp_spec_left (Gamma := Gamma)

theorem derivables_andp_intros {L : Language.{u}} [AndLanguage L]
    [Gamma : Derivable L] [AndSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi y ->
      @Derivable.derivable L Gamma Phi (x && y) :=
  AndSequentCalculus.derivables_andp_intros (Gamma := Gamma)

theorem derivables_andp_elim1 {L : Language.{u}} [AndLanguage L]
    [Gamma : Derivable L] [AndSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi (x && y) ->
      @Derivable.derivable L Gamma Phi x :=
  AndSequentCalculus.derivables_andp_elim1 (Gamma := Gamma)

theorem derivables_andp_elim2 {L : Language.{u}} [AndLanguage L]
    [Gamma : Derivable L] [AndSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi (x && y) ->
      @Derivable.derivable L Gamma Phi y :=
  AndSequentCalculus.derivables_andp_elim2 (Gamma := Gamma)

theorem derivables_orp_intros1 {L : Language.{u}} [OrLanguage L]
    [Gamma : Derivable L] [OrSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi (x || y) :=
  OrSequentCalculus.derivables_orp_intros1 (Gamma := Gamma)

theorem derivables_orp_intros2 {L : Language.{u}} [OrLanguage L]
    [Gamma : Derivable L] [OrSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi y ->
      @Derivable.derivable L Gamma Phi (x || y) :=
  OrSequentCalculus.derivables_orp_intros2 (Gamma := Gamma)

theorem derivables_orp_elim {L : Language.{u}} [OrLanguage L]
    [Gamma : Derivable L] [OrSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y z : @Language.expr L,
      @Derivable.derivable L Gamma (Phi ;; x) z ->
      @Derivable.derivable L Gamma (Phi ;; y) z ->
      @Derivable.derivable L Gamma (Phi ;; (x || y)) z :=
  OrSequentCalculus.derivables_orp_elim (Gamma := Gamma)

theorem derivables_falsep_elim {L : Language.{u}} [FalseLanguage L]
    [Gamma : Derivable L] [FalseSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x : @Language.expr L,
      @Derivable.derivable L Gamma Phi FF ->
      @Derivable.derivable L Gamma Phi x :=
  FalseSequentCalculus.derivables_falsep_elim (Gamma := Gamma)

theorem derivables_contrapositivePP {L : Language.{u}} [NegLanguage L]
    [Gamma : Derivable L] [IntuitionisticNegSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma (Phi ;; y) x ->
      @Derivable.derivable L Gamma (Phi ;; ~~x) (~~y) :=
  IntuitionisticNegSequentCalculus.derivables_contrapositivePP (Gamma := Gamma)

theorem derivables_contradiction_elim {L : Language.{u}} [NegLanguage L]
    [Gamma : Derivable L] [IntuitionisticNegSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi (~~x) ->
      @Derivable.derivable L Gamma Phi y :=
  IntuitionisticNegSequentCalculus.derivables_contradiction_elim (Gamma := Gamma)

theorem derivables_double_negp_intros {L : Language.{u}} [NegLanguage L]
    [Gamma : Derivable L] [IntuitionisticNegSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x : @Language.expr L,
      @Derivable.derivable L Gamma Phi x ->
      @Derivable.derivable L Gamma Phi (~~(~~x)) :=
  IntuitionisticNegSequentCalculus.derivables_double_negp_intros (Gamma := Gamma)

theorem derivables_iffp_intros {L : Language.{u}} [IffLanguage L]
    [Gamma : Derivable L] [IffSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma (Phi ;; x) y ->
      @Derivable.derivable L Gamma (Phi ;; y) x ->
      @Derivable.derivable L Gamma Phi (x ⟷ y) :=
  IffSequentCalculus.derivables_iffp_intros (Gamma := Gamma)

theorem derivables_iffp_elim1 {L : Language.{u}} [IffLanguage L]
    [Gamma : Derivable L] [IffSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi (x ⟷ y) ->
      @Derivable.derivable L Gamma (Phi ;; x) y :=
  IffSequentCalculus.derivables_iffp_elim1 (Gamma := Gamma)

theorem derivables_iffp_elim2 {L : Language.{u}} [IffLanguage L]
    [Gamma : Derivable L] [IffSequentCalculus L Gamma] :
    forall Phi : context (L := L), forall x y : @Language.expr L,
      @Derivable.derivable L Gamma Phi (x ⟷ y) ->
      @Derivable.derivable L Gamma (Phi ;; y) x :=
  IffSequentCalculus.derivables_iffp_elim2 (Gamma := Gamma)

theorem derivables_truep_intros {L : Language.{u}} [TrueLanguage L]
    [Gamma : Derivable L] [TrueSequentCalculus L Gamma] :
    forall Phi : context (L := L), @Derivable.derivable L Gamma Phi TT :=
  TrueSequentCalculus.derivables_truep_intros (Gamma := Gamma)

theorem derivable1s_truep_intros {L : Language.{u}} [AndLanguage L]
    [GammaD1 : Derivable1 L] [AndDeduction L GammaD1] :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x y ->
      @Derivable1.derivable1 L GammaD1 x z ->
      @Derivable1.derivable1 L GammaD1 x (y && z) :=
  AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)

theorem derivable1s_impp_andp_adjoint {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [GammaD1 : Derivable1 L]
    [ImpAndAdjointDeduction L GammaD1] :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (y ⟶ z) <->
      @Derivable1.derivable1 L GammaD1 (x && y) z :=
  ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint (GammaD1 := GammaD1)

theorem derivable1s_contrapositivePP {L : Language.{u}} [NegLanguage L]
    [GammaD1 : Derivable1 L] [IntuitionisticNegDeduction L GammaD1] :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 y x ->
      @Derivable1.derivable1 L GammaD1 (~~x) (~~y) :=
  IntuitionisticNegDeduction.derivable1s_contrapositivePP (GammaD1 := GammaD1)

theorem derivable1s_contradiction_elim {L : Language.{u}} [NegLanguage L]
    [GammaD1 : Derivable1 L] [IntuitionisticNegDeduction L GammaD1] :
  forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 z x ->
      @Derivable1.derivable1 L GammaD1 z (~~x) ->
      @Derivable1.derivable1 L GammaD1 z y :=
  IntuitionisticNegDeduction.derivable1s_contradiction_elim (GammaD1 := GammaD1)

theorem derivable1_contradiction_elim {L : Language.{u}} [MinimumLanguage L]
    [NegLanguage L] [GammaD1 : Derivable1 L] [ImpNegDeduction L GammaD1] :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (~~x) (x ⟶ y) :=
  ImpNegDeduction.derivable1_contradiction_elim (GammaD1 := GammaD1)

theorem logic_equiv_provable_iffp_intros {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] [GammaE : LogicEquiv L]
    [IffLogicEquiv L GammaE] :
    forall x y : @Language.expr L, logic_equiv (L := L) ((x ⟶ y) && (y ⟶ x)) (x ⟷ y) :=
  IffLogicEquiv.logic_equiv_provable_iffp_intros (GammaE := GammaE)

section DerivableRulesFromDeduction

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L]
variable [GammaD1 : Derivable1 L] [bD : BasicDeduction L GammaD1]
variable [andpD : AndDeduction L GammaD1]

theorem derivable1_andp_comm :
    forall x y : @Language.expr L, (x && y) |-- (y && x) := by
  intro x y
  exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
    (x && y) y x
    (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x y)
    (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x y)

theorem derivable1_andp_assoc :
    forall x y z : @Language.expr L, ((x && y) && z) |-- (x && (y && z)) := by
  intro x y z
  let s : @Language.expr L := (x && y) && z
  have hsxy : s |-- (x && y) :=
    AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) (x && y) z
  have hx : s |-- x :=
    derivable1_trans s (x && y) x hsxy
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x y)
  have hy : s |-- y :=
    derivable1_trans s (x && y) y hsxy
      (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x y)
  have hz : s |-- z :=
    AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (x && y) z
  have hyz : s |-- (y && z) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) s y z hy hz
  exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
    s x (y && z) hx hyz

variable [adjD : ImpAndAdjointDeduction L GammaD1]

theorem derivable1_andp_modus_ponens :
    forall x y : @Language.expr L, ((x ⟶ y) && x) |-- y := by
  intro x y
  exact (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) (x ⟶ y) x y).mp (derivable1_refl (x ⟶ y))

theorem derivable1_impp_mono :
    forall x1 y1 x2 y2 : @Language.expr L,
      y1 |-- x1 -> x2 |-- y2 -> (x1 ⟶ x2) |-- (y1 ⟶ y2) := by
  intro x1 y1 x2 y2 hyx hxy
  let s : @Language.expr L := x1 ⟶ x2
  refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) s y1 y2).mpr ?_
  have hs : (s && y1) |-- s :=
    AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) s y1
  have hy1 : (s && y1) |-- y1 :=
    AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) s y1
  have hx1 : (s && y1) |-- x1 := derivable1_trans (s && y1) y1 x1 hy1 hyx
  have hpair : (s && y1) |-- ((x1 ⟶ x2) && x1) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
      (s && y1) (x1 ⟶ x2) x1 hs hx1
  have hx2 : (s && y1) |-- x2 :=
    derivable1_trans (s && y1) ((x1 ⟶ x2) && x1) x2 hpair
      (derivable1_andp_modus_ponens x1 x2)
  exact derivable1_trans (s && y1) x2 y2 hx2 hxy

theorem derivable1_base :
    forall x y : @Language.expr L, x |-- (y ⟶ y) := by
  intro x y
  exact (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) x y y).mpr
      (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x y)

theorem derivable1_orp_elim' [OrLanguage L] [orpD : OrDeduction L GammaD1] :
    forall x y z : @Language.expr L,
      ((x ⟶ z) && (y ⟶ z)) |-- ((x || y) ⟶ z) := by
  intro x y z
  let s : @Language.expr L := (x ⟶ z) && (y ⟶ z)
  have hxBranch : x |-- (s ⟶ z) := by
    refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
      (GammaD1 := GammaD1) x s z).mpr ?_
    have hcomm : (x && s) |-- (s && x) := derivable1_andp_comm x s
    have hsxToS : (s && x) |-- s :=
      AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) s x
    have hsxToX : (s && x) |-- x :=
      AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) s x
    have hsxToImp : (s && x) |-- (x ⟶ z) :=
      derivable1_trans (s && x) s (x ⟶ z) hsxToS
        (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1)
          (x ⟶ z) (y ⟶ z))
    have hpair : (s && x) |-- ((x ⟶ z) && x) :=
      AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
        (s && x) (x ⟶ z) x hsxToImp hsxToX
    exact derivable1_trans (x && s) (s && x) z hcomm
      (derivable1_trans (s && x) ((x ⟶ z) && x) z hpair
        (derivable1_andp_modus_ponens x z))
  have hyBranch : y |-- (s ⟶ z) := by
    refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
      (GammaD1 := GammaD1) y s z).mpr ?_
    have hcomm : (y && s) |-- (s && y) := derivable1_andp_comm y s
    have hsyToS : (s && y) |-- s :=
      AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) s y
    have hsyToY : (s && y) |-- y :=
      AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) s y
    have hsyToImp : (s && y) |-- (y ⟶ z) :=
      derivable1_trans (s && y) s (y ⟶ z) hsyToS
        (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1)
          (x ⟶ z) (y ⟶ z))
    have hpair : (s && y) |-- ((y ⟶ z) && y) :=
      AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
        (s && y) (y ⟶ z) y hsyToImp hsyToY
    exact derivable1_trans (y && s) (s && y) z hcomm
      (derivable1_trans (s && y) ((y ⟶ z) && y) z hpair
        (derivable1_andp_modus_ponens y z))
  have hor : (x || y) |-- (s ⟶ z) :=
    OrDeduction.derivable1_orp_elim (GammaD1 := GammaD1) x y (s ⟶ z)
      hxBranch hyBranch
  have horAdj : ((x || y) && s) |-- z :=
    (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
      (GammaD1 := GammaD1) (x || y) s z).mp hor
  refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) s (x || y) z).mpr ?_
  exact derivable1_trans (s && (x || y)) ((x || y) && s) z
    (derivable1_andp_comm s (x || y)) horAdj

theorem derivable1_negp_l [FalseLanguage L] [NegLanguage L]
    [falsepD : FalseDeduction L GammaD1]
    [inegpD : IntuitionisticNegDeduction L GammaD1] :
    forall x : @Language.expr L, (~~ x) |-- (x ⟶ FF) := by
  intro x
  refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) (~~ x) x FF).mpr ?_
  exact IntuitionisticNegDeduction.derivable1s_contradiction_elim
    (GammaD1 := GammaD1) x FF ((~~ x) && x)
    (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (~~ x) x)
    (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) (~~ x) x)

theorem derivable1_negp_r [FalseLanguage L] [NegLanguage L]
    [falsepD : FalseDeduction L GammaD1]
    [inegpD : IntuitionisticNegDeduction L GammaD1]
    [imppNegD : ImpNegDeduction L GammaD1] :
    forall x : @Language.expr L, (x ⟶ FF) |-- (~~ x) := by
  intro x
  let t : @Language.expr L := (~~ FF) ⟶ (~~ x)
  have hcontr : (x ⟶ FF) |-- t :=
    ImpNegDeduction.derivable1_contrapositivePP (GammaD1 := GammaD1) FF x
  have htNotFalse : t |-- (~~ FF) := by
    have hdn : t |-- (~~ (~~ t)) :=
      IntuitionisticNegDeduction.derivable1_double_negp_intros
        (GammaD1 := GammaD1) t
    have hfalseToNotT : FF |-- (~~ t) :=
      FalseDeduction.derivable1_falsep_elim (GammaD1 := GammaD1) (~~ t)
    have hcontra : (~~ (~~ t)) |-- (~~ FF) :=
      IntuitionisticNegDeduction.derivable1s_contrapositivePP
        (GammaD1 := GammaD1) (~~ t) FF hfalseToNotT
    exact derivable1_trans t (~~ (~~ t)) (~~ FF) hdn hcontra
  have htPair : t |-- (t && (~~ FF)) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
      t t (~~ FF) (derivable1_refl t) htNotFalse
  have htToNotX : t |-- (~~ x) :=
    derivable1_trans t (t && (~~ FF)) (~~ x) htPair
      (derivable1_andp_modus_ponens (~~ FF) (~~ x))
  exact derivable1_trans (x ⟶ FF) t (~~ x) hcontr htToNotX

end DerivableRulesFromDeduction

section Deduction2Axiomatization

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L]
variable [GammaP : Provable L] [GammaD1 : Derivable1 L]
variable [GammaPD1 : ProvableDerivable1 L GammaP GammaD1]
variable [bD : BasicDeduction L GammaD1]
variable [adjD : ImpAndAdjointDeduction L GammaD1]
variable [andpD : AndDeduction L GammaD1]

private theorem derivable1_impp_self_from_source (x y : @Language.expr L) :
    x |-- (y ⟶ y) :=
  derivable1_base x y

theorem Deduction2Axiomatization_GammaD1P :
    Derivable1Provable L GammaP GammaD1 := by
  constructor
  intro x y
  constructor
  · intro hxy
    let f : @Language.expr L := x ⟶ y
    have hf : (f ⟶ f) |-- f := by
      refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
        (GammaD1 := GammaD1) (f ⟶ f) x y).mpr ?_
      exact derivable1_trans ((f ⟶ f) && x) x y
        (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (f ⟶ f) x)
        hxy
    exact (ProvableDerivable1.provable_derivable1
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) f).mpr hf
  · intro hprov
    let f : @Language.expr L := x ⟶ y
    have hf : (f ⟶ f) |-- f :=
      (ProvableDerivable1.provable_derivable1
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) f).mp hprov
    have hfAdj : ((f ⟶ f) && x) |-- y :=
      (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
        (GammaD1 := GammaD1) (f ⟶ f) x y).mp hf
    have hpair : x |-- ((f ⟶ f) && x) :=
      AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
        x (f ⟶ f) x (derivable1_impp_self_from_source x f) (derivable1_refl x)
    exact derivable1_trans x ((f ⟶ f) && x) y hpair hfAdj

private theorem intuitionistic_derivable1_axiom1 :
    forall x y : @Language.expr L, x |-- (y ⟶ x) := by
  intro x y
  exact (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) x y x).mpr
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x y)

private theorem intuitionistic_derivable1_axiom2 :
    forall x y z : @Language.expr L,
      (x ⟶ y ⟶ z) |-- ((x ⟶ y) ⟶ (x ⟶ z)) := by
  intro x y z
  let a : @Language.expr L := x ⟶ y ⟶ z
  let b : @Language.expr L := x ⟶ y
  refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) a b (x ⟶ z)).mpr ?_
  refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) (a && b) x z).mpr ?_
  let s : @Language.expr L := (a && b) && x
  have hsab : s |-- (a && b) :=
    AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) (a && b) x
  have hsa : s |-- a :=
    derivable1_trans s (a && b) a hsab
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) a b)
  have hsb : s |-- b :=
    derivable1_trans s (a && b) b hsab
      (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) a b)
  have hsx : s |-- x :=
    AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (a && b) x
  have hpairBX : s |-- (b && x) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) s b x hsb hsx
  have hsy : s |-- y :=
    derivable1_trans s (b && x) y hpairBX (derivable1_andp_modus_ponens x y)
  have hpairAX : s |-- (a && x) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) s a x hsa hsx
  have hyz : s |-- (y ⟶ z) :=
    derivable1_trans s (a && x) (y ⟶ z) hpairAX
      (derivable1_andp_modus_ponens x (y ⟶ z))
  have hpairYZ : s |-- ((y ⟶ z) && y) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
      s (y ⟶ z) y hyz hsy
  exact derivable1_trans s ((y ⟶ z) && y) z hpairYZ
    (derivable1_andp_modus_ponens y z)

theorem Deduction2Axiomatization_minAX :
    MinimumAxiomatization L GammaP := by
  letI : Derivable1Provable L GammaP GammaD1 :=
    Deduction2Axiomatization_GammaD1P
  constructor
  · intro x y hxy hx
    have hxyDer : x |-- y :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x y).mpr hxy
    have hxDer : (x ⟶ x) |-- x :=
      (ProvableDerivable1.provable_derivable1
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x).mp hx
    refine (ProvableDerivable1.provable_derivable1
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) y).mpr ?_
    have hsourceToX : (y ⟶ y) |-- x := by
      have hsourceToXX : (y ⟶ y) |-- (x ⟶ x) :=
        derivable1_impp_self_from_source (y ⟶ y) x
      exact derivable1_trans (y ⟶ y) (x ⟶ x) x hsourceToXX hxDer
    exact derivable1_trans (y ⟶ y) x y hsourceToX hxyDer
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      x (y ⟶ x)).mp (intuitionistic_derivable1_axiom1 x y)
  · intro x y z
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x ⟶ y ⟶ z) ((x ⟶ y) ⟶ x ⟶ z)).mp
      (intuitionistic_derivable1_axiom2 x y z)

variable [GammaD1P : Derivable1Provable L GammaP GammaD1]

theorem Deduction2Axiomatization_andpAX :
    AndAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (y ⟶ (x && y))).mp
      ((ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
        (GammaD1 := GammaD1) x y (x && y)).mpr (derivable1_refl (x && y)))
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x && y) x).mp
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x y)
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x && y) y).mp
      (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x y)

theorem Deduction2Axiomatization_orpAX [OrLanguage L]
    [orpD : OrDeduction L GammaD1] :
    OrAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (x || y)).mp
      (OrDeduction.derivable1_orp_intros1 (GammaD1 := GammaD1) x y)
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) y (x || y)).mp
      (OrDeduction.derivable1_orp_intros2 (GammaD1 := GammaD1) x y)
  · intro x y z
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x ⟶ z) ((y ⟶ z) ⟶ ((x || y) ⟶ z))).mp
      ((ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
        (GammaD1 := GammaD1) (x ⟶ z) (y ⟶ z) ((x || y) ⟶ z)).mpr
        (derivable1_orp_elim' x y z))

theorem Deduction2Axiomatization_falsepAX [FalseLanguage L]
    [falsepD : FalseDeduction L GammaD1] :
    FalseAxiomatization L GammaP := by
  constructor
  intro x
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1) FF x).mp
    (FalseDeduction.derivable1_falsep_elim (GammaD1 := GammaD1) x)

theorem Deduction2Axiomatization_truepAX [TrueLanguage L]
    [truepD : TrueDeduction L GammaD1] :
    TrueAxiomatization L GammaP := by
  constructor
  exact (ProvableDerivable1.provable_derivable1
    (L := L) (GammaP := GammaP) (GammaD := GammaD1) TT).mpr
    (TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) (TT ⟶ TT))

theorem Deduction2Axiomatization_inegpAX [NegLanguage L] [FalseLanguage L]
    [inegpD : IntuitionisticNegDeduction L GammaD1]
    [imppNegD : ImpNegDeduction L GammaD1] :
    IntuitionisticNegAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (y ⟶ x) ((~~ x) ⟶ (~~ y))).mp
      (ImpNegDeduction.derivable1_contrapositivePP (GammaD1 := GammaD1) x y)
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (~~ x) (x ⟶ y)).mp
      (ImpNegDeduction.derivable1_contradiction_elim (GammaD1 := GammaD1) x y)
  · intro x
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x (~~ (~~ x))).mp
      (IntuitionisticNegDeduction.derivable1_double_negp_intros
        (GammaD1 := GammaD1) x)

theorem Deduction2Axiomatization_iffpAX [IffLanguage L]
    [iffpD : IffDeduction L GammaD1] :
    IffAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))).mp
      (IffDeduction.derivable1_iffp_intros (GammaD1 := GammaD1) x y)
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x ⟷ y) (x ⟶ y)).mp
      (IffDeduction.derivable1_iffp_elim1 (GammaD1 := GammaD1) x y)
  · intro x y
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (x ⟷ y) (y ⟶ x)).mp
      (IffDeduction.derivable1_iffp_elim2 (GammaD1 := GammaD1) x y)

end Deduction2Axiomatization

instance reg_Deduction2Axiomatization_GammaD1P :
    RegisterClass D12P_reg
      (ProofRegistration.mk `GammaD1P ``Deduction2Axiomatization_GammaD1P) 0 := {}

instance reg_Deduction2Axiomatization_minAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `minAX ``Deduction2Axiomatization_minAX) 1 := {}

instance reg_Deduction2Axiomatization_andpAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `andpAX ``Deduction2Axiomatization_andpAX) 2 := {}

instance reg_Deduction2Axiomatization_orpAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `orpAX ``Deduction2Axiomatization_orpAX) 3 := {}

instance reg_Deduction2Axiomatization_falsepAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `falsepAX ``Deduction2Axiomatization_falsepAX) 4 := {}

instance reg_Deduction2Axiomatization_truepAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `truepAX ``Deduction2Axiomatization_truepAX) 5 := {}

instance reg_Deduction2Axiomatization_negpAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `inegpAX ``Deduction2Axiomatization_inegpAX) 6 := {}

instance reg_Deduction2Axiomatization_iffpAX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `iffpAX ``Deduction2Axiomatization_iffpAX) 7 := {}

section DerivableRulesFromSequentCalculus1

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [OrLanguage L]
variable [FalseLanguage L] [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [Gamma : Derivable L]
variable [BasicSequentCalculus L Gamma] [MinimumSequentCalculus L Gamma]
variable [AndSequentCalculus L Gamma] [OrSequentCalculus L Gamma]
variable [FalseSequentCalculus L Gamma] [IntuitionisticNegSequentCalculus L Gamma]
variable [IffSequentCalculus L Gamma] [TrueSequentCalculus L Gamma]

theorem derivable_andp_intros :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- (x ⟶ y ⟶ (x && y)) := by
  intro Phi x y
  exact (deduction_theorem Phi x (y ⟶ (x && y))).mp
    ((deduction_theorem (Phi ;; x) y (x && y)).mp
      (AndSequentCalculus.derivables_andp_intros ((Phi ;; x) ;; y) x y
        (derivable_assum ((Phi ;; x) ;; y) x (Or.inl (Or.inr rfl)))
        (derivable_assum ((Phi ;; x) ;; y) y (Or.inr rfl))))

theorem derivable_andp_elim1 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- ((x && y) ⟶ x) := by
  intro Phi x y
  exact (deduction_theorem Phi (x && y) x).mp
    (AndSequentCalculus.derivables_andp_elim1 (Phi ;; (x && y)) x y
      (derivable_assum1 Phi (x && y)))

theorem derivable_andp_elim2 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- ((x && y) ⟶ y) := by
  intro Phi x y
  exact (deduction_theorem Phi (x && y) y).mp
    (AndSequentCalculus.derivables_andp_elim2 (Phi ;; (x && y)) x y
      (derivable_assum1 Phi (x && y)))

theorem derivable_orp_intros1 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- (x ⟶ (x || y)) := by
  intro Phi x y
  exact (deduction_theorem Phi x (x || y)).mp
    (OrSequentCalculus.derivables_orp_intros1 (Phi ;; x) x y
      (derivable_assum1 Phi x))

theorem derivable_orp_intros2 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- (y ⟶ (x || y)) := by
  intro Phi x y
  exact (deduction_theorem Phi y (x || y)).mp
    (OrSequentCalculus.derivables_orp_intros2 (Phi ;; y) x y
      (derivable_assum1 Phi y))

theorem derivable_orp_elim :
    forall (Phi : context (L := L)) (x y z : @Language.expr L),
      Phi |--- ((x ⟶ z) ⟶ (y ⟶ z) ⟶ ((x || y) ⟶ z)) := by
  intro Phi x y z
  exact (deduction_theorem Phi (x ⟶ z)
      ((y ⟶ z) ⟶ ((x || y) ⟶ z))).mp
    ((deduction_theorem (Phi ;; (x ⟶ z)) (y ⟶ z)
      ((x || y) ⟶ z)).mp
      ((deduction_theorem ((Phi ;; (x ⟶ z)) ;; (y ⟶ z)) (x || y) z).mp
        (OrSequentCalculus.derivables_orp_elim
          ((Phi ;; (x ⟶ z)) ;; (y ⟶ z)) x y z
          ((deduction_theorem (((Phi ;; (x ⟶ z)) ;; (y ⟶ z))) x z).mpr
            (derivable_assum (((Phi ;; (x ⟶ z)) ;; (y ⟶ z))) (x ⟶ z)
              (Or.inl (Or.inr rfl))))
          ((deduction_theorem (((Phi ;; (x ⟶ z)) ;; (y ⟶ z))) y z).mpr
            (derivable_assum (((Phi ;; (x ⟶ z)) ;; (y ⟶ z))) (y ⟶ z)
              (Or.inr rfl))))))

theorem derivable_falsep_elim :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      Phi |--- (FF ⟶ x) := by
  intro Phi x
  exact (deduction_theorem Phi FF x).mp
    (FalseSequentCalculus.derivables_falsep_elim (Phi ;; FF) x
      (derivable_assum1 Phi FF))

theorem derivable_contrapositive :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- ((y ⟶ x) ⟶ (~~ x) ⟶ (~~ y)) := by
  intro Phi x y
  exact (deduction_theorem Phi (y ⟶ x) ((~~ x) ⟶ (~~ y))).mp
    ((deduction_theorem (Phi ;; (y ⟶ x)) (~~ x) (~~ y)).mp
      (IntuitionisticNegSequentCalculus.derivables_contrapositivePP
        (Phi ;; (y ⟶ x)) x y
        ((deduction_theorem (Phi ;; (y ⟶ x)) y x).mpr
          (derivable_assum1 Phi (y ⟶ x)))))

theorem derivable_contradiction_elim1 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- ((~~ x) ⟶ x ⟶ y) := by
  intro Phi x y
  exact (deduction_theorem Phi (~~ x) (x ⟶ y)).mp
    ((deduction_theorem (Phi ;; (~~ x)) x y).mp
      (IntuitionisticNegSequentCalculus.derivables_contradiction_elim
        ((Phi ;; (~~ x)) ;; x) x y
        (derivable_assum ((Phi ;; (~~ x)) ;; x) x (Or.inr rfl))
        (derivable_assum ((Phi ;; (~~ x)) ;; x) (~~ x) (Or.inl (Or.inr rfl)))))

theorem derivable_double_negp_intros :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      Phi |--- (x ⟶ (~~ (~~ x))) := by
  intro Phi x
  exact (deduction_theorem Phi x (~~ (~~ x))).mp
    (IntuitionisticNegSequentCalculus.derivables_double_negp_intros (Phi ;; x) x
      (derivable_assum1 Phi x))

theorem derivable_iffp_intros :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- ((x ⟶ y) ⟶ (y ⟶ x) ⟶ (x ⟷ y)) := by
  intro Phi x y
  exact (deduction_theorem Phi (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))).mp
    ((deduction_theorem (Phi ;; (x ⟶ y)) (y ⟶ x) (x ⟷ y)).mp
      (IffSequentCalculus.derivables_iffp_intros ((Phi ;; (x ⟶ y)) ;; (y ⟶ x)) x y
        ((deduction_theorem ((Phi ;; (x ⟶ y)) ;; (y ⟶ x)) x y).mpr
          (derivable_assum ((Phi ;; (x ⟶ y)) ;; (y ⟶ x)) (x ⟶ y)
            (Or.inl (Or.inr rfl))))
        ((deduction_theorem ((Phi ;; (x ⟶ y)) ;; (y ⟶ x)) y x).mpr
          (derivable_assum ((Phi ;; (x ⟶ y)) ;; (y ⟶ x)) (y ⟶ x)
            (Or.inr rfl)))))

theorem derivable_iffp_elim1 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- ((x ⟷ y) ⟶ (x ⟶ y)) := by
  intro Phi x y
  exact (deduction_theorem Phi (x ⟷ y) (x ⟶ y)).mp
    ((deduction_theorem (Phi ;; (x ⟷ y)) x y).mp
      (IffSequentCalculus.derivables_iffp_elim1 (Phi ;; (x ⟷ y)) x y
        (derivable_assum1 Phi (x ⟷ y))))

theorem derivable_iffp_elim2 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- ((x ⟷ y) ⟶ (y ⟶ x)) := by
  intro Phi x y
  exact (deduction_theorem Phi (x ⟷ y) (y ⟶ x)).mp
    ((deduction_theorem (Phi ;; (x ⟷ y)) y x).mp
      (IffSequentCalculus.derivables_iffp_elim2 (Phi ;; (x ⟷ y)) x y
        (derivable_assum1 Phi (x ⟷ y))))

theorem derivable_truep_intros :
    forall Phi : context (L := L), Phi |--- TT := by
  intro Phi
  exact TrueSequentCalculus.derivables_truep_intros Phi

theorem derivables_orp_elim' :
    forall (Phi : context (L := L)) (x y z : @Language.expr L),
      (Phi |--- (x ⟶ z)) -> (Phi |--- (y ⟶ z)) ->
        (Phi |--- ((x || y) ⟶ z)) := by
  intro Phi x y z hx hy
  exact (deduction_theorem Phi (x || y) z).mp
    (OrSequentCalculus.derivables_orp_elim Phi x y z
      ((deduction_theorem Phi x z).mpr hx)
      ((deduction_theorem Phi y z).mpr hy))

theorem derivables_negp_unfold :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      (Phi |--- (~~ x)) -> ((Phi ;; x) |--- FF) := by
  intro Phi x hnx
  exact IntuitionisticNegSequentCalculus.derivables_contradiction_elim
    (Phi ;; x) x FF
    (derivable_assum1 Phi x)
    (deduction_weaken1 Phi x (~~ x) hnx)

theorem derivables_negp_fold :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      ((Phi ;; x) |--- FF) -> (Phi |--- (~~ x)) := by
  intro Phi x hff
  have hnotFF_to_notx : (Phi ;; (~~ FF)) |--- (~~ x) :=
    IntuitionisticNegSequentCalculus.derivables_contrapositivePP Phi FF x hff
  have hImpRefl : Phi |--- (FF ⟶ FF) :=
    derivable_impp_refl Phi FF
  have hdouble : Phi |--- (~~ (~~ (FF ⟶ FF))) :=
    IntuitionisticNegSequentCalculus.derivables_double_negp_intros Phi
      (FF ⟶ FF) hImpRefl
  have hfalseToNegImp : (Phi ;; FF) |--- (~~ (FF ⟶ FF)) :=
    FalseSequentCalculus.derivables_falsep_elim (Phi ;; FF)
      (~~ (FF ⟶ FF)) (derivable_assum1 Phi FF)
  have hdouble_to_notFF : (Phi ;; (~~ (~~ (FF ⟶ FF)))) |--- (~~ FF) :=
    IntuitionisticNegSequentCalculus.derivables_contrapositivePP Phi
      (~~ (FF ⟶ FF)) FF hfalseToNegImp
  have hnotFF : Phi |--- (~~ FF) :=
    deduction_subst1 Phi (~~ (~~ (FF ⟶ FF))) (~~ FF)
      hdouble hdouble_to_notFF
  exact deduction_subst1 Phi (~~ FF) (~~ x) hnotFF hnotFF_to_notx

theorem derivables_negp_fold_unfold :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      (Phi |--- (~~ x)) <-> ((Phi ;; x) |--- FF) := by
  intro Phi x
  constructor
  · exact derivables_negp_unfold Phi x
  · exact derivables_negp_fold Phi x

theorem derivable_contradiction_elim2 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Phi |--- (x ⟶ (~~ x) ⟶ y) := by
  intro Phi x y
  exact (deduction_theorem Phi x ((~~ x) ⟶ y)).mp
    ((deduction_theorem (Phi ;; x) (~~ x) y).mp
      (IntuitionisticNegSequentCalculus.derivables_contradiction_elim
        ((Phi ;; x) ;; (~~ x)) x y
        (derivable_assum ((Phi ;; x) ;; (~~ x)) x (Or.inl (Or.inr rfl)))
        (derivable_assum ((Phi ;; x) ;; (~~ x)) (~~ x) (Or.inr rfl))))

theorem derivable_iffp_refl :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      Phi |--- (x ⟷ x) := by
  intro Phi x
  have hIntro : Phi |--- ((x ⟶ x) ⟶ (x ⟶ x) ⟶ (x ⟷ x)) :=
    derivable_iffp_intros Phi x x
  have hRefl : Phi |--- (x ⟶ x) :=
    derivable_impp_refl Phi x
  have hStep : Phi |--- ((x ⟶ x) ⟶ (x ⟷ x)) :=
    MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟶ x)
      ((x ⟶ x) ⟶ (x ⟷ x)) hRefl hIntro
  exact MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟶ x)
    (x ⟷ x) hRefl hStep

end DerivableRulesFromSequentCalculus1

section SequentCalculus2Axiomatization

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [OrLanguage L]
variable [FalseLanguage L] [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable L]
variable [GammaPD : ProvableDerivable L GammaP GammaD]
variable [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
variable [AndSequentCalculus L GammaD] [OrSequentCalculus L GammaD]
variable [FalseSequentCalculus L GammaD] [IntuitionisticNegSequentCalculus L GammaD]
variable [IffSequentCalculus L GammaD] [TrueSequentCalculus L GammaD]
variable [MinimumAxiomatization L GammaP]

theorem SequentCalculus2Axiomatization_andpAX :
    AndAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) (x ⟶ y ⟶ (x && y))).mpr
      (derivable_andp_intros (Gamma := GammaD) (empty_context (L := L)) x y)
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) ((x && y) ⟶ x)).mpr
      (derivable_andp_elim1 (Gamma := GammaD) (empty_context (L := L)) x y)
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) ((x && y) ⟶ y)).mpr
      (derivable_andp_elim2 (Gamma := GammaD) (empty_context (L := L)) x y)

theorem SequentCalculus2Axiomatization_orpAX :
    OrAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) (x ⟶ (x || y))).mpr
      (derivable_orp_intros1 (Gamma := GammaD) (empty_context (L := L)) x y)
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) (y ⟶ (x || y))).mpr
      (derivable_orp_intros2 (Gamma := GammaD) (empty_context (L := L)) x y)
  · intro x y z
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      ((x ⟶ z) ⟶ (y ⟶ z) ⟶ ((x || y) ⟶ z))).mpr
      (derivable_orp_elim (Gamma := GammaD) (empty_context (L := L)) x y z)

theorem SequentCalculus2Axiomatization_falsepAX :
    FalseAxiomatization L GammaP := by
  constructor
  intro x
  exact (ProvableDerivable.provable_derivable
    (L := L) (GammaP := GammaP) (GammaD := GammaD) (FF ⟶ x)).mpr
    (derivable_falsep_elim (Gamma := GammaD) (empty_context (L := L)) x)

theorem SequentCalculus2Axiomatization_inegpAX :
    IntuitionisticNegAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      ((y ⟶ x) ⟶ (~~ x) ⟶ (~~ y))).mpr
      (derivable_contrapositive (Gamma := GammaD) (empty_context (L := L)) x y)
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      ((~~ x) ⟶ x ⟶ y)).mpr
      (derivable_contradiction_elim1 (Gamma := GammaD) (empty_context (L := L)) x y)
  · intro x
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD) (x ⟶ (~~ (~~ x)))).mpr
      (derivable_double_negp_intros (Gamma := GammaD) (empty_context (L := L)) x)

theorem SequentCalculus2Axiomatization_iffpAX :
    IffAxiomatization L GammaP := by
  constructor
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      ((x ⟶ y) ⟶ (y ⟶ x) ⟶ (x ⟷ y))).mpr
      (derivable_iffp_intros (Gamma := GammaD) (empty_context (L := L)) x y)
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      ((x ⟷ y) ⟶ (x ⟶ y))).mpr
      (derivable_iffp_elim1 (Gamma := GammaD) (empty_context (L := L)) x y)
  · intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      ((x ⟷ y) ⟶ (y ⟶ x))).mpr
      (derivable_iffp_elim2 (Gamma := GammaD) (empty_context (L := L)) x y)

theorem SequentCalculus2Axiomatization_truepAX :
    TrueAxiomatization L GammaP := by
  constructor
  exact (ProvableDerivable.provable_derivable
    (L := L) (GammaP := GammaP) (GammaD := GammaD) TT).mpr
    (derivable_truep_intros (Gamma := GammaD) (empty_context (L := L)))

end SequentCalculus2Axiomatization

instance reg_SequentCalculus2Axiomatization_andpAX :
    RegisterClass D2P_reg
      (ProofRegistration.mk `andpAX ``SequentCalculus2Axiomatization_andpAX) 2 := {}

instance reg_SequentCalculus2Axiomatization_orpAX :
    RegisterClass D2P_reg
      (ProofRegistration.mk `orpAX ``SequentCalculus2Axiomatization_orpAX) 3 := {}

instance reg_SequentCalculus2Axiomatization_falsepAX :
    RegisterClass D2P_reg
      (ProofRegistration.mk `falsepAX ``SequentCalculus2Axiomatization_falsepAX) 4 := {}

instance reg_SequentCalculus2Axiomatization_inegpAX :
    RegisterClass D2P_reg
      (ProofRegistration.mk `inegpAX ``SequentCalculus2Axiomatization_inegpAX) 5 := {}

instance reg_SequentCalculus2Axiomatization_iffpAX :
    RegisterClass D2P_reg
      (ProofRegistration.mk `iffpAX ``SequentCalculus2Axiomatization_iffpAX) 6 := {}

instance reg_SequentCalculus2Axiomatization_truepAX :
    RegisterClass D2P_reg
      (ProofRegistration.mk `truepAX ``SequentCalculus2Axiomatization_truepAX) 7 := {}

section Axiomatization2SequentCalculus

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [OrLanguage L]
variable [FalseLanguage L] [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable L]
variable [GammaDP : DerivableProvable L GammaP GammaD]
variable [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
variable [MinimumAxiomatization L GammaP]
variable [AndAxiomatization L GammaP] [OrAxiomatization L GammaP]
variable [FalseAxiomatization L GammaP] [IntuitionisticNegAxiomatization L GammaP]
variable [IffAxiomatization L GammaP] [TrueAxiomatization L GammaP]

theorem Axiomatization2SequentCalculus_andpSC :
    AndSequentCalculus L GammaD := by
  letI : ProvableDerivable L GammaP GammaD := Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L GammaD := Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L GammaD := Axiomatization2SequentCalculus_minSC
  constructor
  · intro Phi x y hx hy
    exact MinimumSequentCalculus.deduction_modus_ponens Phi y (x && y) hy
      (MinimumSequentCalculus.deduction_modus_ponens Phi x (y ⟶ (x && y)) hx
        (deduction_weaken0 (GammaP := GammaP) Phi (x ⟶ y ⟶ (x && y))
          (AndAxiomatization.provable_andp_intros x y)))
  · intro Phi x y hxy
    exact MinimumSequentCalculus.deduction_modus_ponens Phi (x && y) x hxy
      (deduction_weaken0 (GammaP := GammaP) Phi ((x && y) ⟶ x)
        (AndAxiomatization.provable_andp_elim1 x y))
  · intro Phi x y hxy
    exact MinimumSequentCalculus.deduction_modus_ponens Phi (x && y) y hxy
      (deduction_weaken0 (GammaP := GammaP) Phi ((x && y) ⟶ y)
        (AndAxiomatization.provable_andp_elim2 x y))

theorem Axiomatization2SequentCalculus_orpSC :
    OrSequentCalculus L GammaD := by
  letI : ProvableDerivable L GammaP GammaD := Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L GammaD := Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L GammaD := Axiomatization2SequentCalculus_minSC
  constructor
  · intro Phi x y hx
    exact MinimumSequentCalculus.deduction_modus_ponens Phi x (x || y) hx
      (deduction_weaken0 (GammaP := GammaP) Phi (x ⟶ (x || y))
        (OrAxiomatization.provable_orp_intros1 x y))
  · intro Phi x y hy
    exact MinimumSequentCalculus.deduction_modus_ponens Phi y (x || y) hy
      (deduction_weaken0 (GammaP := GammaP) Phi (y ⟶ (x || y))
        (OrAxiomatization.provable_orp_intros2 x y))
  · intro Phi x y z hxz hyz
    have hxz' : Phi |--- (x ⟶ z) := (deduction_theorem Phi x z).mp hxz
    have hyz' : Phi |--- (y ⟶ z) := (deduction_theorem Phi y z).mp hyz
    have h1 : Phi |--- ((x ⟶ z) ⟶ (y ⟶ z) ⟶ ((x || y) ⟶ z)) :=
      deduction_weaken0 (GammaP := GammaP) Phi _
        (OrAxiomatization.provable_orp_elim x y z)
    have h2 : Phi |--- ((y ⟶ z) ⟶ ((x || y) ⟶ z)) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟶ z)
        ((y ⟶ z) ⟶ ((x || y) ⟶ z)) hxz' h1
    have h3 : Phi |--- ((x || y) ⟶ z) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (y ⟶ z)
        ((x || y) ⟶ z) hyz' h2
    exact (deduction_theorem Phi (x || y) z).mpr h3

theorem Axiomatization2SequentCalculus_falsepSC :
    FalseSequentCalculus L GammaD := by
  letI : ProvableDerivable L GammaP GammaD := Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L GammaD := Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L GammaD := Axiomatization2SequentCalculus_minSC
  constructor
  intro Phi x hff
  exact MinimumSequentCalculus.deduction_modus_ponens Phi FF x hff
    (deduction_weaken0 (GammaP := GammaP) Phi (FF ⟶ x)
      (FalseAxiomatization.provable_falsep_elim x))

theorem Axiomatization2SequentCalculus_inegpSC :
    IntuitionisticNegSequentCalculus L GammaD := by
  letI : ProvableDerivable L GammaP GammaD := Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L GammaD := Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L GammaD := Axiomatization2SequentCalculus_minSC
  constructor
  · intro Phi x y hyx
    have hyx' : Phi |--- (y ⟶ x) := (deduction_theorem Phi y x).mp hyx
    have hcp : Phi |--- ((y ⟶ x) ⟶ (~~ x) ⟶ (~~ y)) :=
      deduction_weaken0 (GammaP := GammaP) Phi _
        (IntuitionisticNegAxiomatization.provable_contrapositivePP x y)
    have h : Phi |--- ((~~ x) ⟶ (~~ y)) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (y ⟶ x) ((~~ x) ⟶ (~~ y)) hyx' hcp
    exact (deduction_theorem Phi (~~ x) (~~ y)).mpr h
  · intro Phi x y hx hnx
    have h1 : Phi |--- ((~~ x) ⟶ x ⟶ y) :=
      deduction_weaken0 (GammaP := GammaP) Phi _
        (IntuitionisticNegAxiomatization.provable_contradiction_elim1 x y)
    have h2 : Phi |--- (x ⟶ y) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (~~ x) (x ⟶ y) hnx h1
    exact MinimumSequentCalculus.deduction_modus_ponens Phi x y hx h2
  · intro Phi x hx
    exact MinimumSequentCalculus.deduction_modus_ponens Phi x (~~ (~~ x)) hx
      (deduction_weaken0 (GammaP := GammaP) Phi _
        (IntuitionisticNegAxiomatization.provable_double_negp_intros x))

theorem Axiomatization2SequentCalculus_iffpSC :
    IffSequentCalculus L GammaD := by
  letI : ProvableDerivable L GammaP GammaD := Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L GammaD := Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L GammaD := Axiomatization2SequentCalculus_minSC
  constructor
  · intro Phi x y hxy hyx
    have hxy' : Phi |--- (x ⟶ y) := (deduction_theorem Phi x y).mp hxy
    have hyx' : Phi |--- (y ⟶ x) := (deduction_theorem Phi y x).mp hyx
    have h0 : Phi |--- ((x ⟶ y) ⟶ (y ⟶ x) ⟶ (x ⟷ y)) :=
      deduction_weaken0 (GammaP := GammaP) Phi _
        (IffAxiomatization.provable_iffp_intros x y)
    have h1 : Phi |--- ((y ⟶ x) ⟶ (x ⟷ y)) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟶ y)
        ((y ⟶ x) ⟶ (x ⟷ y)) hxy' h0
    exact MinimumSequentCalculus.deduction_modus_ponens Phi (y ⟶ x) (x ⟷ y) hyx' h1
  · intro Phi x y hiff
    have h : Phi |--- ((x ⟷ y) ⟶ (x ⟶ y)) :=
      deduction_weaken0 (GammaP := GammaP) Phi _
        (IffAxiomatization.provable_iffp_elim1 x y)
    have hxy : Phi |--- (x ⟶ y) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟷ y) (x ⟶ y) hiff h
    exact (deduction_theorem Phi x y).mpr hxy
  · intro Phi x y hiff
    have h : Phi |--- ((x ⟷ y) ⟶ (y ⟶ x)) :=
      deduction_weaken0 (GammaP := GammaP) Phi _
        (IffAxiomatization.provable_iffp_elim2 x y)
    have hyx : Phi |--- (y ⟶ x) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟷ y) (y ⟶ x) hiff h
    exact (deduction_theorem Phi y x).mpr hyx

theorem Axiomatization2SequentCalculus_truepSC :
    TrueSequentCalculus L GammaD := by
  letI : ProvableDerivable L GammaP GammaD := Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L GammaD := Axiomatization2SequentCalculus_bSC
  constructor
  intro Phi
  exact deduction_weaken0 (GammaP := GammaP) Phi TT TrueAxiomatization.provable_truep_intros

end Axiomatization2SequentCalculus

instance reg_Axiomatization2SequentCalculus_andpSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `andpSC ``Axiomatization2SequentCalculus_andpSC) 4 := {}

instance reg_Axiomatization2SequentCalculus_orpSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `orpSC ``Axiomatization2SequentCalculus_orpSC) 5 := {}

instance reg_Axiomatization2SequentCalculus_falsepSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `falsepSC ``Axiomatization2SequentCalculus_falsepSC) 6 := {}

instance reg_Axiomatization2SequentCalculus_inegpSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `inegpSC ``Axiomatization2SequentCalculus_inegpSC) 7 := {}

instance reg_Axiomatization2SequentCalculus_iffpSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `iffpSC ``Axiomatization2SequentCalculus_iffpSC) 8 := {}

instance reg_Axiomatization2SequentCalculus_truepSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `truepSC ``Axiomatization2SequentCalculus_truepSC) 9 := {}

private theorem provable_of_empty_derivable {L : Language.{u}}
    [GammaP : Provable L] [GammaD : Derivable L]
    [ProvableDerivable L GammaP GammaD] {x : @Language.expr L} :
    @Derivable.derivable L GammaD (empty_context (L := L)) x ->
      @Provable.provable L GammaP x := by
  intro h
  exact (ProvableDerivable.provable_derivable
    (L := L) (GammaP := GammaP) (GammaD := GammaD) x).mpr h

private theorem empty_derivable_of_provable {L : Language.{u}}
    [GammaP : Provable L] [GammaD : Derivable L]
    [ProvableDerivable L GammaP GammaD] {x : @Language.expr L} :
    @Provable.provable L GammaP x ->
      @Derivable.derivable L GammaD (empty_context (L := L)) x := by
  intro h
  exact (ProvableDerivable.provable_derivable
    (L := L) (GammaP := GammaP) (GammaD := GammaD) x).mp h

private theorem provable_iffp_intro_of {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    (x y : @Language.expr L) :
    @Provable.provable L Gamma (x ⟶ y) ->
      @Provable.provable L Gamma (y ⟶ x) ->
        @Provable.provable L Gamma (x ⟷ y) := by
  intro hxy hyx
  have h1 := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))
    (IffAxiomatization.provable_iffp_intros x y) hxy
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ x) (x ⟷ y) h1 hyx

private theorem Axiomatization2SequentCalculus_andpSC_minimal
    {L : Language.{u}} [MinimumLanguage L] [AndLanguage L]
    [GammaP : Provable L] [GammaD : Derivable L]
    [DerivableProvable L GammaP GammaD]
    [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
    [MinimumAxiomatization L GammaP] [AndAxiomatization L GammaP] :
    AndSequentCalculus L GammaD := by
  letI : ProvableDerivable L GammaP GammaD := Axiomatization2SequentCalculus_GammaPD
  constructor
  · intro Phi x y hx hy
    exact MinimumSequentCalculus.deduction_modus_ponens Phi y (x && y) hy
      (MinimumSequentCalculus.deduction_modus_ponens Phi x (y ⟶ (x && y)) hx
        (deduction_weaken0 (GammaP := GammaP) Phi (x ⟶ y ⟶ (x && y))
          (AndAxiomatization.provable_andp_intros x y)))
  · intro Phi x y hxy
    exact MinimumSequentCalculus.deduction_modus_ponens Phi (x && y) x hxy
      (deduction_weaken0 (GammaP := GammaP) Phi ((x && y) ⟶ x)
        (AndAxiomatization.provable_andp_elim1 x y))
  · intro Phi x y hxy
    exact MinimumSequentCalculus.deduction_modus_ponens Phi (x && y) y hxy
      (deduction_weaken0 (GammaP := GammaP) Phi ((x && y) ⟶ y)
        (AndAxiomatization.provable_andp_elim2 x y))

section DerivableRulesFromAxiomatization1

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [OrLanguage L]
variable [FalseLanguage L] [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma] [AndAxiomatization L Gamma]
variable [OrAxiomatization L Gamma] [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma] [IffAxiomatization L Gamma]
variable [TrueAxiomatization L Gamma]

theorem provables_andp_intros :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma x ->
        @Provable.provable L Gamma y ->
          @Provable.provable L Gamma (x && y) := by
  AddSequentCalculus
  intro x y hx hy
  exact (ProvableDerivable.provable_derivable
    (L := L) (GammaP := Gamma) (GammaD := (inferInstance : Derivable L)) (x && y)).mpr
    (AndSequentCalculus.derivables_andp_intros
      (Gamma := (inferInstance : Derivable L)) (empty_context (L := L)) x y
      ((ProvableDerivable.provable_derivable
        (L := L) (GammaP := Gamma) (GammaD := (inferInstance : Derivable L)) x).mp hx)
      ((ProvableDerivable.provable_derivable
        (L := L) (GammaP := Gamma) (GammaD := (inferInstance : Derivable L)) y).mp hy))

theorem provables_andp_elim1 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x && y) ->
        @Provable.provable L Gamma x := by
  intro x y h
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x && y) x (AndAxiomatization.provable_andp_elim1 x y) h

theorem provables_andp_elim2 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x && y) ->
        @Provable.provable L Gamma y := by
  intro x y h
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x && y) y (AndAxiomatization.provable_andp_elim2 x y) h

theorem provables_iffp_intros :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma (y ⟶ x) ->
          @Provable.provable L Gamma (x ⟷ y) := by
  intro x y hxy hyx
  have h1 := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))
    (IffAxiomatization.provable_iffp_intros x y) hxy
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ x) (x ⟷ y) h1 hyx

theorem provables_iffp_elim1 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟷ y) ->
        @Provable.provable L Gamma (x ⟶ y) := by
  intro x y h
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟷ y) (x ⟶ y) (IffAxiomatization.provable_iffp_elim1 x y) h

theorem provables_iffp_elim2 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟷ y) ->
        @Provable.provable L Gamma (y ⟶ x) := by
  intro x y h
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟷ y) (y ⟶ x) (IffAxiomatization.provable_iffp_elim2 x y) h

theorem provables_impp_elim :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma y ->
        @Provable.provable L Gamma (x ⟶ y) := by
  intro x y hy
  exact aux_minimun_rule00 y x hy

theorem provables_orp_impp_fold :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ z) ->
        @Provable.provable L Gamma (y ⟶ z) ->
          @Provable.provable L Gamma ((x || y) ⟶ z) := by
  intro x y z hx hy
  have h1 := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ z) ((y ⟶ z) ⟶ ((x || y) ⟶ z))
    (OrAxiomatization.provable_orp_elim x y z) hx
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ z) ((x || y) ⟶ z) h1 hy

theorem provables_orp_intros1 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma x ->
        @Provable.provable L Gamma (x || y) := by
  intro x y hx
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) x (x || y) (OrAxiomatization.provable_orp_intros1 x y) hx

theorem provables_orp_intros2 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma y ->
        @Provable.provable L Gamma (x || y) := by
  intro x y hy
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) y (x || y) (OrAxiomatization.provable_orp_intros2 x y) hy

theorem provables_impp_andp_fold :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma (x ⟶ z) ->
          @Provable.provable L Gamma (x ⟶ (y && z)) := by
  AddSequentCalculus
  intro x y z hxy hxz
  have hxyD : (empty_context (L := L)) |--- (x ⟶ y) :=
    empty_derivable_of_provable hxy
  have hxzD : (empty_context (L := L)) |--- (x ⟶ z) :=
    empty_derivable_of_provable hxz
  have hy : (empty_context (L := L) ;; x) |--- y :=
    (deduction_theorem (empty_context (L := L)) x y).mpr hxyD
  have hz : (empty_context (L := L) ;; x) |--- z :=
    (deduction_theorem (empty_context (L := L)) x z).mpr hxzD
  exact provable_of_empty_derivable
    ((deduction_theorem (empty_context (L := L)) x (y && z)).mp
      (AndSequentCalculus.derivables_andp_intros
        (empty_context (L := L) ;; x) y z hy hz))

theorem provable_derives_impp_andp :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟶ (x ⟶ z) ⟶ (x ⟶ (y && z))) := by
  AddSequentCalculus
  intro x y z
  let E : context (L := L) := empty_context (L := L)
  let C : context (L := L) := ((E ;; (x ⟶ y)) ;; (x ⟶ z)) ;; x
  have hxy : C |--- (x ⟶ y) :=
    derivable_assum C (x ⟶ y) (Or.inl (Or.inl (Or.inr rfl)))
  have hxz : C |--- (x ⟶ z) :=
    derivable_assum C (x ⟶ z) (Or.inl (Or.inr rfl))
  have hx : C |--- x :=
    derivable_assum C x (Or.inr rfl)
  have hy : C |--- y :=
    MinimumSequentCalculus.deduction_modus_ponens C x y hx hxy
  have hz : C |--- z :=
    MinimumSequentCalculus.deduction_modus_ponens C x z hx hxz
  have hyz : C |--- (y && z) :=
    AndSequentCalculus.derivables_andp_intros C y z hy hz
  exact provable_of_empty_derivable
    ((deduction_theorem E (x ⟶ y) ((x ⟶ z) ⟶ (x ⟶ (y && z)))).mp
      ((deduction_theorem (E ;; (x ⟶ y)) (x ⟶ z) (x ⟶ (y && z))).mp
        ((deduction_theorem ((E ;; (x ⟶ y)) ;; (x ⟶ z)) x (y && z)).mp hyz)))

theorem provable_iffp_refl :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟷ x) := by
  intro x
  exact provables_iffp_intros x x (provable_impp_refl x) (provable_impp_refl x)

theorem provable_contradiction_elim2 :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (~~ x) ⟶ y) := by
  intro x y
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) ((~~ x) ⟶ x ⟶ y) (x ⟶ (~~ x) ⟶ y)
    (provable_impp_arg_switch (~~ x) x y)
    (IntuitionisticNegAxiomatization.provable_contradiction_elim1 x y)

theorem provable_negp_derives :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((~~ x) ⟶ (x ⟶ FF)) := by
  intro x
  exact IntuitionisticNegAxiomatization.provable_contradiction_elim1 x FF

theorem aux_negp_rule :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma y ->
        @Provable.provable L Gamma ((x ⟶ (~~ y)) ⟶ (~~ x)) := by
  AddSequentCalculus
  intro x y hy
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := x ⟶ (~~ y)
  let Phi : context (L := L) := E ;; A
  have hyD : E |--- y := empty_derivable_of_provable hy
  have hdnyE : E |--- (~~ (~~ y)) :=
    IntuitionisticNegSequentCalculus.derivables_double_negp_intros E y hyD
  have hdnyPhi : Phi |--- (~~ (~~ y)) :=
    deduction_weaken1 E A (~~ (~~ y)) hdnyE
  have hA : (Phi ;; x) |--- A :=
    derivable_assum (Phi ;; x) A (Or.inl (Or.inr rfl))
  have hx : (Phi ;; x) |--- x :=
    derivable_assum1 Phi x
  have hny : (Phi ;; x) |--- (~~ y) :=
    MinimumSequentCalculus.deduction_modus_ponens (Phi ;; x) x (~~ y) hx hA
  have hnotnoty_to_notx : (Phi ;; (~~ (~~ y))) |--- (~~ x) :=
    IntuitionisticNegSequentCalculus.derivables_contrapositivePP Phi (~~ y) x hny
  have hnotx : Phi |--- (~~ x) :=
    deduction_subst1 Phi (~~ (~~ y)) (~~ x) hdnyPhi hnotnoty_to_notx
  exact provable_of_empty_derivable
    ((deduction_theorem E A (~~ x)).mp hnotx)

theorem provable_derives_negp :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ FF) ⟶ (~~ x)) := by
  AddSequentCalculus
  intro x
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := x ⟶ FF
  let Phi : context (L := L) := E ;; A
  let C : context (L := L) := Phi ;; x
  have hA : C |--- A :=
    derivable_assum C A (Or.inl (Or.inr rfl))
  have hx : C |--- x :=
    derivable_assum1 Phi x
  have hff : C |--- FF :=
    MinimumSequentCalculus.deduction_modus_ponens C x FF hx hA
  have hnotx : Phi |--- (~~ x) :=
    derivables_negp_fold Phi x hff
  exact provable_of_empty_derivable
    ((deduction_theorem E A (~~ x)).mp hnotx)

theorem provable_contrapositivePN :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((y ⟶ (~~ x)) ⟶ (x ⟶ (~~ y))) := by
  AddSequentCalculus
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := y ⟶ (~~ x)
  let Phi : context (L := L) := E ;; A
  let Psi : context (L := L) := Phi ;; x
  let C : context (L := L) := Psi ;; y
  have hA : C |--- A :=
    derivable_assum C A (Or.inl (Or.inl (Or.inr rfl)))
  have hy : C |--- y :=
    derivable_assum1 Psi y
  have hnx : C |--- (~~ x) :=
    MinimumSequentCalculus.deduction_modus_ponens C y (~~ x) hy hA
  have hx : C |--- x :=
    derivable_assum C x (Or.inl (Or.inr rfl))
  have hff : C |--- FF :=
    IntuitionisticNegSequentCalculus.derivables_contradiction_elim C x FF hx hnx
  have hny : Psi |--- (~~ y) :=
    derivables_negp_fold Psi y hff
  exact provable_of_empty_derivable
    ((deduction_theorem E A (x ⟶ (~~ y))).mp
      ((deduction_theorem Phi x (~~ y)).mp hny))

end DerivableRulesFromAxiomatization1

section DerivableRulesFromSequentCalculus2

variable {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
variable [Gamma : Derivable L]
variable [BasicSequentCalculus L Gamma] [MinimumSequentCalculus L Gamma]
variable [IntuitionisticNegSequentCalculus L Gamma]

theorem derivables_contrapositivePP' :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      (Phi |--- (y ⟶ x)) -> (Phi |--- ((~~ x) ⟶ (~~ y))) := by
  intro Phi x y hyx
  exact (deduction_theorem Phi (~~ x) (~~ y)).mp
    (IntuitionisticNegSequentCalculus.derivables_contrapositivePP Phi x y
      ((deduction_theorem Phi y x).mpr hyx))

theorem derivables_contrapositivePN' :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      (Phi |--- (y ⟶ (~~ x))) -> (Phi |--- (x ⟶ (~~ y))) := by
  intro Phi x y hy
  let Psi : context (L := L) := Phi ;; x
  have hpp : Phi |--- ((~~ (~~ x)) ⟶ (~~ y)) :=
    derivables_contrapositivePP' Phi (~~ x) y hy
  have hppPsi : Psi |--- ((~~ (~~ x)) ⟶ (~~ y)) :=
    deduction_weaken1 Phi x ((~~ (~~ x)) ⟶ (~~ y)) hpp
  have hdn : Psi |--- (~~ (~~ x)) :=
    IntuitionisticNegSequentCalculus.derivables_double_negp_intros Psi x
      (derivable_assum1 Phi x)
  exact (deduction_theorem Phi x (~~ y)).mp
    (MinimumSequentCalculus.deduction_modus_ponens Psi (~~ (~~ x)) (~~ y) hdn hppPsi)

theorem derivables_contrapositivePN :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      ((Phi ;; y) |--- (~~ x)) -> ((Phi ;; x) |--- (~~ y)) := by
  intro Phi x y h
  have hy : Phi |--- (y ⟶ (~~ x)) :=
    (deduction_theorem Phi y (~~ x)).mp h
  exact (deduction_theorem Phi x (~~ y)).mpr
    (derivables_contrapositivePN' Phi x y hy)

end DerivableRulesFromSequentCalculus2

section DerivableRulesFromAxiomatization2

variable {L : Language.{u}} [MinimumLanguage L]
variable [Gamma : Provable L] [MinimumAxiomatization L Gamma]

theorem solve_iffp_intros_minimal [IffLanguage L]
    [IffAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma (y ⟶ x) ->
          @Provable.provable L Gamma (x ⟷ y) := by
  intro x y hxy hyx
  have h1 := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))
    (IffAxiomatization.provable_iffp_intros x y) hxy
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ x) (x ⟷ y) h1 hyx

theorem impp2orp2_minimal [OrLanguage L] [NegLanguage L]
    [OrAxiomatization L Gamma] [IntuitionisticNegAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((~~ x) || y) ⟶ (x ⟶ y)) := by
  intro x y
  have h1 : @Provable.provable L Gamma
      ((y ⟶ x ⟶ y) ⟶ (((~~ x) || y) ⟶ (x ⟶ y))) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) ((~~ x) ⟶ x ⟶ y)
      ((y ⟶ x ⟶ y) ⟶ (((~~ x) || y) ⟶ (x ⟶ y)))
      (OrAxiomatization.provable_orp_elim (~~ x) y (x ⟶ y))
      (IntuitionisticNegAxiomatization.provable_contradiction_elim1 x y)
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ x ⟶ y) (((~~ x) || y) ⟶ (x ⟶ y)) h1
    (MinimumAxiomatization.axiom1 (Gamma := Gamma) y x)

section andp

variable [AndLanguage L] [AndAxiomatization L Gamma]

private theorem solve_impp_andp_minimal :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma (x ⟶ z) ->
          @Provable.provable L Gamma (x ⟶ (y && z)) := by
  letI : Derivable L := Provable2Derivable (L := L)
  letI : DerivableProvable L Gamma (Provable2Derivable (L := L)) :=
    Provable2Derivable_Normal
  letI : ProvableDerivable L Gamma (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_minSC
  letI : AndSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_andpSC_minimal
  intro x y z hxy hxz
  let E : context (L := L) := empty_context (L := L)
  let C : context (L := L) := E ;; x
  have hxyD : E |--- (x ⟶ y) := empty_derivable_of_provable hxy
  have hxzD : E |--- (x ⟶ z) := empty_derivable_of_provable hxz
  have hy : C |--- y := (deduction_theorem E x y).mpr hxyD
  have hz : C |--- z := (deduction_theorem E x z).mpr hxzD
  exact provable_of_empty_derivable
    ((deduction_theorem E x (y && z)).mp
      (AndSequentCalculus.derivables_andp_intros C y z hy hz))

theorem provable_impp_curry :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y ⟶ z) ⟶ ((x && y) ⟶ z)) := by
  letI : Derivable L := Provable2Derivable (L := L)
  letI : DerivableProvable L Gamma (Provable2Derivable (L := L)) :=
    Provable2Derivable_Normal
  letI : ProvableDerivable L Gamma (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_minSC
  letI : AndSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_andpSC_minimal
  intro x y z
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := x ⟶ y ⟶ z
  let C : context (L := L) := (E ;; A) ;; (x && y)
  have hA : C |--- A := derivable_assum C A (Or.inl (Or.inr rfl))
  have hxy : C |--- (x && y) := derivable_assum1 (E ;; A) (x && y)
  have hx : C |--- x := AndSequentCalculus.derivables_andp_elim1 C x y hxy
  have hy : C |--- y := AndSequentCalculus.derivables_andp_elim2 C x y hxy
  have hyz : C |--- (y ⟶ z) :=
    MinimumSequentCalculus.deduction_modus_ponens C x (y ⟶ z) hx hA
  have hz : C |--- z :=
    MinimumSequentCalculus.deduction_modus_ponens C y z hy hyz
  exact provable_of_empty_derivable
    ((deduction_theorem E A ((x && y) ⟶ z)).mp
      ((deduction_theorem (E ;; A) (x && y) z).mp hz))

theorem provable_impp_uncurry :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (((x && y) ⟶ z) ⟶ (x ⟶ y ⟶ z)) := by
  letI : Derivable L := Provable2Derivable (L := L)
  letI : DerivableProvable L Gamma (Provable2Derivable (L := L)) :=
    Provable2Derivable_Normal
  letI : ProvableDerivable L Gamma (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_minSC
  letI : AndSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_andpSC_minimal
  intro x y z
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := (x && y) ⟶ z
  let C : context (L := L) := ((E ;; A) ;; x) ;; y
  have hA : C |--- A := derivable_assum C A (Or.inl (Or.inl (Or.inr rfl)))
  have hx : C |--- x := derivable_assum C x (Or.inl (Or.inr rfl))
  have hy : C |--- y := derivable_assum1 ((E ;; A) ;; x) y
  have hxy : C |--- (x && y) :=
    AndSequentCalculus.derivables_andp_intros C x y hx hy
  have hz : C |--- z :=
    MinimumSequentCalculus.deduction_modus_ponens C (x && y) z hxy hA
  exact provable_of_empty_derivable
    ((deduction_theorem E A (x ⟶ y ⟶ z)).mp
      ((deduction_theorem (E ;; A) x (y ⟶ z)).mp
        ((deduction_theorem ((E ;; A) ;; x) y z).mp hz)))

theorem provable_andp_impp [IffLanguage L] [IffAxiomatization L Gamma] :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y ⟶ z) ⟷ ((x && y) ⟶ z)) := by
  intro x y z
  exact provable_iffp_intro_of (x ⟶ y ⟶ z) ((x && y) ⟶ z)
    (provable_impp_curry x y z) (provable_impp_uncurry x y z)

theorem provable_andp_impp_comm :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x && y) ⟶ (y && x)) := by
  letI : Derivable L := Provable2Derivable (L := L)
  letI : DerivableProvable L Gamma (Provable2Derivable (L := L)) :=
    Provable2Derivable_Normal
  letI : ProvableDerivable L Gamma (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_minSC
  letI : AndSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_andpSC_minimal
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let C : context (L := L) := E ;; (x && y)
  have hxy : C |--- (x && y) := derivable_assum1 E (x && y)
  have hx : C |--- x := AndSequentCalculus.derivables_andp_elim1 C x y hxy
  have hy : C |--- y := AndSequentCalculus.derivables_andp_elim2 C x y hxy
  exact provable_of_empty_derivable
    ((deduction_theorem E (x && y) (y && x)).mp
      (AndSequentCalculus.derivables_andp_intros C y x hy hx))

theorem provable_andp_comm [IffLanguage L] [IffAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x && y) ⟷ (y && x)) := by
  intro x y
  exact provable_iffp_intro_of (x && y) (y && x)
    (provable_andp_impp_comm x y) (provable_andp_impp_comm y x)

theorem provable_andp_impp_assoc1 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (((x && y) && z) ⟶ (x && (y && z))) := by
  letI : Derivable L := Provable2Derivable (L := L)
  letI : DerivableProvable L Gamma (Provable2Derivable (L := L)) :=
    Provable2Derivable_Normal
  letI : ProvableDerivable L Gamma (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_minSC
  letI : AndSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_andpSC_minimal
  intro x y z
  let E : context (L := L) := empty_context (L := L)
  let C : context (L := L) := E ;; ((x && y) && z)
  have h : C |--- ((x && y) && z) := derivable_assum1 E ((x && y) && z)
  have hxy : C |--- (x && y) := AndSequentCalculus.derivables_andp_elim1 C (x && y) z h
  have hx : C |--- x := AndSequentCalculus.derivables_andp_elim1 C x y hxy
  have hy : C |--- y := AndSequentCalculus.derivables_andp_elim2 C x y hxy
  have hz : C |--- z := AndSequentCalculus.derivables_andp_elim2 C (x && y) z h
  have hyz : C |--- (y && z) := AndSequentCalculus.derivables_andp_intros C y z hy hz
  exact provable_of_empty_derivable
    ((deduction_theorem E ((x && y) && z) (x && (y && z))).mp
      (AndSequentCalculus.derivables_andp_intros C x (y && z) hx hyz))

theorem provable_andp_impp_assoc2 :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma ((x && (y && z)) ⟶ ((x && y) && z)) := by
  letI : Derivable L := Provable2Derivable (L := L)
  letI : DerivableProvable L Gamma (Provable2Derivable (L := L)) :=
    Provable2Derivable_Normal
  letI : ProvableDerivable L Gamma (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_minSC
  letI : AndSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_andpSC_minimal
  intro x y z
  let E : context (L := L) := empty_context (L := L)
  let C : context (L := L) := E ;; (x && (y && z))
  have h : C |--- (x && (y && z)) := derivable_assum1 E (x && (y && z))
  have hx : C |--- x := AndSequentCalculus.derivables_andp_elim1 C x (y && z) h
  have hyz : C |--- (y && z) := AndSequentCalculus.derivables_andp_elim2 C x (y && z) h
  have hy : C |--- y := AndSequentCalculus.derivables_andp_elim1 C y z hyz
  have hz : C |--- z := AndSequentCalculus.derivables_andp_elim2 C y z hyz
  have hxy : C |--- (x && y) := AndSequentCalculus.derivables_andp_intros C x y hx hy
  exact provable_of_empty_derivable
    ((deduction_theorem E (x && (y && z)) ((x && y) && z)).mp
      (AndSequentCalculus.derivables_andp_intros C (x && y) z hxy hz))

theorem provable_andp_assoc [IffLanguage L] [IffAxiomatization L Gamma] :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (((x && y) && z) ⟷ (x && (y && z))) := by
  intro x y z
  exact provable_iffp_intro_of ((x && y) && z) (x && (y && z))
    (provable_andp_impp_assoc1 x y z) (provable_andp_impp_assoc2 x y z)

theorem provable_andp_truep_derives [TrueLanguage L] [TrueAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((x && TT) ⟶ x) := by
  intro x
  exact AndAxiomatization.provable_andp_elim1 x TT

theorem provable_derives_andp_truep [TrueLanguage L] [TrueAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (x && TT)) := by
  intro x
  have hxt : @Provable.provable L Gamma (x ⟶ TT) :=
    aux_minimun_rule00 TT x TrueAxiomatization.provable_truep_intros
  have hstep := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ TT ⟶ (x && TT))
    ((x ⟶ TT) ⟶ x ⟶ (x && TT))
    (MinimumAxiomatization.axiom2 (Gamma := Gamma) x TT (x && TT))
    (AndAxiomatization.provable_andp_intros x TT)
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ TT) (x ⟶ (x && TT)) hstep hxt

theorem provable_andp_truep [TrueLanguage L] [IffLanguage L]
    [TrueAxiomatization L Gamma] [IffAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((x && TT) ⟷ x) := by
  intro x
  exact provable_iffp_intro_of (x && TT) x (provable_andp_truep_derives x) (provable_derives_andp_truep x)

theorem provable_truep_andp_derives [TrueLanguage L] [TrueAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((TT && x) ⟶ x) := by
  intro x
  exact AndAxiomatization.provable_andp_elim2 TT x

theorem provable_derives_truep_andp [TrueLanguage L] [TrueAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (TT && x)) := by
  intro x
  have hintro_switched : @Provable.provable L Gamma (x ⟶ TT ⟶ (TT && x)) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (TT ⟶ x ⟶ (TT && x)) (x ⟶ TT ⟶ (TT && x))
      (provable_impp_arg_switch TT x (TT && x))
      (AndAxiomatization.provable_andp_intros TT x)
  have hxt : @Provable.provable L Gamma (x ⟶ TT) :=
    aux_minimun_rule00 TT x TrueAxiomatization.provable_truep_intros
  have hstep := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ TT ⟶ (TT && x))
    ((x ⟶ TT) ⟶ x ⟶ (TT && x))
    (MinimumAxiomatization.axiom2 (Gamma := Gamma) x TT (TT && x))
    hintro_switched
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ TT) (x ⟶ (TT && x)) hstep hxt

theorem provable_truep_andp [TrueLanguage L] [IffLanguage L]
    [TrueAxiomatization L Gamma] [IffAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((TT && x) ⟷ x) := by
  intro x
  exact provable_iffp_intro_of (TT && x) x (provable_truep_andp_derives x) (provable_derives_truep_andp x)

theorem impp_andp_Adjoint :
    ProofTheoryPatternsP.Adjointness L Gamma andp impp := by
  constructor
  intro x y z
  constructor
  · intro h
    exact MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) ((x && y) ⟶ z) (x ⟶ y ⟶ z)
      (provable_impp_uncurry x y z) h
  · intro h
    exact MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (x ⟶ y ⟶ z) ((x && y) ⟶ z)
      (provable_impp_curry x y z) h

theorem andp_Comm :
    ProofTheoryPatternsP.Commutativity L Gamma andp := by
  constructor
  intro x y
  exact provable_andp_impp_comm x y

theorem andp_Mono :
    ProofTheoryPatternsP.Monotonicity L Gamma andp := by
  letI : ProofTheoryPatternsP.Adjointness L Gamma andp impp := impp_andp_Adjoint
  letI : ProofTheoryPatternsP.Commutativity L Gamma andp := andp_Comm
  exact ProofTheoryPatternsP.Adjoint2Mono (prodp := andp) (funcp := impp)

theorem andp_LU [TrueLanguage L] [TrueAxiomatization L Gamma] :
    ProofTheoryPatternsP.LeftUnit L Gamma TT andp := by
  constructor
  · exact provable_truep_andp_derives
  · exact provable_derives_truep_andp

theorem andp_RU [TrueLanguage L] [TrueAxiomatization L Gamma] :
    ProofTheoryPatternsP.RightUnit L Gamma TT andp := by
  constructor
  · exact provable_andp_truep_derives
  · exact provable_derives_andp_truep

theorem andp_Assoc :
    ProofTheoryPatternsP.Associativity L Gamma andp := by
  constructor
  · intro x y z
    exact provable_andp_impp_assoc2 x y z
  · intro x y z
    exact provable_andp_impp_assoc1 x y z

end andp

variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma] [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]

theorem provable_demorgan_orp_negp :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((~~ x) || (~~ y)) ⟶ (~~ (x && y))) := by
  AddSequentCalculus
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := (~~ x) || (~~ y)
  let B : @Language.expr L := x && y
  let Phi : context (L := L) := E ;; A
  have htoFalse : Phi |--- (B ⟶ FF) := by
    apply (deduction_theorem Phi B FF).mp
    let Psi : context (L := L) := Phi ;; B
    have hA : Psi |--- A :=
      derivable_assum Psi A (Or.inl (Or.inr rfl))
    have hAtoFF : Psi |--- (A ⟶ FF) := by
      apply derivables_orp_elim'
      · apply (deduction_theorem Psi (~~ x) FF).mp
        let C : context (L := L) := Psi ;; (~~ x)
        have hnx : C |--- (~~ x) := derivable_assum1 Psi (~~ x)
        have hB : C |--- B := derivable_assum C B (Or.inl (Or.inr rfl))
        have hx : C |--- x := AndSequentCalculus.derivables_andp_elim1 C x y hB
        have hxf : C |--- (x ⟶ FF) :=
          MinimumSequentCalculus.deduction_modus_ponens C (~~ x) (x ⟶ FF) hnx
            (deduction_weaken0 (GammaP := Gamma) C _ (provable_negp_derives x))
        exact MinimumSequentCalculus.deduction_modus_ponens C x FF hx hxf
      · apply (deduction_theorem Psi (~~ y) FF).mp
        let C : context (L := L) := Psi ;; (~~ y)
        have hny : C |--- (~~ y) := derivable_assum1 Psi (~~ y)
        have hB : C |--- B := derivable_assum C B (Or.inl (Or.inr rfl))
        have hy : C |--- y := AndSequentCalculus.derivables_andp_elim2 C x y hB
        have hyf : C |--- (y ⟶ FF) :=
          MinimumSequentCalculus.deduction_modus_ponens C (~~ y) (y ⟶ FF) hny
            (deduction_weaken0 (GammaP := Gamma) C _ (provable_negp_derives y))
        exact MinimumSequentCalculus.deduction_modus_ponens C y FF hy hyf
    exact MinimumSequentCalculus.deduction_modus_ponens Psi A FF hA hAtoFF
  have hfold : Phi |--- ((B ⟶ FF) ⟶ (~~ B)) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (provable_derives_negp B)
  have hnot : Phi |--- (~~ B) :=
    MinimumSequentCalculus.deduction_modus_ponens Phi (B ⟶ FF) (~~ B) htoFalse hfold
  exact provable_of_empty_derivable
    ((deduction_theorem E A (~~ B)).mp hnot)

theorem provable_demorgan_negp_orp :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((~~ (x || y)) ⟷ ((~~ x) && (~~ y))) := by
  intro x y
  have hleft : @Provable.provable L Gamma ((~~ (x || y)) ⟶ ((~~ x) && (~~ y))) :=
    provables_impp_andp_fold (~~ (x || y)) (~~ x) (~~ y)
      (MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (x ⟶ (x || y)) ((~~ (x || y)) ⟶ (~~ x))
        (IntuitionisticNegAxiomatization.provable_contrapositivePP (x || y) x)
        (OrAxiomatization.provable_orp_intros1 x y))
      (MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (y ⟶ (x || y)) ((~~ (x || y)) ⟶ (~~ y))
        (IntuitionisticNegAxiomatization.provable_contrapositivePP (x || y) y)
        (OrAxiomatization.provable_orp_intros2 x y))
  have hright : @Provable.provable L Gamma (((~~ x) && (~~ y)) ⟶ (~~ (x || y))) := by
    AddSequentCalculus
    let E : context (L := L) := empty_context (L := L)
    let A : @Language.expr L := (~~ x) && (~~ y)
    let B : @Language.expr L := x || y
    let Phi : context (L := L) := E ;; A
    have htoFalse : Phi |--- (B ⟶ FF) := by
      apply derivables_orp_elim'
      · apply (deduction_theorem Phi x FF).mp
        let C : context (L := L) := Phi ;; x
        have hA : C |--- A := derivable_assum C A (Or.inl (Or.inr rfl))
        have hnx : C |--- (~~ x) :=
          AndSequentCalculus.derivables_andp_elim1 C (~~ x) (~~ y) hA
        have hx : C |--- x := derivable_assum1 Phi x
        have hxf : C |--- (x ⟶ FF) :=
          MinimumSequentCalculus.deduction_modus_ponens C (~~ x) (x ⟶ FF) hnx
            (deduction_weaken0 (GammaP := Gamma) C _ (provable_negp_derives x))
        exact MinimumSequentCalculus.deduction_modus_ponens C x FF hx hxf
      · apply (deduction_theorem Phi y FF).mp
        let C : context (L := L) := Phi ;; y
        have hA : C |--- A := derivable_assum C A (Or.inl (Or.inr rfl))
        have hny : C |--- (~~ y) :=
          AndSequentCalculus.derivables_andp_elim2 C (~~ x) (~~ y) hA
        have hy : C |--- y := derivable_assum1 Phi y
        have hyf : C |--- (y ⟶ FF) :=
          MinimumSequentCalculus.deduction_modus_ponens C (~~ y) (y ⟶ FF) hny
            (deduction_weaken0 (GammaP := Gamma) C _ (provable_negp_derives y))
        exact MinimumSequentCalculus.deduction_modus_ponens C y FF hy hyf
    have hfold : Phi |--- ((B ⟶ FF) ⟶ (~~ B)) :=
      deduction_weaken0 (GammaP := Gamma) Phi _ (provable_derives_negp B)
    exact provable_of_empty_derivable
      ((deduction_theorem E A (~~ B)).mp
        (MinimumSequentCalculus.deduction_modus_ponens Phi (B ⟶ FF) (~~ B) htoFalse hfold))
  exact provables_iffp_intros _ _ hleft hright

theorem provable_truep :
    @Provable.provable L Gamma TT := by
  exact TrueAxiomatization.provable_truep_intros

theorem provable_orp_impp_comm :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x || y) ⟶ (y || x)) := by
  intro x y
  exact provables_orp_impp_fold x y (y || x)
    (OrAxiomatization.provable_orp_intros2 y x)
    (OrAxiomatization.provable_orp_intros1 y x)

theorem provables_orp_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      @Provable.provable L Gamma (x1 ⟶ x2) ->
        @Provable.provable L Gamma (y1 ⟶ y2) ->
          @Provable.provable L Gamma ((x1 || y1) ⟶ (x2 || y2)) := by
  intro x1 x2 y1 y2 hx hy
  exact provables_orp_impp_fold x1 y1 (x2 || y2)
    (solve_impp_trans x1 x2 (x2 || y2) hx (OrAxiomatization.provable_orp_intros1 x2 y2))
    (solve_impp_trans y1 y2 (x2 || y2) hy (OrAxiomatization.provable_orp_intros2 x2 y2))

theorem provable_orp_comm :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x || y) ⟷ (y || x)) := by
  intro x y
  exact provables_iffp_intros _ _ (provable_orp_impp_comm x y) (provable_orp_impp_comm y x)

theorem provable_orp_assoc :
    forall x y z : @Language.expr L,
      @Provable.provable L Gamma (((x || y) || z) ⟷ (x || (y || z))) := by
  intro x y z
  have h1 : @Provable.provable L Gamma (((x || y) || z) ⟶ (x || (y || z))) :=
    provables_orp_impp_fold (x || y) z (x || (y || z))
      (provables_orp_impp_fold x y (x || (y || z))
        (OrAxiomatization.provable_orp_intros1 x (y || z))
        (solve_impp_trans y (y || z) (x || (y || z))
          (OrAxiomatization.provable_orp_intros1 y z)
          (OrAxiomatization.provable_orp_intros2 x (y || z))))
      (solve_impp_trans z (y || z) (x || (y || z))
        (OrAxiomatization.provable_orp_intros2 y z)
        (OrAxiomatization.provable_orp_intros2 x (y || z)))
  have h2 : @Provable.provable L Gamma ((x || (y || z)) ⟶ ((x || y) || z)) :=
    provables_orp_impp_fold x (y || z) ((x || y) || z)
      (solve_impp_trans x (x || y) ((x || y) || z)
        (OrAxiomatization.provable_orp_intros1 x y)
        (OrAxiomatization.provable_orp_intros1 (x || y) z))
      (provables_orp_impp_fold y z ((x || y) || z)
        (solve_impp_trans y (x || y) ((x || y) || z)
          (OrAxiomatization.provable_orp_intros2 x y)
          (OrAxiomatization.provable_orp_intros1 (x || y) z))
        (OrAxiomatization.provable_orp_intros2 (x || y) z))
  exact provables_iffp_intros _ _ h1 h2

theorem or_Comm :
    ProofTheoryPatternsP.Commutativity L Gamma orp := by
  constructor
  intro x y
  exact provable_orp_impp_comm x y

theorem orp_Mono :
    ProofTheoryPatternsP.Monotonicity L Gamma orp := by
  constructor
  intro x1 y1 x2 y2 hx hy
  exact provables_orp_mono x1 x2 y1 y2 hx hy

theorem provable_falsep_orp_derives :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((FF || x) ⟶ x) := by
  intro x
  exact provables_orp_impp_fold FF x x
    (FalseAxiomatization.provable_falsep_elim x) (provable_impp_refl x)

theorem provable_derives_falsep_orp :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (FF || x)) := by
  intro x
  exact OrAxiomatization.provable_orp_intros2 FF x

theorem provable_falsep_orp :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((FF || x) ⟷ x) := by
  intro x
  exact provables_iffp_intros _ _ (provable_falsep_orp_derives x) (provable_derives_falsep_orp x)

theorem provable_orp_falsep :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((x || FF) ⟷ x) := by
  intro x
  exact provables_iffp_intros _ _
    (provables_orp_impp_fold x FF x (provable_impp_refl x)
      (FalseAxiomatization.provable_falsep_elim x))
    (OrAxiomatization.provable_orp_intros1 x FF)

theorem provable_truep_impp :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (((TT : @Language.expr L) ⟶ x) ⟷ x) := by
  intro x
  have h1 : @Provable.provable L Gamma (((TT : @Language.expr L) ⟶ x) ⟶ x) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) TT (((TT : @Language.expr L) ⟶ x) ⟶ x)
      (aux_minimun_theorem02 TT x) TrueAxiomatization.provable_truep_intros
  have h2 : @Provable.provable L Gamma (x ⟶ ((TT : @Language.expr L) ⟶ x)) :=
    MinimumAxiomatization.axiom1 (Gamma := Gamma) x TT
  exact provables_iffp_intros _ _ h1 h2

theorem provable_andp_dup :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((x && x) ⟷ x) := by
  intro x
  exact provables_iffp_intros _ _
    (AndAxiomatization.provable_andp_elim1 x x)
    (provables_impp_andp_fold x x x (provable_impp_refl x) (provable_impp_refl x))

theorem provable_orp_dup1 :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((x || x) ⟶ x) := by
  intro x
  exact provables_orp_impp_fold x x x (provable_impp_refl x) (provable_impp_refl x)

theorem provable_orp_dup2 :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (x || x)) := by
  intro x
  exact OrAxiomatization.provable_orp_intros1 x x

theorem provable_orp_dup :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((x || x) ⟷ x) := by
  intro x
  exact provables_iffp_intros _ _ (provable_orp_dup1 x) (provable_orp_dup2 x)

theorem provable_negp :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((~~ x) ⟷ (x ⟶ FF)) := by
  intro x
  exact provables_iffp_intros _ _ (provable_negp_derives x) (provable_derives_negp x)

theorem provable_iffp :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟷ y) ⟷ ((x ⟶ y) && (y ⟶ x))) := by
  intro x y
  have h1 : @Provable.provable L Gamma ((x ⟷ y) ⟶ ((x ⟶ y) && (y ⟶ x))) :=
    provables_impp_andp_fold (x ⟷ y) (x ⟶ y) (y ⟶ x)
      (IffAxiomatization.provable_iffp_elim1 x y)
      (IffAxiomatization.provable_iffp_elim2 x y)
  have h2 : @Provable.provable L Gamma (((x ⟶ y) && (y ⟶ x)) ⟶ (x ⟷ y)) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) ((x ⟶ y) ⟶ (y ⟶ x) ⟶ (x ⟷ y))
      (((x ⟶ y) && (y ⟶ x)) ⟶ (x ⟷ y))
      (provable_impp_curry (x ⟶ y) (y ⟶ x) (x ⟷ y))
      (IffAxiomatization.provable_iffp_intros x y)
  exact provables_iffp_intros _ _ h1 h2

theorem provable_neqp_orp_derives :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((~~ x) || y) ⟶ (x ⟶ y)) := by
  intro x y
  exact provables_orp_impp_fold (~~ x) y (x ⟶ y)
    (IntuitionisticNegAxiomatization.provable_contradiction_elim1 x y)
    (MinimumAxiomatization.axiom1 (Gamma := Gamma) y x)

end DerivableRulesFromAxiomatization2

section DerivableRulesFromDeductionOr

variable {L : Language.{u}} [OrLanguage L]
variable [GammaD1 : Derivable1 L]
variable [BasicDeduction L GammaD1] [OrDeduction L GammaD1]

theorem derivable1_orp_comm :
    forall x y : @Language.expr L, (x || y) |-- (y || x) := by
  intro x y
  exact OrDeduction.derivable1_orp_elim x y (y || x)
    (OrDeduction.derivable1_orp_intros2 y x)
    (OrDeduction.derivable1_orp_intros1 y x)

theorem derivable1_orp_assoc1 :
    forall x y z : @Language.expr L,
      ((x || y) || z) |-- (x || (y || z)) := by
  intro x y z
  apply OrDeduction.derivable1_orp_elim
  · apply OrDeduction.derivable1_orp_elim
    · exact OrDeduction.derivable1_orp_intros1 x (y || z)
    · exact derivable1_trans y (y || z) (x || (y || z))
        (OrDeduction.derivable1_orp_intros1 y z)
        (OrDeduction.derivable1_orp_intros2 x (y || z))
  · exact derivable1_trans z (y || z) (x || (y || z))
      (OrDeduction.derivable1_orp_intros2 y z)
      (OrDeduction.derivable1_orp_intros2 x (y || z))

theorem derivable1_orp_mono :
    forall x1 x2 y1 y2 : @Language.expr L,
      x1 |-- x2 -> y1 |-- y2 -> (x1 || y1) |-- (x2 || y2) := by
  intro x1 x2 y1 y2 hx hy
  apply OrDeduction.derivable1_orp_elim
  · exact derivable1_trans x1 x2 (x2 || y2) hx
      (OrDeduction.derivable1_orp_intros1 x2 y2)
  · exact derivable1_trans y1 y2 (x2 || y2) hy
      (OrDeduction.derivable1_orp_intros2 x2 y2)

theorem derivable1_orp_Comm :
    ProofTheoryPatterns.D1.Commutativity L GammaD1 orp := by
  constructor
  intro x y
  exact derivable1_orp_comm x y

theorem derivable1_orp_Mono :
    ProofTheoryPatterns.D1.Monotonicity L GammaD1 orp := by
  constructor
  intro x1 y1 x2 y2 hx hy
  exact derivable1_orp_mono x1 x2 y1 y2 hx hy

end DerivableRulesFromDeductionOr

section DerivableRulesFromLogicEquiv

variable {L : Language.{u}} [MinimumLanguage L] [OrLanguage L] [IffLanguage L]
variable [GammaE : LogicEquiv L] [GammaP : Provable L]
variable [EquivProvable L GammaP GammaE]
variable [MinimumAxiomatization L GammaP] [OrAxiomatization L GammaP]
variable [IffAxiomatization L GammaP]

theorem logic_equiv_iffp :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE x y <->
        @Provable.provable L GammaP (x ⟷ y) := by
  intro x y
  constructor
  · intro h
    have hp := (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaE) x y).mp h
    have h1 := MinimumAxiomatization.modus_ponens
      (Gamma := GammaP) (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))
      (IffAxiomatization.provable_iffp_intros x y) hp.left
    exact MinimumAxiomatization.modus_ponens
      (Gamma := GammaP) (y ⟶ x) (x ⟷ y) h1 hp.right
  · intro h
    have hxy := MinimumAxiomatization.modus_ponens
      (Gamma := GammaP) (x ⟷ y) (x ⟶ y)
      (IffAxiomatization.provable_iffp_elim1 x y) h
    have hyx := MinimumAxiomatization.modus_ponens
      (Gamma := GammaP) (x ⟷ y) (y ⟶ x)
      (IffAxiomatization.provable_iffp_elim2 x y) h
    exact (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaE) x y).mpr
      ⟨hxy, hyx⟩

end DerivableRulesFromLogicEquiv

theorem provable_derivable1_true
    {L : Language.{u}} [MinimumLanguage L] [TrueLanguage L]
    [GammaP : Provable L] [GammaD1 : Derivable1 L]
    [MinimumAxiomatization L GammaP] [TrueDeduction L GammaD1]
    [BasicDeduction L GammaD1] [Derivable1Provable L GammaP GammaD1]
    [ProvableDerivable1 L GammaP GammaD1] :
    forall x : @Language.expr L,
      @Provable.provable L GammaP x <-> @Derivable1.derivable1 L GammaD1 TT x := by
  intro x
  constructor
  · intro hx
    exact provable_right x TT hx
  · intro h
    have ht : @Derivable1.derivable1 L GammaD1 (x ⟶ x) TT :=
      TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) (x ⟶ x)
    have hx : @Derivable1.derivable1 L GammaD1 (x ⟶ x) x :=
      derivable1_trans (x ⟶ x) TT x ht h
    exact (ProvableDerivable1.provable_derivable1
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x).mpr hx

instance reg_Axiomatization2Deduction_GammaPD1 :
    RegisterClass P2D1_reg
      (ProofRegistration.mk `GammaPD1 ``Axiomatization2Deduction_GammaPD1) 1 := {}

section Axiomatization2LogicEquiv

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaE : LogicEquiv L]
variable [EquivProvable L GammaP GammaE]
variable [MinimumAxiomatization L GammaP]

theorem Axiomatization2LogicEquiv_imppE :
    ImpLogicEquiv L GammaE := by
  constructor
  intro x1 x2 y1 y2 hx hy
  have hxP := (EquivProvable.logic_equiv_provable
    (L := L) (GammaP := GammaP) (GammaL := GammaE) x1 x2).mp hx
  have hyP := (EquivProvable.logic_equiv_provable
    (L := L) (GammaP := GammaP) (GammaL := GammaE) y1 y2).mp hy
  exact (EquivProvable.logic_equiv_provable
    (L := L) (GammaP := GammaP) (GammaL := GammaE) (x1 ⟶ y1) (x2 ⟶ y2)).mpr
    ⟨(provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper
        x1 x2 hxP.right y1 y2 hyP.left,
      (provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper
        x2 x1 hxP.left y2 y1 hyP.right⟩

end Axiomatization2LogicEquiv

section Intuitionistic820AdditionalRules

namespace PropositionalLogic.ProofTheory.Intuitionistic

abbrev derivable1_impp_refl := @Unifysl.derivable1_base

end PropositionalLogic.ProofTheory.Intuitionistic

theorem derivable1s_andp_mono {L : Language.{u}} [AndLanguage L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [AndDeduction L GammaD1] :
    forall x1 x2 y1 y2 : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x1 x2 ->
      @Derivable1.derivable1 L GammaD1 y1 y2 ->
      @Derivable1.derivable1 L GammaD1 (x1 && y1) (x2 && y2) := by
  intro x1 x2 y1 y2 hx hy
  have hx' : @Derivable1.derivable1 L GammaD1 (x1 && y1) x2 :=
    derivable1_trans (x1 && y1) x1 x2
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x1 y1) hx
  have hy' : @Derivable1.derivable1 L GammaD1 (x1 && y1) y2 :=
    derivable1_trans (x1 && y1) y1 y2
      (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x1 y1) hy
  exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
    (x1 && y1) x2 y2 hx' hy'

private theorem derivable1_andp_assoc_rev {L : Language.{u}} [AndLanguage L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [AndDeduction L GammaD1] :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x && (y && z)) ((x && y) && z) := by
  intro x y z
  let s : @Language.expr L := x && (y && z)
  have hx : @Derivable1.derivable1 L GammaD1 s x :=
    AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x (y && z)
  have hyz : @Derivable1.derivable1 L GammaD1 s (y && z) :=
    AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x (y && z)
  have hy : @Derivable1.derivable1 L GammaD1 s y :=
    derivable1_trans s (y && z) y hyz
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) y z)
  have hz : @Derivable1.derivable1 L GammaD1 s z :=
    derivable1_trans s (y && z) z hyz
      (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) y z)
  have hxy : @Derivable1.derivable1 L GammaD1 s (x && y) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) s x y hx hy
  exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) s (x && y) z hxy hz

private theorem derivable1_andp_comm_no_min {L : Language.{u}} [AndLanguage L]
    [GammaD1 : Derivable1 L] [AndDeduction L GammaD1] :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x && y) (y && x) := by
  intro x y
  exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) (x && y) y x
    (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x y)
    (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x y)

private theorem derivable1_andp_assoc_no_min {L : Language.{u}} [AndLanguage L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [AndDeduction L GammaD1] :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 ((x && y) && z) (x && (y && z)) := by
  intro x y z
  let s : @Language.expr L := (x && y) && z
  have hsxy : @Derivable1.derivable1 L GammaD1 s (x && y) :=
    AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) (x && y) z
  have hx : @Derivable1.derivable1 L GammaD1 s x :=
    derivable1_trans s (x && y) x hsxy
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x y)
  have hy : @Derivable1.derivable1 L GammaD1 s y :=
    derivable1_trans s (x && y) y hsxy
      (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x y)
  have hz : @Derivable1.derivable1 L GammaD1 s z :=
    AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (x && y) z
  have hyz : @Derivable1.derivable1 L GammaD1 s (y && z) :=
    AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) s y z hy hz
  exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) s x (y && z) hx hyz

private theorem derivable1_orp_assoc_rev {L : Language.{u}} [OrLanguage L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [OrDeduction L GammaD1] :
    forall x y z : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 (x || (y || z)) ((x || y) || z) := by
  intro x y z
  apply OrDeduction.derivable1_orp_elim
  · exact derivable1_trans x (x || y) ((x || y) || z)
      (OrDeduction.derivable1_orp_intros1 (GammaD1 := GammaD1) x y)
      (OrDeduction.derivable1_orp_intros1 (GammaD1 := GammaD1) (x || y) z)
  · apply OrDeduction.derivable1_orp_elim
    · exact derivable1_trans y (x || y) ((x || y) || z)
        (OrDeduction.derivable1_orp_intros2 (GammaD1 := GammaD1) x y)
        (OrDeduction.derivable1_orp_intros1 (GammaD1 := GammaD1) (x || y) z)
    · exact OrDeduction.derivable1_orp_intros2 (GammaD1 := GammaD1) (x || y) z

section Deduction2LogicEquiv

variable {L : Language.{u}}
variable [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
variable [EquivDerivable1 L GammaD1 GammaE]
variable [BasicDeduction L GammaD1]

theorem Deduction2LogicEquiv_andpE [AndLanguage L]
    [AndDeduction L GammaD1] : AndLogicEquiv L GammaE := by
  constructor
  · intro x1 x2 y1 y2 hx hy
    have hxD := (__logic_equiv_derivable1 (L := L) x1 x2).mp hx
    have hyD := (__logic_equiv_derivable1 (L := L) y1 y2).mp hy
    exact (__logic_equiv_derivable1 (L := L) (x1 && y1) (x2 && y2)).mpr
      ⟨derivable1s_andp_mono x1 x2 y1 y2 hxD.left hyD.left,
        derivable1s_andp_mono x2 x1 y2 y1 hxD.right hyD.right⟩
  · intro x y
    exact (__logic_equiv_derivable1 (L := L) (x && y) (y && x)).mpr
      ⟨derivable1_andp_comm_no_min x y, derivable1_andp_comm_no_min y x⟩
  · intro x y z
    exact (__logic_equiv_derivable1 (L := L) ((x && y) && z) (x && (y && z))).mpr
      ⟨derivable1_andp_assoc_no_min x y z, derivable1_andp_assoc_rev x y z⟩

theorem Deduction2LogicEquiv_orpE [OrLanguage L]
    [OrDeduction L GammaD1] : OrLogicEquiv L GammaE := by
  constructor
  · intro x1 x2 y1 y2 hx hy
    have hxD := (__logic_equiv_derivable1 (L := L) x1 x2).mp hx
    have hyD := (__logic_equiv_derivable1 (L := L) y1 y2).mp hy
    exact (__logic_equiv_derivable1 (L := L) (x1 || y1) (x2 || y2)).mpr
      ⟨derivable1_orp_mono x1 x2 y1 y2 hxD.left hyD.left,
        derivable1_orp_mono x2 x1 y2 y1 hxD.right hyD.right⟩
  · intro x y
    exact (__logic_equiv_derivable1 (L := L) (x || y) (y || x)).mpr
      ⟨derivable1_orp_comm x y, derivable1_orp_comm y x⟩
  · intro x y z
    exact (__logic_equiv_derivable1 (L := L) ((x || y) || z) (x || (y || z))).mpr
      ⟨derivable1_orp_assoc1 x y z, derivable1_orp_assoc_rev x y z⟩

theorem Deduction2LogicEquiv_truepandpE [AndLanguage L] [TrueLanguage L]
    [AndDeduction L GammaD1] [TrueDeduction L GammaD1] :
    TrueAndLogicEquiv L GammaE := by
  constructor
  · intro x
    exact (__logic_equiv_derivable1 (L := L) (x && TT) x).mpr
      ⟨AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x TT,
        AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) x x TT
          (derivable1_refl x)
          (TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) x)⟩
  · intro x
    exact (__logic_equiv_derivable1 (L := L) (TT && x) x).mpr
      ⟨AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) TT x,
        AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) x TT x
          (TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) x)
          (derivable1_refl x)⟩

theorem logic_equiv_andp_swap [AndLanguage L] [AndDeduction L GammaD1]
    [AndLogicEquiv L GammaE] :
    forall x y z : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (x && (y && z)) (y && (x && z)) := by
  intro x y z
  have hcomm1 := (__logic_equiv_derivable1 (L := L) ((y && z) && x) (x && (y && z))).mp
    (AndLogicEquiv.logic_equiv_andp_comm (GammaE := GammaE) (y && z) x)
  have hassoc1 := (__logic_equiv_derivable1 (L := L) ((y && z) && x) (y && (z && x))).mp
    (AndLogicEquiv.logic_equiv_andp_assoc (GammaE := GammaE) y z x)
  have hzxe := (__logic_equiv_derivable1 (L := L) (z && x) (x && z)).mp
    (AndLogicEquiv.logic_equiv_andp_comm (GammaE := GammaE) z x)
  have hy : @Derivable1.derivable1 L GammaD1 y y := derivable1_refl y
  have hcongr1 : @Derivable1.derivable1 L GammaD1 (y && (z && x)) (y && (x && z)) :=
    derivable1s_andp_mono y y (z && x) (x && z) hy hzxe.left
  have hforward : @Derivable1.derivable1 L GammaD1 (x && (y && z)) (y && (x && z)) :=
    derivable1_trans (x && (y && z)) ((y && z) && x) (y && (x && z))
      hcomm1.right
      (derivable1_trans ((y && z) && x) (y && (z && x)) (y && (x && z))
        hassoc1.left hcongr1)
  have hcomm2 := (__logic_equiv_derivable1 (L := L) ((x && z) && y) (y && (x && z))).mp
    (AndLogicEquiv.logic_equiv_andp_comm (GammaE := GammaE) (x && z) y)
  have hassoc2 := (__logic_equiv_derivable1 (L := L) ((x && z) && y) (x && (z && y))).mp
    (AndLogicEquiv.logic_equiv_andp_assoc (GammaE := GammaE) x z y)
  have hzye := (__logic_equiv_derivable1 (L := L) (z && y) (y && z)).mp
    (AndLogicEquiv.logic_equiv_andp_comm (GammaE := GammaE) z y)
  have hx : @Derivable1.derivable1 L GammaD1 x x := derivable1_refl x
  have hcongr2 : @Derivable1.derivable1 L GammaD1 (x && (z && y)) (x && (y && z)) :=
    derivable1s_andp_mono x x (z && y) (y && z) hx hzye.left
  have hbackward : @Derivable1.derivable1 L GammaD1 (y && (x && z)) (x && (y && z)) :=
    derivable1_trans (y && (x && z)) ((x && z) && y) (x && (y && z))
      hcomm2.right
      (derivable1_trans ((x && z) && y) (x && (z && y)) (x && (y && z))
        hassoc2.left hcongr2)
  exact (__logic_equiv_derivable1 (L := L) (x && (y && z)) (y && (x && z))).mpr
    ⟨hforward, hbackward⟩

end Deduction2LogicEquiv

end Intuitionistic820AdditionalRules

instance reg_Axiomatization2LogicEquiv_imppE :
    RegisterClass P2E_reg
      (ProofRegistration.mk `imppE ``Axiomatization2LogicEquiv_imppE) 1 := {}

end Unifysl
