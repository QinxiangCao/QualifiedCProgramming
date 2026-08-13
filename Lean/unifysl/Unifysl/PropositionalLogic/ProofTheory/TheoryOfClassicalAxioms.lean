import Unifysl.PropositionalLogic.ProofTheory.GodelDummett

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `PropositionalLogic/ProofTheory/TheoryOfClassicalAxioms.v`:
- Class `PeirceLaw`
- Field `__provable_peirce_law`
- Class `ByContradiction`
- Field `__by_contradiction`
- Class `DoubleNegElimination`
- Field `__double_negp_elim`
- Class `ClassicAnalysis`
- Field `__classic_analysis`
- Class `ExcludedMiddle`
- Field `__excluded_middle`
- Class `ImplyToOr`
- Field `__provable_derives_negp_orp`
- Lemma `ExcludedMiddle2ClassicAnalysis`
- Lemma `ClassicAnalysis2ExcludedMiddle`
- Lemma `ClassicAnalysis2ImplyToOr`
- Lemma `ImplyToOr2ExcludedMiddle`
- Lemma `Peirce2ByContradiction`
- Lemma `ByContradiction2DoubleNegElimination`
- Lemma `DoubleNegElimination2ClassicAnalysis`
- Lemma `ClassicAnalysis2DoubleNegElimination`
- Lemma `ClassicAnalysis2PeirceLaw`
- Lemma `ByContradiction2IntuitionisticNegAxiomatization`
-/

universe u

namespace Unifysl

open PropositionalLanguageNotation

class PeirceLaw (L : Language.{u}) [MinimumLanguage L]
    (Gamma : Provable L) : Prop where
  __provable_peirce_law :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((x ⟶ y) ⟶ x) ⟶ x)

namespace PeirceLaw

end PeirceLaw

theorem __provable_peirce_law {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Provable L] [PeirceLaw L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((x ⟶ y) ⟶ x) ⟶ x) :=
  PeirceLaw.__provable_peirce_law (Gamma := Gamma)

class ByContradiction (L : Language.{u}) [MinimumLanguage L]
    [NegLanguage L] (Gamma : Provable L) : Prop where
  __by_contradiction :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((~~ x) ⟶ y) ⟶ ((~~ x) ⟶ (~~ y)) ⟶ x)

class DoubleNegElimination (L : Language.{u}) [MinimumLanguage L]
    [NegLanguage L] (Gamma : Provable L) : Prop where
  __double_negp_elim :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((~~ (~~ x)) ⟶ x)

class ClassicAnalysis (L : Language.{u}) [MinimumLanguage L]
    [NegLanguage L] (Gamma : Provable L) : Prop where
  __classic_analysis :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟶ ((~~ x) ⟶ y) ⟶ y)

class ExcludedMiddle (L : Language.{u}) [OrLanguage L]
    [NegLanguage L] (Gamma : Provable L) : Prop where
  __excluded_middle :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x || (~~ x))

class ImplyToOr (L : Language.{u}) [MinimumLanguage L]
    [OrLanguage L] [NegLanguage L] (Gamma : Provable L) : Prop where
  __provable_derives_negp_orp :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟶ ((~~ x) || y))

namespace ImplyToOr

end ImplyToOr

theorem __provable_derives_negp_orp {L : Language.{u}} [MinimumLanguage L]
    [OrLanguage L] [NegLanguage L]
    [Gamma : Provable L] [ImplyToOr L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟶ ((~~ x) || y)) :=
  ImplyToOr.__provable_derives_negp_orp (Gamma := Gamma)

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

theorem Axiomatization2SequentCalculus_orpSC_minimal
    {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [GammaP : Provable L] [GammaD : Derivable L]
    [ProvableDerivable L GammaP GammaD]
    [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
    [OrAxiomatization L GammaP] :
    OrSequentCalculus L GammaD := by
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
    have h0 : Phi |--- ((x ⟶ z) ⟶ (y ⟶ z) ⟶ ((x || y) ⟶ z)) :=
      deduction_weaken0 (GammaP := GammaP) Phi _
        (OrAxiomatization.provable_orp_elim x y z)
    have h1 : Phi |--- ((y ⟶ z) ⟶ ((x || y) ⟶ z)) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟶ z)
        ((y ⟶ z) ⟶ ((x || y) ⟶ z)) hxz' h0
    have h2 : Phi |--- ((x || y) ⟶ z) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (y ⟶ z)
        ((x || y) ⟶ z) hyz' h1
    exact (deduction_theorem Phi (x || y) z).mpr h2

theorem Axiomatization2SequentCalculus_inegpSC_minimal
    {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [GammaP : Provable L] [GammaD : Derivable L]
    [ProvableDerivable L GammaP GammaD]
    [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
    [IntuitionisticNegAxiomatization L GammaP] :
    IntuitionisticNegSequentCalculus L GammaD := by
  constructor
  · intro Phi x y hyx
    have hyx' : Phi |--- (y ⟶ x) := (deduction_theorem Phi y x).mp hyx
    have hcp : Phi |--- ((y ⟶ x) ⟶ (~~ x) ⟶ (~~ y)) :=
      deduction_weaken0 (GammaP := GammaP) Phi _
        (IntuitionisticNegAxiomatization.provable_contrapositivePP x y)
    have h : Phi |--- ((~~ x) ⟶ (~~ y)) :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (y ⟶ x)
        ((~~ x) ⟶ (~~ y)) hyx' hcp
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

private theorem solve_orp_impp_minimal
    {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [OrAxiomatization L Gamma] :
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

private theorem orp_comm_impp_minimal
    {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [OrAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x || y) ⟶ (y || x)) := by
  intro x y
  exact solve_orp_impp_minimal x y (y || x)
    (OrAxiomatization.provable_orp_intros2 y x)
    (OrAxiomatization.provable_orp_intros1 y x)

private theorem contradiction_elim2_minimal
    {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [IntuitionisticNegAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (~~ x) ⟶ y) := by
  intro x y
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) ((~~ x) ⟶ x ⟶ y) (x ⟶ (~~ x) ⟶ y)
    (provable_impp_arg_switch (~~ x) x y)
    (IntuitionisticNegAxiomatization.provable_contradiction_elim1 x y)

private theorem negp_aux_rule_minimal
    {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [IntuitionisticNegAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma y ->
        @Provable.provable L Gamma ((x ⟶ (~~ y)) ⟶ (~~ x)) := by
  intro x y hy
  have hdny : @Provable.provable L Gamma (~~ (~~ y)) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) y (~~ (~~ y))
      (IntuitionisticNegAxiomatization.provable_double_negp_intros y) hy
  have hcp :
      @Provable.provable L Gamma ((x ⟶ (~~ y)) ⟶ (~~ (~~ y)) ⟶ (~~ x)) :=
    IntuitionisticNegAxiomatization.provable_contrapositivePP (~~ y) x
  have hswap :
      @Provable.provable L Gamma
        (((x ⟶ (~~ y)) ⟶ (~~ (~~ y)) ⟶ (~~ x)) ⟶
          (~~ (~~ y)) ⟶ (x ⟶ (~~ y)) ⟶ (~~ x)) :=
    provable_impp_arg_switch (x ⟶ (~~ y)) (~~ (~~ y)) (~~ x)
  have hstep :
      @Provable.provable L Gamma ((~~ (~~ y)) ⟶ (x ⟶ (~~ y)) ⟶ (~~ x)) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) _ _ hswap hcp
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (~~ (~~ y)) ((x ⟶ (~~ y)) ⟶ (~~ x)) hstep hdny

private theorem contrapositivePN_minimal
    {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [IntuitionisticNegAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((y ⟶ (~~ x)) ⟶ (x ⟶ (~~ y))) := by
  AddSequentCalculus
  letI : IntuitionisticNegSequentCalculus L (inferInstance : Derivable L) :=
    Axiomatization2SequentCalculus_inegpSC_minimal
      (GammaP := Gamma) (GammaD := (inferInstance : Derivable L))
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := y ⟶ (~~ x)
  let Phi : context (L := L) := E ;; A
  have hA : Phi |--- A := derivable_assum1 E A
  have hxy : Phi |--- (x ⟶ (~~ y)) :=
    derivables_contrapositivePN' Phi x y hA
  exact provable_of_empty_derivable
    ((deduction_theorem E A (x ⟶ (~~ y))).mp hxy)

section ExcludedMiddle2ClassicAnalysis

variable {L : Language.{u}} [MinimumLanguage L]
variable [OrLanguage L] [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [OrAxiomatization L Gamma]
variable [ExcludedMiddle L Gamma]

theorem ExcludedMiddle2ClassicAnalysis : ClassicAnalysis L Gamma := by
  constructor
  AddSequentCalculus
  letI : OrSequentCalculus L (inferInstance : Derivable L) :=
    Axiomatization2SequentCalculus_orpSC_minimal
      (GammaP := Gamma) (GammaD := (inferInstance : Derivable L))
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := x ⟶ y
  let B : @Language.expr L := (~~ x) ⟶ y
  let Phi : context (L := L) := (E ;; A) ;; B
  have hem : Phi |--- (x || (~~ x)) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (ExcludedMiddle.__excluded_middle x)
  have hxcase : (Phi ;; x) |--- y := by
    have hA : (Phi ;; x) |--- A :=
      derivable_assum (Phi ;; x) A (Or.inl (Or.inl (Or.inr rfl)))
    have hx : (Phi ;; x) |--- x := derivable_assum1 Phi x
    exact MinimumSequentCalculus.deduction_modus_ponens (Phi ;; x) x y hx hA
  have hnxcase : (Phi ;; (~~ x)) |--- y := by
    have hB : (Phi ;; (~~ x)) |--- B :=
      derivable_assum (Phi ;; (~~ x)) B (Or.inl (Or.inr rfl))
    have hnx : (Phi ;; (~~ x)) |--- (~~ x) := derivable_assum1 Phi (~~ x)
    exact MinimumSequentCalculus.deduction_modus_ponens (Phi ;; (~~ x)) (~~ x) y hnx hB
  have hy : Phi |--- y :=
    OrSequentCalculus.derivables_orp_elim Phi x (~~ x) y hxcase hnxcase
      |> fun h => deduction_subst1 Phi (x || (~~ x)) y hem h
  exact provable_of_empty_derivable
    ((deduction_theorem E A (B ⟶ y)).mp
      ((deduction_theorem (E ;; A) B y).mp hy))

end ExcludedMiddle2ClassicAnalysis

section ClassicAnalysis2ImplyToOr

variable {L : Language.{u}} [MinimumLanguage L]
variable [OrLanguage L] [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [OrAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [ClassicAnalysis L Gamma]

theorem ClassicAnalysis2ExcludedMiddle : ExcludedMiddle L Gamma := by
  constructor
  intro x
  have hca := ClassicAnalysis.__classic_analysis
    (L := L) (Gamma := Gamma) x (x || (~~ x))
  have h1 := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ (x || (~~ x))) (((~~ x) ⟶ (x || (~~ x))) ⟶ (x || (~~ x)))
    hca (OrAxiomatization.provable_orp_intros1 x (~~ x))
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) ((~~ x) ⟶ (x || (~~ x))) (x || (~~ x))
    h1 (OrAxiomatization.provable_orp_intros2 x (~~ x))

theorem ClassicAnalysis2ImplyToOr : ImplyToOr L Gamma := by
  letI : ExcludedMiddle L Gamma := ClassicAnalysis2ExcludedMiddle
  constructor
  AddSequentCalculus
  letI : OrSequentCalculus L (inferInstance : Derivable L) :=
    Axiomatization2SequentCalculus_orpSC_minimal
      (GammaP := Gamma) (GammaD := (inferInstance : Derivable L))
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := x ⟶ y
  let Z : @Language.expr L := (~~ x) || y
  let Phi : context (L := L) := E ;; A
  have hem : Phi |--- (x || (~~ x)) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (ExcludedMiddle.__excluded_middle x)
  have hxcase : (Phi ;; x) |--- Z := by
    have hA : (Phi ;; x) |--- A := derivable_assum (Phi ;; x) A (Or.inl (Or.inr rfl))
    have hx : (Phi ;; x) |--- x := derivable_assum1 Phi x
    have hy : (Phi ;; x) |--- y :=
      MinimumSequentCalculus.deduction_modus_ponens (Phi ;; x) x y hx hA
    exact OrSequentCalculus.derivables_orp_intros2 (Phi ;; x) (~~ x) y hy
  have hnxcase : (Phi ;; (~~ x)) |--- Z := by
    exact OrSequentCalculus.derivables_orp_intros1 (Phi ;; (~~ x)) (~~ x) y
      (derivable_assum1 Phi (~~ x))
  have hz : Phi |--- Z :=
    OrSequentCalculus.derivables_orp_elim Phi x (~~ x) Z hxcase hnxcase
      |> fun h => deduction_subst1 Phi (x || (~~ x)) Z hem h
  exact provable_of_empty_derivable
    ((deduction_theorem E A Z).mp hz)

end ClassicAnalysis2ImplyToOr

section ImplyToOr2ExcludedMiddle

variable {L : Language.{u}} [MinimumLanguage L]
variable [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [ImplyToOr L Gamma]

theorem ImplyToOr2ExcludedMiddle : ExcludedMiddle L Gamma := by
  constructor
  intro x
  have h1 : @Provable.provable L Gamma ((~~ x) || x) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (x ⟶ x) ((~~ x) || x)
      (ImplyToOr.__provable_derives_negp_orp x x) (provable_impp_refl x)
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) ((~~ x) || x) (x || (~~ x))
    (orp_comm_impp_minimal (~~ x) x) h1

end ImplyToOr2ExcludedMiddle

section PeirceLaw2ByContradiction

variable {L : Language.{u}} [MinimumLanguage L]
variable [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [PeirceLaw L Gamma]

theorem Peirce2ByContradiction : ByContradiction L Gamma := by
  constructor
  AddSequentCalculus
  letI : IntuitionisticNegSequentCalculus L (inferInstance : Derivable L) :=
    Axiomatization2SequentCalculus_inegpSC_minimal
      (GammaP := Gamma) (GammaD := (inferInstance : Derivable L))
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := (~~ x) ⟶ y
  let B : @Language.expr L := (~~ x) ⟶ (~~ y)
  let K : @Language.expr L := x ⟶ (~~ (x ⟶ x))
  let Phi : context (L := L) := (E ;; A) ;; B
  let C : context (L := L) := Phi ;; K
  have hnxx : C |--- (~~ x) := by
    have hK : C |--- K := derivable_assum1 Phi K
    have haux : C |--- (K ⟶ (~~ x)) :=
      deduction_weaken0 (GammaP := Gamma) C _
        (negp_aux_rule_minimal x (x ⟶ x) (provable_impp_refl x))
    exact MinimumSequentCalculus.deduction_modus_ponens C K (~~ x) hK haux
  have hy : C |--- y := by
    have hA : C |--- A := derivable_assum C A (Or.inl (Or.inl (Or.inr rfl)))
    exact MinimumSequentCalculus.deduction_modus_ponens C (~~ x) y hnxx hA
  have hny : C |--- (~~ y) := by
    have hB : C |--- B := derivable_assum C B (Or.inl (Or.inr rfl))
    exact MinimumSequentCalculus.deduction_modus_ponens C (~~ x) (~~ y) hnxx hB
  have hx : C |--- x := by
    have hce : C |--- (y ⟶ (~~ y) ⟶ x) :=
      deduction_weaken0 (GammaP := Gamma) C _ (contradiction_elim2_minimal y x)
    exact MinimumSequentCalculus.deduction_modus_ponens C (~~ y) x hny
      (MinimumSequentCalculus.deduction_modus_ponens C y ((~~ y) ⟶ x) hy hce)
  have hKtoX : Phi |--- (K ⟶ x) := (deduction_theorem Phi K x).mp hx
  have hpeirce : Phi |--- ((K ⟶ x) ⟶ x) :=
    deduction_weaken0 (GammaP := Gamma) Phi _
      (PeirceLaw.__provable_peirce_law x (~~ (x ⟶ x)))
  have hxPhi : Phi |--- x :=
    MinimumSequentCalculus.deduction_modus_ponens Phi (K ⟶ x) x hKtoX hpeirce
  exact provable_of_empty_derivable
    ((deduction_theorem E A (B ⟶ x)).mp
      ((deduction_theorem (E ;; A) B x).mp hxPhi))

end PeirceLaw2ByContradiction

section ByContradiction2DoubleNegElimination

variable {L : Language.{u}} [MinimumLanguage L]
variable [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [ByContradiction L Gamma]

theorem ByContradiction2DoubleNegElimination :
    DoubleNegElimination L Gamma := by
  constructor
  AddSequentCalculus
  intro x
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := ~~ (~~ x)
  let Phi : context (L := L) := E ;; A
  have hbc : Phi |--- (((~~ x) ⟶ (~~ x)) ⟶ ((~~ x) ⟶ A) ⟶ x) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (ByContradiction.__by_contradiction x (~~ x))
  have hrefl : Phi |--- ((~~ x) ⟶ (~~ x)) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (provable_impp_refl (~~ x))
  have hAimp : Phi |--- ((~~ x) ⟶ A) := by
    apply (deduction_theorem Phi (~~ x) A).mp
    exact derivable_assum (Phi ;; (~~ x)) A (Or.inl (Or.inr rfl))
  have hx : Phi |--- x :=
    MinimumSequentCalculus.deduction_modus_ponens Phi ((~~ x) ⟶ A) x hAimp
      (MinimumSequentCalculus.deduction_modus_ponens Phi ((~~ x) ⟶ (~~ x))
        (((~~ x) ⟶ A) ⟶ x) hrefl hbc)
  exact provable_of_empty_derivable
    ((deduction_theorem E A x).mp hx)

end ByContradiction2DoubleNegElimination

section DoubleNegElimination2ClassicAnalysis

variable {L : Language.{u}} [MinimumLanguage L]
variable [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [DoubleNegElimination L Gamma]

theorem DoubleNegElimination2ClassicAnalysis : ClassicAnalysis L Gamma := by
  constructor
  AddSequentCalculus
  letI : IntuitionisticNegSequentCalculus L (inferInstance : Derivable L) :=
    Axiomatization2SequentCalculus_inegpSC_minimal
      (GammaP := Gamma) (GammaD := (inferInstance : Derivable L))
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := x ⟶ y
  let B : @Language.expr L := (~~ x) ⟶ y
  let Phi : context (L := L) := (E ;; A) ;; B
  let N : @Language.expr L := ~~ y
  have hNtoNotRefl : Phi |--- (N ⟶ (~~ (x ⟶ x))) := by
    apply (deduction_theorem Phi N (~~ (x ⟶ x))).mp
    let C : context (L := L) := Phi ;; N
    have hA : C |--- A := derivable_assum C A (Or.inl (Or.inl (Or.inr rfl)))
    have hB : C |--- B := derivable_assum C B (Or.inl (Or.inr rfl))
    have hN : C |--- N := derivable_assum1 Phi N
    have hnotx : C |--- (~~ x) := by
      have hcp : C |--- (A ⟶ N ⟶ (~~ x)) :=
        deduction_weaken0 (GammaP := Gamma) C _
          (IntuitionisticNegAxiomatization.provable_contrapositivePP y x)
      exact MinimumSequentCalculus.deduction_modus_ponens C N (~~ x) hN
        (MinimumSequentCalculus.deduction_modus_ponens C A (N ⟶ (~~ x)) hA hcp)
    have hdnotx : C |--- (~~ (~~ x)) := by
      have hcp : C |--- (B ⟶ N ⟶ (~~ (~~ x))) :=
        deduction_weaken0 (GammaP := Gamma) C _
          (IntuitionisticNegAxiomatization.provable_contrapositivePP y (~~ x))
      exact MinimumSequentCalculus.deduction_modus_ponens C N (~~ (~~ x)) hN
        (MinimumSequentCalculus.deduction_modus_ponens C B (N ⟶ (~~ (~~ x))) hB hcp)
    have hce : C |--- ((~~ x) ⟶ (~~ (~~ x)) ⟶ (~~ (x ⟶ x))) :=
      deduction_weaken0 (GammaP := Gamma) C _
        (contradiction_elim2_minimal (~~ x) (~~ (x ⟶ x)))
    exact MinimumSequentCalculus.deduction_modus_ponens C (~~ (~~ x)) (~~ (x ⟶ x)) hdnotx
      (MinimumSequentCalculus.deduction_modus_ponens C (~~ x)
        ((~~ (~~ x)) ⟶ (~~ (x ⟶ x))) hnotx hce)
  have hdny : Phi |--- (~~ (~~ y)) := by
    have haux : Phi |--- ((N ⟶ (~~ (x ⟶ x))) ⟶ (~~ N)) :=
      deduction_weaken0 (GammaP := Gamma) Phi _
        (negp_aux_rule_minimal N (x ⟶ x) (provable_impp_refl x))
    exact MinimumSequentCalculus.deduction_modus_ponens Phi (N ⟶ (~~ (x ⟶ x))) (~~ N)
      hNtoNotRefl haux
  have hy : Phi |--- y :=
    MinimumSequentCalculus.deduction_modus_ponens Phi (~~ (~~ y)) y hdny
      (deduction_weaken0 (GammaP := Gamma) Phi _ (DoubleNegElimination.__double_negp_elim y))
  exact provable_of_empty_derivable
    ((deduction_theorem E A (B ⟶ y)).mp
      ((deduction_theorem (E ;; A) B y).mp hy))

end DoubleNegElimination2ClassicAnalysis

section ClassicAnalysis2PeirceLaw

variable {L : Language.{u}} [MinimumLanguage L]
variable [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [ClassicAnalysis L Gamma]

theorem ClassicAnalysis2DoubleNegElimination : DoubleNegElimination L Gamma := by
  constructor
  AddSequentCalculus
  intro x
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := ~~ (~~ x)
  let Phi : context (L := L) := E ;; A
  have hca : Phi |--- ((x ⟶ x) ⟶ ((~~ x) ⟶ x) ⟶ x) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (ClassicAnalysis.__classic_analysis x x)
  have hrefl : Phi |--- (x ⟶ x) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (provable_impp_refl x)
  have hnotx_to_x : Phi |--- ((~~ x) ⟶ x) := by
    apply (deduction_theorem Phi (~~ x) x).mp
    let C : context (L := L) := Phi ;; (~~ x)
    have hA : C |--- A := derivable_assum C A (Or.inl (Or.inr rfl))
    have hnx : C |--- (~~ x) := derivable_assum1 Phi (~~ x)
    have hce : C |--- (A ⟶ (~~ x) ⟶ x) :=
      deduction_weaken0 (GammaP := Gamma) C _
        (IntuitionisticNegAxiomatization.provable_contradiction_elim1 (~~ x) x)
    exact MinimumSequentCalculus.deduction_modus_ponens C (~~ x) x hnx
      (MinimumSequentCalculus.deduction_modus_ponens C A ((~~ x) ⟶ x) hA hce)
  have hx : Phi |--- x :=
    MinimumSequentCalculus.deduction_modus_ponens Phi ((~~ x) ⟶ x) x hnotx_to_x
      (MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟶ x)
        (((~~ x) ⟶ x) ⟶ x) hrefl hca)
  exact provable_of_empty_derivable
    ((deduction_theorem E A x).mp hx)

theorem ClassicAnalysis2PeirceLaw : PeirceLaw L Gamma := by
  constructor
  AddSequentCalculus
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := (x ⟶ y) ⟶ x
  let Phi : context (L := L) := E ;; A
  have hca : Phi |--- ((x ⟶ x) ⟶ ((~~ x) ⟶ x) ⟶ x) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (ClassicAnalysis.__classic_analysis x x)
  have hrefl : Phi |--- (x ⟶ x) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (provable_impp_refl x)
  have hnotx_to_x : Phi |--- ((~~ x) ⟶ x) := by
    apply (deduction_theorem Phi (~~ x) x).mp
    let C : context (L := L) := Phi ;; (~~ x)
    have hA : C |--- A := derivable_assum C A (Or.inl (Or.inr rfl))
    have hnx : C |--- (~~ x) := derivable_assum1 Phi (~~ x)
    have hxy : C |--- (x ⟶ y) := by
      apply (deduction_theorem C x y).mp
      let D : context (L := L) := C ;; x
      have hnxD : D |--- (~~ x) :=
        derivable_assum D (~~ x) (Or.inl (Or.inr rfl))
      have hxD : D |--- x := derivable_assum1 C x
      have hce : D |--- ((~~ x) ⟶ x ⟶ y) :=
        deduction_weaken0 (GammaP := Gamma) D _
          (IntuitionisticNegAxiomatization.provable_contradiction_elim1 x y)
      exact MinimumSequentCalculus.deduction_modus_ponens D x y hxD
        (MinimumSequentCalculus.deduction_modus_ponens D (~~ x) (x ⟶ y) hnxD hce)
    exact MinimumSequentCalculus.deduction_modus_ponens C (x ⟶ y) x hxy hA
  have hx : Phi |--- x :=
    MinimumSequentCalculus.deduction_modus_ponens Phi ((~~ x) ⟶ x) x hnotx_to_x
      (MinimumSequentCalculus.deduction_modus_ponens Phi (x ⟶ x)
        (((~~ x) ⟶ x) ⟶ x) hrefl hca)
  exact provable_of_empty_derivable
    ((deduction_theorem E A x).mp hx)

end ClassicAnalysis2PeirceLaw

section ByContradiction2IntuitionisticNegAxiomatization

variable {L : Language.{u}} [MinimumLanguage L]
variable [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [ByContradiction L Gamma]

theorem ByContradiction2IntuitionisticNegAxiomatization :
    IntuitionisticNegAxiomatization L Gamma := by
  letI : DoubleNegElimination L Gamma := ByContradiction2DoubleNegElimination
  constructor
  · intro x y
    AddSequentCalculus
    let E : context (L := L) := empty_context (L := L)
    let A : @Language.expr L := y ⟶ x
    let B : @Language.expr L := ~~ x
    let Ctx : context (L := L) := (E ;; A) ;; B
    let NNY : @Language.expr L := ~~ (~~ y)
    have h1 : Ctx |--- (NNY ⟶ x) := by
      apply (deduction_theorem Ctx NNY x).mp
      let C : context (L := L) := Ctx ;; NNY
      have hA : C |--- A := derivable_assum C A (Or.inl (Or.inl (Or.inr rfl)))
      have hnny : C |--- NNY := derivable_assum1 Ctx NNY
      have hy : C |--- y :=
        MinimumSequentCalculus.deduction_modus_ponens C NNY y hnny
          (deduction_weaken0 (GammaP := Gamma) C _
            (DoubleNegElimination.__double_negp_elim y))
      exact MinimumSequentCalculus.deduction_modus_ponens C y x hy hA
    have h2 : Ctx |--- (NNY ⟶ B) := by
      apply (deduction_theorem Ctx NNY B).mp
      exact derivable_assum (Ctx ;; NNY) B (Or.inl (Or.inr rfl))
    have hbc : Ctx |--- ((NNY ⟶ x) ⟶ (NNY ⟶ B) ⟶ (~~ y)) :=
      deduction_weaken0 (GammaP := Gamma) Ctx _
        (ByContradiction.__by_contradiction (~~ y) x)
    have hnoty : Ctx |--- (~~ y) :=
      MinimumSequentCalculus.deduction_modus_ponens Ctx (NNY ⟶ B) (~~ y) h2
        (MinimumSequentCalculus.deduction_modus_ponens Ctx (NNY ⟶ x)
          ((NNY ⟶ B) ⟶ (~~ y)) h1 hbc)
    exact provable_of_empty_derivable
      ((deduction_theorem E A (B ⟶ (~~ y))).mp
        ((deduction_theorem (E ;; A) B (~~ y)).mp hnoty))
  · intro x y
    AddSequentCalculus
    let E : context (L := L) := empty_context (L := L)
    let A : @Language.expr L := ~~ x
    let Phi : context (L := L) := E ;; A
    have hxtoY : Phi |--- (x ⟶ y) := by
      apply (deduction_theorem Phi x y).mp
      let C : context (L := L) := Phi ;; x
      let NY : @Language.expr L := ~~ y
      have hx : C |--- x := derivable_assum1 Phi x
      have hA : C |--- A := derivable_assum C A (Or.inl (Or.inr rfl))
      have h1 : C |--- (NY ⟶ x) := by
        apply (deduction_theorem C NY x).mp
        exact deduction_weaken1 C NY x hx
      have h2 : C |--- (NY ⟶ A) := by
        apply (deduction_theorem C NY A).mp
        exact deduction_weaken1 C NY A hA
      have hbc : C |--- ((NY ⟶ x) ⟶ (NY ⟶ A) ⟶ y) :=
        deduction_weaken0 (GammaP := Gamma) C _
          (ByContradiction.__by_contradiction y x)
      exact MinimumSequentCalculus.deduction_modus_ponens C (NY ⟶ A) y h2
        (MinimumSequentCalculus.deduction_modus_ponens C (NY ⟶ x)
          ((NY ⟶ A) ⟶ y) h1 hbc)
    exact provable_of_empty_derivable
      ((deduction_theorem E A (x ⟶ y)).mp hxtoY)
  · intro x
    AddSequentCalculus
    let E : context (L := L) := empty_context (L := L)
    let Phi : context (L := L) := E ;; x
    let P : @Language.expr L := ~~ (~~ x)
    let NP : @Language.expr L := ~~ P
    have h1 : Phi |--- (NP ⟶ x) := by
      apply (deduction_theorem Phi NP x).mp
      exact derivable_assum (Phi ;; NP) x (Or.inl (Or.inr rfl))
    have h2 : Phi |--- (NP ⟶ (~~ x)) :=
      deduction_weaken0 (GammaP := Gamma) Phi _
        (DoubleNegElimination.__double_negp_elim (~~ x))
    have hbc : Phi |--- ((NP ⟶ x) ⟶ (NP ⟶ (~~ x)) ⟶ P) :=
      deduction_weaken0 (GammaP := Gamma) Phi _
        (ByContradiction.__by_contradiction P x)
    have hp : Phi |--- P :=
      MinimumSequentCalculus.deduction_modus_ponens Phi (NP ⟶ (~~ x)) P h2
        (MinimumSequentCalculus.deduction_modus_ponens Phi (NP ⟶ x)
          ((NP ⟶ (~~ x)) ⟶ P) h1 hbc)
    exact provable_of_empty_derivable
      ((deduction_theorem E x P).mp hp)

end ByContradiction2IntuitionisticNegAxiomatization

end Unifysl
