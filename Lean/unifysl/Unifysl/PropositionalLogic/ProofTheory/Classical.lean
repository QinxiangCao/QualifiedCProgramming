import Unifysl.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `PropositionalLogic/ProofTheory/Classical.v`:
- Classes: `ClassicalAxiomatization`, `ClassicalSequentCalculus`,
  `ClassicalDeduction`, `ClassicalPropositionalLogicEquiv`,
  `deduction_derived_neg`
- Provable rules: `provable_by_contradiction`, `provable_double_negp_elim`,
  `provable_classic_analysis`, `provable_excluded_middle`, `provable_derives_negp_orp`, `provable_negp_orp`,
  `Peirce2cpAX`, `provable_double_negp`, `Classical2GodelDummett`,
  `provable_contrapositiveNN`, `provable_contrapositiveNP`, `provables_classic`,
  `provable_impp_negp_derives`
- Sequent rules and conversions: `derivable_excluded_middle`,
  `Axiomatization2SequentCalculus_cpSC`,
  `SequentCalculus2Axiomatization_cpAX`,
  `derivables_contrapositiveNN`, `derivables_contrapositiveNP`,
  `derivables_negp_fold2`, `derivable_double_negp_rev`,
  `aux_classical_to_contrapositivepp`,
  `aux_classical_to_contradiction_elim`,
  `aux_classical_to_provable_double_negp_intros`,
  `Classical2Intuitionistic_cSC`
- Derived negation rules: `derivables_negp_andp_fold1_`, `derivables_negp_andp_fold2_`,
  `derivables_negp_orp_intros__`, `derivables_negp_orp_intros_`, `derivables_negp_impp_`,
  `derivables_negp_impp_fold__`, `derivables_negp_impp_fold_`,
  `derivable_negp_falsep_r_`, `SequentCalculus2DeductionDerivedNeg`
- Register instances:
  `reg_Axiomatization2SequentCalculus_cpSC`,
  `reg_SequentCalculus2Axiomatization_cpAX`
- Coq commented alternative proofs are not active declarations.
- Coq `-->` and `<-->` are represented by Lean-safe `⟶` and `⟷`.
- 8.20 projection/theorem aliases use `provable_*`, `derivables_*`,
  `derivable1_*`, and `logic_equiv_*` names.
-/

universe u

namespace Unifysl

open PropositionalLanguageNotation

class ClassicalAxiomatization (L : Language.{u}) [MinimumLanguage L]
    (Gamma : Provable L) : Prop where
  peirce_law :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((x ⟶ y) ⟶ x) ⟶ x)

theorem provable_peirce_law {L : Language.{u}} [MinimumLanguage L]
    [Gamma : Provable L] [ClassicalAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((x ⟶ y) ⟶ x) ⟶ x) :=
  ClassicalAxiomatization.peirce_law (Gamma := Gamma)

class ClassicalSequentCalculus (L : Language.{u}) [NegLanguage L]
    (Gamma : Derivable L) : Prop where
  derivable_by_contradiction :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L Gamma (Phi ;; (~~ x)) y ->
        @Derivable.derivable L Gamma (Phi ;; (~~ x)) (~~ y) ->
          @Derivable.derivable L Gamma Phi x

theorem derivables_by_contradiction {L : Language.{u}} [NegLanguage L]
    [Gamma : Derivable L] [ClassicalSequentCalculus L Gamma] :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L Gamma (Phi ;; (~~ x)) y ->
        @Derivable.derivable L Gamma (Phi ;; (~~ x)) (~~ y) ->
          @Derivable.derivable L Gamma Phi x :=
  ClassicalSequentCalculus.derivable_by_contradiction (Gamma := Gamma)

class ClassicalDeduction (L : Language.{u}) [OrLanguage L]
    [NegLanguage L] (GammaD1 : Derivable1 L) : Prop where
  deduction_excluded_middle :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (y || (~~ y))

theorem derivable1_excluded_middle {L : Language.{u}} [OrLanguage L]
    [NegLanguage L] [GammaD1 : Derivable1 L]
    [ClassicalDeduction L GammaD1] :
    forall x y : @Language.expr L,
      @Derivable1.derivable1 L GammaD1 x (y || (~~ y)) :=
  ClassicalDeduction.deduction_excluded_middle (GammaD1 := GammaD1)

class ClassicalPropositionalLogicEquiv (L : Language.{u})
    [MinimumLanguage L] [AndLanguage L] [NegLanguage L]
    (GammaE : LogicEquiv L) : Prop where
  equiv_excluded_middle :
    forall x : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE x (~~ (~~ x))
  equiv_DeMorgen :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (~~ (x && y)) ((~~ x) && (~~ y))

theorem logic_equiv_excluded_middle {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [NegLanguage L] [GammaE : LogicEquiv L]
    [ClassicalPropositionalLogicEquiv L GammaE] :
    forall x : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE x (~~ (~~ x)) :=
  ClassicalPropositionalLogicEquiv.equiv_excluded_middle (GammaE := GammaE)

theorem logic_equiv_DeMorgen {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [NegLanguage L] [GammaE : LogicEquiv L]
    [ClassicalPropositionalLogicEquiv L GammaE] :
    forall x y : @Language.expr L,
      @LogicEquiv.logic_equiv L GammaE (~~ (x && y)) ((~~ x) && (~~ y)) :=
  ClassicalPropositionalLogicEquiv.equiv_DeMorgen (GammaE := GammaE)

private theorem provable_of_empty_derivable {L : Language.{u}}
    [GammaP : Provable L] [GammaD : Derivable L]
    [ProvableDerivable L GammaP GammaD] {x : @Language.expr L} :
    @Derivable.derivable L GammaD (empty_context (L := L)) x ->
      @Provable.provable L GammaP x := by
  intro h
  exact (ProvableDerivable.provable_derivable
    (L := L) (GammaP := GammaP) (GammaD := GammaD) x).mpr h

section DerivableRulesFromAxiomatization0

variable {L : Language.{u}} [MinimumLanguage L]
variable [OrLanguage L] [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [OrAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [ClassicalAxiomatization L Gamma]

private instance classical_to_peirce_law : PeirceLaw L Gamma where
  __provable_peirce_law x y := ClassicalAxiomatization.peirce_law x y

theorem provable_by_contradiction :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma
        (((~~ x) ⟶ y) ⟶ ((~~ x) ⟶ (~~ y)) ⟶ x) := by
  letI : ByContradiction L Gamma := Peirce2ByContradiction
  intro x y
  exact ByContradiction.__by_contradiction x y

theorem provable_double_negp_elim :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((~~ (~~ x)) ⟶ x) := by
  letI : ByContradiction L Gamma := Peirce2ByContradiction
  letI : DoubleNegElimination L Gamma := ByContradiction2DoubleNegElimination
  intro x
  exact DoubleNegElimination.__double_negp_elim x

theorem provable_classic_analysis :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟶ ((~~ x) ⟶ y) ⟶ y) := by
  letI : ByContradiction L Gamma := Peirce2ByContradiction
  letI : DoubleNegElimination L Gamma := ByContradiction2DoubleNegElimination
  letI : ClassicAnalysis L Gamma := DoubleNegElimination2ClassicAnalysis
  intro x y
  exact ClassicAnalysis.__classic_analysis x y

theorem provable_excluded_middle :
    forall x : @Language.expr L,
      @Provable.provable L Gamma (x || (~~ x)) := by
  letI : ByContradiction L Gamma := Peirce2ByContradiction
  letI : DoubleNegElimination L Gamma := ByContradiction2DoubleNegElimination
  letI : ClassicAnalysis L Gamma := DoubleNegElimination2ClassicAnalysis
  letI : ExcludedMiddle L Gamma := ClassicAnalysis2ExcludedMiddle
  intro x
  exact ExcludedMiddle.__excluded_middle x

theorem provable_derives_negp_orp :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟶ ((~~ x) || y)) := by
  letI : ByContradiction L Gamma := Peirce2ByContradiction
  letI : DoubleNegElimination L Gamma := ByContradiction2DoubleNegElimination
  letI : ClassicAnalysis L Gamma := DoubleNegElimination2ClassicAnalysis
  letI : ImplyToOr L Gamma := ClassicAnalysis2ImplyToOr
  intro x y
  exact ImplyToOr.__provable_derives_negp_orp x y

theorem provable_negp_orp [IffLanguage L] [IffAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ y) ⟷ ((~~ x) || y)) := by
  intro x y
  exact solve_iffp_intros_minimal (x ⟶ y) ((~~ x) || y)
    (provable_derives_negp_orp x y) (impp2orp2_minimal x y)

theorem Peirce2cpAX [PeirceLaw L Gamma] :
    ClassicalAxiomatization L Gamma := by
  constructor
  intro x y
  exact PeirceLaw.__provable_peirce_law x y

end DerivableRulesFromAxiomatization0

section SequentCalculus2ExcludedMiddleSC

variable {L : Language.{u}} [NegLanguage L] [OrLanguage L]
variable [Gamma : Derivable L]
variable [ClassicalSequentCalculus L Gamma]
variable [BasicSequentCalculus L Gamma]
variable [IntuitionisticNegSequentCalculus L Gamma]
variable [OrSequentCalculus L Gamma]

theorem derivable_excluded_middle :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      Phi |--- (x || (~~ x)) := by
  intro Phi x
  let em : @Language.expr L := x || (~~ x)
  exact ClassicalSequentCalculus.derivable_by_contradiction Phi em x
    (by
      let Psi : context (L := L) := Phi ;; (~~ em)
      exact ClassicalSequentCalculus.derivable_by_contradiction Psi x (~~ x)
        (by
          exact derivable_assum (Psi ;; (~~ x)) (~~ x) (Or.inr rfl))
        (by
          have hbase : Psi |--- (~~ (~~ x)) := by
            exact IntuitionisticNegSequentCalculus.derivables_contrapositivePP
              Phi em (~~ x)
              (OrSequentCalculus.derivables_orp_intros2 (Phi ;; (~~ x)) x (~~ x)
                (derivable_assum1 Phi (~~ x)))
          exact deduction_weaken Psi (Psi ;; (~~ x)) (~~ (~~ x))
            (by
              intro z hz
              exact Or.inl hz)
            hbase))
    (by
      exact IntuitionisticNegSequentCalculus.derivables_contrapositivePP
        Phi em x
        (OrSequentCalculus.derivables_orp_intros1 (Phi ;; x) x (~~ x)
          (derivable_assum1 Phi x)))

end SequentCalculus2ExcludedMiddleSC

section Axiomatization2SequentCalculus

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [OrLanguage L]
variable [FalseLanguage L] [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable L]
variable [GammaPD : ProvableDerivable L GammaP GammaD]
variable [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
variable [MinimumAxiomatization L GammaP]
variable [AndAxiomatization L GammaP] [OrAxiomatization L GammaP]
variable [FalseAxiomatization L GammaP] [IntuitionisticNegAxiomatization L GammaP]
variable [IffAxiomatization L GammaP] [TrueAxiomatization L GammaP]
variable [ClassicalAxiomatization L GammaP]
variable [AndSequentCalculus L GammaD] [OrSequentCalculus L GammaD]
variable [FalseSequentCalculus L GammaD] [IntuitionisticNegSequentCalculus L GammaD]
variable [IffSequentCalculus L GammaD] [TrueSequentCalculus L GammaD]

theorem Axiomatization2SequentCalculus_cpSC :
    ClassicalSequentCalculus L GammaD := by
  letI : PeirceLaw L GammaP := ⟨ClassicalAxiomatization.peirce_law⟩
  letI : ByContradiction L GammaP := Peirce2ByContradiction
  constructor
  intro Phi x y hy hny
  have hby : Phi |--- (((~~ x) ⟶ y) ⟶ ((~~ x) ⟶ (~~ y)) ⟶ x) :=
    deduction_weaken0 (GammaP := GammaP) Phi _
      (ByContradiction.__by_contradiction x y)
  have hyImp : Phi |--- ((~~ x) ⟶ y) :=
    (deduction_theorem Phi (~~ x) y).mp hy
  have hnyImp : Phi |--- ((~~ x) ⟶ (~~ y)) :=
    (deduction_theorem Phi (~~ x) (~~ y)).mp hny
  have hstep : Phi |--- (((~~ x) ⟶ (~~ y)) ⟶ x) :=
    MinimumSequentCalculus.deduction_modus_ponens Phi ((~~ x) ⟶ y)
      (((~~ x) ⟶ (~~ y)) ⟶ x) hyImp hby
  exact MinimumSequentCalculus.deduction_modus_ponens Phi ((~~ x) ⟶ (~~ y))
    x hnyImp hstep

end Axiomatization2SequentCalculus

instance reg_Axiomatization2SequentCalculus_cpSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `cpSC ``Axiomatization2SequentCalculus_cpSC) 10 := {}

section SequentCalculus2Axiomatization

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [OrLanguage L]
variable [FalseLanguage L] [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable L]
variable [GammaPD : ProvableDerivable L GammaP GammaD]
variable [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
variable [AndSequentCalculus L GammaD] [OrSequentCalculus L GammaD]
variable [FalseSequentCalculus L GammaD] [IntuitionisticNegSequentCalculus L GammaD]
variable [IffSequentCalculus L GammaD] [TrueSequentCalculus L GammaD]
variable [ClassicalSequentCalculus L GammaD]
variable [MinimumAxiomatization L GammaP]
variable [AndAxiomatization L GammaP] [OrAxiomatization L GammaP]
variable [FalseAxiomatization L GammaP] [IntuitionisticNegAxiomatization L GammaP]
variable [IffAxiomatization L GammaP] [TrueAxiomatization L GammaP]

theorem SequentCalculus2Axiomatization_cpAX :
    ClassicalAxiomatization L GammaP := by
  have hBy :
      forall x y : @Language.expr L,
        @Provable.provable L GammaP
          (((~~ x) ⟶ y) ⟶ ((~~ x) ⟶ (~~ y)) ⟶ x) := by
    intro x y
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := GammaD)
      (((~~ x) ⟶ y) ⟶ ((~~ x) ⟶ (~~ y)) ⟶ x)).mpr
      ((deduction_theorem (empty_context (L := L)) ((~~ x) ⟶ y)
        (((~~ x) ⟶ (~~ y)) ⟶ x)).mp
        ((deduction_theorem ((empty_context (L := L)) ;; ((~~ x) ⟶ y))
          ((~~ x) ⟶ (~~ y)) x).mp
          (by
            let E : context (L := L) := empty_context (L := L)
            let Phi0 : context (L := L) := E ;; ((~~ x) ⟶ y)
            let Phi : context (L := L) := Phi0 ;; ((~~ x) ⟶ (~~ y))
            exact ClassicalSequentCalculus.derivable_by_contradiction Phi x y
              (by
                have hImp : (Phi ;; (~~ x)) |--- ((~~ x) ⟶ y) :=
                  derivable_assum (Phi ;; (~~ x)) ((~~ x) ⟶ y)
                    (Or.inl (Or.inl (Or.inr rfl)))
                have hnx : (Phi ;; (~~ x)) |--- (~~ x) :=
                  derivable_assum1 Phi (~~ x)
                exact MinimumSequentCalculus.deduction_modus_ponens
                  (Phi ;; (~~ x)) (~~ x) y hnx hImp)
              (by
                have hImp : (Phi ;; (~~ x)) |--- ((~~ x) ⟶ (~~ y)) :=
                  derivable_assum (Phi ;; (~~ x)) ((~~ x) ⟶ (~~ y))
                    (Or.inl (Or.inr rfl))
                have hnx : (Phi ;; (~~ x)) |--- (~~ x) :=
                  derivable_assum1 Phi (~~ x)
                exact MinimumSequentCalculus.deduction_modus_ponens
                  (Phi ;; (~~ x)) (~~ x) (~~ y) hnx hImp))))
  letI : ByContradiction L GammaP := ⟨hBy⟩
  letI : DoubleNegElimination L GammaP := ByContradiction2DoubleNegElimination
  letI : ClassicAnalysis L GammaP := DoubleNegElimination2ClassicAnalysis
  letI : PeirceLaw L GammaP := ClassicAnalysis2PeirceLaw
  constructor
  exact PeirceLaw.__provable_peirce_law

end SequentCalculus2Axiomatization

instance reg_SequentCalculus2Axiomatization_cpAX :
    RegisterClass D2P_reg
      (ProofRegistration.mk `cpAX ``SequentCalculus2Axiomatization_cpAX) 8 := {}

section ClassicalNegCore

variable {L : Language.{u}} [NegLanguage L]
variable [Gamma : Derivable L]
variable [BasicSequentCalculus L Gamma]
variable [ClassicalSequentCalculus L Gamma]

theorem derivable_double_negp_rev :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      (Phi ;; (~~ (~~ x))) |--- x := by
  intro Phi x
  exact ClassicalSequentCalculus.derivable_by_contradiction
    (Phi ;; (~~ (~~ x))) x (~~ x)
    (derivable_assum ((Phi ;; (~~ (~~ x))) ;; (~~ x)) (~~ x) (Or.inr rfl))
    (derivable_assum ((Phi ;; (~~ (~~ x))) ;; (~~ x)) (~~ (~~ x))
      (Or.inl (Or.inr rfl)))

end ClassicalNegCore

section DerivableRulesFromSequentCalculus

variable {L : Language.{u}} [MinimumLanguage L] [OrLanguage L] [NegLanguage L]
variable [Gamma : Derivable L]
variable [BasicSequentCalculus L Gamma] [MinimumSequentCalculus L Gamma]
variable [OrSequentCalculus L Gamma] [IntuitionisticNegSequentCalculus L Gamma]
variable [ClassicalSequentCalculus L Gamma]

theorem derivables_contrapositiveNN :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      (Phi |--- ((~~ y) ⟶ (~~ x))) ->
      (Phi |--- (x ⟶ y)) := by
  intro Phi x y h
  apply (deduction_theorem Phi x y).mp
  let C : context (L := L) := Phi ;; x
  exact ClassicalSequentCalculus.derivable_by_contradiction C y x
    (derivable_assum (C ;; (~~ y)) x (Or.inl (Or.inr rfl)))
    (by
      have hImp : (C ;; (~~ y)) |--- ((~~ y) ⟶ (~~ x)) :=
        deduction_weaken Phi (C ;; (~~ y)) ((~~ y) ⟶ (~~ x))
          (by
            intro z hz
            exact Or.inl (Or.inl hz))
          h
      have hny : (C ;; (~~ y)) |--- (~~ y) := derivable_assum1 C (~~ y)
      exact MinimumSequentCalculus.deduction_modus_ponens
        (C ;; (~~ y)) (~~ y) (~~ x) hny hImp)

theorem derivables_contrapositiveNP :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      (Phi |--- ((~~ y) ⟶ x)) ->
      (Phi |--- ((~~ x) ⟶ y)) := by
  intro Phi x y h
  apply (deduction_theorem Phi (~~ x) y).mp
  let C : context (L := L) := Phi ;; (~~ x)
  exact ClassicalSequentCalculus.derivable_by_contradiction C y x
    (by
      have hImp : (C ;; (~~ y)) |--- ((~~ y) ⟶ x) :=
        deduction_weaken Phi (C ;; (~~ y)) ((~~ y) ⟶ x)
          (by
            intro z hz
            exact Or.inl (Or.inl hz))
          h
      have hny : (C ;; (~~ y)) |--- (~~ y) := derivable_assum1 C (~~ y)
      exact MinimumSequentCalculus.deduction_modus_ponens
        (C ;; (~~ y)) (~~ y) x hny hImp)
    (derivable_assum (C ;; (~~ y)) (~~ x) (Or.inl (Or.inr rfl)))

theorem derivables_negp_fold2 :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      ((Phi ;; x) |--- (~~ x)) ->
      (Phi |--- (~~ x)) := by
  intro Phi x h
  exact ClassicalSequentCalculus.derivable_by_contradiction Phi (~~ x) x
    (derivable_double_negp_rev Phi x)
    (by
      let C : context (L := L) := Phi ;; (~~ (~~ x))
      have hx : C |--- x := derivable_double_negp_rev Phi x
      exact deduction_subst C (Singleton _ x) (~~ x)
        (by
          intro z hz
          cases hz
          exact hx)
        (deduction_weaken (Phi ;; x) (Union _ C (Singleton _ x)) (~~ x)
          (by
            intro z hz
            cases hz with
            | inl hPhi => exact Or.inl (Or.inl hPhi)
            | inr hxz => exact Or.inr hxz)
          h))

end DerivableRulesFromSequentCalculus

section ClassicalNeg2IntuitionisticNeg

variable {L : Language.{u}} [NegLanguage L]
variable [GammaD : Derivable L]
variable [BasicSequentCalculus L GammaD]
variable [ClassicalSequentCalculus L GammaD]

theorem aux_classical_to_contrapositivepp :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      ((Phi ;; y) |--- x) -> ((Phi ;; (~~ x)) |--- (~~ y)) := by
  intro Phi x y h
  exact ClassicalSequentCalculus.derivable_by_contradiction (Phi ;; (~~ x)) (~~ y) x
    (by
      let C : context (L := L) := (Phi ;; (~~ x)) ;; (~~ (~~ y))
      have hy : C |--- y := derivable_double_negp_rev (Phi ;; (~~ x)) y
      exact deduction_subst C (Singleton _ y) x
        (by
          intro z hz
          cases hz
          exact hy)
        (deduction_weaken (Phi ;; y) (Union _ C (Singleton _ y)) x
          (by
            intro z hz
            cases hz with
            | inl hPhi => exact Or.inl (Or.inl (Or.inl hPhi))
            | inr hyz => exact Or.inr hyz)
          h))
    (derivable_assum (((Phi ;; (~~ x)) ;; (~~ (~~ y)))) (~~ x)
      (Or.inl (Or.inr rfl)))

theorem aux_classical_to_contradiction_elim :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      (Phi |--- x) -> (Phi |--- (~~ x)) -> (Phi |--- y) := by
  intro Phi x y hx hnx
  exact ClassicalSequentCalculus.derivable_by_contradiction Phi y x
    (deduction_weaken1 Phi (~~ y) x hx)
    (deduction_weaken1 Phi (~~ y) (~~ x) hnx)

theorem aux_classical_to_provable_double_negp_intros :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      (Phi |--- x) -> (Phi |--- (~~ (~~ x))) := by
  intro Phi x hx
  exact ClassicalSequentCalculus.derivable_by_contradiction Phi (~~ (~~ x)) x
    (deduction_weaken1 Phi (~~ (~~ (~~ x))) x hx)
    (derivable_double_negp_rev Phi (~~ x))

theorem Classical2Intuitionistic_cSC :
    IntuitionisticNegSequentCalculus L GammaD := by
  constructor
  · exact aux_classical_to_contrapositivepp
  · exact aux_classical_to_contradiction_elim
  · exact aux_classical_to_provable_double_negp_intros

end ClassicalNeg2IntuitionisticNeg

section DerivableRulesFromAxiomatization1

variable {L : Language.{u}} [MinimumLanguage L]
variable [OrLanguage L] [NegLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [OrAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [ClassicalAxiomatization L Gamma]

theorem provable_double_negp [IffLanguage L] [IffAxiomatization L Gamma] :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((~~ (~~ x)) ⟷ x) := by
  intro x
  exact solve_iffp_intros_minimal (~~ (~~ x)) x
    (provable_double_negp_elim x)
    (IntuitionisticNegAxiomatization.provable_double_negp_intros x)

instance Classical2GodelDummett :
    GodelDummettAxiomatization L Gamma := by
  constructor
  intro x y
  let Z : @Language.expr L := (x ⟶ y) || (y ⟶ x)
  have hem : @Provable.provable L Gamma (x || (~~ x)) :=
    provable_excluded_middle x
  have hxZ : @Provable.provable L Gamma (x ⟶ Z) := by
    have hxyx : @Provable.provable L Gamma (x ⟶ (y ⟶ x)) :=
      MinimumAxiomatization.axiom1 (Gamma := Gamma) x y
    have hr : @Provable.provable L Gamma ((y ⟶ x) ⟶ Z) :=
      OrAxiomatization.provable_orp_intros2 (x ⟶ y) (y ⟶ x)
    exact aux_minimun_rule02 x (y ⟶ x) Z hxyx hr
  have hnxZ : @Provable.provable L Gamma ((~~ x) ⟶ Z) := by
    have hnxy : @Provable.provable L Gamma ((~~ x) ⟶ (x ⟶ y)) :=
      IntuitionisticNegAxiomatization.provable_contradiction_elim1 x y
    have hl : @Provable.provable L Gamma ((x ⟶ y) ⟶ Z) :=
      OrAxiomatization.provable_orp_intros1 (x ⟶ y) (y ⟶ x)
    exact aux_minimun_rule02 (~~ x) (x ⟶ y) Z hnxy hl
  have helim : @Provable.provable L Gamma ((x || (~~ x)) ⟶ Z) := by
    have h1 : @Provable.provable L Gamma
        (((~~ x) ⟶ Z) ⟶ ((x || (~~ x)) ⟶ Z)) :=
      MinimumAxiomatization.modus_ponens
        (Gamma := Gamma) (x ⟶ Z)
        (((~~ x) ⟶ Z) ⟶ ((x || (~~ x)) ⟶ Z))
        (OrAxiomatization.provable_orp_elim x (~~ x) Z) hxZ
    exact MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) ((~~ x) ⟶ Z) ((x || (~~ x)) ⟶ Z) h1 hnxZ
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x || (~~ x)) Z helim hem

theorem provable_contrapositiveNN :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((~~ y) ⟶ (~~ x)) ⟶ (x ⟶ y)) := by
  AddSequentCalculus
  letI : IntuitionisticNegSequentCalculus L (inferInstance : Derivable L) :=
    Axiomatization2SequentCalculus_inegpSC_minimal
      (GammaP := Gamma) (GammaD := (inferInstance : Derivable L))
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := (~~ y) ⟶ (~~ x)
  let Phi : context (L := L) := E ;; A
  have hA : Phi |--- A := derivable_assum1 E A
  have hx_dny : Phi |--- (x ⟶ (~~ (~~ y))) :=
    derivables_contrapositivePN' Phi x (~~ y) hA
  have hdne : Phi |--- ((~~ (~~ y)) ⟶ y) :=
    deduction_weaken0 (GammaP := Gamma) Phi _ (provable_double_negp_elim y)
  have hxy : Phi |--- (x ⟶ y) :=
    deduction_impp_trans Phi x (~~ (~~ y)) y hx_dny hdne
  exact provable_of_empty_derivable
    ((deduction_theorem E A (x ⟶ y)).mp hxy)

theorem provable_contrapositiveNP :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (((~~ y) ⟶ x) ⟶ ((~~ x) ⟶ y)) := by
  AddSequentCalculus
  letI : IntuitionisticNegSequentCalculus L (inferInstance : Derivable L) :=
    Axiomatization2SequentCalculus_inegpSC_minimal
      (GammaP := Gamma) (GammaD := (inferInstance : Derivable L))
  intro x y
  let E : context (L := L) := empty_context (L := L)
  let A : @Language.expr L := (~~ y) ⟶ x
  let B : @Language.expr L := (~~ y) ⟶ (~~ x)
  let Phi : context (L := L) := E ;; A
  let Psi : context (L := L) := Phi ;; (~~ x)
  have hA : Psi |--- A :=
    derivable_assum Psi A (Or.inl (Or.inr rfl))
  have hnx : Psi |--- (~~ x) := derivable_assum1 Phi (~~ x)
  have hB : Psi |--- B :=
    MinimumSequentCalculus.deduction_modus_ponens Psi (~~ x) B hnx
      (derivable_axiom1 Psi (~~ x) (~~ y))
  have hbc : Psi |--- (A ⟶ B ⟶ y) :=
    deduction_weaken0 (GammaP := Gamma) Psi _ (provable_by_contradiction y x)
  have hby : Psi |--- (B ⟶ y) :=
    MinimumSequentCalculus.deduction_modus_ponens Psi A (B ⟶ y) hA hbc
  have hy : Psi |--- y :=
    MinimumSequentCalculus.deduction_modus_ponens Psi B y hB hby
  exact provable_of_empty_derivable
    ((deduction_theorem E A ((~~ x) ⟶ y)).mp
      ((deduction_theorem Phi (~~ x) y).mp hy))

theorem provables_classic :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ y) ->
        @Provable.provable L Gamma ((~~ x) ⟶ y) ->
          @Provable.provable L Gamma y := by
  intro x y hxy hnxy
  have hstep : @Provable.provable L Gamma (((~~ x) ⟶ y) ⟶ y) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (x ⟶ y) (((~~ x) ⟶ y) ⟶ y)
      (provable_classic_analysis x y) hxy
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) ((~~ x) ⟶ y) y hstep hnxy

theorem provable_impp_negp_derives :
    forall x : @Language.expr L,
      @Provable.provable L Gamma ((x ⟶ (~~ x)) ⟶ (~~ x)) := by
  intro x
  let A : @Language.expr L := (~~ x) ⟶ (~~ x)
  have hfinish : @Provable.provable L Gamma ((A ⟶ (~~ x)) ⟶ (~~ x)) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) A ((A ⟶ (~~ x)) ⟶ (~~ x))
      (aux_minimun_theorem02 A (~~ x))
      (provable_impp_refl (~~ x))
  exact aux_minimun_rule02 (x ⟶ (~~ x)) (A ⟶ (~~ x)) (~~ x)
    (provable_classic_analysis x (~~ x)) hfinish

end DerivableRulesFromAxiomatization1

section DerivedSequentCalculusRules

variable {L : Language.{u}} [MinimumLanguage L] [NegLanguage L] [AndLanguage L]
variable [OrLanguage L] [FalseLanguage L] [TrueLanguage L]
variable [GammaD : Derivable L]
variable [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
variable [AndSequentCalculus L GammaD] [OrSequentCalculus L GammaD]
variable [FalseSequentCalculus L GammaD]
variable [IntuitionisticNegSequentCalculus L GammaD] [TrueSequentCalculus L GammaD]
variable [ClassicalSequentCalculus L GammaD]

theorem derivables_negp_andp_fold1_ :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (~~ (P && Q))) := by
  intro Phi P Q h
  have hbase : (Phi ;; (~~ P)) |--- (~~ (P && Q)) :=
    IntuitionisticNegSequentCalculus.derivables_contrapositivePP Phi P (P && Q)
      (AndSequentCalculus.derivables_andp_elim1 (Phi ;; (P && Q)) P Q
        (derivable_assum1 Phi (P && Q)))
  exact deduction_subst1 Phi (~~ P) (~~ (P && Q)) h hbase

theorem derivables_negp_andp_fold2_ :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P && Q))) := by
  intro Phi P Q h
  have hbase : (Phi ;; (~~ Q)) |--- (~~ (P && Q)) :=
    IntuitionisticNegSequentCalculus.derivables_contrapositivePP Phi Q (P && Q)
      (AndSequentCalculus.derivables_andp_elim2 (Phi ;; (P && Q)) P Q
        (derivable_assum1 Phi (P && Q)))
  exact deduction_subst1 Phi (~~ Q) (~~ (P && Q)) h hbase

theorem derivables_negp_orp_intros__ :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      ((Phi ;; (~~ P)) ;; (~~ Q)) |--- (~~ (P || Q)) := by
  intro Phi P Q
  let C : context (L := L) := Phi ;; (~~ P)
  have hPrem : (C ;; (P || Q)) |--- Q :=
    OrSequentCalculus.derivables_orp_elim C P Q Q
      (IntuitionisticNegSequentCalculus.derivables_contradiction_elim
        (C ;; P) P Q
        (derivable_assum1 C P)
        (derivable_assum (C ;; P) (~~ P) (Or.inl (Or.inr rfl))))
      (derivable_assum1 C Q)
  exact IntuitionisticNegSequentCalculus.derivables_contrapositivePP C Q (P || Q) hPrem

theorem derivables_negp_orp_intros_ :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P || Q))) := by
  intro Phi P Q hP hQ
  have hbase : ((Phi ;; (~~ P)) ;; (~~ Q)) |--- (~~ (P || Q)) :=
    derivables_negp_orp_intros__ Phi P Q
  have hQ' : (Phi ;; (~~ P)) |--- (~~ Q) :=
    deduction_weaken1 Phi (~~ P) (~~ Q) hQ
  have h1 : (Phi ;; (~~ P)) |--- (~~ (P || Q)) :=
    deduction_subst1 (Phi ;; (~~ P)) (~~ Q) (~~ (P || Q)) hQ' hbase
  exact deduction_subst1 Phi (~~ P) (~~ (P || Q)) hP h1

theorem derivables_negp_impp_ :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (P ⟶ Q)) := by
  intro Phi P Q h
  apply (deduction_theorem Phi P Q).mp
  exact IntuitionisticNegSequentCalculus.derivables_contradiction_elim
    (Phi ;; P) P Q
    (derivable_assum1 Phi P)
    (deduction_weaken1 Phi P (~~ P) h)

theorem derivables_negp_impp_fold__ :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      ((Phi ;; P) ;; (~~ Q)) |--- (~~ (P ⟶ Q)) := by
  intro Phi P Q
  let C : context (L := L) := Phi ;; P
  have hPrem : (C ;; (P ⟶ Q)) |--- Q :=
    MinimumSequentCalculus.deduction_modus_ponens (C ;; (P ⟶ Q)) P Q
      (derivable_assum (C ;; (P ⟶ Q)) P (Or.inl (Or.inr rfl)))
      (derivable_assum1 C (P ⟶ Q))
  exact IntuitionisticNegSequentCalculus.derivables_contrapositivePP C Q (P ⟶ Q) hPrem

theorem derivables_negp_impp_fold_ :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- P) -> (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P ⟶ Q))) := by
  intro Phi P Q hP hQ
  have hbase : ((Phi ;; P) ;; (~~ Q)) |--- (~~ (P ⟶ Q)) :=
    derivables_negp_impp_fold__ Phi P Q
  have hQ' : (Phi ;; P) |--- (~~ Q) :=
    deduction_weaken1 Phi P (~~ Q) hQ
  have h1 : (Phi ;; P) |--- (~~ (P ⟶ Q)) :=
    deduction_subst1 (Phi ;; P) (~~ Q) (~~ (P ⟶ Q)) hQ' hbase
  exact deduction_subst1 Phi P (~~ (P ⟶ Q)) hP h1

theorem derivable_negp_falsep_r_ :
    forall Phi : context (L := L), Phi |--- (~~ FF) := by
  intro Phi
  exact ClassicalSequentCalculus.derivable_by_contradiction Phi (~~ FF) FF
    (derivable_double_negp_rev Phi FF)
    (FalseSequentCalculus.derivables_falsep_elim (Phi ;; (~~ (~~ FF))) (~~ FF)
      (derivable_double_negp_rev Phi FF))

class deduction_derived_neg (L : Language.{u}) [MinimumLanguage L] [NegLanguage L]
    [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    (GammaD : Derivable L) : Prop where
  derivables_negp_andp_fold1 :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (~~ (P && Q)))
  derivables_negp_andp_fold2 :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P && Q)))
  derivables_negp_orp_intros :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P || Q)))
  derivables_negp_impp :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (P ⟶ Q))
  derivables_negp_impp_fold :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- P) -> (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P ⟶ Q)))
  derivable_negp_falsep_r :
    forall Phi : context (L := L), Phi |--- (~~ FF)

namespace deduction_derived_neg

theorem deduction_and_neg1 {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    {GammaD : Derivable L} (self : deduction_derived_neg L GammaD) :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (~~ (P && Q))) :=
  self.derivables_negp_andp_fold1

theorem deduction_and_neg2 {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    {GammaD : Derivable L} (self : deduction_derived_neg L GammaD) :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P && Q))) :=
  self.derivables_negp_andp_fold2

theorem deduction_or_neg {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    {GammaD : Derivable L} (self : deduction_derived_neg L GammaD) :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P || Q))) :=
  self.derivables_negp_orp_intros

theorem deduction_imp_neg1 {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    {GammaD : Derivable L} (self : deduction_derived_neg L GammaD) :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- (~~ P)) -> (Phi |--- (P ⟶ Q)) :=
  self.derivables_negp_impp

theorem deduction_imp_neg2 {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    {GammaD : Derivable L} (self : deduction_derived_neg L GammaD) :
    forall (Phi : context (L := L)) (P Q : @Language.expr L),
      (Phi |--- P) -> (Phi |--- (~~ Q)) -> (Phi |--- (~~ (P ⟶ Q))) :=
  self.derivables_negp_impp_fold

theorem deduction_false_neg {L : Language.{u}} [MinimumLanguage L] [NegLanguage L]
    [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    {GammaD : Derivable L} (self : deduction_derived_neg L GammaD) :
    forall Phi : context (L := L), Phi |--- (~~ FF) :=
  self.derivable_negp_falsep_r

end deduction_derived_neg

theorem SequentCalculus2DeductionDerivedNeg :
    deduction_derived_neg L GammaD := by
  constructor
  · exact derivables_negp_andp_fold1_
  · exact derivables_negp_andp_fold2_
  · exact derivables_negp_orp_intros_
  · exact derivables_negp_impp_
  · exact derivables_negp_impp_fold_
  · exact derivable_negp_falsep_r_

end DerivedSequentCalculusRules

end Unifysl
