import Lean
import Unifysl.PropositionalLogic.ProofTheory.Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `PropositionalLogic/ProofTheory/TheoryOfPropositionalConnectives.v`:
- Definition classes:
  `AndDefinition_Or_Neg`, `IffDefinition_And_Imp`,
  `TrueDefinition_False_Imp`, `NegDefinition_False_Imp`,
  `OrDefinition_Imp_Neg`, `TrueDefinition_Imp_Self`,
  `TrueDefinition_Neg_False`, `FalseDefinition_Neg_True`.
- Builder definitions:
  `OrNeg2And`, `AndImp2Iff`, `FalseImp2True`, `FalseImp2Neg`,
  `ImpNeg2Or`, `ImpSelf2True`, `NegFalse2True`, `NegTrue2False`.
- Normality lemmas and `FromDefToAX` conversion lemmas for the above.
- Ltac tactics:
  `AddConnective_iffp`, `AddConnective_truep`, `AddConnective_negp`,
  `AddConnective_truep_impp_self`.
-/

universe u

namespace Unifysl

open PropositionalLanguageNotation

class AndDefinition_Or_Neg (L : Language.{u}) [OrLanguage L]
    [NegLanguage L] [AndLanguage L] : Prop where
  orp_negp2andp :
    forall x y : @Language.expr L,
      (x && y) = (~~ ((~~ x) || (~~ y)))

class IffDefinition_And_Imp (L : Language.{u}) [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] : Prop where
  andp_impp2iffp :
    forall x y : @Language.expr L,
      (x ⟷ y) = ((x ⟶ y) && (y ⟶ x))

class TrueDefinition_False_Imp (L : Language.{u}) [MinimumLanguage L]
    [FalseLanguage L] [TrueLanguage L] : Prop where
  falsep_impp2truep :
    TT = (FF ⟶ FF)

class NegDefinition_False_Imp (L : Language.{u}) [MinimumLanguage L]
    [FalseLanguage L] [NegLanguage L] : Prop where
  falsep_impp2negp :
    forall x : @Language.expr L,
      (~~ x) = (x ⟶ FF)

class OrDefinition_Imp_Neg (L : Language.{u}) [MinimumLanguage L]
    [NegLanguage L] [OrLanguage L] : Prop where
  impp_negp2orp :
    forall x y : @Language.expr L,
      (x || y) = ((~~ x) ⟶ y)

class TrueDefinition_Imp_Self (L : Language.{u}) [MinimumLanguage L]
    [TrueLanguage L] : Prop where
  impp_self2truep :
    exists x : @Language.expr L,
      TT = (x ⟶ x)

class TrueDefinition_Neg_False (L : Language.{u}) [FalseLanguage L]
    [NegLanguage L] [TrueLanguage L] : Prop where
  negp_falsep2truep :
    TT = (~~ FF)

class FalseDefinition_Neg_True (L : Language.{u}) [TrueLanguage L]
    [NegLanguage L] [FalseLanguage L] : Prop where
  negp_truep2falsep :
    FF = (~~ TT)

def OrNeg2And {L : Language.{u}} [OrLanguage L] [NegLanguage L] :
    AndLanguage L where
  andp := fun x y => ~~ ((~~ x) || (~~ y))

def AndImp2Iff {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] :
    IffLanguage L where
  iffp := fun x y => (x ⟶ y) && (y ⟶ x)

def FalseImp2True {L : Language.{u}} [MinimumLanguage L] [FalseLanguage L] :
    TrueLanguage L where
  truep := FF ⟶ FF

def FalseImp2Neg {L : Language.{u}} [MinimumLanguage L] [FalseLanguage L] :
    NegLanguage L where
  negp := fun x => x ⟶ FF

def ImpNeg2Or {L : Language.{u}} [MinimumLanguage L] [NegLanguage L] :
    OrLanguage L where
  orp := fun x y => (~~ x) ⟶ y

def ImpSelf2True {L : Language.{u}} [MinimumLanguage L]
    (x : @Language.expr L) : TrueLanguage L where
  truep := x ⟶ x

def NegFalse2True {L : Language.{u}} [FalseLanguage L] [NegLanguage L] :
    TrueLanguage L where
  truep := ~~ FF

def NegTrue2False {L : Language.{u}} [TrueLanguage L] [NegLanguage L] :
    FalseLanguage L where
  falsep := ~~ TT

private theorem tpc_contradiction_elim2 {L : Language.{u}}
    [MinimumLanguage L] [NegLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma]
    [IntuitionisticNegAxiomatization L Gamma] :
    forall x y : @Language.expr L,
      @Provable.provable L Gamma (x ⟶ (~~ x) ⟶ y) := by
  intro x y
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) ((~~ x) ⟶ x ⟶ y) (x ⟶ (~~ x) ⟶ y)
    (provable_impp_arg_switch (~~ x) x y)
    (IntuitionisticNegAxiomatization.provable_contradiction_elim1 x y)

private theorem tpc_negp_aux_rule {L : Language.{u}}
    [MinimumLanguage L] [NegLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma]
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

private theorem tpc_Axiomatization2SequentCalculus_falsepSC
    {L : Language.{u}} [MinimumLanguage L] [FalseLanguage L]
    [GammaP : Provable L] [GammaD : Derivable L]
    [ProvableDerivable L GammaP GammaD]
    [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
    [FalseAxiomatization L GammaP] :
    FalseSequentCalculus L GammaD := by
  constructor
  intro Phi x hff
  exact MinimumSequentCalculus.deduction_modus_ponens Phi FF x hff
    (deduction_weaken0 (GammaP := GammaP) Phi (FF ⟶ x)
      (FalseAxiomatization.provable_falsep_elim x))

private theorem tpc_deduction_negp_fold {L : Language.{u}}
    [MinimumLanguage L] [FalseLanguage L] [NegLanguage L]
    [GammaD : Derivable L]
    [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
    [FalseSequentCalculus L GammaD]
    [IntuitionisticNegSequentCalculus L GammaD] :
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

theorem OrNeg2And_Normal {L : Language.{u}} [OrLanguage L] [NegLanguage L] :
    @AndDefinition_Or_Neg L _ _
      (OrNeg2And (L := L) : AndLanguage L) := by
  exact @AndDefinition_Or_Neg.mk L _ _
    (OrNeg2And (L := L) : AndLanguage L) (by intro x y; rfl)

theorem AndImp2Iff_Normal {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] :
    @IffDefinition_And_Imp L _ _
      (AndImp2Iff (L := L) : IffLanguage L) := by
  exact @IffDefinition_And_Imp.mk L _ _
    (AndImp2Iff (L := L) : IffLanguage L) (by intro x y; rfl)

theorem FalseImp2True_Normal {L : Language.{u}} [MinimumLanguage L]
    [FalseLanguage L] :
    @TrueDefinition_False_Imp L _ _
      (FalseImp2True (L := L) : TrueLanguage L) := by
  exact @TrueDefinition_False_Imp.mk L _ _
    (FalseImp2True (L := L) : TrueLanguage L) rfl

theorem FalseImp2Neg_Normal {L : Language.{u}} [MinimumLanguage L]
    [FalseLanguage L] :
    @NegDefinition_False_Imp L _ _
      (FalseImp2Neg (L := L) : NegLanguage L) := by
  exact @NegDefinition_False_Imp.mk L _ _
    (FalseImp2Neg (L := L) : NegLanguage L) (by intro x; rfl)

theorem ImpNeg2Or_Normal {L : Language.{u}} [MinimumLanguage L]
    [NegLanguage L] :
    @OrDefinition_Imp_Neg L _ _
      (ImpNeg2Or (L := L) : OrLanguage L) := by
  exact @OrDefinition_Imp_Neg.mk L _ _
    (ImpNeg2Or (L := L) : OrLanguage L) (by intro x y; rfl)

theorem ImpSelf2True_Normal {L : Language.{u}} [MinimumLanguage L]
    (x : @Language.expr L) :
    @TrueDefinition_Imp_Self L _
      (ImpSelf2True (L := L) x : TrueLanguage L) := by
  exact @TrueDefinition_Imp_Self.mk L _
    (ImpSelf2True (L := L) x : TrueLanguage L) ⟨x, rfl⟩

theorem NegFalse2True_Normal {L : Language.{u}} [FalseLanguage L]
    [NegLanguage L] :
    @TrueDefinition_Neg_False L _ _
      (NegFalse2True (L := L) : TrueLanguage L) := by
  exact @TrueDefinition_Neg_False.mk L _ _
    (NegFalse2True (L := L) : TrueLanguage L) rfl

theorem NegTrue2False_Normal {L : Language.{u}} [TrueLanguage L]
    [NegLanguage L] :
    @FalseDefinition_Neg_True L _ _
      (NegTrue2False (L := L) : FalseLanguage L) := by
  exact @FalseDefinition_Neg_True.mk L _ _
    (NegTrue2False (L := L) : FalseLanguage L) rfl

theorem AndFromDefToAX_Or_Neg {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
    [GammaP : Provable L] [MinimumAxiomatization L GammaP]
    [OrAxiomatization L GammaP] [FalseAxiomatization L GammaP]
    [IntuitionisticNegAxiomatization L GammaP]
    [ClassicalAxiomatization L GammaP] [AndDefinition_Or_Neg L] :
    AndAxiomatization L GammaP := by
  letI : Derivable L := Provable2Derivable (L := L)
  letI : DerivableProvable L GammaP (Provable2Derivable (L := L)) :=
    Provable2Derivable_Normal
  letI : ProvableDerivable L GammaP (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_minSC
  letI : OrSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_orpSC_minimal
      (GammaP := GammaP) (GammaD := (Provable2Derivable (L := L)))
  letI : FalseSequentCalculus L (Provable2Derivable (L := L)) :=
    tpc_Axiomatization2SequentCalculus_falsepSC
      (GammaP := GammaP) (GammaD := (Provable2Derivable (L := L)))
  letI : IntuitionisticNegSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_inegpSC_minimal
      (GammaP := GammaP) (GammaD := (Provable2Derivable (L := L)))
  letI : PeirceLaw L GammaP := ⟨ClassicalAxiomatization.peirce_law⟩
  letI : ByContradiction L GammaP := Peirce2ByContradiction
  letI : DoubleNegElimination L GammaP := ByContradiction2DoubleNegElimination
  constructor
  · intro x y
    rw [AndDefinition_Or_Neg.orp_negp2andp x y]
    let E : context (L := L) := empty_context (L := L)
    let A : @Language.expr L := (~~ x) || (~~ y)
    let C : context (L := L) := (E ;; x) ;; y
    have hnot : C |--- (~~ A) := by
      apply tpc_deduction_negp_fold C A
      let D : context (L := L) := C ;; A
      have hAtoFalse : D |--- (A ⟶ FF) := by
        apply (deduction_theorem D A FF).mp
        apply OrSequentCalculus.derivables_orp_elim
        · let Dx : context (L := L) := D ;; (~~ x)
          have hx : Dx |--- x := by
            solve_assum
          have hnx : Dx |--- (~~ x) := by
            solve_assum
          exact IntuitionisticNegSequentCalculus.derivables_contradiction_elim
            Dx x FF hx hnx
        · let Dy : context (L := L) := D ;; (~~ y)
          have hy : Dy |--- y := by
            solve_assum
          have hny : Dy |--- (~~ y) := by
            solve_assum
          exact IntuitionisticNegSequentCalculus.derivables_contradiction_elim
            Dy y FF hy hny
      have hA : D |--- A := by
        solve_assum
      exact MinimumSequentCalculus.deduction_modus_ponens D A FF hA hAtoFalse
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := (inferInstance : Derivable L))
      (x ⟶ y ⟶ (~~ A))).mpr
      ((deduction_theorem E x (y ⟶ (~~ A))).mp
        ((deduction_theorem (E ;; x) y (~~ A)).mp hnot))
  · intro x y
    rw [AndDefinition_Or_Neg.orp_negp2andp x y]
    let E : context (L := L) := empty_context (L := L)
    let A : @Language.expr L := (~~ x) || (~~ y)
    let C : context (L := L) := E ;; (~~ A)
    have hnnx : C |--- (~~ (~~ x)) := by
      apply tpc_deduction_negp_fold C (~~ x)
      let D : context (L := L) := C ;; (~~ x)
      have hnx : D |--- (~~ x) := by
        solve_assum
      have hA : D |--- A :=
        OrSequentCalculus.derivables_orp_intros1 D (~~ x) (~~ y) hnx
      have hnA : D |--- (~~ A) := by
        solve_assum
      exact IntuitionisticNegSequentCalculus.derivables_contradiction_elim
        D A FF hA hnA
    have hx : C |--- x :=
      MinimumSequentCalculus.deduction_modus_ponens C (~~ (~~ x)) x hnnx
        (deduction_weaken0 (GammaP := GammaP) C _
          (DoubleNegElimination.__double_negp_elim x))
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := (inferInstance : Derivable L))
      ((~~ A) ⟶ x)).mpr
      ((deduction_theorem E (~~ A) x).mp hx)
  · intro x y
    rw [AndDefinition_Or_Neg.orp_negp2andp x y]
    let E : context (L := L) := empty_context (L := L)
    let A : @Language.expr L := (~~ x) || (~~ y)
    let C : context (L := L) := E ;; (~~ A)
    have hnny : C |--- (~~ (~~ y)) := by
      apply tpc_deduction_negp_fold C (~~ y)
      let D : context (L := L) := C ;; (~~ y)
      have hny : D |--- (~~ y) := by
        solve_assum
      have hA : D |--- A :=
        OrSequentCalculus.derivables_orp_intros2 D (~~ x) (~~ y) hny
      have hnA : D |--- (~~ A) := by
        solve_assum
      exact IntuitionisticNegSequentCalculus.derivables_contradiction_elim
        D A FF hA hnA
    have hy : C |--- y :=
      MinimumSequentCalculus.deduction_modus_ponens C (~~ (~~ y)) y hnny
        (deduction_weaken0 (GammaP := GammaP) C _
          (DoubleNegElimination.__double_negp_elim y))
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := (inferInstance : Derivable L))
      ((~~ A) ⟶ y)).mpr
      ((deduction_theorem E (~~ A) y).mp hy)

theorem IffFromDefToAX_And_Imp {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] [GammaP : Provable L]
    [MinimumAxiomatization L GammaP] [AndAxiomatization L GammaP]
    [IffDefinition_And_Imp L] :
    IffAxiomatization L GammaP := by
  constructor
  · intro x y
    rw [IffDefinition_And_Imp.andp_impp2iffp x y]
    exact AndAxiomatization.provable_andp_intros (x ⟶ y) (y ⟶ x)
  · intro x y
    rw [IffDefinition_And_Imp.andp_impp2iffp x y]
    exact AndAxiomatization.provable_andp_elim1 (x ⟶ y) (y ⟶ x)
  · intro x y
    rw [IffDefinition_And_Imp.andp_impp2iffp x y]
    exact AndAxiomatization.provable_andp_elim2 (x ⟶ y) (y ⟶ x)

theorem TrueFromDefToAX_False_Imp {L : Language.{u}} [MinimumLanguage L]
    [FalseLanguage L] [TrueLanguage L] [GammaP : Provable L]
    [MinimumAxiomatization L GammaP] [FalseAxiomatization L GammaP]
    [TrueDefinition_False_Imp L] :
    TrueAxiomatization L GammaP := by
  constructor
  rw [TrueDefinition_False_Imp.falsep_impp2truep]
  exact provable_impp_refl FF

theorem NegFromDefToAX_False_Imp {L : Language.{u}} [MinimumLanguage L]
    [FalseLanguage L] [NegLanguage L] [GammaP : Provable L]
    [MinimumAxiomatization L GammaP] [FalseAxiomatization L GammaP]
    [NegDefinition_False_Imp L] :
    IntuitionisticNegAxiomatization L GammaP := by
  constructor
  · intro x y
    rw [NegDefinition_False_Imp.falsep_impp2negp x,
      NegDefinition_False_Imp.falsep_impp2negp y]
    exact provable_impp_trans y x FF
  · intro x y
    rw [NegDefinition_False_Imp.falsep_impp2negp x]
    exact aux_minimun_rule01 FF y x (FalseAxiomatization.provable_falsep_elim y)
  · intro x
    rw [NegDefinition_False_Imp.falsep_impp2negp x,
      NegDefinition_False_Imp.falsep_impp2negp (x ⟶ FF)]
    exact aux_minimun_theorem02 x FF

theorem OrFromDefToAX_Imp_Neg {L : Language.{u}} [MinimumLanguage L]
    [OrLanguage L] [NegLanguage L] [GammaP : Provable L]
    [MinimumAxiomatization L GammaP]
    [IntuitionisticNegAxiomatization L GammaP]
    [ClassicalAxiomatization L GammaP] [OrDefinition_Imp_Neg L] :
    OrAxiomatization L GammaP := by
  letI : Derivable L := Provable2Derivable (L := L)
  letI : DerivableProvable L GammaP (Provable2Derivable (L := L)) :=
    Provable2Derivable_Normal
  letI : ProvableDerivable L GammaP (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_GammaPD
  letI : BasicSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_bSC
  letI : MinimumSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_minSC
  letI : IntuitionisticNegSequentCalculus L (Provable2Derivable (L := L)) :=
    Axiomatization2SequentCalculus_inegpSC_minimal
      (GammaP := GammaP) (GammaD := (Provable2Derivable (L := L)))
  letI : PeirceLaw L GammaP := ⟨ClassicalAxiomatization.peirce_law⟩
  letI : ByContradiction L GammaP := Peirce2ByContradiction
  letI : DoubleNegElimination L GammaP := ByContradiction2DoubleNegElimination
  letI : ClassicAnalysis L GammaP := DoubleNegElimination2ClassicAnalysis
  constructor
  · intro x y
    rw [OrDefinition_Imp_Neg.impp_negp2orp x y]
    exact tpc_contradiction_elim2 x y
  · intro x y
    rw [OrDefinition_Imp_Neg.impp_negp2orp x y]
    let minRules : MinimumAxiomatization L GammaP := inferInstance
    exact match minRules with
    | ⟨_, hbase, _⟩ => hbase y (~~ x)
  · intro x y z
    rw [OrDefinition_Imp_Neg.impp_negp2orp x y]
    let E : context (L := L) := empty_context (L := L)
    let C : context (L := L) := ((E ;; (x ⟶ z)) ;; (y ⟶ z)) ;; ((~~ x) ⟶ y)
    have hxz : C |--- (x ⟶ z) := by
      solve_assum
    have hyz : C |--- (y ⟶ z) := by
      solve_assum
    have hnxy : C |--- ((~~ x) ⟶ y) := by
      solve_assum
    have hnxz : C |--- ((~~ x) ⟶ z) :=
      deduction_impp_trans C (~~ x) y z hnxy hyz
    have hclassic : C |--- ((x ⟶ z) ⟶ ((~~ x) ⟶ z) ⟶ z) :=
      deduction_weaken0 (GammaP := GammaP) C _
        (ClassicAnalysis.__classic_analysis x z)
    have hstep : C |--- (((~~ x) ⟶ z) ⟶ z) :=
      MinimumSequentCalculus.deduction_modus_ponens C (x ⟶ z)
        (((~~ x) ⟶ z) ⟶ z) hxz hclassic
    have hz : C |--- z :=
      MinimumSequentCalculus.deduction_modus_ponens C ((~~ x) ⟶ z)
        z hnxz hstep
    exact (ProvableDerivable.provable_derivable
      (L := L) (GammaP := GammaP) (GammaD := (inferInstance : Derivable L))
      ((x ⟶ z) ⟶ (y ⟶ z) ⟶ (((~~ x) ⟶ y) ⟶ z))).mpr
      ((deduction_theorem E (x ⟶ z)
          ((y ⟶ z) ⟶ (((~~ x) ⟶ y) ⟶ z))).mp
        ((deduction_theorem (E ;; (x ⟶ z)) (y ⟶ z)
            (((~~ x) ⟶ y) ⟶ z)).mp
          ((deduction_theorem ((E ;; (x ⟶ z)) ;; (y ⟶ z))
              ((~~ x) ⟶ y) z).mp hz)))

theorem TrueFromDefToAX_Imp_Self {L : Language.{u}} [MinimumLanguage L]
    [TrueLanguage L] [GammaP : Provable L]
    [MinimumAxiomatization L GammaP] [TrueDefinition_Imp_Self L] :
    TrueAxiomatization L GammaP := by
  rcases TrueDefinition_Imp_Self.impp_self2truep (L := L) with ⟨x, hx⟩
  constructor
  rw [hx]
  exact provable_impp_refl x

theorem TrueFromDefToAX_Neg_False {L : Language.{u}} [MinimumLanguage L]
    [FalseLanguage L] [TrueLanguage L] [NegLanguage L]
    [GammaP : Provable L] [MinimumAxiomatization L GammaP]
    [FalseAxiomatization L GammaP]
    [IntuitionisticNegAxiomatization L GammaP]
    [TrueDefinition_Neg_False L] :
    TrueAxiomatization L GammaP := by
  constructor
  rw [TrueDefinition_Neg_False.negp_falsep2truep]
  have hFalseToNegRefl : @Provable.provable L GammaP (FF ⟶ (~~ (FF ⟶ FF))) :=
    FalseAxiomatization.provable_falsep_elim (~~ (FF ⟶ FF))
  exact MinimumAxiomatization.modus_ponens
    (Gamma := GammaP) (FF ⟶ (~~ (FF ⟶ FF))) (~~ FF)
    (tpc_negp_aux_rule FF (FF ⟶ FF) (provable_impp_refl FF))
    hFalseToNegRefl

theorem FalseFromDefToAX_Neg_True {L : Language.{u}} [MinimumLanguage L]
    [FalseLanguage L] [TrueLanguage L] [NegLanguage L]
    [GammaP : Provable L] [MinimumAxiomatization L GammaP]
    [TrueAxiomatization L GammaP]
    [IntuitionisticNegAxiomatization L GammaP]
    [FalseDefinition_Neg_True L] :
    FalseAxiomatization L GammaP := by
  constructor
  intro x
  rw [FalseDefinition_Neg_True.negp_truep2falsep]
  exact MinimumAxiomatization.modus_ponens
    (Gamma := GammaP) TT ((~~ TT) ⟶ x)
    (tpc_contradiction_elim2 TT x) TrueAxiomatization.provable_truep_intros

open Lean Meta Elab Term Tactic

namespace AddConnectiveLocal

private def languageType? (type : Expr) : MetaM Bool := do
  pure <| (← whnf type).isConstOf ``Language

private def findLocalLanguage : TacticM (Name × Expr) := withMainContext do
  let lctx ← getLCtx
  let mut found : Array (Name × Expr) := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      if ← languageType? decl.type then
        found := found.push (decl.userName, mkFVar decl.fvarId)
  match found.size with
  | 1 => pure found[0]!
  | 0 => throwError "AddConnective could not find a local `Language`"
  | _ => throwError "AddConnective found more than one local `Language`"

private def findLocalProvableName (L : Expr) : TacticM Name := withMainContext do
  let lctx ← getLCtx
  let mut found : Array Name := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      let type ← whnf decl.type
      if type.isAppOf ``Provable then
        let args := type.getAppArgs
        if args.size == 1 then
          if ← isDefEq args[0]! L then
            found := found.push decl.userName
  match found.size with
  | 1 => pure found[0]!
  | 0 => throwError "AddConnective could not find a local `Provable` for the current language"
  | _ => throwError "AddConnective found more than one local `Provable` for the current language"

private def languageLevel (L : Expr) : MetaM Level := do
  let type ← whnf (← inferType L)
  match type.getAppFn with
  | Expr.const ``Language [u] => pure u
  | _ => throwError "expected a Language expression, got{indentExpr type}"

private def exprTypeFor (L : Expr) : MetaM Expr := do
  let u ← languageLevel L
  pure <| mkApp (mkConst ``Language.expr [u]) L

private def findLocalExpr (L : Expr) : TacticM (Name × Expr) := withMainContext do
  let target ← exprTypeFor L
  let lctx ← getLCtx
  let mut found : Array (Name × Expr) := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      if ← isDefEq (← whnf decl.type) target then
        found := found.push (decl.userName, mkFVar decl.fvarId)
  match found.size with
  | 0 => throwError "AddConnective_truep_impp_self could not find a local expression"
  | _ => pure found[found.size - 1]!

private def assertLocalInstance (baseName : Name) (type value : Expr) : TacticM FVarId :=
  withMainContext do
    let userName ← mkFreshUserName baseName
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    if type.hasExprMVar || value.hasExprMVar then
      throwError "local instance {userName} contains unresolved metavariables"
    let goal ← getMainGoal
    let (ids, goal) ← goal.assertHypotheses #[
      { userName := userName
        type := type
        value := value
        binderInfo := BinderInfo.instImplicit
        kind := LocalDeclKind.default }]
    replaceMainGoal [goal]
    withMainContext do
      discard <| synthInstance type
    pure ids[0]!

private def letIFromSyntax (baseName : Name) (typeStx valueStx : TSyntax `term) :
    TacticM (TSyntax `ident) := withMainContext do
  let userName ← mkFreshUserName baseName
  let id := mkIdent userName
  evalTactic (← `(tactic| letI $id:ident : $typeStx := $valueStx))
  withMainContext do
    let type ← Term.elabType typeStx
    discard <| synthInstance type
  pure id

private def addIffp : TacticM Unit := withMainContext do
  let (LName, LExpr) ← findLocalLanguage
  let GammaPName ← findLocalProvableName LExpr
  let LId := mkIdent LName
  let GammaPId := mkIdent GammaPName
  let iffpLId ← letIFromSyntax `iffpL (← `(IffLanguage $LId))
    (← `(AndImp2Iff (L := $LId)))
  let _ ← letIFromSyntax `iffpDef
    (← `(@IffDefinition_And_Imp $LId _ _ $iffpLId))
    (← `(AndImp2Iff_Normal (L := $LId)))
  let _ ← letIFromSyntax `iffpAX
    (← `(@IffAxiomatization $LId _ $iffpLId $GammaPId))
    (← `(IffFromDefToAX_And_Imp (L := $LId) (GammaP := $GammaPId)))

private def addTruep : TacticM Unit := withMainContext do
  let (LName, LExpr) ← findLocalLanguage
  let GammaPName ← findLocalProvableName LExpr
  let LId := mkIdent LName
  let GammaPId := mkIdent GammaPName
  let truepLId ← letIFromSyntax `truepL (← `(TrueLanguage $LId))
    (← `(FalseImp2True (L := $LId)))
  let _ ← letIFromSyntax `truepDef
    (← `(@TrueDefinition_False_Imp $LId _ _ $truepLId))
    (← `(FalseImp2True_Normal (L := $LId)))
  let _ ← letIFromSyntax `truepAX
    (← `(@TrueAxiomatization $LId $truepLId $GammaPId))
    (← `(TrueFromDefToAX_False_Imp (L := $LId) (GammaP := $GammaPId)))

private def addNegp : TacticM Unit := withMainContext do
  let (LName, LExpr) ← findLocalLanguage
  let GammaPName ← findLocalProvableName LExpr
  let LId := mkIdent LName
  let GammaPId := mkIdent GammaPName
  let negpLId ← letIFromSyntax `negpL (← `(NegLanguage $LId))
    (← `(FalseImp2Neg (L := $LId)))
  let _ ← letIFromSyntax `negpDef
    (← `(@NegDefinition_False_Imp $LId _ _ $negpLId))
    (← `(FalseImp2Neg_Normal (L := $LId)))
  let _ ← letIFromSyntax `inegpAX
    (← `(@IntuitionisticNegAxiomatization $LId _ $negpLId $GammaPId))
    (← `(NegFromDefToAX_False_Imp (L := $LId) (GammaP := $GammaPId)))

private def addTruepImpSelfWith (xStx : TSyntax `term) : TacticM Unit := withMainContext do
  let (LName, LExpr) ← findLocalLanguage
  let GammaPName ← findLocalProvableName LExpr
  let LId := mkIdent LName
  let GammaPId := mkIdent GammaPName
  let xType ← exprTypeFor LExpr
  discard <| Term.elabTerm xStx (some xType)
  let truepLId ← letIFromSyntax `truepL (← `(TrueLanguage $LId))
    (← `(ImpSelf2True (L := $LId) $xStx))
  let _ ← letIFromSyntax `truepDef
    (← `(@TrueDefinition_Imp_Self $LId _ $truepLId))
    (← `(ImpSelf2True_Normal (L := $LId) $xStx))
  let _ ← letIFromSyntax `truepAX
    (← `(@TrueAxiomatization $LId $truepLId $GammaPId))
    (← `(TrueFromDefToAX_Imp_Self (L := $LId) (GammaP := $GammaPId)))

private def addTruepImpSelfWithExpr (x : Expr) : TacticM Unit := withMainContext do
  let (_, LExpr) ← findLocalLanguage
  let u ← languageLevel LExpr
  let minL ← synthInstance (mkApp (mkConst ``MinimumLanguage [u]) LExpr)
  let gammaP ← synthInstance (mkApp (mkConst ``Provable [u]) LExpr)
  let minAXType := mkAppN (mkConst ``MinimumAxiomatization [u]) #[LExpr, minL, gammaP]
  let minAX ← synthInstance minAXType
  let truepType := mkApp (mkConst ``TrueLanguage [u]) LExpr
  let truepValue := mkAppN (mkConst ``ImpSelf2True [u]) #[LExpr, minL, x]
  let truepId ← assertLocalInstance `truepL truepType truepValue
  let truepExpr := mkFVar truepId
  let defType := mkAppN (mkConst ``TrueDefinition_Imp_Self [u]) #[LExpr, minL, truepExpr]
  let defValue := mkAppN (mkConst ``ImpSelf2True_Normal [u]) #[LExpr, minL, x]
  let defId ← assertLocalInstance `truepDef defType defValue
  let defExpr := mkFVar defId
  let axType := mkAppN (mkConst ``TrueAxiomatization [u]) #[LExpr, truepExpr, gammaP]
  let axValue := mkAppN (mkConst ``TrueFromDefToAX_Imp_Self [u])
    #[LExpr, minL, truepExpr, gammaP, minAX, defExpr]
  discard <| assertLocalInstance `truepAX axType axValue

private def addTruepImpSelf : TacticM Unit := withMainContext do
  let (_, LExpr) ← findLocalLanguage
  let (_, x) ← findLocalExpr LExpr
  addTruepImpSelfWithExpr x

end AddConnectiveLocal

syntax "AddConnective_iffp" : tactic
syntax "AddConnective_truep" : tactic
syntax "AddConnective_negp" : tactic
syntax "AddConnective_truep_impp_self" : tactic
syntax "AddConnective_truep_impp_self" ident : tactic
syntax "AddConnective_truep_impp_self" "(" term ")" : tactic

elab "AddConnective_iffp" : tactic =>
  AddConnectiveLocal.addIffp

elab "AddConnective_truep" : tactic =>
  AddConnectiveLocal.addTruep

elab "AddConnective_negp" : tactic =>
  AddConnectiveLocal.addNegp

elab "AddConnective_truep_impp_self" : tactic =>
  AddConnectiveLocal.addTruepImpSelf

elab "AddConnective_truep_impp_self" x:ident : tactic =>
  AddConnectiveLocal.addTruepImpSelfWith ⟨x.raw⟩

elab "AddConnective_truep_impp_self" "(" x:term ")" : tactic =>
  AddConnectiveLocal.addTruepImpSelfWith x

end Unifysl
