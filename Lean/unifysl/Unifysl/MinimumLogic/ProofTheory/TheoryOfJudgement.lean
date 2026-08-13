import Unifysl.MinimumLogic.ProofTheory.RewriteClass

/-!
Coq inventory from `MinimumLogic/ProofTheory/TheoryOfJudgement.v`:
- `Axiomatization2Deduction_bD`:
  a minimum Hilbert-style axiomatization plus `Derivable1Provable`
  yields `BasicDeduction`.
- `Axiomatization2Equiv_bE`:
  a minimum Hilbert-style axiomatization plus `EquivProvable`
  yields `BasicLogicEquiv`.
- `Axiomatization2Deduction_GammaPD1`:
  a minimum Hilbert-style axiomatization plus `Derivable1FromProvable`
  yields `ProvableFromDerivable1`.
- `Axiomatization2Deduction_minD`:
  a minimum Hilbert-style axiomatization plus `Derivable1FromProvable`
  yields `MinimumDeduction`.
-/

universe u

namespace Unifysl

section Axiomatization2Deduction

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaD1 : Derivable1 L]
variable [GammaD1P : Derivable1FromProvable L GammaP GammaD1]
variable [minAX : MinimumAxiomatization L GammaP]

theorem Axiomatization2Deduction_bD [_GammaD : Derivable L] :
    BasicDeduction L GammaD1 := by
  constructor
  · intro x
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x x).mpr
      (provable_impp_refl x)
  · intro x y z hxy hyz
    have hxyProv : @Provable.provable L GammaP (x ⟶ y) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x y).mp hxy
    have hyzProv : @Provable.provable L GammaP (y ⟶ z) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) y z).mp hyz
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) x z).mpr
      (aux_minimun_rule02 x y z hxyProv hyzProv)

end Axiomatization2Deduction

section Axiomatization2LogicEquiv

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaL : LogicEquiv L]
variable [GammaEP : EquivProvable L GammaP GammaL]
variable [minAX : MinimumAxiomatization L GammaP]

theorem Axiomatization2Equiv_bE [_GammaD : Derivable L] :
    BasicLogicEquiv L GammaL := by
  constructor
  · intro x
    exact (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaL) x x).mpr
      ⟨provable_impp_refl x, provable_impp_refl x⟩
  · intro x y hxy
    have hprov := (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaL) x y).mp hxy
    exact (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaL) y x).mpr
      ⟨hprov.right, hprov.left⟩
  · intro x y z hxy hyz
    have hxyProv := (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaL) x y).mp hxy
    have hyzProv := (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaL) y z).mp hyz
    exact (EquivProvable.logic_equiv_provable
      (L := L) (GammaP := GammaP) (GammaL := GammaL) x z).mpr
      ⟨aux_minimun_rule02 x y z hxyProv.left hyzProv.left,
        aux_minimun_rule02 z y x hyzProv.right hxyProv.right⟩

end Axiomatization2LogicEquiv

section Derivable1_Provable

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaP : Provable L] [GammaD1 : Derivable1 L]

section provable2derivable1

variable [GammaD1P : Derivable1Provable L GammaP GammaD1]
variable [minAX : MinimumAxiomatization L GammaP]

theorem Axiomatization2Deduction_GammaPD1 :
    ProvableFromDerivable1 L GammaP GammaD1 := by
  constructor
  intro x
  constructor
  · intro hx
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x ⟶ x) x).mpr
      (aux_minimun_rule00 x (x ⟶ x) hx)
  · intro hder
    have himp : @Provable.provable L GammaP ((x ⟶ x) ⟶ x) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) (x ⟶ x) x).mp hder
    exact MinimumAxiomatization.modus_ponens
      (Gamma := GammaP) (x ⟶ x) x himp (provable_impp_refl x)

theorem Axiomatization2Deduction_minD :
    MinimumDeduction L GammaD1 := by
  constructor
  · intro x y z hxy hy
    have hxyProv : @Provable.provable L GammaP (x ⟶ y ⟶ z) :=
      (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1) x (y ⟶ z)).mp hxy
    have hyProv : @Provable.provable L GammaP (x ⟶ y) :=
      (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1) x y).mp hy
    have hstep : @Provable.provable L GammaP ((x ⟶ y) ⟶ (x ⟶ z)) :=
      provables_modus_ponens (x ⟶ y ⟶ z) ((x ⟶ y) ⟶ (x ⟶ z))
        (provable_axiom2 x y z) hxyProv
    exact (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1) x z).mpr
      (provables_modus_ponens (x ⟶ y) (x ⟶ z) hstep hyProv)
  · intro x y z h
    have hProv : @Provable.provable L GammaP ((x ⟶ y) ⟶ z) :=
      (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1)
        (x ⟶ y) z).mp h
    have h1 : @Provable.provable L GammaP ((y ⟶ x ⟶ y) ⟶ (y ⟶ z)) :=
      aux_minimun_rule01 (x ⟶ y) z y hProv
    have h0 : @Provable.provable L GammaP (x ⟶ (y ⟶ x ⟶ y)) :=
      aux_minimun_rule00 (y ⟶ x ⟶ y) x (provable_axiom1 y x)
    exact (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1)
      x (y ⟶ z)).mpr
      (aux_minimun_rule02 x (y ⟶ x ⟶ y) (y ⟶ z) h0 h1)
  · intro x y
    exact (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1)
      x (y ⟶ y)).mpr
      (aux_minimun_rule00 (y ⟶ y) x (provable_impp_refl y))
  · intro x y
    exact (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1)
      x (y ⟶ x)).mpr
      (provable_axiom1 x y)
  · intro x y z
    exact (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1)
      (x ⟶ y ⟶ z) ((x ⟶ y) ⟶ (x ⟶ z))).mpr
      (provable_axiom2 x y z)

end provable2derivable1

end Derivable1_Provable

end Unifysl
