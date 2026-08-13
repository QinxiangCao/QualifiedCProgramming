import Unifysl.PropositionalLogic.ProofTheory.Intuitionistic

/-!
Coq inventory from `PropositionalLogic/ProofTheory/RewriteClass.v`:
- Active instances:
  `provables_andp_proper_impp`,
  `provables_orp_proper_impp`, `provables_negp_proper_impp`,
  `provable_iffp_rewrite`, `provable_iffp_equiv`,
  `provable_proper_iffp`,
  `provables_impp_proper_iffp`,
  `provables_andp_proper_iffp`, `provables_orp_proper_iffp`,
  `provables_iffp_proper_iffp`, `provables_negp_proper_iffp`,
  `derivables_proper_iffp`,
  `derivable1s_impp_proper`, `derivable1s_andp_proper`,
  `derivable1s_orp_proper`, `derivable1s_negp_proper`,
  `logic_equiv_impp_proper`, `logic_equiv_andp_proper`,
  `logic_equiv_orp_proper`, `logic_equiv_negp_proper`,
  `logic_equiv_iffp_proper`.
-/

universe u

namespace Unifysl

open Relation_ext
open PropositionalLanguageNotation

section RewriteClass1

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [OrLanguage L]
variable [FalseLanguage L] [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [GammaP : Provable L]
variable [minAX : MinimumAxiomatization L GammaP]
variable [andpAX : AndAxiomatization L GammaP]
variable [orpAX : OrAxiomatization L GammaP]
variable [falsepAX : FalseAxiomatization L GammaP]
variable [inegpAX : IntuitionisticNegAxiomatization L GammaP]
variable [iffpAX : IffAxiomatization L GammaP]
variable [truepAX : TrueAxiomatization L GammaP]

private def provableImppRel : @Language.expr L -> @Language.expr L -> Prop :=
  fun x y => @Provable.provable L GammaP (x ⟶ y)

private def provableIffpRel : @Language.expr L -> @Language.expr L -> Prop :=
  fun x y => @Provable.provable L GammaP (x ⟷ y)

instance provables_andp_proper_impp :
    Proper
      (provableImppRel (L := L) (GammaP := GammaP) ==>
        provableImppRel (L := L) (GammaP := GammaP) ==>
        provableImppRel (L := L) (GammaP := GammaP))
      (fun x y : @Language.expr L => x && y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact provables_impp_andp_fold (x1 && y1) x2 y2
      (solve_impp_trans (x1 && y1) x1 x2 (AndAxiomatization.provable_andp_elim1 x1 y1) hx)
      (solve_impp_trans (x1 && y1) y1 y2 (AndAxiomatization.provable_andp_elim2 x1 y1) hy)

instance provables_orp_proper_impp :
    Proper
      (provableImppRel (L := L) (GammaP := GammaP) ==>
        provableImppRel (L := L) (GammaP := GammaP) ==>
        provableImppRel (L := L) (GammaP := GammaP))
      (fun x y : @Language.expr L => x || y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact provables_orp_mono x1 x2 y1 y2 hx hy

instance provables_negp_proper_impp :
    Proper
      (flipRel (provableImppRel (L := L) (GammaP := GammaP)) ==>
        provableImppRel (L := L) (GammaP := GammaP))
      (fun x : @Language.expr L => ~~ x) where
  proper := by
    intro x1 x2 hx
    exact MinimumAxiomatization.modus_ponens
      (Gamma := GammaP) (x2 ⟶ x1) ((~~ x1) ⟶ (~~ x2))
      (IntuitionisticNegAxiomatization.provable_contrapositivePP x1 x2) hx

instance provable_iffp_rewrite :
    RewriteRelation (provableIffpRel (L := L) (GammaP := GammaP)) where

instance provable_iffp_equiv :
    Equivalence (provableIffpRel (L := L) (GammaP := GammaP)) where
  refl := by
    intro x
    exact provable_iffp_refl x
  symm := by
    intro x y hxy
    exact provables_iffp_intros y x (provables_iffp_elim2 x y hxy) (provables_iffp_elim1 x y hxy)
  trans := by
    intro x y z hxy hyz
    exact provables_iffp_intros x z
      (solve_impp_trans x y z (provables_iffp_elim1 x y hxy) (provables_iffp_elim1 y z hyz))
      (solve_impp_trans z y x (provables_iffp_elim2 y z hyz) (provables_iffp_elim2 x y hxy))

instance provable_proper_iffp :
    Proper (provableIffpRel (L := L) (GammaP := GammaP) ==> Iff)
      (fun x : @Language.expr L => @Provable.provable L GammaP x) where
  proper := by
    intro x y hxy
    constructor
    · intro hx
      exact MinimumAxiomatization.modus_ponens
        (Gamma := GammaP) x y (provables_iffp_elim1 x y hxy) hx
    · intro hy
      exact MinimumAxiomatization.modus_ponens
        (Gamma := GammaP) y x (provables_iffp_elim2 x y hxy) hy

instance provables_impp_proper_iffp :
    Proper
      (provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP))
      (fun x y : @Language.expr L => x ⟶ y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact provables_iffp_intros (x1 ⟶ y1) (x2 ⟶ y2)
      ((provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper
        x1 x2 (provables_iffp_elim2 x1 x2 hx)
        y1 y2 (provables_iffp_elim1 y1 y2 hy))
      ((provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper
        x2 x1 (provables_iffp_elim1 x1 x2 hx)
        y2 y1 (provables_iffp_elim2 y1 y2 hy))

instance provables_andp_proper_iffp :
    Proper
      (provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP))
      (fun x y : @Language.expr L => x && y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact provables_iffp_intros (x1 && y1) (x2 && y2)
      ((provables_andp_proper_impp (L := L) (GammaP := GammaP)).proper
        x1 x2 (provables_iffp_elim1 x1 x2 hx)
        y1 y2 (provables_iffp_elim1 y1 y2 hy))
      ((provables_andp_proper_impp (L := L) (GammaP := GammaP)).proper
        x2 x1 (provables_iffp_elim2 x1 x2 hx)
        y2 y1 (provables_iffp_elim2 y1 y2 hy))

instance provables_orp_proper_iffp :
    Proper
      (provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP))
      (fun x y : @Language.expr L => x || y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact provables_iffp_intros (x1 || y1) (x2 || y2)
      ((provables_orp_proper_impp (L := L) (GammaP := GammaP)).proper
        x1 x2 (provables_iffp_elim1 x1 x2 hx)
        y1 y2 (provables_iffp_elim1 y1 y2 hy))
      ((provables_orp_proper_impp (L := L) (GammaP := GammaP)).proper
        x2 x1 (provables_iffp_elim2 x1 x2 hx)
        y2 y1 (provables_iffp_elim2 y1 y2 hy))

instance provables_iffp_proper_iffp :
    Proper
      (provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP))
      (fun x y : @Language.expr L => x ⟷ y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    let A : @Language.expr L := x1 ⟷ y1
    let B : @Language.expr L := (x1 ⟶ y1) && (y1 ⟶ x1)
    let C : @Language.expr L := (x2 ⟶ y2) && (y2 ⟶ x2)
    let D : @Language.expr L := x2 ⟷ y2
    have hAB : @Provable.provable L GammaP (A ⟶ B) :=
      provables_iffp_elim1 A B (provable_iffp x1 y1)
    have hBC : @Provable.provable L GammaP (B ⟶ C) :=
      (provables_andp_proper_impp (L := L) (GammaP := GammaP)).proper
        (x1 ⟶ y1) (x2 ⟶ y2)
        ((provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper
          x1 x2 (provables_iffp_elim2 x1 x2 hx)
          y1 y2 (provables_iffp_elim1 y1 y2 hy))
        (y1 ⟶ x1) (y2 ⟶ x2)
        ((provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper
          y1 y2 (provables_iffp_elim2 y1 y2 hy)
          x1 x2 (provables_iffp_elim1 x1 x2 hx))
    have hCD : @Provable.provable L GammaP (C ⟶ D) :=
      provables_iffp_elim2 D C (provable_iffp x2 y2)
    have hForward : @Provable.provable L GammaP (A ⟶ D) :=
      solve_impp_trans A B D hAB (solve_impp_trans B C D hBC hCD)
    have hDC : @Provable.provable L GammaP (D ⟶ C) :=
      provables_iffp_elim1 D C (provable_iffp x2 y2)
    have hCB : @Provable.provable L GammaP (C ⟶ B) :=
      (provables_andp_proper_impp (L := L) (GammaP := GammaP)).proper
        (x2 ⟶ y2) (x1 ⟶ y1)
        ((provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper
          x2 x1 (provables_iffp_elim1 x1 x2 hx)
          y2 y1 (provables_iffp_elim2 y1 y2 hy))
        (y2 ⟶ x2) (y1 ⟶ x1)
        ((provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper
          y2 y1 (provables_iffp_elim1 y1 y2 hy)
          x2 x1 (provables_iffp_elim2 x1 x2 hx))
    have hBA : @Provable.provable L GammaP (B ⟶ A) :=
      provables_iffp_elim2 A B (provable_iffp x1 y1)
    have hBackward : @Provable.provable L GammaP (D ⟶ A) :=
      solve_impp_trans D C A hDC (solve_impp_trans C B A hCB hBA)
    exact provables_iffp_intros A D hForward hBackward

instance provables_negp_proper_iffp :
    Proper
      (provableIffpRel (L := L) (GammaP := GammaP) ==>
        provableIffpRel (L := L) (GammaP := GammaP))
      (fun x : @Language.expr L => ~~ x) where
  proper := by
    intro x1 x2 hx
    exact provables_iffp_intros (~~ x1) (~~ x2)
      ((provables_negp_proper_impp (L := L) (GammaP := GammaP)).proper
        x1 x2 (provables_iffp_elim2 x1 x2 hx))
      ((provables_negp_proper_impp (L := L) (GammaP := GammaP)).proper
        x2 x1 (provables_iffp_elim1 x1 x2 hx))

end RewriteClass1

section RewriteClass2

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [OrLanguage L]
variable [FalseLanguage L] [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [GammaP : Provable L] [GammaD : Derivable L]
variable [GammaPD : ProvableDerivable L GammaP GammaD]
variable [bSC : BasicSequentCalculus L GammaD]
variable [minSC : MinimumSequentCalculus L GammaD]
variable [andpSC : AndSequentCalculus L GammaD]
variable [orpSC : OrSequentCalculus L GammaD]
variable [falsepSC : FalseSequentCalculus L GammaD]
variable [inegpSC : IntuitionisticNegSequentCalculus L GammaD]
variable [iffpSC : IffSequentCalculus L GammaD]
variable [truepSC : TrueSequentCalculus L GammaD]

instance derivables_proper_iffp :
    Proper (Eq ==> provableIffpRel (L := L) (GammaP := GammaP) ==> Iff)
      (fun Phi (x : @Language.expr L) => @Derivable.derivable L GammaD Phi x) where
  proper := by
    intro Phi Phi' hPhi x y hxy
    subst Phi'
    have hiffD : @Derivable.derivable L GammaD Phi (x ⟷ y) :=
      deduction_weaken0 (GammaP := GammaP) Phi (x ⟷ y) hxy
    have hxyD : @Derivable.derivable L GammaD Phi (x ⟶ y) :=
      (deduction_theorem Phi x y).mp
        (IffSequentCalculus.derivables_iffp_elim1 Phi x y hiffD)
    have hyxD : @Derivable.derivable L GammaD Phi (y ⟶ x) :=
      (deduction_theorem Phi y x).mp
        (IffSequentCalculus.derivables_iffp_elim2 Phi x y hiffD)
    constructor
    · intro hx
      exact MinimumSequentCalculus.deduction_modus_ponens Phi x y hx hxyD
    · intro hy
      exact MinimumSequentCalculus.deduction_modus_ponens Phi y x hy hyxD

end RewriteClass2

section RewriteClass3

variable {L : Language.{u}} [GammaD1 : Derivable1 L]
variable [bD : BasicDeduction L GammaD1]

section impp

variable [MinimumLanguage L] [AndLanguage L]
variable [adjD : ImpAndAdjointDeduction L GammaD1]
variable [andpD : AndDeduction L GammaD1]

instance derivable1s_impp_proper :
    Proper (flipRel (derivable1 (L := L)) ==> derivable1 (L := L) ==> derivable1 (L := L))
      (fun x y : @Language.expr L => x ⟶ y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact derivable1_impp_mono x1 x2 y1 y2 hx hy

end impp

section andp

variable [AndLanguage L] [andpD : AndDeduction L GammaD1]

instance derivable1s_andp_proper :
    Proper (derivable1 (L := L) ==> derivable1 (L := L) ==> derivable1 (L := L))
      (fun x y : @Language.expr L => x && y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) (x1 && y1) x2 y2
      (derivable1_trans (x1 && y1) x1 x2
        (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x1 y1) hx)
      (derivable1_trans (x1 && y1) y1 y2
        (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x1 y1) hy)

end andp

section orp

variable [OrLanguage L] [orpD : OrDeduction L GammaD1]

instance derivable1s_orp_proper :
    Proper (derivable1 (L := L) ==> derivable1 (L := L) ==> derivable1 (L := L))
      (fun x y : @Language.expr L => x || y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact derivable1_orp_mono x1 x2 y1 y2 hx hy

end orp

section negp

variable [NegLanguage L] [inegpD : IntuitionisticNegDeduction L GammaD1]

instance derivable1s_negp_proper :
    Proper (flipRel (derivable1 (L := L)) ==> derivable1 (L := L))
      (fun x : @Language.expr L => ~~ x) where
  proper := by
    intro x1 x2 hx
    exact IntuitionisticNegDeduction.derivable1s_contrapositivePP
      (GammaD1 := GammaD1) x1 x2 hx

end negp

end RewriteClass3

section RewriteClass4

variable {L : Language.{u}} [GammaE : LogicEquiv L]
variable [bE : BasicLogicEquiv L GammaE]

section impp

variable [MinimumLanguage L] [imppE : ImpLogicEquiv L GammaE]

instance logic_equiv_impp_proper :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
      (fun x y : @Language.expr L => x ⟶ y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact ImpLogicEquiv.logic_equiv_impp (Gamma := GammaE) x1 x2 y1 y2 hx hy

end impp

section andp

variable [AndLanguage L] [andpE : AndLogicEquiv L GammaE]

instance logic_equiv_andp_proper :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
      (fun x y : @Language.expr L => x && y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact AndLogicEquiv.logic_equiv_andp_congr (GammaE := GammaE) x1 x2 y1 y2 hx hy

end andp

section orp

variable [OrLanguage L] [orpE : OrLogicEquiv L GammaE]

instance logic_equiv_orp_proper :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
      (fun x y : @Language.expr L => x || y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    exact OrLogicEquiv.logic_equiv_orp_congr (GammaE := GammaE) x1 x2 y1 y2 hx hy

end orp

section negp

variable [NegLanguage L] [negpE : NegLogicEquiv L GammaE]

instance logic_equiv_negp_proper :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L))
      (fun x : @Language.expr L => ~~ x) where
  proper := by
    intro x y hxy
    exact NegLogicEquiv.logic_equiv_negp_intros (GammaE := GammaE) x y hxy

end negp

section iffp

variable [MinimumLanguage L] [AndLanguage L] [IffLanguage L]
variable [imppE : ImpLogicEquiv L GammaE]
variable [andpE : AndLogicEquiv L GammaE]
variable [iffpE : IffLogicEquiv L GammaE]

instance logic_equiv_iffp_proper :
    Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
      (fun x y : @Language.expr L => x ⟷ y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    have hfold1 :
        logic_equiv (L := L) (x1 ⟷ y1) ((x1 ⟶ y1) && (y1 ⟶ x1)) :=
      logic_equiv_symm ((x1 ⟶ y1) && (y1 ⟶ x1)) (x1 ⟷ y1)
        (IffLogicEquiv.logic_equiv_provable_iffp_intros (GammaE := GammaE) x1 y1)
    have hcongr :
        logic_equiv (L := L) ((x1 ⟶ y1) && (y1 ⟶ x1))
          ((x2 ⟶ y2) && (y2 ⟶ x2)) :=
      AndLogicEquiv.logic_equiv_andp_congr (GammaE := GammaE)
        (x1 ⟶ y1) (x2 ⟶ y2) (y1 ⟶ x1) (y2 ⟶ x2)
        (ImpLogicEquiv.logic_equiv_impp (Gamma := GammaE) x1 x2 y1 y2 hx hy)
        (ImpLogicEquiv.logic_equiv_impp (Gamma := GammaE) y1 y2 x1 x2 hy hx)
    have hfold2 :
        logic_equiv (L := L) ((x2 ⟶ y2) && (y2 ⟶ x2)) (x2 ⟷ y2) :=
      IffLogicEquiv.logic_equiv_provable_iffp_intros (GammaE := GammaE) x2 y2
    exact logic_equiv_trans (x1 ⟷ y1) ((x1 ⟶ y1) && (y1 ⟶ x1)) (x2 ⟷ y2)
      hfold1
      (logic_equiv_trans ((x1 ⟶ y1) && (y1 ⟶ x1))
        ((x2 ⟶ y2) && (y2 ⟶ x2)) (x2 ⟷ y2) hcongr hfold2)

end iffp

end RewriteClass4

end Unifysl
