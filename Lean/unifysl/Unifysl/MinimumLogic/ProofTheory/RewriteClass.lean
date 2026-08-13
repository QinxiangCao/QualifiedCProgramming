import Unifysl.MinimumLogic.ProofTheory.Minimum

/-!
Coq inventory from `MinimumLogic/ProofTheory/RewriteClass.v`:
- Instance `provable_impp_rewrite`.
- Instances/proper morphisms:
  `provable_impp_refl_instance`, `provable_proper_impp`,
  `provables_impp_proper_impp`, `provable_proper_derivable1`,
  `derivable_proper_impp`, `derivable_proper_derivable1`,
  `provable_proper_equiv`, `derivable_proper_equiv`.
- Coq rewrite smoke-test modules `TestInAxiomatization`,
  `TestInSequentCalculus`.
- Lemma `imp_derivable`.

Lean note: this file reuses `RewriteRelation`, `flipRel`, `implRel` from
`GeneralLogic.ProofTheory.BasicDeduction` and `Proper`/`==>` from
`Lib.Relation_ext`.
-/

universe u

namespace Unifysl

open Relation_ext

section RewriteClass

variable {L : Language.{u}} [MinimumLanguage L] [GammaP : Provable L]

private def provableImppRel : @Language.expr L -> @Language.expr L -> Prop :=
  fun x y => @Provable.provable L GammaP (x ⟶ y)

instance provable_impp_rewrite :
    RewriteRelation (provableImppRel (L := L) (GammaP := GammaP)) where

section Provable

variable [minAX : MinimumAxiomatization L GammaP]

instance provable_impp_refl_instance :
    Reflexive (provableImppRel (L := L) (GammaP := GammaP)) := by
  intro x
  exact provable_impp_refl x

instance provable_proper_impp :
    Proper ((provableImppRel (L := L) (GammaP := GammaP)) ==> implRel)
      (fun x : @Language.expr L => @Provable.provable L GammaP x) where
  proper := by
    intro x y hxy hx
    exact MinimumAxiomatization.modus_ponens (Gamma := GammaP) x y hxy hx

instance provables_impp_proper_impp :
    Proper
      (flipRel (provableImppRel (L := L) (GammaP := GammaP)) ==>
        (provableImppRel (L := L) (GammaP := GammaP)) ==>
        (provableImppRel (L := L) (GammaP := GammaP)))
      (fun x y : @Language.expr L => x ⟶ y) where
  proper := by
    intro x1 x2 hx y1 y2 hy
    have hy_lift :
        @Provable.provable L GammaP ((x1 ⟶ y1) ⟶ x1 ⟶ y2) :=
      aux_minimun_rule01 y1 y2 x1 hy
    have hx1 :
        @Provable.provable L GammaP (x1 ⟶ (x1 ⟶ y1) ⟶ y2) :=
      MinimumAxiomatization.modus_ponens (Gamma := GammaP) _ _
        (provable_impp_arg_switch (x1 ⟶ y1) x1 y2) hy_lift
    have hx2 :
        @Provable.provable L GammaP (x2 ⟶ (x1 ⟶ y1) ⟶ y2) :=
      aux_minimun_rule02 x2 x1 ((x1 ⟶ y1) ⟶ y2) hx hx1
    exact MinimumAxiomatization.modus_ponens (Gamma := GammaP) _ _
      (provable_impp_arg_switch x2 (x1 ⟶ y1) y2) hx2

section Derivable1_provable

variable [GammaD : Derivable1 L]
variable [GammaD1P : Derivable1Provable L GammaP GammaD]

instance provable_proper_derivable1 :
    Proper ((derivable1 (L := L)) ==> implRel)
      (fun x : @Language.expr L => @Provable.provable L GammaP x) where
  proper := by
    intro x y hxy hx
    have hprov :
        @Provable.provable L GammaP (x ⟶ y) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD) x y).mp hxy
    exact MinimumAxiomatization.modus_ponens (Gamma := GammaP) x y hprov hx

end Derivable1_provable

end Provable

section Derivable

variable [GammaD : Derivable L]
variable [GammaPD : ProvableDerivable L GammaP GammaD]
variable [bSC : BasicSequentCalculus L GammaD]
variable [minSC : MinimumSequentCalculus L GammaD]

instance derivable_proper_impp :
    Proper
      (Eq ==>
        (provableImppRel (L := L) (GammaP := GammaP)) ==>
        implRel)
      (fun Phi (x : @Language.expr L) => @Derivable.derivable L GammaD Phi x) where
  proper := by
    intro Phi Phi' hPhi x y hxy hDer
    subst Phi'
    have hImp :
        @Derivable.derivable L GammaD Phi (x ⟶ y) :=
      deduction_weaken0 (GammaP := GammaP) Phi (x ⟶ y) hxy
    exact MinimumSequentCalculus.deduction_modus_ponens Phi x y hDer hImp

section Derivable1

variable [GammaD1 : Derivable1 L]
variable [GammaD1P : Derivable1Provable L GammaP GammaD1]

instance derivable_proper_derivable1 :
    Proper (Eq ==> (derivable1 (L := L)) ==> implRel)
      (fun Phi (x : @Language.expr L) => @Derivable.derivable L GammaD Phi x) where
  proper := by
    intro Phi Phi' hPhi x y hxy hDer
    subst Phi'
    have hprov :
        @Provable.provable L GammaP (x ⟶ y) :=
      (Derivable1Provable.derivable1_provable
        (L := L) (GammaP := GammaP) (GammaD := GammaD1) x y).mp hxy
    have hImp :
        @Derivable.derivable L GammaD Phi (x ⟶ y) :=
      deduction_weaken0 (GammaP := GammaP) Phi (x ⟶ y) hprov
    exact MinimumSequentCalculus.deduction_modus_ponens Phi x y hDer hImp

end Derivable1

end Derivable

section Logic_equiv

variable [GammaE : LogicEquiv L]
variable [GammaEP : EquivProvable L GammaP GammaE]
variable [minAX : MinimumAxiomatization L GammaP]

instance provable_proper_equiv :
    Proper ((logic_equiv (L := L)) ==> Iff)
      (fun x : @Language.expr L => @Provable.provable L GammaP x) where
  proper := by
    intro x y hxy
    have hprov :=
      (EquivProvable.logic_equiv_provable
        (L := L) (GammaP := GammaP) (GammaL := GammaE) x y).mp hxy
    constructor
    · intro hx
      exact MinimumAxiomatization.modus_ponens (Gamma := GammaP) x y hprov.left hx
    · intro hy
      exact MinimumAxiomatization.modus_ponens (Gamma := GammaP) y x hprov.right hy

variable [GammaD : Derivable L]
variable [GammaPD : ProvableDerivable L GammaP GammaD]
variable [bSC : BasicSequentCalculus L GammaD]
variable [minSC : MinimumSequentCalculus L GammaD]

instance derivable_proper_equiv :
    Proper (Eq ==> (logic_equiv (L := L)) ==> Iff)
      (fun Phi (x : @Language.expr L) => @Derivable.derivable L GammaD Phi x) where
  proper := by
    intro Phi Phi' hPhi x y hxy
    subst Phi'
    have hprov :=
      (EquivProvable.logic_equiv_provable
        (L := L) (GammaP := GammaP) (GammaL := GammaE) x y).mp hxy
    constructor
    · intro hx
      have hImp :
          @Derivable.derivable L GammaD Phi (x ⟶ y) :=
        deduction_weaken0 (GammaP := GammaP) Phi (x ⟶ y) hprov.left
      exact MinimumSequentCalculus.deduction_modus_ponens Phi x y hx hImp
    · intro hy
      have hImp :
          @Derivable.derivable L GammaD Phi (y ⟶ x) :=
        deduction_weaken0 (GammaP := GammaP) Phi (y ⟶ x) hprov.right
      exact MinimumSequentCalculus.deduction_modus_ponens Phi y x hy hImp

end Logic_equiv

end RewriteClass

namespace TestInAxiomatization

theorem test_derivable_impp
    {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaD : Derivable L]
    [GammaDP : DerivableProvable L GammaP GammaD]
    [minAX : MinimumAxiomatization L GammaP]
    (Phi : context (L := L)) (y1 y2 : @Language.expr L) :
    @Provable.provable L GammaP (y1 ⟶ y2) ->
      @Derivable.derivable L GammaD Phi y1 ->
        @Derivable.derivable L GammaD Phi y2 := by
  intro hy hDer
  letI : ProvableDerivable L GammaP GammaD :=
    Axiomatization2SequentCalculus_GammaPD
  letI : MinimumSequentCalculus L GammaD :=
    Axiomatization2SequentCalculus_minSC
  letI : BasicSequentCalculus L GammaD :=
    Axiomatization2SequentCalculus_bSC
  exact (derivable_proper_impp (L := L) (GammaP := GammaP) (GammaD := GammaD)).proper
    Phi Phi rfl y1 y2 hy hDer

theorem test_impp_proper
    {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [minAX : MinimumAxiomatization L GammaP]
    (x1 y1 x2 y2 : @Language.expr L) :
    @Provable.provable L GammaP (x2 ⟶ x1) ->
      @Provable.provable L GammaP (y1 ⟶ y2) ->
        @Provable.provable L GammaP ((x1 ⟶ y1) ⟶ (x2 ⟶ y2)) := by
  intro hx hy
  exact (provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper x1 x2 hx y1 y2 hy

end TestInAxiomatization

namespace TestInSequentCalculus

theorem test_derivable_impp
    {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaD : Derivable L]
    [GammaPD : ProvableDerivable L GammaP GammaD]
    [bSC : BasicSequentCalculus L GammaD]
    [minSC : MinimumSequentCalculus L GammaD]
    (Phi : context (L := L)) (y1 y2 : @Language.expr L) :
    @Provable.provable L GammaP (y1 ⟶ y2) ->
      @Derivable.derivable L GammaD Phi y1 ->
        @Derivable.derivable L GammaD Phi y2 := by
  intro hy hDer
  exact (derivable_proper_impp (L := L) (GammaP := GammaP) (GammaD := GammaD)).proper
    Phi Phi rfl y1 y2 hy hDer

theorem test_impp_proper
    {L : Language.{u}} [MinimumLanguage L]
    [GammaP : Provable L] [GammaD : Derivable L]
    [GammaPD : ProvableDerivable L GammaP GammaD]
    [bSC : BasicSequentCalculus L GammaD]
    [minSC : MinimumSequentCalculus L GammaD]
    (x1 y1 x2 y2 : @Language.expr L) :
    @Provable.provable L GammaP (x2 ⟶ x1) ->
      @Provable.provable L GammaP (y1 ⟶ y2) ->
        @Provable.provable L GammaP ((x1 ⟶ y1) ⟶ (x2 ⟶ y2)) := by
  intro hx hy
  letI : MinimumAxiomatization L GammaP :=
    SequentCalculus2Axiomatization_minAX
  exact (provables_impp_proper_impp (L := L) (GammaP := GammaP)).proper x1 x2 hx y1 y2 hy

end TestInSequentCalculus

section imp_der

variable {L : Language.{u}} [MinimumLanguage L]
variable [GammaD : Derivable L]
variable [bSC : BasicSequentCalculus L GammaD]
variable [minSC : MinimumSequentCalculus L GammaD]

theorem imp_derivable :
    (forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD Phi (x ⟶ y)) <->
    (forall (Phi : context (L := L)) (x y : @Language.expr L),
      @Derivable.derivable L GammaD Phi x ->
        @Derivable.derivable L GammaD Phi y) := by
  constructor
  · intro h Phi x y hx
    exact MinimumSequentCalculus.deduction_modus_ponens Phi x y hx (h Phi x y)
  · intro h Phi x y
    exact MinimumSequentCalculus.deduction_impp_intros Phi x y
      (h (Phi ;; x) x y (derivable_assum1 Phi x))

end imp_der

end Unifysl
