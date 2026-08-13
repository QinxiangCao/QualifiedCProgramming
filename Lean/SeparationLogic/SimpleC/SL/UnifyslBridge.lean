import AUXLib.SetoidRewrite
import Unifysl.GeneralLogic.ProofTheory.BasicLogicEquiv
import Unifysl.LogicGenerator.demo932.Facade
import Unifysl.ShallowQuantifierLogic.ProofTheory

namespace SimpleC.SL.UnifyslBridge

class UnifyslProperFunction {A : Sort u} {B : Sort v}
    (RA : A -> A -> Prop) (f : A -> B)
    (RB : outParam (B -> B -> Prop)) : Prop where
  proper : forall x y, RA x y -> RB (f x) (f y)

set_option synthInstance.checkSynthOrder false in
instance unifyslProperFunction_of_proper
    {A : Sort u} {B : Sort v} {RA : A -> A -> Prop} {RB : B -> B -> Prop}
    (f : A -> B)
    [h : Unifysl.Relation_ext.Proper
      (Unifysl.Relation_ext.respectful RA RB) f] :
    UnifyslProperFunction RA f RB where
  proper := h.proper

set_option synthInstance.checkSynthOrder false in
instance (priority := low) unifyslProperFunction_apply
    {A : Sort u} {B : Sort v} {C : Sort w}
    {RA : A -> A -> Prop} {RB : B -> B -> Prop} {RC : C -> C -> Prop}
    (f : A -> B -> C) (x : A)
    [h : UnifyslProperFunction RA f
      (Unifysl.Relation_ext.respectful RB RC)]
    [hr : AUXLib.Reflexive RA] :
    UnifyslProperFunction RB (f x) RC where
  proper := h.proper x x (hr.refl x)

set_option synthInstance.checkSynthOrder false in
instance auxProperFunction_of_unifyslProperFunction
    {A : Sort u} {B : Sort v} {RA : A -> A -> Prop} {RB : B -> B -> Prop}
    (f : A -> B) [h : UnifyslProperFunction RA f RB] :
    AUXLib.ProperFunction RA f RB where
  proper := h.proper

set_option synthInstance.checkSynthOrder false in
instance auxFlippedProperFunction_of_unifyslProperFunction
    {A : Sort u} {B : Sort v} {RA : A -> A -> Prop} {RB : B -> B -> Prop}
    (f : A -> B) [h : UnifyslProperFunction (Unifysl.flipRel RA) f RB] :
    AUXLib.ProperFunction (AUXLib.flipRel RA) f RB where
  proper := h.proper

set_option synthInstance.checkSynthOrder false in
instance (priority := low) auxFlipBothProperFunction_of_unifyslProperFunction
    {A : Sort u} {B : Sort v} {RA : A -> A -> Prop} {RB : B -> B -> Prop}
    (f : A -> B) [h : UnifyslProperFunction RA f RB] :
    AUXLib.ProperFunction (AUXLib.flipRel RA) f (AUXLib.flipRel RB) where
  proper x y hxy := h.proper y x hxy

set_option synthInstance.checkSynthOrder false in
instance (priority := low) auxFlipBinaryProperFunction_of_unifyslProperFunction
    {A : Sort u} {B : Sort v} {C : Sort w}
    {RA : A -> A -> Prop} {RB : B -> B -> Prop} {RC : C -> C -> Prop}
    (f : A -> B -> C)
    [h : UnifyslProperFunction RA f
      (Unifysl.Relation_ext.respectful RB RC)] :
    AUXLib.ProperFunction (AUXLib.flipRel RA) f
      (AUXLib.respectful (AUXLib.flipRel RB) (AUXLib.flipRel RC)) where
  proper x y hxy x' y' hxy' := h.proper y x hxy y' x' hxy'

def auxProperOfUnifyslProper
    {A : Sort u} {R : A -> A -> Prop} {x : A}
    (h : Unifysl.Relation_ext.Proper R x) : AUXLib.Proper R x where
  proper := h.proper

instance (priority := low) auxUnifyslFlipReflexive
    {A : Sort u} {R : A -> A -> Prop} [h : AUXLib.Reflexive R] :
    AUXLib.Reflexive (Unifysl.flipRel R) where
  refl := h.refl

instance auxDerivable1Reflexive
    {L : Unifysl.Language.{u}} [Gamma : Unifysl.Derivable1 L]
    [BD : Unifysl.BasicDeduction L Gamma] :
    AUXLib.Reflexive (Unifysl.derivable1 (L := L)) where
  refl := Unifysl.derivable1_refl

instance auxLogicEquivReflexive
    {L : Unifysl.Language.{u}} [Gamma : Unifysl.LogicEquiv L]
    [BE : Unifysl.BasicLogicEquiv L Gamma] :
    AUXLib.Reflexive (Unifysl.logic_equiv (L := L)) where
  refl := Unifysl.logic_equiv_refl

instance unifyslImplRelForwardTransport :
    AUXLib.ForwardTransport Unifysl.implRel where
  transport h := h

instance unifyslImplRelReflexive : AUXLib.Reflexive Unifysl.implRel where
  refl _ h := h

private theorem exp_mono
    {L : Unifysl.Language.{u}} [Unifysl.ShallowExistsLanguage L]
    [GammaD : Unifysl.Derivable1 L] [Unifysl.BasicDeduction L GammaD]
    [Unifysl.ShallowExistsDeduction L GammaD]
    {A : Type v} {P Q : A -> @Unifysl.Language.expr L}
    (hPQ : forall x, Unifysl.derivable1 (L := L) (P x) (Q x)) :
    Unifysl.derivable1 (L := L) (Unifysl.exp P) (Unifysl.exp Q) := by
  apply Unifysl.derivable1s_exp_l
  intro x
  exact Unifysl.derivable1_trans (P x) (Q x) (Unifysl.exp Q)
    (hPQ x)
    (Unifysl.derivable1s_exp_r (Q x) Q x (Unifysl.derivable1_refl (Q x)))

private theorem allp_mono
    {L : Unifysl.Language.{u}} [Unifysl.ShallowForallLanguage L]
    [GammaD : Unifysl.Derivable1 L] [Unifysl.BasicDeduction L GammaD]
    [Unifysl.ShallowForallDeduction L GammaD]
    {A : Type v} {P Q : A -> @Unifysl.Language.expr L}
    (hPQ : forall x, Unifysl.derivable1 (L := L) (P x) (Q x)) :
    Unifysl.derivable1 (L := L) (Unifysl.allp P) (Unifysl.allp Q) := by
  apply Unifysl.derivable1s_allp_r
  intro x
  exact Unifysl.derivable1_trans (Unifysl.allp P) (P x) (Q x)
    (Unifysl.derivable1s_allp_l P (P x) x (Unifysl.derivable1_refl (P x)))
    (hPQ x)

instance auxExpProperDerivable1
    {L : Unifysl.Language.{u}} [Unifysl.ShallowExistsLanguage L]
    [GammaD : Unifysl.Derivable1 L] [Unifysl.BasicDeduction L GammaD]
    [Unifysl.ShallowExistsDeduction L GammaD]
    (A : Type v) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A (Unifysl.derivable1 (L := L)))
      (@Unifysl.exp L _ A) (Unifysl.derivable1 (L := L)) where
  proper _ _ hPQ := exp_mono hPQ

instance auxAllpProperDerivable1
    {L : Unifysl.Language.{u}} [Unifysl.ShallowForallLanguage L]
    [GammaD : Unifysl.Derivable1 L] [Unifysl.BasicDeduction L GammaD]
    [Unifysl.ShallowForallDeduction L GammaD]
    (A : Type v) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A (Unifysl.derivable1 (L := L)))
      (@Unifysl.allp L _ A) (Unifysl.derivable1 (L := L)) where
  proper _ _ hPQ := allp_mono hPQ

instance auxExpProperLogicEquiv
    {L : Unifysl.Language.{u}} [Unifysl.ShallowExistsLanguage L]
    [GammaD : Unifysl.Derivable1 L] [Unifysl.BasicDeduction L GammaD]
    [Unifysl.ShallowExistsDeduction L GammaD]
    [GammaE : Unifysl.LogicEquiv L]
    [Unifysl.EquivDerivable1 L GammaD GammaE]
    (A : Type v) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A (Unifysl.logic_equiv (L := L)))
      (@Unifysl.exp L _ A) (Unifysl.logic_equiv (L := L)) where
  proper P Q hPQ := by
    apply (Unifysl.__logic_equiv_derivable1 (Unifysl.exp P) (Unifysl.exp Q)).mpr
    constructor
    · apply exp_mono
      intro x
      exact ((Unifysl.__logic_equiv_derivable1 (P x) (Q x)).mp (hPQ x)).left
    · apply exp_mono
      intro x
      exact ((Unifysl.__logic_equiv_derivable1 (P x) (Q x)).mp (hPQ x)).right

instance auxAllpProperLogicEquiv
    {L : Unifysl.Language.{u}} [Unifysl.ShallowForallLanguage L]
    [GammaD : Unifysl.Derivable1 L] [Unifysl.BasicDeduction L GammaD]
    [Unifysl.ShallowForallDeduction L GammaD]
    [GammaE : Unifysl.LogicEquiv L]
    [Unifysl.EquivDerivable1 L GammaD GammaE]
    (A : Type v) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A (Unifysl.logic_equiv (L := L)))
      (@Unifysl.allp L _ A) (Unifysl.logic_equiv (L := L)) where
  proper P Q hPQ := by
    apply (Unifysl.__logic_equiv_derivable1 (Unifysl.allp P) (Unifysl.allp Q)).mpr
    constructor
    · apply allp_mono
      intro x
      exact ((Unifysl.__logic_equiv_derivable1 (P x) (Q x)).mp (hPQ x)).left
    · apply allp_mono
      intro x
      exact ((Unifysl.__logic_equiv_derivable1 (P x) (Q x)).mp (hPQ x)).right

open Unifysl.LogicGenerator.demo932

instance facadeDerivable1Reflexive (ctx : Facade.Context.{u, v}) :
    AUXLib.Reflexive ctx.derivable1 where
  refl := ctx.derivable1_refl

instance facadeLogicEquivReflexive (ctx : Facade.Context.{u, v}) :
    AUXLib.Reflexive ctx.logic_equiv where
  refl := ctx.logic_equiv_refl

instance facadeDerivable1Proper (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.flipRel ctx.derivable1)
        (AUXLib.respectful ctx.derivable1 Unifysl.implRel))
      ctx.derivable1 where
  proper := ctx.Theorems.derivable1_proper_derivable1_inst.proper

instance facadeDerivable1ProperLogicEquiv (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.flipRel ctx.logic_equiv)
        (AUXLib.respectful ctx.logic_equiv Unifysl.implRel))
      ctx.derivable1 where
  proper x x' hx y y' hy hxy :=
    ctx.derivable1_trans x' x y'
      hx.left
      (ctx.derivable1_trans x y y' hxy hy.left)

-- Rewriting a proposition-valued entailment target needs transport in both
-- directions.  The one-way `implRel` instance above remains available for
-- Coq-style `Proper` inference; this stronger result is selected when the
-- output relation is inferred by `rel_rw`.
instance (priority := high) facadeDerivable1ProperLogicEquivIff
    (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.flipRel ctx.logic_equiv)
        (AUXLib.respectful ctx.logic_equiv Iff))
      ctx.derivable1 where
  proper x x' hx y y' hy := by
    constructor
    · intro hxy
      exact ctx.derivable1_trans x' x y'
        hx.left
        (ctx.derivable1_trans x y y' hxy hy.left)
    · intro hx'y'
      exact ctx.derivable1_trans x x' y
        hx.right
        (ctx.derivable1_trans x' y' y hx'y' hy.right)

instance facadeLogicEquivProper (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful ctx.logic_equiv
        (AUXLib.respectful ctx.logic_equiv Unifysl.implRel))
      ctx.logic_equiv where
  proper := ctx.Theorems.logic_equiv_proper_logic_equiv_inst.proper

instance (priority := high) facadeSepconProperDerivable1
    (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful ctx.derivable1
        (AUXLib.respectful ctx.derivable1 ctx.derivable1))
      ctx.sepcon where
  proper := ctx.derivable1s_sepcon_proper.proper

instance (priority := high) facadeAndpProperDerivable1
    (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful ctx.derivable1
        (AUXLib.respectful ctx.derivable1 ctx.derivable1))
      ctx.andp where
  proper := ctx.derivable1s_andp_proper.proper

instance (priority := high) facadeOrpProperDerivable1
    (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful ctx.derivable1
        (AUXLib.respectful ctx.derivable1 ctx.derivable1))
      ctx.orp where
  proper := ctx.derivable1s_orp_proper.proper

instance (priority := high) facadeLogicEquivProperIff
    (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful ctx.logic_equiv
        (AUXLib.respectful ctx.logic_equiv Iff))
      ctx.logic_equiv where
  proper x x' hx y y' hy := by
    constructor
    · intro hxy
      exact ctx.logic_equiv_trans x' x y'
        (ctx.logic_equiv_symm x x' hx)
        (ctx.logic_equiv_trans x y y' hxy hy)
    · intro hx'y'
      exact ctx.logic_equiv_trans x x' y
        hx
        (ctx.logic_equiv_trans x' y' y hx'y'
          (ctx.logic_equiv_symm y y' hy))

instance facadeSepconProperFlippedLogicEquiv (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.flipRel ctx.logic_equiv)
        (AUXLib.respectful (AUXLib.flipRel ctx.logic_equiv)
          (AUXLib.flipRel ctx.logic_equiv)))
      ctx.sepcon where
  proper x x' hx y y' hy :=
    ctx.logic_equiv_sepcon_proper.proper x' x hx y' y hy

instance facadeAndpProperFlippedLogicEquiv (ctx : Facade.Context.{u, v}) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.flipRel ctx.logic_equiv)
        (AUXLib.respectful (AUXLib.flipRel ctx.logic_equiv)
          (AUXLib.flipRel ctx.logic_equiv)))
      ctx.andp where
  proper x x' hx y y' hy :=
    ctx.logic_equiv_andp_proper.proper x' x hx y' y hy

instance facadeExpProperDerivable1 (ctx : Facade.Context.{u, v}) (A : Type v) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.pointwise_relation A ctx.derivable1) ctx.derivable1)
      (ctx.exp A) where
  proper _ _ hPQ := by
    intro m hP
    rcases hP with ⟨x, hx⟩
    exact ⟨x, hPQ x m hx⟩

instance facadeAllpProperDerivable1 (ctx : Facade.Context.{u, v}) (A : Type v) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.pointwise_relation A ctx.derivable1) ctx.derivable1)
      (ctx.allp A) where
  proper _ _ hPQ m hP x := hPQ x m (hP x)

instance facadeExpProperLogicEquiv (ctx : Facade.Context.{u, v}) (A : Type v) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.pointwise_relation A ctx.logic_equiv) ctx.logic_equiv)
      (ctx.exp A) where
  proper _ _ hPQ := by
    constructor
    · intro m hP
      rcases hP with ⟨x, hx⟩
      exact ⟨x, (hPQ x).left m hx⟩
    · intro m hP
      rcases hP with ⟨x, hx⟩
      exact ⟨x, (hPQ x).right m hx⟩

instance facadeAllpProperLogicEquiv (ctx : Facade.Context.{u, v}) (A : Type v) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.pointwise_relation A ctx.logic_equiv) ctx.logic_equiv)
      (ctx.allp A) where
  proper _ _ hPQ := by
    constructor
    · intro m hP x
      exact (hPQ x).left m (hP x)
    · intro m hP x
      exact (hPQ x).right m (hP x)

end SimpleC.SL.UnifyslBridge
