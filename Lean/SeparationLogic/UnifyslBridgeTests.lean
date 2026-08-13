import SimpleC.SL.UnifyslBridge

namespace UnifyslBridgeTests

open Unifysl

instance natLeRight_unifysl_congr (k : Nat) :
    Relation_ext.Proper
      (Relation_ext.respectful Nat.le implRel)
      (Nat.le k) where
  proper := by
    intro a b hab hka
    exact Nat.le_trans hka hab

instance : AUXLib.Reflexive Nat.le where
  refl := Nat.le_refl

example (k : Nat) :
    AUXLib.Proper
      (Relation_ext.respectful Nat.le implRel)
      (Nat.le k) :=
  SimpleC.SL.UnifyslBridge.auxProperOfUnifyslProper inferInstance

example (k : Nat) :
    AUXLib.ProperFunction Nat.le (Nat.le k) implRel := inferInstance

example : AUXLib.ForwardTransport implRel := inferInstance

example {L : Language} [Gamma : Derivable1 L] [BD : BasicDeduction L Gamma] :
    AUXLib.ProperFunction
      (AUXLib.flipRel (derivable1 (L := L)))
      (derivable1 (L := L))
      (Relation_ext.respectful (derivable1 (L := L)) implRel) := inferInstance

example {L : Language} [Gamma : LogicEquiv L] [BE : BasicLogicEquiv L Gamma]
    (x : @Language.expr L) :
    AUXLib.ProperFunction
      (logic_equiv (L := L))
      (logic_equiv (L := L) x)
      implRel := inferInstance

example {L : Language} [Gamma : Derivable1 L] [_BD : BasicDeduction L Gamma]
    (x1 x2 y1 y2 : @Language.expr L)
    (hx : derivable1 (L := L) x1 x2)
    (hy : derivable1 (L := L) y1 y2)
    (hmid : derivable1 (L := L) x2 y1) :
    derivable1 (L := L) x1 y2 := by
  rel_rw [← hy]
  rel_rw [← hmid]
  exact hx

example {L : Language} [Gamma : Derivable1 L] [_BD : BasicDeduction L Gamma]
    (x1 x2 y : @Language.expr L)
    (hx : derivable1 (L := L) x1 x2)
    (hmid : derivable1 (L := L) x2 y) :
    derivable1 (L := L) x1 y := by
  rel_rw [hx]
  exact hmid

example {L : Language} [Gamma : Derivable1 L] [_BD : BasicDeduction L Gamma]
    (x1 x2 y : @Language.expr L)
    (_hx : derivable1 (L := L) x1 x2)
    (_hleft : derivable1 (L := L) x1 y) : True := by
  fail_if_success rel_rw [_hx] at _hleft
  trivial

example {L : Language} [Gamma : Derivable1 L] [BD : BasicDeduction L Gamma]
    (x1 x2 y : @Language.expr L)
    (hx : derivable1 (L := L) x1 x2)
    (hmid : derivable1 (L := L) x2 y) :
    derivable1 (L := L) x1 y := by
  rel_rw [← hx] at hmid
  exact hmid

example {L : Language} [ShallowExistsLanguage L]
    [Gamma : Derivable1 L] [BasicDeduction L Gamma]
    [ShallowExistsDeduction L Gamma] (A : Type) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A (derivable1 (L := L)))
      (@exp L _ A) (derivable1 (L := L)) := inferInstance

example {L : Language} [ShallowForallLanguage L]
    [Gamma : Derivable1 L] [BasicDeduction L Gamma]
    [ShallowForallDeduction L Gamma] (A : Type) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A (derivable1 (L := L)))
      (@allp L _ A) (derivable1 (L := L)) := inferInstance

example {L : Language} [ShallowExistsLanguage L]
    [Gamma : Derivable1 L] [BasicDeduction L Gamma]
    [ShallowExistsDeduction L Gamma]
    {A : Type} (P Q : @Language.expr L)
    (h : derivable1 (L := L) P Q) :
    derivable1 (L := L) (exp (fun _ : A => P)) (exp (fun _ : A => Q)) := by
  rel_rw [h]
  exact derivable1_refl (exp (fun _ : A => Q))

example {L : Language} [ShallowForallLanguage L]
    [Gamma : Derivable1 L] [BasicDeduction L Gamma]
    [ShallowForallDeduction L Gamma]
    {A : Type} (P Q : @Language.expr L)
    (h : derivable1 (L := L) P Q) :
    derivable1 (L := L) (allp (fun _ : A => P)) (allp (fun _ : A => Q)) := by
  rel_rw [h]
  exact derivable1_refl (allp (fun _ : A => Q))

example {L : Language} [ShallowExistsLanguage L] [ShallowForallLanguage L]
    [Gamma : Derivable1 L] [BasicDeduction L Gamma]
    [ShallowExistsDeduction L Gamma] [ShallowForallDeduction L Gamma]
    {A B : Type} (P Q : A -> B -> @Language.expr L)
    (h : forall x y, derivable1 (L := L) (P x y) (Q x y)) :
    derivable1 (L := L)
      (exp (fun x => allp (fun y => P x y)))
      (exp (fun x => allp (fun y => Q x y))) := by
  rel_rw [h]
  exact derivable1_refl (exp (fun x => allp (fun y => Q x y)))

example {L : Language} [ShallowExistsLanguage L]
    [GammaD : Derivable1 L] [BasicDeduction L GammaD]
    [ShallowExistsDeduction L GammaD]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD GammaE]
    (A : Type) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A (logic_equiv (L := L)))
      (@exp L _ A) (logic_equiv (L := L)) := inferInstance

example {L : Language} [ShallowExistsLanguage L]
    [GammaD : Derivable1 L] [BasicDeduction L GammaD]
    [ShallowExistsDeduction L GammaD]
    [GammaE : LogicEquiv L] [BasicLogicEquiv L GammaE]
    [EquivDerivable1 L GammaD GammaE]
    {A : Type} (P Q : @Language.expr L)
    (h : logic_equiv (L := L) P Q) :
    logic_equiv (L := L)
      (exp (fun _ : A => P)) (exp (fun _ : A => Q)) := by
  rel_rw [← h]
  exact logic_equiv_refl (exp (fun _ : A => P))

example {A : Type} (P Q : A -> Prop)
    (h : forall x, implRel (P x) (Q x)) :
    (forall x, P x) -> forall x, Q x := by
  rel_rw [h]
  exact fun hQ => hQ

open LogicGenerator.demo932

example (ctx : Facade.Context.{0, 0}) (A : Type) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A ctx.derivable1)
      (ctx.exp A) ctx.derivable1 := inferInstance

example (ctx : Facade.Context.{0, 0}) (A : Type) :
    AUXLib.ProperFunction
      (AUXLib.pointwise_relation A ctx.logic_equiv)
      (ctx.allp A) ctx.logic_equiv := inferInstance

-- Keep the source one-way Proper relations selectable alongside the Iff adapters.
example (ctx : Facade.Context.{0, 0}) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.flipRel ctx.logic_equiv)
        (AUXLib.respectful ctx.logic_equiv Unifysl.implRel))
      ctx.derivable1 := inferInstance

example (ctx : Facade.Context.{0, 0}) :
    AUXLib.Proper
      (AUXLib.respectful ctx.logic_equiv
        (AUXLib.respectful ctx.logic_equiv Unifysl.implRel))
      ctx.logic_equiv := inferInstance

example (ctx : Facade.Context.{0, 0}) :
    AUXLib.Proper
      (AUXLib.respectful (AUXLib.flipRel ctx.logic_equiv)
        (AUXLib.respectful ctx.logic_equiv Iff))
      ctx.derivable1 := inferInstance

example (ctx : Facade.Context.{0, 0}) :
    AUXLib.Proper
      (AUXLib.respectful ctx.logic_equiv
        (AUXLib.respectful ctx.logic_equiv Iff))
      ctx.logic_equiv := inferInstance

example (ctx : Facade.Context.{0, 0}) (P Q R : ctx.expr)
    (hQR : ctx.logic_equiv Q R) (hPR : ctx.derivable1 P R) :
    ctx.derivable1 P Q := by
  rel_rw [hQR]
  exact hPR

example (ctx : Facade.Context.{0, 0}) {A : Type} (P Q : ctx.expr)
    (h : ctx.derivable1 P Q) :
    ctx.derivable1 (ctx.exp A (fun _ => P)) (ctx.exp A (fun _ => Q)) := by
  rel_rw [h]
  exact ctx.derivable1_refl (ctx.exp A (fun _ => Q))

example (ctx : Facade.Context.{0, 0})
    (P Q R S T : ctx.expr) (hPQ : ctx.logic_equiv P Q)
    (h : ctx.derivable1 (ctx.sepcon (ctx.andp Q R) S) T) :
    ctx.derivable1 (ctx.sepcon (ctx.andp P R) S) T := by
  rel_rw [hPQ]
  exact h

end UnifyslBridgeTests
