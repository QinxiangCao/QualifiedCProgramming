import AUXLib.Morphisms

universe u v

namespace FP

open AUXLib

def lift_fun0 {A : Type u} {B : Type v} (f : B) : A -> B := fun _ => f

def lift_fun1 {A : Type u} {B : Type v} (f : B -> B) :
    (A -> B) -> A -> B := fun g a => f (g a)

def lift_fun2 {A : Type u} {B : Type v} (f : B -> B -> B) :
    (A -> B) -> (A -> B) -> A -> B := fun g h a => f (g a) (h a)

def lift_binder {A : Type u} {B : Type v} (f : (Nat -> B) -> B) :
    (Nat -> A -> B) -> A -> B := fun g a => f (fun n => g n a)

def lift_rel1 {A : Type u} {B : Type v} (P : B -> Prop) :
    (A -> B) -> Prop := fun f => forall a, P (f a)

def lift_rel2 {A : Type u} {B : Type v} (P : B -> B -> Prop) :
    (A -> B) -> (A -> B) -> Prop := fun f g => forall a, P (f a) (g a)

def lift_set_summary {A : Type u} {B : Type v} (F : (B -> Prop) -> B) :
    ((A -> B) -> Prop) -> A -> B :=
  fun P a => F (fun b => exists f, P f /\ f a = b)

theorem lift_fun2_proper {A : Type u} (f : A -> A -> A)
    (R1 R2 R3 : A -> A -> Prop)
    [hf : Proper (R1 ==> R2 ==> R3) f] {B : Type v} :
    Proper (lift_rel2 R1 ==> lift_rel2 R2 ==> lift_rel2 R3)
      (@lift_fun2 B A f) where
  proper x x' hx y y' hy b := hf.proper _ _ (hx b) _ _ (hy b)

end FP

export FP (lift_fun0 lift_fun1 lift_fun2 lift_binder lift_rel1 lift_rel2
  lift_set_summary lift_fun2_proper)
