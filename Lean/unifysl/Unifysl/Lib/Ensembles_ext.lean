import Unifysl.Lib.Relation_ext

universe u v

namespace Unifysl

open Relation_ext

abbrev Ensemble (A : Type u) : Type u :=
  A -> Prop

def In (A : Type u) (P : Ensemble A) (x : A) : Prop :=
  P x

def Full_set (A : Type u) : Ensemble A :=
  fun _ => True

def Empty_set (A : Type u) : Ensemble A :=
  fun _ => False

def Included (A : Type u) (B C : Ensemble A) : Prop :=
  forall x, In A B x -> In A C x

def Same_set (A : Type u) (B C : Ensemble A) : Prop :=
  Included A B C /\ Included A C B

def Intersection (A : Type u) (B C : Ensemble A) : Ensemble A :=
  fun x => B x /\ C x

def Union (A : Type u) (B C : Ensemble A) : Ensemble A :=
  fun x => B x \/ C x

def Complement (A : Type u) (B : Ensemble A) : Ensemble A :=
  fun x => ¬ B x

def Singleton (A : Type u) (x : A) : Ensemble A :=
  fun y => x = y

def Disjoint (A : Type u) (B C : Ensemble A) : Prop :=
  forall x, B x -> C x -> False

theorem Full_intro (A : Type u) (x : A) : In A (Full_set A) x := by
  trivial

theorem In_singleton (A : Type u) (x : A) : In A (Singleton A x) x := by
  rfl

theorem Union_introl (A : Type u) (B C : Ensemble A) (x : A) :
    In A B x -> In A (Union A B C) x :=
  Or.inl

theorem Union_intror (A : Type u) (B C : Ensemble A) (x : A) :
    In A C x -> In A (Union A B C) x :=
  Or.inr

theorem Intersection_intro (A : Type u) (B C : Ensemble A) (x : A) :
    In A B x -> In A C x -> In A (Intersection A B C) x := by
  intro hB hC
  exact ⟨hB, hC⟩

theorem Complement_intro (A : Type u) (B : Ensemble A) (x : A) :
    (¬ In A B x) -> In A (Complement A B) x :=
  id

theorem Disjoint_intro (A : Type u) (B C : Ensemble A) :
    (forall x, ¬ (In A B x /\ In A C x)) -> Disjoint A B C := by
  intro h x hB hC
  exact h x ⟨hB, hC⟩

theorem Full_set_spec : forall (A : Type u) (v : A), Full_set A v <-> True := by
  intro A v
  rfl

theorem Empty_set_spec : forall (A : Type u) (v : A), Empty_set A v <-> False := by
  intro A v
  rfl

theorem Intersection_spec :
    forall (A : Type u) (v : A) (P Q : Ensemble A),
      Intersection A P Q v <-> P v /\ Q v := by
  intro A v P Q
  rfl

theorem Union_spec :
    forall (A : Type u) (v : A) (P Q : Ensemble A),
      Union A P Q v <-> P v \/ Q v := by
  intro A v P Q
  rfl

theorem Disjoint_spec :
    forall (A : Type u) (P Q : Ensemble A),
      Disjoint A P Q <-> (forall x, P x -> Q x -> False) := by
  intro A P Q
  rfl

theorem Singleton_spec :
    forall (U : Type u) (x y : U), Singleton U x y <-> x = y := by
  intro U x y
  rfl

theorem Included_Full_set :
    forall (A : Type u) (P : Ensemble A), Included A P (Full_set A) := by
  intro A P x hx
  trivial

theorem Intersection_Complement :
    forall (A : Type u) (P Q : Ensemble A),
      Same_set A
        (Intersection A (Complement A P) (Complement A Q))
        (Complement A (Union A P Q)) := by
  intro A P Q
  constructor
  · intro x hx hUnion
    cases hUnion with
    | inl hp => exact hx.left hp
    | inr hq => exact hx.right hq
  · intro x hx
    constructor
    · intro hp
      exact hx (Or.inl hp)
    · intro hq
      exact hx (Or.inr hq)

theorem Union_iff :
    forall (U : Type u) (A B : Ensemble U) (x : U),
      In U (Union U A B) x <-> In U A x \/ In U B x := by
  intro U A B x
  rfl

theorem Empty_set_iff :
    forall (U : Type u) (x : U), In U (Empty_set U) x <-> False := by
  intro U x
  rfl

theorem Singleton_iff :
    forall (U : Type u) (x y : U), In U (Singleton U x) y <-> x = y := by
  intro U x y
  rfl

theorem Same_set_refl :
    forall (A : Type u) (S : Ensemble A), Same_set A S S := by
  intro A S
  constructor <;> intro x hx <;> exact hx

theorem Same_set_sym :
    forall (A : Type u) (S1 S2 : Ensemble A),
      Same_set A S1 S2 -> Same_set A S2 S1 := by
  intro A S1 S2 h
  exact ⟨h.right, h.left⟩

theorem Same_set_trans :
    forall (A : Type u) (S1 S2 S3 : Ensemble A),
      Same_set A S1 S2 -> Same_set A S2 S3 -> Same_set A S1 S3 := by
  intro A S1 S2 S3 h12 h23
  constructor
  · intro x hx
    exact h23.left x (h12.left x hx)
  · intro x hx
    exact h12.right x (h23.right x hx)

instance Same_set_rel {A : Type u} : Equivalence (Same_set A) where
  refl := Same_set_refl A
  symm := by
    intro S1 S2 h
    exact Same_set_sym A S1 S2 h
  trans := by
    intro S1 S2 S3 h12 h23
    exact Same_set_trans A S1 S2 S3 h12 h23

theorem Same_set_spec :
    forall (A : Type u) (P Q : Ensemble A),
      Same_set A P Q <-> pointwise_relation A Iff P Q := by
  intro A P Q
  constructor
  · intro h x
    exact ⟨h.left x, h.right x⟩
  · intro h
    constructor
    · intro x hx
      exact (h x).mp hx
    · intro x hx
      exact (h x).mpr hx

theorem Complement_Empty_set :
    forall (A : Type u), Same_set A (Complement A (Empty_set A)) (Full_set A) := by
  intro A
  constructor
  · intro x hx
    trivial
  · intro x hx hEmpty
    exact hEmpty

theorem Intersection_comm :
    forall (A : Type u) (P Q : Ensemble A),
      Same_set A (Intersection A P Q) (Intersection A Q P) := by
  intro A P Q
  constructor
  · intro x hx
    exact ⟨hx.right, hx.left⟩
  · intro x hx
    exact ⟨hx.right, hx.left⟩

theorem Intersection_assoc :
    forall (A : Type u) (P Q R : Ensemble A),
      Same_set A
        (Intersection A (Intersection A P Q) R)
        (Intersection A P (Intersection A Q R)) := by
  intro A P Q R
  constructor
  · intro x hx
    exact ⟨hx.left.left, hx.left.right, hx.right⟩
  · intro x hx
    exact ⟨⟨hx.left, hx.right.left⟩, hx.right.right⟩

theorem Union_comm :
    forall (A : Type u) (P Q : Ensemble A),
      Same_set A (Union A P Q) (Union A Q P) := by
  intro A P Q
  constructor
  · intro x hx
    exact hx.symm
  · intro x hx
    exact hx.symm

theorem Union_assoc :
    forall (A : Type u) (P Q R : Ensemble A),
      Same_set A
        (Union A (Union A P Q) R)
        (Union A P (Union A Q R)) := by
  intro A P Q R
  constructor
  · intro x hx
    cases hx with
    | inl hpq =>
        cases hpq with
        | inl hp => exact Or.inl hp
        | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  · intro x hx
    cases hx with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
        cases hqr with
        | inl hq => exact Or.inl (Or.inr hq)
        | inr hr => exact Or.inr hr

theorem Intersection_Union_distr_l :
    forall (A : Type u) (P Q R : Ensemble A),
      Same_set A
        (Intersection A (Union A Q R) P)
        (Union A (Intersection A Q P) (Intersection A R P)) := by
  intro A P Q R
  constructor
  · intro x hx
    cases hx.left with
    | inl hq => exact Or.inl ⟨hq, hx.right⟩
    | inr hr => exact Or.inr ⟨hr, hx.right⟩
  · intro x hx
    cases hx with
    | inl hqp => exact ⟨Or.inl hqp.left, hqp.right⟩
    | inr hrp => exact ⟨Or.inr hrp.left, hrp.right⟩

theorem Intersection_Union_distr_r :
    forall (A : Type u) (P Q R : Ensemble A),
      Same_set A
        (Intersection A P (Union A Q R))
        (Union A (Intersection A P Q) (Intersection A P R)) := by
  intro A P Q R
  constructor
  · intro x hx
    cases hx.right with
    | inl hq => exact Or.inl ⟨hx.left, hq⟩
    | inr hr => exact Or.inr ⟨hx.left, hr⟩
  · intro x hx
    cases hx with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

instance Included_proper (V : Type u) :
    Proper (Same_set V ==> Same_set V ==> Iff) (Included V) where
  proper := by
    intro P1 P2 hP Q1 Q2 hQ
    constructor
    · intro h x hx
      exact hQ.left x (h x (hP.right x hx))
    · intro h x hx
      exact hQ.right x (h x (hP.left x hx))

instance complement_proper (V : Type u) :
    Proper (Same_set V ==> Same_set V) (Complement V) where
  proper := by
    intro P Q h
    constructor
    · intro x hx hq
      exact hx (h.right x hq)
    · intro x hx hp
      exact hx (h.left x hp)

instance Union_proper (V : Type u) :
    Proper (Same_set V ==> Same_set V ==> Same_set V) (Union V) where
  proper := by
    intro P1 P2 hP Q1 Q2 hQ
    constructor
    · intro x hx
      cases hx with
      | inl hp => exact Or.inl (hP.left x hp)
      | inr hq => exact Or.inr (hQ.left x hq)
    · intro x hx
      cases hx with
      | inl hp => exact Or.inl (hP.right x hp)
      | inr hq => exact Or.inr (hQ.right x hq)

instance Disjoint_proper (V : Type u) :
    Proper (Same_set V ==> Same_set V ==> Iff) (Disjoint V) where
  proper := by
    intro P1 P2 hP Q1 Q2 hQ
    constructor
    · intro h x hp hq
      exact h x (hP.right x hp) (hQ.right x hq)
    · intro h x hp hq
      exact h x (hP.left x hp) (hQ.left x hq)

theorem Union_Included {A : Type u} :
    forall (P Q R : Ensemble A),
      Included A (Union A P Q) R <-> Included A P R /\ Included A Q R := by
  intro P Q R
  constructor
  · intro h
    constructor
    · intro x hp
      exact h x (Or.inl hp)
    · intro x hq
      exact h x (Or.inr hq)
  · intro h x hx
    cases hx with
    | inl hp => exact h.left x hp
    | inr hq => exact h.right x hq

theorem left_Included_Union {A : Type u} :
    forall (P Q : Ensemble A), Included A P (Union A P Q) := by
  intro P Q x hp
  exact Or.inl hp

theorem right_Included_Union {A : Type u} :
    forall (P Q : Ensemble A), Included A Q (Union A P Q) := by
  intro P Q x hq
  exact Or.inr hq

theorem Union_Empty_left {A : Type u} :
    forall (P : Ensemble A), Same_set A (Union A (Empty_set A) P) P := by
  intro P
  constructor
  · intro x hx
    cases hx with
    | inl hEmpty => cases hEmpty
    | inr hp => exact hp
  · intro x hp
    exact Or.inr hp

theorem Union_Empty_right {A : Type u} :
    forall (P : Ensemble A), Same_set A (Union A P (Empty_set A)) P := by
  intro P
  constructor
  · intro x hx
    cases hx with
    | inl hp => exact hp
    | inr hEmpty => cases hEmpty
  · intro x hp
    exact Or.inl hp

theorem Intersection_Full_left {A : Type u} :
    forall (P : Ensemble A), Same_set A (Intersection A (Full_set A) P) P := by
  intro P
  constructor
  · intro x hx
    exact hx.right
  · intro x hp
    exact ⟨True.intro, hp⟩

theorem Intersection_Full_right {A : Type u} :
    forall (P : Ensemble A), Same_set A (Intersection A P (Full_set A)) P := by
  intro P
  constructor
  · intro x hx
    exact hx.left
  · intro x hp
    exact ⟨hp, True.intro⟩

theorem Intersection_Empty_left {A : Type u} :
    forall (P : Ensemble A),
      Same_set A (Intersection A (Empty_set A) P) (Empty_set A) := by
  intro P
  constructor
  · intro x hx
    exact hx.left
  · intro x hEmpty
    cases hEmpty

theorem Intersection_Empty_right {A : Type u} :
    forall (P : Ensemble A),
      Same_set A (Intersection A P (Empty_set A)) (Empty_set A) := by
  intro P
  constructor
  · intro x hx
    exact hx.right
  · intro x hEmpty
    cases hEmpty

theorem Intersection_absort_right :
    forall (U : Type u) (A B : Ensemble U),
      Included U A B -> Same_set U (Intersection U A B) A := by
  intro U A B h
  constructor
  · intro x hx
    exact hx.left
  · intro x hx
    exact ⟨hx, h x hx⟩

theorem Intersection_absort_left :
    forall (U : Type u) (A B : Ensemble U),
      Included U B A -> Same_set U (Intersection U A B) B := by
  intro U A B h
  constructor
  · intro x hx
    exact hx.right
  · intro x hx
    exact ⟨h x hx, hx⟩

theorem Complement_Included_rev :
    forall (U : Type u) (P Q : Ensemble U),
      Included U P Q -> Included U (Complement U Q) (Complement U P) := by
  intro U P Q h x hx hp
  exact hx (h x hp)

instance Intersection_proper {A : Type u} :
    Proper (Same_set A ==> Same_set A ==> Same_set A) (Intersection A) where
  proper := by
    intro P1 P2 hP Q1 Q2 hQ
    constructor
    · intro x hx
      exact ⟨hP.left x hx.left, hQ.left x hx.right⟩
    · intro x hx
      exact ⟨hP.right x hx.left, hQ.right x hx.right⟩

theorem Included_Disjoint :
    forall (A : Type u) (P Q P' Q' : Ensemble A),
      Included A P P' ->
      Included A Q Q' ->
      Disjoint A P' Q' ->
      Disjoint A P Q := by
  intro A P Q P' Q' hP hQ hD x hp hq
  exact hD x (hP x hp) (hQ x hq)

theorem Union_left_Disjoint :
    forall (A : Type u) (P Q R : Ensemble A),
      Disjoint A (Union A P Q) R <-> Disjoint A P R /\ Disjoint A Q R := by
  intro A P Q R
  constructor
  · intro h
    constructor
    · intro x hp hr
      exact h x (Or.inl hp) hr
    · intro x hq hr
      exact h x (Or.inr hq) hr
  · intro h x hpq hr
    cases hpq with
    | inl hp => exact h.left x hp hr
    | inr hq => exact h.right x hq hr

theorem Union_right_Disjoint :
    forall (A : Type u) (P Q R : Ensemble A),
      Disjoint A R (Union A P Q) <-> Disjoint A R P /\ Disjoint A R Q := by
  intro A P Q R
  constructor
  · intro h
    constructor
    · intro x hr hp
      exact h x hr (Or.inl hp)
    · intro x hr hq
      exact h x hr (Or.inr hq)
  · intro h x hr hpq
    cases hpq with
    | inl hp => exact h.left x hr hp
    | inr hq => exact h.right x hr hq

theorem Included_Complement_Disjoint :
    forall (A : Type u) (P Q : Ensemble A),
      Included A P (Complement A Q) <-> Disjoint A P Q := by
  intro A P Q
  constructor
  · intro h x hp hq
    exact h x hp hq
  · intro h x hp hq
    exact h x hp hq

theorem Disjoint_comm :
    forall (A : Type u) (P Q : Ensemble A),
      Disjoint A P Q <-> Disjoint A Q P := by
  intro A P Q
  constructor
  · intro h x hq hp
    exact h x hp hq
  · intro h x hp hq
    exact h x hq hp

theorem Disjoint_Empty_set_right {A : Type u} (P : Ensemble A) :
    Disjoint A P (Empty_set A) := by
  intro x hp hEmpty
  cases hEmpty

theorem Disjoint_Empty_set_left {A : Type u} (P : Ensemble A) :
    Disjoint A (Empty_set A) P := by
  intro x hEmpty hp
  cases hEmpty

theorem Included_trans :
    forall {A : Type u} (P Q R : Ensemble A),
      Included A P Q -> Included A Q R -> Included A P R := by
  intro A P Q R hPQ hQR x hp
  exact hQR x (hPQ x hp)

theorem Intersection1_Included :
    forall {A : Type u} (P Q R : Ensemble A),
      Included A P R -> Included A (Intersection A P Q) R := by
  intro A P Q R h x hx
  exact h x hx.left

theorem Intersection2_Included :
    forall {A : Type u} (P Q R : Ensemble A),
      Included A Q R -> Included A (Intersection A P Q) R := by
  intro A P Q R h x hx
  exact h x hx.right

theorem Included_refl :
    forall (A : Type u) (P : Ensemble A), Included A P P := by
  intro A P x hx
  exact hx

def app_same_set {A : Type u} {P Q : Ensemble A}
    (H : Same_set A P Q) (x : A) : P x <-> Q x :=
  (Same_set_spec A P Q).mp H x

instance app_same_set_coeFun {A : Type u} {P Q : Ensemble A} :
    CoeFun (Same_set A P Q) (fun _ => forall x, P x <-> Q x) where
  coe H := app_same_set H

def respectful_set {A : Type u} {B : Type v} (X : Ensemble B) (f : A -> B) :
    Ensemble A :=
  fun x => X (f x)

inductive image_set {A : Type u} {B : Type v} :
    Ensemble A -> (A -> B) -> Ensemble B where
  | image_set_intro :
      forall (X : Ensemble A) (f : A -> B) (x : A),
        X x -> image_set X f (f x)

export image_set (image_set_intro)

theorem image_set_spec :
    forall {A : Type u} {B : Type v} (f : A -> B) (X : Ensemble A) (y : B),
      image_set X f y <-> exists x : A, X x /\ y = f x := by
  intro A B f X y
  constructor
  · intro h
    cases h with
    | image_set_intro x hx =>
        exact ⟨x, hx, rfl⟩
  · intro h
    rcases h with ⟨x, hx, hy⟩
    cases hy
    exact image_set_intro X f x hx

instance respectful_set_proper {A : Type u} {B : Type v} :
    Proper
      (Same_set B ==> pointwise_relation A (@Eq B) ==> Same_set A)
      (@respectful_set A B) where
  proper := by
    intro X Y hXY f g hfg
    constructor
    · intro x hx
      have hxy : Y (f x) := hXY.left (f x) hx
      rw [hfg x] at hxy
      exact hxy
    · intro x hy
      have hyx : X (g x) := hXY.right (g x) hy
      rw [← hfg x] at hyx
      exact hyx

instance image_set_proper2 {A : Type u} {B : Type v} :
    Proper (Same_set A ==> Eq ==> Same_set B) (@image_set A B) where
  proper := by
    intro X Y hXY f g hfg
    cases hfg
    constructor
    · intro y hy
      rcases (image_set_spec f X y).mp hy with ⟨x, hx, hyx⟩
      exact (image_set_spec f Y y).mpr ⟨x, hXY.left x hx, hyx⟩
    · intro y hy
      rcases (image_set_spec f Y y).mp hy with ⟨x, hx, hyx⟩
      exact (image_set_spec f X y).mpr ⟨x, hXY.right x hx, hyx⟩

theorem resp_Included :
    forall {A : Type u} {B : Type v} (X Y : Ensemble B) (f : A -> B),
      Included B X Y ->
      Included A (respectful_set X f) (respectful_set Y f) := by
  intro A B X Y f h x hx
  exact h (f x) hx

theorem resp_Same_set :
    forall {A : Type u} {B : Type v} (X Y : Ensemble B) (f : A -> B),
      Same_set B X Y ->
      Same_set A (respectful_set X f) (respectful_set Y f) := by
  intro A B X Y f h
  constructor
  · exact resp_Included X Y f h.left
  · exact resp_Included Y X f h.right

theorem resp_Intersection :
    forall {A : Type u} {B : Type v} (X Y : Ensemble B) (f : A -> B),
      Same_set A
        (respectful_set (Intersection B X Y) f)
        (Intersection A (respectful_set X f) (respectful_set Y f)) := by
  intro A B X Y f
  constructor
  · intro x hx
    exact hx
  · intro x hx
    exact hx

theorem resp_Union :
    forall {A : Type u} {B : Type v} (X Y : Ensemble B) (f : A -> B),
      Same_set A
        (respectful_set (Union B X Y) f)
        (Union A (respectful_set X f) (respectful_set Y f)) := by
  intro A B X Y f
  constructor
  · intro x hx
    exact hx
  · intro x hx
    exact hx

theorem resp_Complement :
    forall {A : Type u} {B : Type v} (X : Ensemble B) (f : A -> B),
      Same_set A
        (respectful_set (Complement B X) f)
        (Complement A (respectful_set X f)) := by
  intro A B X f
  constructor
  · intro x hx
    exact hx
  · intro x hx
    exact hx

theorem resp_Disjoint :
    forall {A : Type u} {B : Type v} (X Y : Ensemble B) (f : A -> B),
      Disjoint B X Y ->
      Disjoint A (respectful_set X f) (respectful_set Y f) := by
  intro A B X Y f h x hx hy
  exact h (f x) hx hy

theorem resp_Empty :
    forall {A : Type u} {B : Type v} (f : A -> B),
      Same_set A (respectful_set (Empty_set B) f) (Empty_set A) := by
  intro A B f
  constructor
  · intro x hx
    exact hx
  · intro x hx
    exact hx

theorem image_Included :
    forall {A : Type u} {B : Type v} (f : A -> B) (X Y : Ensemble A),
      Included A X Y ->
      Included B (image_set X f) (image_set Y f) := by
  intro A B f X Y h y hy
  rcases (image_set_spec f X y).mp hy with ⟨x, hx, hyx⟩
  exact (image_set_spec f Y y).mpr ⟨x, h x hx, hyx⟩

theorem image_Same_set :
    forall {A : Type u} {B : Type v} (f : A -> B) (X Y : Ensemble A),
      Same_set A X Y ->
      Same_set B (image_set X f) (image_set Y f) := by
  intro A B f X Y h
  constructor
  · exact image_Included f X Y h.left
  · exact image_Included f Y X h.right

theorem image_Intersection :
    forall {A : Type u} {B : Type v} (X Y : Ensemble A) (f : A -> B),
      Included B
        (image_set (Intersection A X Y) f)
        (Intersection B (image_set X f) (image_set Y f)) := by
  intro A B X Y f y hy
  cases hy with
  | image_set_intro x hx =>
      exact ⟨image_set_intro X f x hx.left, image_set_intro Y f x hx.right⟩

theorem image_Union :
    forall {A : Type u} {B : Type v} (X Y : Ensemble A) (f : A -> B),
      Same_set B
        (image_set (Union A X Y) f)
        (Union B (image_set X f) (image_set Y f)) := by
  intro A B X Y f
  constructor
  · intro y hy
    cases hy with
    | image_set_intro x hx =>
        cases hx with
        | inl hx => exact Or.inl (image_set_intro X f x hx)
        | inr hy => exact Or.inr (image_set_intro Y f x hy)
  · intro y hy
    cases hy with
    | inl hx =>
        cases hx with
        | image_set_intro x hx =>
            exact image_set_intro (Union A X Y) f x (Or.inl hx)
    | inr hy =>
        cases hy with
        | image_set_intro x hy =>
            exact image_set_intro (Union A X Y) f x (Or.inr hy)

theorem image_Disjoint_rev :
    forall {A : Type u} {B : Type v} (X Y : Ensemble A) (f : A -> B),
      Disjoint B (image_set X f) (image_set Y f) ->
      Disjoint A X Y := by
  intro A B X Y f h x hx hy
  exact h (f x) (image_set_intro X f x hx) (image_set_intro Y f x hy)

theorem image_Empty :
    forall {A : Type u} {B : Type v} (f : A -> B),
      Same_set B (image_set (Empty_set A) f) (Empty_set B) := by
  intro A B f
  constructor
  · intro y hy
    cases hy with
    | image_set_intro x hx => exact hx
  · intro y hy
    cases hy

theorem image_single :
    forall {A : Type u} {B : Type v} (a : A) (f : A -> B),
      Same_set B (image_set (Eq a) f) (Eq (f a)) := by
  intro A B a f
  constructor
  · intro y hy
    rcases (image_set_spec f (Eq a) y).mp hy with ⟨x, hx, hyx⟩
    cases hx
    exact hyx.symm
  · intro y hy
    cases hy
    exact image_set_intro (Eq a) f a rfl

def Countable_Union (A : Type u) (P : Nat -> Ensemble A) : Ensemble A :=
  fun x => exists i, P i x

def Non_Empty {U : Type u} (A : Ensemble U) : Prop :=
  exists x, A x

def Binart_set_list (U : Type u) (A B : Ensemble U) : Nat -> Ensemble U
  | 0 => A
  | 1 => B
  | _ => Empty_set U

theorem Union_is_Countable_Union :
    forall {U : Type u} (A B : Ensemble U),
      Same_set U (Union U A B) (Countable_Union U (Binart_set_list U A B)) := by
  intro U A B
  constructor
  · intro x hx
    cases hx with
    | inl ha => exact ⟨0, ha⟩
    | inr hb => exact ⟨1, hb⟩
  · intro x hx
    rcases hx with ⟨i, hi⟩
    cases i with
    | zero => exact Or.inl hi
    | succ i =>
        cases i with
        | zero => exact Or.inr hi
        | succ i => cases hi

theorem Intersection_is_Complement_Union
    (classic : forall P : Prop, P \/ ¬ P) :
    forall {U : Type u} (A B : Ensemble U),
      Same_set U
        (Intersection U A B)
        (Complement U (Union U (Complement U A) (Complement U B))) := by
  intro U A B
  constructor
  · intro x hx hUnion
    cases hUnion with
    | inl hna => exact hna hx.left
    | inr hnb => exact hnb hx.right
  · intro x hx
    have ha : A x := by
      cases classic (A x) with
      | inl ha => exact ha
      | inr hna => exact False.elim (hx (Or.inl hna))
    have hb : B x := by
      cases classic (B x) with
      | inl hb => exact hb
      | inr hnb => exact False.elim (hx (Or.inr hnb))
    exact ⟨ha, hb⟩

end Unifysl
