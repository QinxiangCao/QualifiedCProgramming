import MonadLib.MonadErr.MonadErrLoop
import AUXLib.ListLib.Base

namespace MonadLib

open AUXLib
open FP
open MonadErr
open scoped MonadNotation

def Hoare {Sigma A : Type} (P : Sigma -> Prop) (c : program Sigma A)
    (Q : A -> Sigma -> Prop) : Prop :=
  (forall a s1 s2, P s1 -> c.nrm s1 a s2 -> Q a s2) /\
  (forall s1, P s1 -> c.err s1 -> False)

theorem Hoare_proequiv {A Sigma : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (Q : A -> Sigma -> Prop) :
    equiv c1 c2 -> Hoare P c1 Q -> Hoare P c2 Q := by
  rintro he ⟨hn, herr⟩
  constructor
  · intro a s1 s2 hp hc
    exact hn a s1 s2 hp ((he.nrmequiv s1 a s2).mpr hc)
  · intro s1 hp hc
    exact herr s1 hp ((he.errequiv s1).mpr hc)

instance Hoare_programequiv_iff_Proper {Sigma A : Type} (P : Sigma -> Prop) :
    Proper (equiv ==> Eq ==> Iff) (@Hoare Sigma A P) where
  proper c1 c2 hc Q1 Q2 hQ := by
    subst Q2
    constructor
    · exact Hoare_proequiv c1 c2 P Q1 hc
    · exact Hoare_proequiv c2 c1 P Q1 (AUXLib.Equivalence.symm _ _ hc)

instance Hoare_setsequiv_iff_Proper {Sigma A : Type} :
    Proper (Sets.equiv ==> Eq ==> Sets.equiv ==> Iff) (@Hoare Sigma A) where
  proper P1 P2 hP c1 c2 hc Q1 Q2 hQ := by
    subst c2
    constructor
    · rintro ⟨hn, he⟩
      exact ⟨fun a s1 s2 hp hrun =>
          (hQ a s2).mp (hn a s1 s2 ((hP s1).mpr hp) hrun),
        fun s hp herr => he s ((hP s).mpr hp) herr⟩
    · rintro ⟨hn, he⟩
      exact ⟨fun a s1 s2 hp hrun =>
          (hQ a s2).mpr (hn a s1 s2 ((hP s1).mp hp) hrun),
        fun s hp herr => he s ((hP s).mp hp) herr⟩

theorem Hoare_bind {A B Sigma : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) (R : B -> Sigma -> Prop)
    (c1 : program Sigma A) (c2 : A -> program Sigma B) :
    Hoare P c1 Q -> (forall a, Hoare (Q a) (c2 a) R) ->
      Hoare P (MonadErr.bind c1 c2) R := by
  rintro ⟨h1n, h1e⟩ h2
  constructor
  · rintro b s1 s2 hp ⟨a, s0, hrun1, hrun2⟩
    exact (h2 a).1 b s0 s2 (h1n a s1 s0 hp hrun1) hrun2
  · intro s1 hp h
    rcases h with h | ⟨a, s0, hrun, he⟩
    · exact h1e s1 hp h
    · exact (h2 a).2 s0 (h1n a s1 s0 hp hrun) he

theorem Hoare_assert {Sigma : Type} (P : Sigma -> Prop) (Q : Prop) :
    Q -> Hoare P (assert Q) (fun _ => P) := by
  intro hQ
  constructor
  · rintro _ s1 s2 hp ⟨rfl, _⟩; exact hp
  · intro _ _ he; exact he hQ

theorem Hoare_assertS {Sigma : Type} (P Q : Sigma -> Prop) :
    (forall s, P s -> Q s) -> Hoare P (assertS Q) (fun _ => P) := by
  intro hPQ
  constructor
  · rintro _ s1 s2 hp ⟨rfl, _⟩; exact hp
  · intro s hp he; exact he (hPQ s hp)

theorem Hoare_any {Sigma A : Type} (P : Sigma -> Prop) :
    Hoare P (any A) (fun _ => P) := by
  constructor
  · intro _ _ _ hp hs
    subst hs
    exact hp
  · intro _ _ h; exact False.elim h

theorem Hoare_any_bind {Sigma A B : Type} (P : Sigma -> Prop)
    (f : A -> program Sigma B) (Q : B -> Sigma -> Prop) :
    (forall a, Hoare P (f a) Q) ->
      Hoare P (a <- any A ;; f a) Q := by
  intro h
  exact Hoare_bind P (fun _ => P) Q (any A) f (Hoare_any P) h

theorem Hoare_get {A Sigma : Type} (P : Sigma -> Prop)
    (Pa : Sigma -> A -> Prop) :
    Hoare P (get Pa) (fun a s2 => Pa s2 a /\ P s2) := by
  constructor
  · rintro a s1 s2 hp ⟨ha, rfl⟩; exact ⟨ha, hp⟩
  · intro _ _ h; exact False.elim h

theorem Hoare_update {Sigma : Type} (P : Sigma -> Prop)
    (Q : Sigma -> Sigma -> Prop) :
    Hoare P (update Q) (fun _ s2 => exists s1, Q s1 s2 /\ P s1) := by
  exact ⟨fun _ s1 s2 hp h => ⟨s1, h, hp⟩, fun _ _ h => False.elim h⟩

theorem Hoare_conseq {Sigma A : Type} (P1 P2 : Sigma -> Prop)
    (f : program Sigma A) (Q1 Q2 : A -> Sigma -> Prop) :
    (forall s, P1 s -> P2 s) ->
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P2 f Q2 -> Hoare P1 f Q1 := by
  rintro hp hq ⟨hn, he⟩
  exact ⟨fun a s1 s2 hpre hrun => hq a s2 (hn a s1 s2 (hp s1 hpre) hrun),
    fun s hpre herr => he s (hp s hpre) herr⟩

theorem Hoare_spec_derivation {Sigma A L : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop)
    (SpecP : L -> Sigma -> Prop) (SpecQ : L -> A -> Sigma -> Prop) :
    (forall l, Hoare (SpecP l) c (SpecQ l)) ->
    (forall s, P s -> exists l, SpecP l s) ->
    (forall s0 a s1, P s0 ->
      (forall l, SpecP l s0 -> SpecQ l a s1) -> Q a s1) ->
    Hoare P c Q := by
  intro hspec hlive hderive
  constructor
  · intro a s0 s1 hp hrun
    exact hderive s0 a s1 hp fun l hpl => (hspec l).1 a s0 s1 hpl hrun
  · intro s hp herr
    rcases hlive s hp with ⟨l, hpl⟩
    exact (hspec l).2 s hpl herr

theorem Hoare_implies {A Sigma : Type} (P P' : Sigma -> Prop) (P0 : Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall s, P s -> P0 /\ P' s) ->
    (P0 -> Hoare P' c Q) -> Hoare P c Q := by
  intro hp h
  by_cases hex : exists s, P s
  · rcases hex with ⟨s, hs⟩
    exact Hoare_conseq P P' c Q Q (fun s hs => (hp s hs).2)
      (fun _ _ => id) (h (hp s hs).1)
  · exact ⟨fun _ s _ hs => False.elim (hex ⟨s, hs⟩),
      fun s hs => False.elim (hex ⟨s, hs⟩)⟩

theorem Hoare_unit_pre {A : Type} (P : Prop) (c : program Unit A)
    (Q : A -> Unit -> Prop) :
    (P -> Hoare (fun _ => True) c Q) -> Hoare (fun _ => P) c Q := by
  intro h
  by_cases hp : P
  · exact Hoare_conseq (fun _ => P) (fun _ => True) c Q Q
      (fun _ _ => trivial) (fun _ _ => id) (h hp)
  · exact ⟨fun _ _ _ hP => False.elim (hp hP),
      fun _ hP => False.elim (hp hP)⟩

theorem Hoare_cons_pre {B Sigma : Type} (P P' : Sigma -> Prop)
    (c : program Sigma B) (Q : B -> Sigma -> Prop) :
    (forall s, P' s -> P s) -> Hoare P c Q -> Hoare P' c Q := by
  intro h hhoare
  exact Hoare_conseq P' P c Q Q h (fun _ _ => id) hhoare

theorem Hoare_cons_post {A Sigma : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q Q' : A -> Sigma -> Prop) :
    (forall a s, Q a s -> Q' a s) -> Hoare P c Q -> Hoare P c Q' := by
  intro h hhoare
  exact Hoare_conseq P P c Q' Q (fun _ => id) h hhoare

theorem Hoare_choice {A Sigma : Type} (P : Sigma -> Prop)
    (c1 c2 : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P c1 Q -> Hoare P c2 Q -> Hoare P (choice c1 c2) Q := by
  rintro ⟨h1n, h1e⟩ ⟨h2n, h2e⟩
  constructor
  · rintro a s1 s2 hp (h | h)
    · exact h1n a s1 s2 hp h
    · exact h2n a s1 s2 hp h
  · rintro s hp (h | h)
    · exact h1e s hp h
    · exact h2e s hp h

theorem Hoare_choice_disj {Sigma A : Type} (P : Sigma -> Prop)
    (c1 c2 : program Sigma A) (Q1 Q2 : A -> Sigma -> Prop) :
    Hoare P c1 Q1 -> Hoare P c2 Q2 ->
      Hoare P (choice c1 c2) (fun a s => Q1 a s \/ Q2 a s) := by
  rintro ⟨h1n, h1e⟩ ⟨h2n, h2e⟩
  constructor
  · rintro a s1 s2 hp (h | h)
    · exact Or.inl (h1n a s1 s2 hp h)
    · exact Or.inr (h2n a s1 s2 hp h)
  · rintro s hp (h | h)
    · exact h1e s hp h
    · exact h2e s hp h

theorem Hoare_assume' {Sigma : Type} (P : Sigma -> Prop) (Q : Prop) :
    Q -> Hoare P (testPure Q) (fun _ s => P s /\ Q) := by
  intro hQ
  constructor
  · rintro _ s1 s2 hp ⟨rfl, h⟩; exact ⟨hp, h⟩
  · intro _ _ h; exact False.elim h

theorem Hoare_assume_bind {A Sigma : Type} (P1 : Sigma -> Prop) (P2 : Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (P2 -> Hoare P1 c Q) -> Hoare P1 (testPure P2 ;; c) Q := by
  intro h
  by_cases hp : P2
  · apply Hoare_bind P1 (fun _ => P1) Q (testPure P2) (fun _ => c)
    · exact Hoare_cons_post P1 (testPure P2) (fun _ s => P1 s /\ P2)
        (fun _ => P1) (fun _ _ h => h.1) (Hoare_assume' P1 P2 hp)
    · intro _; exact h hp
  · constructor
    · rintro _ _ _ _ ⟨_, _, ⟨_, hfalse⟩, _⟩; exact False.elim (hp hfalse)
    · rintro _ _ (herr | ⟨_, _, ⟨_, hfalse⟩, _⟩)
      · exact False.elim herr
      · exact False.elim (hp hfalse)

theorem Hoare_assumeS {Sigma : Type} (P1 P2 : Sigma -> Prop) :
    Hoare P1 (test P2) (fun _ s => P1 s /\ P2 s) := by
  constructor
  · rintro _ s1 s2 hp ⟨rfl, h2⟩; exact ⟨hp, h2⟩
  · intro _ _ h; exact False.elim h

theorem Hoare_assumeS_bind {A Sigma : Type} (P1 P2 : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare (fun s => P1 s /\ P2 s) c Q -> Hoare P1 (test P2 ;; c) Q := by
  intro h
  exact Hoare_bind P1 (fun _ s => P1 s /\ P2 s) Q (test P2) (fun _ => c)
    (Hoare_assumeS P1 P2) (fun _ => h)

theorem Hoare_assert_bind {A Sigma : Type} (P : Sigma -> Prop) (P' : Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall s, P s -> P') -> (P' -> Hoare P c Q) ->
      Hoare P (assert P' ;; c) Q := by
  intro hp h
  by_cases hex : exists s, P s
  · rcases hex with ⟨s, hs⟩
    exact Hoare_bind P (fun _ => P) Q (assert P') (fun _ => c)
      (Hoare_assert P P' (hp s hs)) (fun _ => h (hp s hs))
  · exact ⟨fun _ s _ hs => False.elim (hex ⟨s, hs⟩),
      fun s hs => False.elim (hex ⟨s, hs⟩)⟩

theorem Hoare_assertS_bind {A Sigma : Type} (P Q : Sigma -> Prop)
    (c : program Sigma A) (R : A -> Sigma -> Prop) :
    (forall s, P s -> Q s) ->
      (Hoare P (assertS Q ;; c) R <-> Hoare P c R) := by
  intro hpq
  constructor
  · rintro ⟨hn, he⟩
    constructor
    · intro a s1 s2 hp hrun
      exact hn a s1 s2 hp ⟨(), s1, ⟨rfl, hpq s1 hp⟩, hrun⟩
    · intro s hp herr
      exact he s hp (Or.inr ⟨(), s, ⟨rfl, hpq s hp⟩, herr⟩)
  · intro h
    exact Hoare_bind P (fun _ => P) R (assertS Q) (fun _ => c)
      (Hoare_assertS P Q hpq) (fun _ => h)

theorem Hoare_step {Sigma A : Type} (P : Sigma -> Prop) (f : program Sigma A) :
    (forall s, P s -> Not (f.err s)) ->
      Hoare P f (fun a s2 => exists s1, f.nrm s1 a s2 /\ P s1) := by
  intro he
  exact ⟨fun a s1 s2 hp hn => ⟨s1, hn, hp⟩,
    fun s hp herr => he s hp herr⟩

theorem Hoare_state_intro {A Sigma : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall s0, P s0 -> Hoare (fun s => s = s0) c Q) -> Hoare P c Q := by
  intro h
  exact ⟨fun a s1 s2 hp hn => (h s1 hp).1 a s1 s2 rfl hn,
    fun s hp he => (h s hp).2 s rfl he⟩

theorem Hoare_ret {A Sigma : Type} (P : Sigma -> Prop) (a : A)
    (Q : A -> Sigma -> Prop) :
    (forall s, P s -> Q a s) -> Hoare P (MonadErr.ret a) Q := by
  intro h
  constructor
  · rintro r s1 s2 hp ⟨hr, hs⟩
    subst r
    subst s2
    exact h s1 hp
  · intro _ _ he; exact False.elim he

theorem Hoare_post_true {A Sigma : Type} (P : Sigma -> Prop)
    (c : program Sigma A) :
    (forall s, P s -> Not (c.err s)) -> Hoare P c (fun _ _ => True) := by
  intro h
  exact ⟨fun _ _ _ _ _ => trivial, fun s hp he => h s hp he⟩

theorem Hoare_progrefine {A Sigma : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (Q : A -> Sigma -> Prop) :
    (forall s a s', c2.nrm s a s' -> c1.nrm s a s') ->
    (forall s, c2.err s -> c1.err s) ->
    Hoare P c1 Q -> Hoare P c2 Q := by
  rintro hn he ⟨h1n, h1e⟩
  exact ⟨fun a s1 s2 hp hrun => h1n a s1 s2 hp (hn s1 a s2 hrun),
    fun s hp herr => h1e s hp (he s herr)⟩

theorem Hoare_equiv_iff {Sigma A : Type} (P : Sigma -> Prop)
    (c1 c2 : program Sigma A) (Q : A -> Sigma -> Prop) :
    equiv c1 c2 -> (Hoare P c1 Q <-> Hoare P c2 Q) := by
  intro h
  exact ⟨Hoare_proequiv c1 c2 P Q h,
    Hoare_proequiv c2 c1 P Q (AUXLib.Equivalence.symm _ _ h)⟩

theorem Hoare_step_s {A Sigma : Type} (s0 : Sigma) (c : program Sigma A) :
    Not (c.err s0) -> Hoare (fun s => s = s0) c (fun a s1 => c.nrm s0 a s1) := by
  intro he
  constructor
  · intro _ s1 _ hs hrun
    subst s1
    exact hrun
  · intro s hs herr
    subst s
    exact he herr

theorem Hoare_assume_s {Sigma : Type} (s0 : Sigma) (Q : Sigma -> Prop) :
    Q s0 -> Hoare (fun s => s = s0) (test Q)
      (fun _ s1 => s1 = s0 /\ Q s0) := by
  intro hq
  constructor
  · rintro _ s1 s2 hs ⟨rfl, h⟩
    subst s1
    exact ⟨rfl, h⟩
  · intro _ _ h; exact False.elim h

def continue_case {A B Sigma : Type} : CntOrBrk A B -> program Sigma A
  | .by_continue a => {
      nrm := fun s1 r s2 => s1 = s2 /\ r = a
      err := fun _ => False }
  | .by_break _ => ProgramPO.bot

def break_case {A B Sigma : Type} : CntOrBrk A B -> program Sigma B
  | .by_continue _ => ProgramPO.bot
  | .by_break b => {
      nrm := fun s1 r s2 => s1 = s2 /\ r = b
      err := fun _ => False }

theorem Hoare_cnt_cnt {A B Sigma : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) (a : A) :
    (forall s, P s -> Q a s) ->
      Hoare P (@continue_case A B Sigma (.by_continue a)) Q := by
  intro h
  constructor
  · rintro r s1 s2 hp ⟨rfl, rfl⟩; exact h s1 hp
  · intro _ _ he; exact False.elim he

theorem Hoare_brk_brk {A B Sigma : Type} (P : Sigma -> Prop)
    (Q : B -> Sigma -> Prop) (b : B) :
    (forall s, P s -> Q b s) ->
      Hoare P (@break_case A B Sigma (.by_break b)) Q := by
  intro h
  constructor
  · rintro r s1 s2 hp ⟨rfl, rfl⟩; exact h s1 hp
  · intro _ _ he; exact False.elim he

theorem Hoare_brk_cnt {A B Sigma : Type} (P : Sigma -> Prop)
    (Q : B -> Sigma -> Prop) (a : A) :
    Hoare P (@break_case A B Sigma (.by_continue a)) Q := by
  exact ⟨fun _ _ _ _ h => False.elim h, fun _ _ h => False.elim h⟩

theorem Hoare_cnt_brk {A B Sigma : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) (b : B) :
    Hoare P (@continue_case A B Sigma (.by_break b)) Q := by
  exact ⟨fun _ _ _ _ h => False.elim h, fun _ _ h => False.elim h⟩

theorem Hoare_sum {A B Sigma : Type} (P : Sigma -> Prop)
    (c : program Sigma (CntOrBrk A B)) (Q : A -> Sigma -> Prop)
    (R : B -> Sigma -> Prop) :
    Hoare P (x <- c ;; continue_case x) Q ->
    Hoare P (x <- c ;; break_case x) R ->
    Hoare P c (fun x s => match x with
      | .by_continue a => Q a s
      | .by_break b => R b s) := by
  rintro hq hr
  constructor
  · intro ab s1 s2 hp hrun
    cases ab with
    | by_continue a =>
        exact hq.1 a s1 s2 hp
          ⟨.by_continue a, s2, hrun, ⟨rfl, rfl⟩⟩
    | by_break b =>
        exact hr.1 b s1 s2 hp
          ⟨.by_break b, s2, hrun, ⟨rfl, rfl⟩⟩
  · intro s hp herr
    exact hq.2 s hp (Or.inl herr)

theorem Hoare_conj {A Sigma : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q R : A -> Sigma -> Prop) :
    Hoare P c Q -> Hoare P c R ->
      Hoare P c (fun a s => Q a s /\ R a s) := by
  rintro ⟨hqn, hqe⟩ ⟨hrn, _⟩
  exact ⟨fun a s1 s2 hp hn => ⟨hqn a s1 s2 hp hn, hrn a s1 s2 hp hn⟩, hqe⟩

theorem Hoare_disj {Sigma A : Type} (P1 P2 : Sigma -> Prop)
    (f : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P1 f Q -> Hoare P2 f Q ->
      Hoare (fun s => P1 s \/ P2 s) f Q := by
  rintro h1 h2
  constructor
  · intro a s1 s2 hp hn
    exact hp.elim (fun h => h1.1 a s1 s2 h hn) (fun h => h2.1 a s1 s2 h hn)
  · intro s hp he
    exact hp.elim (fun h => h1.2 s h he) (fun h => h2.2 s h he)

theorem Hoare_pre_ex {Sigma A X : Type} (P : X -> Sigma -> Prop)
    (f : program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall x, Hoare (P x) f Q) ->
      Hoare (fun s => exists x, P x s) f Q := by
  intro h
  constructor
  · intro a s1 s2 hp hn
    rcases hp with ⟨x, hx⟩
    exact (h x).1 a s1 s2 hx hn
  · intro s hp he
    rcases hp with ⟨x, hx⟩
    exact (h x).2 s hx he

theorem Hoare_stateless {A Sigma : Type} (P : Prop) (c : program Sigma A)
    (Q : A -> Sigma -> Prop) :
    (P -> Hoare (fun _ => True) c Q) -> Hoare (fun _ => P) c Q := by
  intro h
  by_cases hp : P
  · exact Hoare_cons_pre (fun _ => True) (fun _ => P) c Q
      (fun _ _ => trivial) (h hp)
  · exact ⟨fun _ _ _ hP => False.elim (hp hP),
      fun _ hP => False.elim (hp hP)⟩

theorem Hoare_stateless' {A Sigma : Type} (P : Prop) (P' : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (P -> Hoare P' c Q) -> Hoare (fun s => P' s /\ P) c Q := by
  intro h
  by_cases hp : P
  · exact Hoare_cons_pre P' (fun s => P' s /\ P) c Q (fun _ h => h.1) (h hp)
  · exact ⟨fun _ _ _ hpre => False.elim (hp hpre.2),
      fun _ hpre => False.elim (hp hpre.2)⟩

theorem Hoare_bot {Sigma A : Type} (P : Sigma -> Prop) (Q : A -> Sigma -> Prop) :
    Hoare P ProgramPO.bot Q := by
  exact ⟨fun _ _ _ _ h => False.elim h, fun _ _ h => False.elim h⟩

theorem Hoare_update_bind {Sigma A : Type} (P : Sigma -> Prop)
    (f : Sigma -> Sigma -> Prop) (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall s1, P s1 -> Hoare (fun s2 => f s1 s2) c Q) ->
      Hoare P (update f ;; c) Q := by
  intro h
  constructor
  · rintro a s1 s2 hp ⟨_, s0, hf, hc⟩
    exact (h s1 hp).1 a s0 s2 hf hc
  · rintro s hp (he | ⟨_, s0, hf, he⟩)
    · exact False.elim he
    · exact (h s hp).2 s0 hf he

theorem Hoare_update_s {Sigma : Type} (s0 : Sigma) (f : Sigma -> Sigma -> Prop) :
    Hoare (fun s => s = s0) (update f) (fun _ s1 => f s0 s1) := by
  constructor
  · intro _ s1 _ hs hf
    subst s1
    exact hf
  · intro _ _ he; exact False.elim he

theorem Hoare_update' {Sigma : Type} (s0 : Sigma) (f : Sigma -> Sigma) :
    Hoare (fun s => s = s0) (update' f) (fun _ s1 => s1 = f s0) :=
  Hoare_update_s s0 (fun s s' => s' = f s)

theorem Hoare_get_s {Sigma A : Type} (s0 : Sigma) (Pa : Sigma -> A -> Prop) :
    Hoare (fun s => s = s0) (get Pa) (fun a s1 => s1 = s0 /\ Pa s0 a) := by
  constructor
  · rintro a s1 s2 hs ⟨hp, heq⟩
    subst s1
    subst s2
    exact ⟨rfl, hp⟩
  · intro _ _ he; exact False.elim he

theorem Hoare_get' {Sigma A : Type} (s0 : Sigma) (fa : Sigma -> A) :
    Hoare (fun s => s = s0) (get' fa) (fun a s1 => s1 = s0 /\ a = fa s0) :=
  Hoare_get_s s0 (fun s a => a = fa s)

private theorem Hoare_indexed_union {Sigma A I : Type} (P : Sigma -> Prop)
    (cs : I -> program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall i, Hoare P (cs i) Q) ->
      Hoare P (ProgramPO.indexed_union cs) Q := by
  intro h
  constructor
  · rintro a s1 s2 hp ⟨i, hi⟩; exact (h i).1 a s1 s2 hp hi
  · rintro s hp ⟨i, hi⟩; exact (h i).2 s hp hi

theorem Hoare_BW_fix {Sigma A B : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B)
    (P : A -> Sigma -> Prop) (Q : A -> B -> Sigma -> Prop) (a : A) :
    (forall W : A -> program Sigma B,
      (forall a, Hoare (P a) (W a) (fun b s => Q a b s)) ->
      forall a, Hoare (P a) (f W a) (fun b s => Q a b s)) ->
    Hoare (P a) (BW_fix f a) (fun b s => Q a b s) := by
  intro hstep
  have hiter : forall n a,
      Hoare (P a) (FP.nat_iter n f (fun _ => ProgramPO.bot) a)
        (fun b s => Q a b s) := by
    intro n
    induction n with
    | zero => intro a; exact Hoare_bot _ _
    | succ n ih =>
        intro a
        simpa [FP.nat_iter] using
          hstep (FP.nat_iter n f (fun _ => ProgramPO.bot)) ih a
  change Hoare (P a)
    (ProgramPO.indexed_union (fun n => FP.nat_iter n f (fun _ => ProgramPO.bot) a))
    (fun b s => Q a b s)
  exact Hoare_indexed_union _ _ _ (fun n => hiter n a)

theorem Hoare_BW_fix_logicv {Sigma A B C : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B)
    (P : A -> C -> Sigma -> Prop) (Q : A -> C -> B -> Sigma -> Prop)
    (a : A) (c : C) :
    (forall W : A -> program Sigma B,
      (forall a c, Hoare (P a c) (W a) (fun b s => Q a c b s)) ->
      forall a c, Hoare (P a c) (f W a) (fun b s => Q a c b s)) ->
    Hoare (P a c) (BW_fix f a) (fun b s => Q a c b s) := by
  intro hstep
  have hiter : forall n a c,
      Hoare (P a c) (FP.nat_iter n f (fun _ => ProgramPO.bot) a)
        (fun b s => Q a c b s) := by
    intro n
    induction n with
    | zero => intro a c; exact Hoare_bot _ _
    | succ n ih =>
        intro a c
        simpa [FP.nat_iter] using
          hstep (FP.nat_iter n f (fun _ => ProgramPO.bot)) ih a c
  change Hoare (P a c)
    (ProgramPO.indexed_union (fun n => FP.nat_iter n f (fun _ => ProgramPO.bot) a))
    (fun b s => Q a c b s)
  exact Hoare_indexed_union _ _ _ (fun n => hiter n a c)

theorem Hoare_BW_fix_prog {Sigma A : Type}
    (f : program Sigma A -> program Sigma A)
    (P : Sigma -> Prop) (Q : A -> Sigma -> Prop) :
    (forall W, Hoare P W Q -> Hoare P (f W) Q) ->
      Hoare P (BW_fix f) Q := by
  intro hstep
  have hiter : forall n, Hoare P (FP.nat_iter n f ProgramPO.bot) Q := by
    intro n
    induction n with
    | zero => exact Hoare_bot P Q
    | succ n ih => simpa [FP.nat_iter] using hstep _ ih
  change Hoare P (ProgramPO.indexed_union (fun n => FP.nat_iter n f ProgramPO.bot)) Q
  exact Hoare_indexed_union _ _ _ hiter

theorem Hoare_BW_fix_logicv_conj' {Sigma A B C : Type}
    (f : (A -> program Sigma B) -> A -> program Sigma B)
    (P1 : A -> C -> Sigma -> Prop) (Q1 : A -> C -> B -> Sigma -> Prop)
    (a : A) (c : C) {D : Type}
    (P2 : A -> D -> Sigma -> Prop) (Q2 : A -> D -> B -> Sigma -> Prop) :
    (forall a d, Hoare (P2 a d) (BW_fix f a) (Q2 a d)) ->
    (forall W : A -> program Sigma B,
      (forall a d, Hoare (P2 a d) (W a) (Q2 a d)) ->
      (forall a c, Hoare (P1 a c) (W a) (Q1 a c)) ->
      (forall a d, Hoare (P2 a d) (f W a) (Q2 a d)) ->
      forall a c, Hoare (P1 a c) (f W a) (Q1 a c)) ->
    Hoare (P1 a c) (BW_fix f a) (Q1 a c) := by
  intro hfix2 hstep
  have hiter2 : forall n a d,
      Hoare (P2 a d) (FP.nat_iter n f (fun _ => ProgramPO.bot) a) (Q2 a d) := by
    intro n a d
    apply Hoare_progrefine (BW_fix f a)
      (FP.nat_iter n f (fun _ => ProgramPO.bot) a) (P2 a d) (Q2 a d)
    · intro s b s' hn
      exact ⟨n, hn⟩
    · intro s he
      exact ⟨n, he⟩
    · exact hfix2 a d
  have hiter1 : forall n a c,
      Hoare (P1 a c) (FP.nat_iter n f (fun _ => ProgramPO.bot) a) (Q1 a c) := by
    intro n
    induction n with
    | zero => intro a c; exact Hoare_bot _ _
    | succ n ih =>
        intro a c
        simpa [FP.nat_iter] using
          hstep (FP.nat_iter n f (fun _ => ProgramPO.bot))
            (hiter2 n) ih (hiter2 (n + 1)) a c
  change Hoare (P1 a c)
    (ProgramPO.indexed_union
      (fun n => FP.nat_iter n f (fun _ => ProgramPO.bot) a)) (Q1 a c)
  exact Hoare_indexed_union _ _ _ (fun n => hiter1 n a c)

theorem Hoare_whileP {Sigma : Type} (cond : Sigma -> Prop)
    (body : program Sigma Unit) (P : Sigma -> Prop) :
    Hoare (fun s => cond s /\ P s) body (fun _ s => P s) ->
      Hoare P (whileP cond body) (fun _ s => P s /\ Not (cond s)) := by
  intro hbody
  unfold whileP
  apply Hoare_BW_fix_prog (whileP_f cond body) P
    (fun _ s => P s /\ Not (cond s))
  intro W hW
  unfold whileP_f
  apply Hoare_choice
  · apply Hoare_assumeS_bind
    apply Hoare_bind (fun s => P s /\ cond s) (fun _ s => P s)
      (fun _ s => P s /\ Not (cond s)) body
    · exact Hoare_cons_pre (fun s => cond s /\ P s) (fun s => P s /\ cond s)
        body (fun _ s => P s) (fun _ h => ⟨h.2, h.1⟩) hbody
    · intro _; exact hW
  · apply Hoare_assumeS_bind
    exact Hoare_ret (fun s => P s /\ Not (cond s)) ()
      (fun _ s => P s /\ Not (cond s)) (fun _ => id)

theorem Hoare_while {Sigma : Type} (cond : program Sigma Bool)
    (body : program Sigma Unit) (P : Sigma -> Prop) :
    Hoare P cond (fun _ s => P s) ->
    Hoare P body (fun _ s => P s) ->
      Hoare P («while» cond body) (fun _ s => P s) := by
  intro hcond hbody
  unfold «while»
  apply Hoare_BW_fix_prog (while_f cond body) P (fun _ s => P s)
  intro W hW
  unfold while_f
  apply Hoare_bind P (fun _ s => P s) (fun _ s => P s) cond
  · exact hcond
  · intro b
    cases b
    · exact Hoare_ret P () (fun _ s => P s) (fun _ => id)
    · apply Hoare_bind P (fun _ s => P s) (fun _ s => P s) body
      · exact hbody
      · intro _; exact hW

theorem Hoare_whileret {Sigma A : Type}
    (cond : A -> program Sigma Bool) (body : A -> program Sigma A)
    (P : A -> Sigma -> Prop) (a : A) :
    (forall a, Hoare (P a) (cond a) (fun _ s => P a s)) ->
    (forall a, Hoare (P a) (body a) P) ->
      Hoare (P a) (whileret cond body a) P := by
  intro hcond hbody
  unfold whileret
  apply Hoare_BW_fix (whileret_f cond body) P (fun _ => P) a
  intro W hW a0
  unfold whileret_f
  apply Hoare_bind (P a0) (fun _ s => P a0 s) P (cond a0)
  · exact hcond a0
  · intro b
    cases b
    · exact Hoare_ret (P a0) a0 P (fun _ => id)
    · apply Hoare_bind (P a0) P P (body a0)
      · exact hbody a0
      · exact hW

theorem Hoare_whileretP {Sigma A : Type}
    (cond : A -> Sigma -> Prop) (body : A -> program Sigma A)
    (P : A -> Sigma -> Prop) (a : A) :
    (forall a, Hoare (fun s => cond a s /\ P a s) (body a) P) ->
      Hoare (P a) (whileretP cond body a)
        (fun a s => P a s /\ Not (cond a s)) := by
  intro hbody
  unfold whileretP
  apply Hoare_BW_fix (whileretP_f cond body) P
    (fun _ b s => P b s /\ Not (cond b s)) a
  intro W hW a0
  unfold whileretP_f
  apply Hoare_choice
  · apply Hoare_assumeS_bind
    apply Hoare_bind (fun s => P a0 s /\ cond a0 s) P
      (fun b s => P b s /\ Not (cond b s)) (body a0)
    · exact Hoare_cons_pre (fun s => cond a0 s /\ P a0 s)
        (fun s => P a0 s /\ cond a0 s) (body a0) P
        (fun _ h => ⟨h.2, h.1⟩) (hbody a0)
    · exact hW
  · apply Hoare_assumeS_bind
    exact Hoare_ret (fun s => P a0 s /\ Not (cond a0 s)) a0
      (fun b s => P b s /\ Not (cond b s)) (fun _ => id)

structure monad_funcspec {Sigma A R : Type} : Type 1 where
  mFS_lv : Type
  mFS_pre : A -> mFS_lv -> Sigma -> Prop
  mFS_Post : A -> mFS_lv -> R -> Sigma -> Prop

abbrev mk_mfs {Sigma A R : Type} :=
  @monad_funcspec.mk Sigma A R

abbrev monad_funcspecs {Sigma A R : Type} : Type 1 :=
  List (@monad_funcspec Sigma A R)

def monad_sat_funcspec {Sigma A R : Type} (m : A -> program Sigma R)
    (fs : @monad_funcspec Sigma A R) : Prop :=
  forall a lv, Hoare (fs.mFS_pre a lv) (m a) (fs.mFS_Post a lv)

theorem Hoare_fix_logicv_fspecs {Sigma A R : Type}
    (f : (A -> program Sigma R) -> A -> program Sigma R)
    (fspecs : monad_funcspecs (Sigma := Sigma) (A := A) (R := R))
    (fs : monad_funcspec (Sigma := Sigma) (A := A) (R := R)) :
    Forall (fun fs0 => monad_sat_funcspec (fun a => BW_fix f a) fs0) fspecs ->
    (forall W : A -> program Sigma R,
      Forall (fun fs0 => monad_sat_funcspec W fs0) fspecs ->
      (forall a lv, Hoare (fs.mFS_pre a lv) (W a) (fs.mFS_Post a lv)) ->
      forall a lv, Hoare (fs.mFS_pre a lv) (f W a) (fs.mFS_Post a lv)) ->
    forall a lv, Hoare (fs.mFS_pre a lv) (BW_fix f a) (fs.mFS_Post a lv) := by
  intro hsat hstep
  have hforall : forall n,
      Forall (fun fs0 => monad_sat_funcspec
        (FP.nat_iter n f (fun _ => ProgramPO.bot)) fs0) fspecs := by
    intro n
    apply Forall.iff_forall_mem.mpr
    intro fs0 hmem a lv
    apply Hoare_progrefine (BW_fix f a)
      (FP.nat_iter n f (fun _ => ProgramPO.bot) a)
      (fs0.mFS_pre a lv) (fs0.mFS_Post a lv)
    · intro s r s' hn; exact ⟨n, hn⟩
    · intro s he; exact ⟨n, he⟩
    · exact (hsat.mem hmem) a lv
  have hiter : forall n a lv,
      Hoare (fs.mFS_pre a lv)
        (FP.nat_iter n f (fun _ => ProgramPO.bot) a) (fs.mFS_Post a lv) := by
    intro n
    induction n with
    | zero => intro a lv; exact Hoare_bot _ _
    | succ n ih =>
        intro a lv
        simpa [FP.nat_iter] using
          hstep (FP.nat_iter n f (fun _ => ProgramPO.bot)) (hforall n) ih a lv
  intro a lv
  change Hoare (fs.mFS_pre a lv)
    (ProgramPO.indexed_union
      (fun n => FP.nat_iter n f (fun _ => ProgramPO.bot) a))
    (fs.mFS_Post a lv)
  exact Hoare_indexed_union _ _ _ (fun n => hiter n a lv)

theorem Hoare_repeat_break {Sigma A B : Type}
    (f : A -> program Sigma (CntOrBrk A B)) (P : A -> Sigma -> Prop)
    (Q : B -> Sigma -> Prop) :
    (forall a, Hoare (P a) (f a) (fun ab s => match ab with
      | .by_continue a' => P a' s
      | .by_break b => Q b s)) ->
    forall a, Hoare (P a) (repeat_break f a) Q := by
  intro hf a
  apply Hoare_BW_fix (repeat_break_f f) P (fun _ => Q) a
  intro W hW a0
  unfold repeat_break_f
  apply Hoare_bind (P a0)
    (fun ab s => match ab with
      | .by_continue a' => P a' s
      | .by_break b => Q b s)
    Q (f a0)
  · exact hf a0
  · intro ab
    cases ab with
    | by_continue a' => exact hW a'
    | by_break b => exact Hoare_ret (Q b) b Q (fun _ => id)

theorem Hoare_repeat_break' {Sigma A B : Type}
    (body : A -> program Sigma (CntOrBrk A B)) (P : A -> Sigma -> Prop)
    (Q : B -> Sigma -> Prop) :
    (forall a, Hoare (P a) (x <- body a ;; continue_case x) P) ->
    (forall a, Hoare (P a) (x <- body a ;; break_case x) Q) ->
    forall a, Hoare (P a) (repeat_break body a) Q := by
  intro hc hb
  apply Hoare_repeat_break body P Q
  intro a
  exact Hoare_sum (P a) (body a) P Q (hc a) (hb a)

theorem Hoare_repeat_break_noin {Sigma B : Type}
    (body : program Sigma (CntOrBrk Unit B)) (P : Sigma -> Prop)
    (Q : B -> Sigma -> Prop) :
    Hoare P body (fun ab s => match ab with
      | .by_continue _ => P s
      | .by_break b => Q b s) ->
    Hoare P (repeat_break_noin body) Q := by
  intro hb
  apply Hoare_BW_fix_prog (repeat_break_f_noinput body) P Q
  intro W hW
  unfold repeat_break_f_noinput
  apply Hoare_bind P
    (fun ab s => match ab with
      | .by_continue _ => P s
      | .by_break b => Q b s)
    Q body
  · exact hb
  · intro ab
    cases ab with
    | by_continue _ => exact hW
    | by_break b => exact Hoare_ret (Q b) b Q (fun _ => id)

theorem range_plus_1_aux (P : Int -> Prop) (lo hi : Int) :
    (forall i, lo <= i /\ i < hi -> P i) ->
    forall i, lo + 1 <= i /\ i < hi -> P i := by
  intro h i hiBounds
  apply h i
  omega

theorem Hoare_range_iter' {A Sigma : Type}
    (f : Int -> A -> program Sigma A) (P : Int -> A -> Sigma -> Prop)
    (lo hi : Int) :
    lo <= hi ->
    (forall i, lo <= i /\ i < hi -> forall a,
      Hoare (P i a) (f i a) (fun b => P (i + 1) b)) ->
    forall a, Hoare (P lo a) (range_iter lo hi f a) (fun b => P hi b) := by
  intro hlohi hbody a
  unfold range_iter
  apply Hoare_cons_pre
    (fun s => P lo a s /\ lo <= lo /\ lo <= hi) (P lo a)
    (BW_fix (range_iter_f hi f) (lo, a)) (fun b => P hi b)
  · intro s hp; exact ⟨hp, by omega, hlohi⟩
  · apply Hoare_BW_fix (range_iter_f hi f)
      (fun p s => P p.1 p.2 s /\ lo <= p.1 /\ p.1 <= hi)
      (fun _ b s => P hi b s) (lo, a)
    intro W hW p
    rcases p with ⟨i, a0⟩
    unfold range_iter_f
    apply Hoare_choice
    · apply Hoare_assume_bind
      intro hilthi
      apply Hoare_implies
        (fun s => P i a0 s /\ lo <= i /\ i <= hi)
        (fun s => P i a0 s /\ lo <= i /\ i <= hi) (lo <= i) _ _
      · intro _ hs; exact ⟨hs.2.1, hs⟩
      · intro hloi
        apply Hoare_bind
          (fun s => P i a0 s /\ lo <= i /\ i <= hi)
          (fun b s => P (i + 1) b s)
          (fun b s => P hi b s) (f i a0)
        · apply Hoare_cons_pre (P i a0)
            (fun s => P i a0 s /\ lo <= i /\ i <= hi)
            (f i a0) (fun b => P (i + 1) b)
          · exact fun _ h => h.1
          · exact hbody i ⟨hloi, hilthi⟩ a0
        · intro b
          apply Hoare_cons_pre
            (fun s => P (i + 1) b s /\ lo <= i + 1 /\ i + 1 <= hi)
            (P (i + 1) b) (W (i + 1, b)) (fun b => P hi b)
          · intro s hp; exact ⟨hp, by omega, by omega⟩
          · exact hW (i + 1, b)
    · apply Hoare_assume_bind
      intro higehi
      apply Hoare_ret
      intro s hs
      have : i = hi := by omega
      subst i
      exact hs.1

theorem Hoare_range_iter_break' {A B Sigma : Type}
    (f : Int -> A -> program Sigma (CntOrBrk A B))
    (P : Int -> A -> Sigma -> Prop) (Q : B -> Sigma -> Prop)
    (lo hi : Int) :
    lo <= hi ->
    (forall i, lo <= i /\ i < hi -> forall a,
      Hoare (P i a) (f i a) (fun res s => match res with
        | .by_continue a' => P (i + 1) a' s
        | .by_break b => Q b s)) ->
    forall a, Hoare (P lo a) (range_iter_break lo hi f a)
      (fun res s => match res with
        | .by_continue a' => P hi a' s
        | .by_break b => Q b s) := by
  intro hlohi hbody a
  unfold range_iter_break
  apply Hoare_cons_pre
    (fun s => P lo a s /\ lo <= lo /\ lo <= hi) (P lo a)
    (BW_fix (range_iter_break_f hi f) (lo, a)) _
  · intro s hp; exact ⟨hp, by omega, hlohi⟩
  · apply Hoare_BW_fix (range_iter_break_f hi f)
      (fun p s => P p.1 p.2 s /\ lo <= p.1 /\ p.1 <= hi)
      (fun _ res s => match res with
        | .by_continue a' => P hi a' s
        | .by_break b => Q b s) (lo, a)
    intro W hW p
    rcases p with ⟨i, a0⟩
    unfold range_iter_break_f
    apply Hoare_choice
    · apply Hoare_assume_bind
      intro hilthi
      apply Hoare_implies
        (fun s => P i a0 s /\ lo <= i /\ i <= hi)
        (fun s => P i a0 s /\ lo <= i /\ i <= hi) (lo <= i) _ _
      · intro _ hs; exact ⟨hs.2.1, hs⟩
      · intro hloi
        apply Hoare_bind
          (fun s => P i a0 s /\ lo <= i /\ i <= hi)
          (fun res s => match res with
            | .by_continue a' => P (i + 1) a' s
            | .by_break b => Q b s) _ (f i a0)
        · apply Hoare_cons_pre (P i a0)
            (fun s => P i a0 s /\ lo <= i /\ i <= hi) (f i a0) _
          · exact fun _ h => h.1
          · exact hbody i ⟨hloi, hilthi⟩ a0
        · intro res
          cases res with
          | by_continue a' =>
              apply Hoare_cons_pre
                (fun s => P (i + 1) a' s /\ lo <= i + 1 /\ i + 1 <= hi)
                (P (i + 1) a') (W (i + 1, a')) _
              · intro s hp; exact ⟨hp, by omega, by omega⟩
              · exact hW (i + 1, a')
          | by_break b =>
              exact Hoare_ret (Q b) (by_break b : CntOrBrk A B) _ (fun _ => id)
    · apply Hoare_assume_bind
      intro higehi
      apply Hoare_ret
      intro s hs
      have : i = hi := by omega
      subst i
      exact hs.1

theorem Hoare_range_iter {A Sigma : Type}
    (f : Int -> A -> program Sigma A) (Q : Sigma -> Prop)
    (P : Int -> A -> Sigma -> Prop) (lo hi : Int) :
    lo <= hi -> forall a,
    (forall s, Q s -> P lo a s) ->
    (forall i, lo <= i /\ i < hi -> forall a,
      Hoare (P i a) (f i a) (P (i + 1))) ->
    Hoare Q (range_iter lo hi f a) (P hi) := by
  intro hlohi a hpre hbody
  exact Hoare_cons_pre (P lo a) Q (range_iter lo hi f a) (P hi)
    hpre (Hoare_range_iter' f P lo hi hlohi hbody a)

theorem Hoare_range_iter_break {A B Sigma : Type}
    (f : Int -> A -> program Sigma (CntOrBrk A B))
    (P : Int -> A -> Sigma -> Prop) (Q1 : Sigma -> Prop)
    (Q2 : B -> Sigma -> Prop) (lo hi : Int) :
    lo <= hi -> forall a,
    (forall s, Q1 s -> P lo a s) ->
    (forall i, lo <= i /\ i < hi -> forall a,
      Hoare (P i a) (f i a) (fun res s => match res with
        | .by_continue a' => P (i + 1) a' s
        | .by_break b => Q2 b s)) ->
    Hoare Q1 (range_iter_break lo hi f a)
      (fun res s => match res with
        | .by_continue a' => P hi a' s
        | .by_break b => Q2 b s) := by
  intro hlohi a hpre hbody
  exact Hoare_cons_pre (P lo a) Q1 (range_iter_break lo hi f a) _
    hpre (Hoare_range_iter_break' f P Q2 lo hi hlohi hbody a)

theorem app_singleton_tail {A : Type} (pfx : List A) (a : A) (l : List A) :
    (pfx ++ [a]) ++ l = pfx ++ a :: l := by
  simp

theorem Hoare_list_iter_aux {Sigma A B : Type}
    (P : List A -> B -> Sigma -> Prop) (body : A -> B -> program Sigma B)
    (pfx : List A) :
    (forall pfx x b, Hoare (fun s => P pfx b s) (body x b)
      (fun b' s => P (pfx ++ [x]) b' s)) ->
    forall l b, Hoare (fun s => P pfx b s) (list_iter body l b)
      (fun b' s => P (pfx ++ l) b' s) := by
  intro h l
  induction l generalizing pfx with
  | nil =>
      intro b
      simpa [list_iter] using Hoare_ret (fun s => P pfx b s) b
        (fun b' s => P pfx b' s) (fun _ => id)
  | cons x xs ih =>
      intro b
      apply Hoare_bind (fun s => P pfx b s)
        (fun b' s => P (pfx ++ [x]) b' s)
        (fun b' s => P (pfx ++ x :: xs) b' s) (body x b)
      · exact h pfx x b
      · intro b'
        apply Hoare_cons_post (fun s => P (pfx ++ [x]) b' s)
          (list_iter body xs b')
          (fun b'' s => P ((pfx ++ [x]) ++ xs) b'' s)
          (fun b'' s => P (pfx ++ x :: xs) b'' s)
        · intro _ _ hp
          simpa [app_singleton_tail] using hp
        · exact ih (pfx ++ [x]) b'

theorem Hoare_list_iter {Sigma A B : Type}
    (P : List A -> B -> Sigma -> Prop) (body : A -> B -> program Sigma B) :
    (forall pfx x b, Hoare (fun s => P pfx b s) (body x b)
      (fun b' s => P (pfx ++ [x]) b' s)) ->
    forall l b, Hoare (fun s => P [] b s) (list_iter body l b)
      (fun b' s => P l b' s) := by
  intro h l b
  simpa using Hoare_list_iter_aux P body [] h l b

theorem range_iter_no_iter {A Sigma : Type}
    (f : Int -> A -> program Sigma A) (P : A -> Sigma -> Prop)
    (lo hi : Int) :
    hi < lo -> forall a, Hoare (P a) (range_iter lo hi f a) P := by
  intro hhilo a
  apply Hoare_proequiv
    (choice
      (testPure (lo < hi) ;; b <- f lo a ;; range_iter (lo + 1) hi f b)
      (testPure (lo >= hi) ;; MonadErr.ret a))
    (range_iter lo hi f a) (P a) P
  · exact AUXLib.Equivalence.symm _ _ (range_iter_unfold hi f lo a)
  · apply Hoare_choice
    · apply Hoare_assume_bind
      intro hlohi
      omega
    · apply Hoare_assume_bind
      intro _
      exact Hoare_ret (P a) a P (fun _ => id)

theorem Hoare_forset {Sigma A : Type}
    (P : (A -> Prop) -> Sigma -> Prop) (uPred : A -> Prop)
    (body : A -> program Sigma Unit)
    (ProperP : Proper (Sets.equiv ==> Eq ==> Iff) P) :
    (forall done a,
      (forall x, done x -> uPred x) ->
      Hoare (fun s => P done s /\ uPred a /\ Not (done a))
        (body a) (fun _ s => P (fun x => done x \/ x = a) s)) ->
    Hoare (fun s => P (fun _ => False) s) (forset uPred body)
      (fun _ s => P uPred s) := by
  intro hbody
  apply Hoare_cons_pre
    (fun s => P (fun a => uPred a /\ Not (uPred a)) s /\
      forall x, uPred x -> uPred x)
    (fun s => P (fun _ => False) s) (forset uPred body)
    (fun _ s => P uPred s)
  · intro s hp
    have heq : Sets.equiv
        (fun a => uPred a /\ Not (uPred a)) (fun _ : A => False) := by
      intro x
      constructor
      · intro h; exact h.2 h.1
      · intro h; exact False.elim h
    exact ⟨(ProperP.proper _ _ heq s s rfl).mpr hp, fun _ h => h⟩
  · unfold forset
    apply Hoare_BW_fix (forset_f body)
      (fun todo s =>
        P (fun a => uPred a /\ Not (todo a)) s /\
        forall x, todo x -> uPred x)
      (fun _ _ s => P uPred s) uPred
    intro W hW todo
    unfold forset_f
    apply Hoare_choice
    · apply Hoare_bind
        (fun s => P (fun a => uPred a /\ Not (todo a)) s /\
          forall x, todo x -> uPred x)
        (fun a s => todo a /\
          (P (fun x => uPred x /\ Not (todo x)) s /\
            forall x, todo x -> uPred x))
        (fun _ s => P uPred s) (get (fun _ a => todo a))
      · exact Hoare_get _ _
      · intro a
        apply Hoare_implies
          (fun s => todo a /\
            (P (fun x => uPred x /\ Not (todo x)) s /\
              forall x, todo x -> uPred x))
          (fun s => todo a /\
            (P (fun x => uPred x /\ Not (todo x)) s /\
              forall x, todo x -> uPred x))
          (todo a /\ forall x, todo x -> uPred x) _ _
        · rintro _ hs
          exact ⟨⟨hs.1, hs.2.2⟩, hs⟩
        · rintro ⟨ha, hsub⟩
          apply Hoare_bind
            (fun s => todo a /\
              (P (fun x => uPred x /\ Not (todo x)) s /\
                forall x, todo x -> uPred x))
            (fun _ s => P
              (fun x => (uPred x /\ Not (todo x)) \/ x = a) s)
            (fun _ s => P uPred s) (body a)
          · apply Hoare_cons_pre
              (fun s => P (fun x => uPred x /\ Not (todo x)) s /\
                uPred a /\ Not (uPred a /\ Not (todo a)))
              (fun s => todo a /\
                (P (fun x => uPred x /\ Not (todo x)) s /\
                  forall x, todo x -> uPred x))
              (body a) _
            · rintro s ⟨_, hp, _⟩
              exact ⟨hp, hsub a ha, fun hdone => hdone.2 ha⟩
            · exact hbody (fun x => uPred x /\ Not (todo x)) a
                (fun _ h => h.1)
          · intro _
            apply Hoare_cons_pre
              (fun s =>
                P (fun x => uPred x /\ Not (todo x /\ x ≠ a)) s /\
                forall x, todo x /\ x ≠ a -> uPred x)
              (fun s => P
                (fun x => (uPred x /\ Not (todo x)) \/ x = a) s)
              (W (fun x => todo x /\ x ≠ a)) (fun _ s => P uPred s)
            · intro s hp
              have heq : Sets.equiv
                  (fun x => uPred x /\ Not (todo x /\ x ≠ a))
                  (fun x => (uPred x /\ Not (todo x)) \/ x = a) := by
                intro x
                constructor
                · rintro ⟨hu, hnot⟩
                  by_cases ht : todo x
                  · right
                    apply Classical.byContradiction
                    intro hxa
                    exact hnot ⟨ht, hxa⟩
                  · left; exact ⟨hu, ht⟩
                · intro hx
                  rcases hx with ⟨hu, hnt⟩ | hxa
                  · exact ⟨hu, fun h => hnt h.1⟩
                  · subst x
                    exact ⟨hsub a ha, fun h => h.2 rfl⟩
              exact ⟨(ProperP.proper _ _ heq s s rfl).mpr hp,
                fun x h => hsub x h.1⟩
            · exact hW (fun x => todo x /\ x ≠ a)
    · apply Hoare_assume_bind
      intro hempty
      apply Hoare_ret
      intro s hs
      have heq : Sets.equiv (fun x => uPred x /\ Not (todo x)) uPred := by
        intro x
        constructor
        · exact fun h => h.1
        · intro hu; exact ⟨hu, hempty x⟩
      exact (ProperP.proper _ _ heq s s rfl).mp hs.1

def weakestpre {Sigma A : Type} (c : program Sigma A)
    (Q : A -> Sigma -> Prop) : Sigma -> Prop :=
  fun s => Not (c.err s) /\ forall r s', c.nrm s r s' -> Q r s'

def valid_angelic_triple {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) : Prop :=
  forall s1, P s1 -> exists a s2, c.nrm s1 a s2 /\ Q a s2

theorem wp_spec {Sigma A : Type} (c : program Sigma A) (s1 s2 : Sigma) (a : A) :
    c.nrm s1 a s2 -> forall Q, weakestpre c Q s1 -> Q a s2 := by
  intro hn Q hwp
  exact hwp.2 a s2 hn

theorem wp_spec_err {Sigma A : Type} (c : program Sigma A) (s1 : Sigma)
    (Q : A -> Sigma -> Prop) :
    weakestpre c Q s1 -> Not (c.err s1) := by
  exact fun h => h.1

theorem wp_self {Sigma A : Type} (c : program Sigma A) (s : Sigma) :
    Not (c.err s) -> weakestpre c (fun a s' => c.nrm s a s') s := by
  intro he
  exact ⟨he, fun _ _ hn => hn⟩

theorem wp_Hoare {Sigma A : Type} (c : program Sigma A)
    (Q : A -> Sigma -> Prop) : Hoare (weakestpre c Q) c Q := by
  exact ⟨fun a s1 s2 h hn => h.2 a s2 hn,
    fun s h he => h.1 he⟩

theorem wp_Hoare_iff {Sigma A : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) (c : program Sigma A) :
    (forall s, P s -> weakestpre c Q s) <-> Hoare P c Q := by
  constructor
  · intro h
    exact Hoare_cons_pre (weakestpre c Q) P c Q h (wp_Hoare c Q)
  · rintro ⟨hn, he⟩ s hp
    exact ⟨fun herr => he s hp herr, fun a s' hrun => hn a s s' hp hrun⟩

theorem wp_progequiv {Sigma A : Type} (c1 c2 : program Sigma A)
    (Q : A -> Sigma -> Prop) :
    equiv c2 c1 -> Sets.equiv (weakestpre c1 Q) (weakestpre c2 Q) := by
  intro he s
  constructor <;> rintro ⟨herr, hn⟩
  · exact ⟨fun h => herr ((he.errequiv s).mp h),
      fun a s' h => hn a s' ((he.nrmequiv s a s').mp h)⟩
  · exact ⟨fun h => herr ((he.errequiv s).mpr h),
      fun a s' h => hn a s' ((he.nrmequiv s a s').mpr h)⟩

theorem wp_progrefine {Sigma A : Type} (c1 c2 : program Sigma A)
    (Q : A -> Sigma -> Prop) :
    (forall s a s', c2.nrm s a s' -> c1.nrm s a s') ->
    (forall s, c2.err s -> c1.err s) ->
    forall s, weakestpre c1 Q s -> weakestpre c2 Q s := by
  rintro hn he s ⟨hnoerr, hpost⟩
  exact ⟨fun herr => hnoerr (he s herr),
    fun a s' hrun => hpost a s' (hn s a s' hrun)⟩

theorem wp_conseq {Sigma A : Type} (c : program Sigma A)
    (Q1 Q2 : A -> Sigma -> Prop) :
    (forall a s, Q1 a s -> Q2 a s) ->
    forall s, weakestpre c Q1 s -> weakestpre c Q2 s := by
  rintro h s ⟨he, hn⟩
  exact ⟨he, fun a s' hrun => h a s' (hn a s' hrun)⟩

theorem wp_bind {Sigma A B : Type} (f : program Sigma A)
    (g : A -> program Sigma B) (Q : B -> Sigma -> Prop) :
    Sets.equiv (weakestpre (MonadErr.bind f g) Q)
      (weakestpre f (fun a => weakestpre (g a) Q)) := by
  intro s
  constructor
  · rintro ⟨he, hn⟩
    constructor
    · intro hferr
      exact he (Or.inl hferr)
    · intro a s' hfn
      constructor
      · intro hgerr
        exact he (Or.inr ⟨a, s', hfn, hgerr⟩)
      · intro b s'' hgn
        exact hn b s'' ⟨a, s', hfn, hgn⟩
  · rintro ⟨he, hn⟩
    constructor
    · rintro (hferr | ⟨a, s', hfn, hgerr⟩)
      · exact he hferr
      · exact (hn a s' hfn).1 hgerr
    · rintro b s'' ⟨a, s', hfn, hgn⟩
      exact (hn a s' hfn).2 b s'' hgn

theorem wp_ret {Sigma A : Type} (a : A) (Q : A -> Sigma -> Prop) :
    Sets.equiv (weakestpre (MonadErr.ret a) Q) (Q a) := by
  intro s
  constructor
  · intro h
    exact h.2 a s ⟨rfl, rfl⟩
  · intro h
    constructor
    · exact fun he => False.elim he
    · rintro r s' ⟨rfl, rfl⟩; exact h

theorem wp_choice {Sigma A : Type} (c1 c2 : program Sigma A)
    (Q : A -> Sigma -> Prop) :
    Sets.equiv (weakestpre (choice c1 c2) Q)
      (fun s => weakestpre c1 Q s /\ weakestpre c2 Q s) := by
  intro s
  constructor
  · rintro ⟨he, hn⟩
    exact ⟨⟨fun h => he (Or.inl h), fun a s' h => hn a s' (Or.inl h)⟩,
      ⟨fun h => he (Or.inr h), fun a s' h => hn a s' (Or.inr h)⟩⟩
  · rintro ⟨⟨he1, hn1⟩, ⟨he2, hn2⟩⟩
    exact ⟨fun h => h.elim he1 he2,
      fun a s' h => h.elim (hn1 a s') (hn2 a s')⟩

theorem wp_assume_coqprop {Sigma : Type} (P : Prop)
    (Q : Unit -> Sigma -> Prop) :
    P -> Sets.equiv (weakestpre (testPure P) Q) (Q ()) := by
  intro hp s
  constructor
  · intro h; exact h.2 () s ⟨rfl, hp⟩
  · intro h
    exact ⟨fun he => False.elim he,
      fun r s' hn => by rcases hn with ⟨rfl, _⟩; exact h⟩

theorem wp_assume {Sigma : Type} (P : Sigma -> Prop)
    (Q : Unit -> Sigma -> Prop) :
    Sets.equiv (weakestpre (test P) Q) (fun s => P s -> Q () s) := by
  intro s
  constructor
  · intro h hp; exact h.2 () s ⟨rfl, hp⟩
  · intro h
    exact ⟨fun he => False.elim he,
      fun r s' hn => by rcases hn with ⟨rfl, hp⟩; exact h hp⟩

theorem wp_any {Sigma A : Type} (Q : A -> Sigma -> Prop) :
    Sets.equiv (weakestpre (any A) Q) (fun s => forall a, Q a s) := by
  intro s
  constructor
  · intro h a; exact h.2 a s rfl
  · intro h
    exact ⟨fun he => False.elim he,
      fun a s' hs => by subst s'; exact h a⟩

theorem wp_assert {Sigma : Type} (P : Prop) (Q : Unit -> Sigma -> Prop) :
    Sets.equiv (weakestpre (assert P) Q) (fun s => P /\ Q () s) := by
  intro s
  constructor
  · intro h
    have hp : P := Classical.byContradiction h.1
    exact ⟨hp, h.2 () s ⟨rfl, hp⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨fun hnp => hnp hp,
      fun r s' hn => by rcases hn with ⟨rfl, _⟩; exact hq⟩

theorem wp_assertS {Sigma : Type} (P : Sigma -> Prop)
    (Q : Unit -> Sigma -> Prop) :
    Sets.equiv (weakestpre (assertS P) Q) (fun s => P s /\ Q () s) := by
  intro s
  constructor
  · intro h
    have hp : P s := Classical.byContradiction h.1
    exact ⟨hp, h.2 () s ⟨rfl, hp⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨fun hnp => hnp hp,
      fun r s' hn => by rcases hn with ⟨rfl, _⟩; exact hq⟩

theorem wp_get {Sigma A : Type} (Pa : Sigma -> A -> Prop)
    (Q : A -> Sigma -> Prop) :
    Sets.equiv (weakestpre (get Pa) Q)
      (fun s => forall a, Pa s a -> Q a s) := by
  intro s
  constructor
  · intro h a ha; exact h.2 a s ⟨ha, rfl⟩
  · intro h
    exact ⟨fun he => False.elim he,
      fun a s' hn => by rcases hn with ⟨ha, rfl⟩; exact h a ha⟩

theorem wp_get' {Sigma A : Type} (f : Sigma -> A)
    (Q : A -> Sigma -> Prop) :
    Sets.equiv (weakestpre (get' f) Q)
      (fun s => forall a, a = f s -> Q a s) := by
  simpa [get'] using wp_get (Sigma := Sigma) (A := A)
    (fun s a => a = f s) Q

theorem wp_update {Sigma : Type} (P : Sigma -> Sigma -> Prop)
    (Q : Unit -> Sigma -> Prop) :
    Sets.equiv (weakestpre (update P) Q)
      (fun s => forall s', P s s' -> Q () s') := by
  intro s
  constructor
  · intro h s' hp; exact h.2 () s' hp
  · intro h
    exact ⟨fun he => False.elim he,
      fun r s' hp => by cases r; exact h s' hp⟩

theorem wp_update' {Sigma : Type} (f : Sigma -> Sigma)
    (Q : Unit -> Sigma -> Prop) :
    Sets.equiv (weakestpre (update' f) Q)
      (fun s => forall s', s' = f s -> Q () s') := by
  simpa [update'] using wp_update (Sigma := Sigma)
    (fun s s' => s' = f s) Q

macro "hoare_bind" h:term : tactic =>
  `(tactic|
    apply Hoare_bind <;>
      first | exact $h | intro)

macro "hoare_bind'" h:term : tactic =>
  `(tactic|
    apply Hoare_bind <;>
      first | exact $h | (simp <;> try intro _))

syntax "hoare_conj" : tactic

namespace HoareConjTactic

open Lean Meta Elab Tactic

private def stripPostLambdas (e : Expr) : Expr :=
  let e := e.consumeMData
  let body1 := match e with
    | .lam _ _ body _ => body.consumeMData
    | _ => e
  match body1 with
  | .lam _ _ body _ => body.consumeMData
  | _ => body1

private def hasVisibleConjunction : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.consumeMData.getAppFn.isConstOf ``Hoare do return false
  let args := target.consumeMData.getAppArgs
  unless args.size >= 1 do return false
  let postBody := stripPostLambdas args[args.size - 1]!
  return postBody.getAppFn.isConstOf ``And

partial def run : TacticM Unit := do
  unless ← hasVisibleConjunction do return
  evalTactic (← `(tactic| apply Hoare_conj))
  let goals ← getGoals
  match goals with
  | left :: right :: rest =>
      setGoals [right]
      run
      let rightGoals ← getGoals
      setGoals (left :: rightGoals ++ rest)
  | _ => throwError "hoare_conj: Hoare_conj did not produce two subgoals"

end HoareConjTactic

elab_rules : tactic
  | `(tactic| hoare_conj) => HoareConjTactic.run

macro "hoare_intros" : tactic =>
  `(tactic| (apply Hoare_pre_ex; intro))

macro "stateless_intros" : tactic =>
  `(tactic|
    (repeat first | apply Hoare_stateless | apply Hoare_stateless') <;>
      intro)

macro "monad_law" : tactic =>
  `(tactic|
    (repeat first
        | rel_rw [bind_assoc]
        | rel_rw [bind_ret_l]
        | rel_rw [bind_ret_r]) <;>
      try exact AUXLib.Equivalence.refl _)

macro "intro_bound" : tactic =>
  `(tactic|
    (repeat first | unfold Sets.equiv | intro) <;>
      simp only [Sets.lift_SETS, Sets.Prop_SETS])

syntax "monad_equiv" : tactic
syntax "__err_monad_equiv_match" : tactic
syntax "__err_monad_equiv_struct" : tactic
syntax "__err_match_bind_equiv" : tactic

namespace MonadEquivTactic

open Lean Meta Elab Tactic

private def containsFVar (target : FVarId) : Expr -> Bool
  | .fvar id => id == target
  | .app fn arg => containsFVar target fn || containsFVar target arg
  | .lam _ type body _ => containsFVar target type || containsFVar target body
  | .forallE _ type body _ => containsFVar target type || containsFVar target body
  | .letE _ type value body _ =>
      containsFVar target type || containsFVar target value ||
        containsFVar target body
  | .mdata _ body => containsFVar target body
  | .proj _ _ body => containsFVar target body
  | _ => false

private def splitCntOrBrk : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if type.consumeMData.getAppFn.isConstOf ``MonadLib.CntOrBrk &&
          containsFVar localDecl.fvarId target then
        let subgoals ← goal.cases localDecl.fvarId
        replaceMainGoal (subgoals.toList.map (·.mvarId))
        return
  throwError "monad_equiv: no CntOrBrk match discriminant found"

private def evalIfGoalsRemain (tactic : Syntax) : TacticM Unit := do
  pruneSolvedGoals
  unless (← getGoals).isEmpty do
    evalTactic tactic

private def closeReflexiveEquiv : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let args := target.getAppArgs
  unless args.size >= 2 do
    return false
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  unless ← isDefEq lhs rhs do
    return false
  let proof ← mkAppM ``AUXLib.Equivalence.refl #[lhs]
  goal.assign proof
  replaceMainGoal []
  return true

private def run : TacticM Unit := do
  let closedInitially ← closeReflexiveEquiv
  if closedInitially then
    return
  evalIfGoalsRemain (← `(tactic| try unfold continue_case))
  evalIfGoalsRemain (← `(tactic| try unfold break_case))
  pruneSolvedGoals
  let closedAfterUnfold ← closeReflexiveEquiv
  if (← getGoals).isEmpty || closedAfterUnfold then
    return
  evalIfGoalsRemain (← `(tactic|
    first
      | __err_monad_equiv_struct
      | (err_prog_nf <;> __err_monad_equiv_struct)))

end MonadEquivTactic

elab_rules : tactic
  | `(tactic| __err_monad_equiv_match) => MonadEquivTactic.splitCntOrBrk
  | `(tactic| monad_equiv) => MonadEquivTactic.run

macro_rules
  | `(tactic| __err_monad_equiv_struct) =>
      `(tactic|
        first
          | exact AUXLib.Equivalence.refl _
          | assumption
          | (__err_monad_equiv_match <;> __err_monad_equiv_struct)
          | (apply bind_equiv
              · __err_monad_equiv_struct
              · intro <;> __err_monad_equiv_struct)
          | (intro <;> __err_monad_equiv_struct)
          | rfl)
  | `(tactic| __err_match_bind_equiv) =>
      `(tactic|
        (apply bind_equiv
         · exact AUXLib.Equivalence.refl _
         · intro
           apply bind_equiv
           · exact AUXLib.Equivalence.refl _
           · intro
             apply bind_equiv
             · __err_monad_equiv_match <;> exact AUXLib.Equivalence.refl _
             · intro
               __err_monad_equiv_match <;> exact AUXLib.Equivalence.refl _))

syntax "err_hoare_step" : tactic

syntax "__err_hoare_close" : tactic

macro_rules
  | `(tactic| __err_hoare_close) =>
      `(tactic| first
        | assumption
        | solve_by_elim
        | rfl
        | trivial
        | (constructor <;> __err_hoare_close))

private theorem hoare_result_case_tactic_rule {A Sigma : Type}
    (P : Sigma -> Prop) (Q : A -> Sigma -> Prop) (a : A) :
    (forall s, P s -> Q a s) ->
      Hoare P
        ({ nrm := fun s1 r s2 => s1 = s2 /\ r = a
           err := fun _ => False } : program Sigma A) Q := by
  intro h
  constructor
  · rintro r s1 s2 hp ⟨rfl, rfl⟩
    exact h s1 hp
  · intro _ _ he
    exact False.elim he

theorem hoare_bind_assoc_tactic_rule {A B C Sigma : Type}
    (P : Sigma -> Prop) (c0 : program Sigma A)
    (c1 : A -> program Sigma B) (c2 : B -> program Sigma C)
    (Q : C -> Sigma -> Prop) :
    Hoare P (MonadErr.bind c0 (fun a => MonadErr.bind (c1 a) c2)) Q ->
      Hoare P (MonadErr.bind (MonadErr.bind c0 c1) c2) Q := by
  intro h
  exact Hoare_proequiv _ _ P Q
    (AUXLib.Equivalence.symm _ _ (bind_assoc c0 c1 c2)) h

theorem hoare_bind_choice_tactic_rule {A B Sigma : Type}
    (P : Sigma -> Prop) (c0 c1 : program Sigma A)
    (c2 : A -> program Sigma B) (Q : B -> Sigma -> Prop) :
    Hoare P (MonadErr.bind c0 c2) Q ->
    Hoare P (MonadErr.bind c1 c2) Q ->
      Hoare P (MonadErr.bind (choice c0 c1) c2) Q := by
  intro h0 h1
  have hchoice := Hoare_choice P
    (MonadErr.bind c0 c2) (MonadErr.bind c1 c2) Q h0 h1
  exact Hoare_proequiv _ _ P Q
    (AUXLib.Equivalence.symm _ _ (bind_choice_equiv c0 c1 c2)) hchoice

theorem hoare_bind_ret_l_tactic_rule {A B Sigma : Type}
    (P : Sigma -> Prop) (a : A) (c : A -> program Sigma B)
    (Q : B -> Sigma -> Prop) :
    Hoare P (c a) Q -> Hoare P (MonadErr.bind (MonadErr.ret a) c) Q := by
  intro h
  exact Hoare_proequiv _ _ P Q
    (AUXLib.Equivalence.symm _ _ (bind_ret_l a c)) h

namespace ErrHoareStepTactic

open Lean Meta Elab Tactic

private def hasHead (e : Expr) (decl : Name) : Bool :=
  e.consumeMData.getAppFn.isConstOf decl

private def programOfHoare? (target : Expr) : Option Expr := do
  guard (hasHead target ``MonadLib.Hoare)
  let args := target.consumeMData.getAppArgs
  guard (args.size >= 2)
  return args[args.size - 2]!

private def bindSource? (program : Expr) : Option Expr := do
  guard (hasHead program ``MonadLib.bind ||
    hasHead program ``MonadLib.MonadErr.bind)
  let args := program.consumeMData.getAppArgs
  guard (args.size >= 2)
  return args[args.size - 2]!

private def exposeProgramHead (program : Expr) : MetaM Expr := do
  let head := program.consumeMData.getAppFn
  if head.isConstOf ``MonadLib.bind ||
      head.isConstOf ``MonadLib.MonadErr.bind ||
      head.isConstOf ``MonadLib.choice ||
      head.isConstOf ``MonadLib.ret ||
      head.isConstOf ``MonadLib.MonadErr.ret ||
      head.isConstOf ``MonadLib.break ||
      head.isConstOf ``MonadLib.continue ||
      head.isConstOf ``MonadLib.continue_case ||
      head.isConstOf ``MonadLib.break_case then
    return program
  return (← unfoldDefinition? program).getD program

def run : TacticM Unit := withMainContext do
  evalTactic (← `(tactic| try simp only))
  let target ← instantiateMVars (← getMainTarget)
  let some program0 := programOfHoare? target |
    throwError "hoare_step: expected a Hoare goal"
  let program ← exposeProgramHead program0
  if let some source := bindSource? program then
    if hasHead source ``MonadLib.bind ||
        hasHead source ``MonadLib.MonadErr.bind then
      evalTactic (← `(tactic| apply hoare_bind_assoc_tactic_rule))
    else if hasHead source ``MonadLib.assert then
      evalTactic (← `(tactic|
        apply Hoare_assert_bind <;>
          first
          | (intro _ _; try __err_hoare_close)
          | (intro _; try __err_hoare_close)))
    else if hasHead source ``MonadLib.testPure then
      evalTactic (← `(tactic|
        apply Hoare_assume_bind; intro _; try __err_hoare_close))
    else if hasHead source ``MonadLib.test then
      evalTactic (← `(tactic|
        apply Hoare_assumeS_bind <;> try __err_hoare_close))
    else if hasHead source ``MonadLib.choice then
      evalTactic (← `(tactic| apply hoare_bind_choice_tactic_rule))
    else if hasHead source ``MonadLib.ret ||
        hasHead source ``MonadLib.MonadErr.ret then
      evalTactic (← `(tactic|
        apply hoare_bind_ret_l_tactic_rule <;> try __err_hoare_close))
    else if hasHead source ``MonadLib.break then
      evalTactic (← `(tactic|
        unfold MonadLib.break
        apply hoare_bind_ret_l_tactic_rule))
    else if hasHead source ``MonadLib.continue then
      evalTactic (← `(tactic|
        unfold MonadLib.continue
        apply hoare_bind_ret_l_tactic_rule))
    else
      evalTactic (← `(tactic| apply Hoare_bind))
  else if hasHead program ``MonadLib.choice then
    evalTactic (← `(tactic|
      apply Hoare_choice <;> try __err_hoare_close))
  else if hasHead program ``MonadLib.ret ||
      hasHead program ``MonadLib.MonadErr.ret then
    evalTactic (← `(tactic|
      apply Hoare_ret; intro _ _; try __err_hoare_close))
  else if hasHead program ``MonadLib.break then
    evalTactic (← `(tactic| unfold MonadLib.break; apply Hoare_ret))
  else if hasHead program ``MonadLib.continue then
    evalTactic (← `(tactic| unfold MonadLib.continue; apply Hoare_ret))
  else if hasHead program ``MonadLib.continue_case ||
      hasHead program ``MonadLib.break_case then
    let args := program.consumeMData.getAppArgs
    let result := args[args.size - 1]!
    if hasHead program ``MonadLib.continue_case then
      if hasHead result ``MonadLib.CntOrBrk.by_continue then
        evalTactic (← `(tactic|
          apply Hoare_cnt_cnt; intro _ _; try __err_hoare_close))
      else if hasHead result ``MonadLib.CntOrBrk.by_break then
        evalTactic (← `(tactic| apply Hoare_cnt_brk))
      else
        throwError "hoare_step: continue_case argument is not constructor-headed"
    else if hasHead result ``MonadLib.CntOrBrk.by_break then
      evalTactic (← `(tactic|
        apply Hoare_brk_brk; intro _ _; try __err_hoare_close))
    else if hasHead result ``MonadLib.CntOrBrk.by_continue then
      evalTactic (← `(tactic| apply Hoare_brk_cnt))
    else
      throwError "hoare_step: break_case argument is not constructor-headed"
  else
    throwError "hoare_step: unsupported program root: {program}"

end ErrHoareStepTactic

elab_rules : tactic
  | `(tactic| err_hoare_step) => ErrHoareStepTactic.run

syntax "err_hoare_auto" : tactic

private theorem hoare_assertS_tactic_rule {A Sigma : Type}
    (P Q : Sigma -> Prop) (c : program Sigma A)
    (R : A -> Sigma -> Prop) :
    (forall s, P s -> Q s) -> Hoare P c R ->
      Hoare P (assertS Q ;; c) R := by
  intro hpq hc
  exact (Hoare_assertS_bind P Q c R hpq).mpr hc

namespace ErrHoareAutoTactic

open Lean Meta Elab Tactic

private def hasHead (e : Expr) (decl : Name) : Bool :=
  e.consumeMData.getAppFn.isConstOf decl

private def programOfHoare? (target : Expr) : Option Expr := do
  guard (hasHead target ``MonadLib.Hoare)
  let args := target.consumeMData.getAppArgs
  guard (args.size >= 2)
  return args[args.size - 2]!

private def bindSource? (program : Expr) : Option Expr := do
  guard (hasHead program ``MonadLib.bind ||
    hasHead program ``MonadLib.MonadErr.bind)
  let args := program.consumeMData.getAppArgs
  guard (args.size >= 2)
  return args[args.size - 2]!

private def exposeProgramHead (program : Expr) : MetaM Expr := do
  let head := program.consumeMData.getAppFn
  if head.isConstOf ``MonadLib.bind ||
      head.isConstOf ``MonadLib.MonadErr.bind ||
      head.isConstOf ``MonadLib.choice ||
      head.isConstOf ``MonadLib.ret ||
      head.isConstOf ``MonadLib.MonadErr.ret ||
      head.isConstOf ``MonadLib.break ||
      head.isConstOf ``MonadLib.continue ||
      head.isConstOf ``MonadLib.continue_case ||
      head.isConstOf ``MonadLib.break_case then
    return program
  return (← unfoldDefinition? program).getD program

private def splitCntOrBrkLocal : TacticM Bool := withMainContext do
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if type.consumeMData.getAppFn.isConstOf ``MonadLib.CntOrBrk then
        let subgoals ← (← getMainGoal).cases localDecl.fvarId
        replaceMainGoal (subgoals.toList.map (·.mvarId))
        evalTactic (← `(tactic| all_goals try err_hoare_auto))
        return true
  return false

private def runFallback (target : Expr) : TacticM Unit := do
  if target.consumeMData.isForall then
    evalTactic (← `(tactic| intro; try err_hoare_auto))
  else
    evalTactic (← `(tactic|
      try (first
        | assumption
        | trivial
        | __err_hoare_close)))

def run : TacticM Unit := withMainContext do
  evalTactic (← `(tactic| try simp only))
  let target ← instantiateMVars (← getMainTarget)
  let some program0 := programOfHoare? target | return ← runFallback target
  let program ← exposeProgramHead program0
  if let some source := bindSource? program then
    if hasHead source ``MonadLib.bind ||
        hasHead source ``MonadLib.MonadErr.bind then
      evalTactic (← `(tactic|
        apply hoare_bind_assoc_tactic_rule <;> try err_hoare_auto))
    else if hasHead source ``MonadLib.assert then
      evalTactic (← `(tactic|
        apply Hoare_assert_bind <;>
          try err_hoare_auto <;> try __err_hoare_close))
    else if hasHead source ``MonadLib.testPure then
      evalTactic (← `(tactic|
        apply Hoare_assume_bind <;> try err_hoare_auto))
    else if hasHead source ``MonadLib.test then
      evalTactic (← `(tactic|
        apply Hoare_assumeS_bind <;> try err_hoare_auto))
    else if hasHead source ``MonadLib.assertS then
      evalTactic (← `(tactic|
        apply hoare_assertS_tactic_rule <;>
          try err_hoare_auto <;> try __err_hoare_close))
    else if hasHead source ``MonadLib.choice then
      evalTactic (← `(tactic|
        apply hoare_bind_choice_tactic_rule <;> try err_hoare_auto))
    else if hasHead source ``MonadLib.ret ||
        hasHead source ``MonadLib.MonadErr.ret then
      evalTactic (← `(tactic|
        apply hoare_bind_ret_l_tactic_rule <;> try err_hoare_auto))
    else if hasHead source ``MonadLib.break then
      evalTactic (← `(tactic|
        unfold MonadLib.break;
        apply hoare_bind_ret_l_tactic_rule <;> try err_hoare_auto))
    else if hasHead source ``MonadLib.continue then
      evalTactic (← `(tactic|
        unfold MonadLib.continue;
        apply hoare_bind_ret_l_tactic_rule <;> try err_hoare_auto))
    else
      evalTactic (← `(tactic| try assumption))
  else if hasHead program ``MonadLib.choice then
    evalTactic (← `(tactic|
      apply Hoare_choice <;> try err_hoare_auto))
  else if hasHead program ``MonadLib.ret ||
      hasHead program ``MonadLib.MonadErr.ret then
    evalTactic (← `(tactic|
      apply Hoare_ret; intro _ _; try __err_hoare_close))
  else if hasHead program ``MonadLib.break then
    evalTactic (← `(tactic| unfold MonadLib.break; try err_hoare_auto))
  else if hasHead program ``MonadLib.continue then
    evalTactic (← `(tactic| unfold MonadLib.continue; try err_hoare_auto))
  else if hasHead program ``MonadLib.continue_case then
    let args := program.consumeMData.getAppArgs
    let result := args[args.size - 1]!
    if hasHead result ``MonadLib.CntOrBrk.by_continue then
      evalTactic (← `(tactic|
        apply Hoare_cnt_cnt; intro _ _; try __err_hoare_close))
    else if hasHead result ``MonadLib.CntOrBrk.by_break then
      evalTactic (← `(tactic| apply Hoare_cnt_brk))
    else
      evalTactic (← `(tactic|
        apply hoare_result_case_tactic_rule;
          intro _ _; try __err_hoare_close))
  else if hasHead program ``MonadLib.break_case then
    let args := program.consumeMData.getAppArgs
    let result := args[args.size - 1]!
    if hasHead result ``MonadLib.CntOrBrk.by_break then
      evalTactic (← `(tactic|
        apply Hoare_brk_brk; intro _ _; try __err_hoare_close))
    else if hasHead result ``MonadLib.CntOrBrk.by_continue then
      evalTactic (← `(tactic| apply Hoare_brk_cnt))
    else
      evalTactic (← `(tactic|
        apply hoare_result_case_tactic_rule;
          intro _ _; try __err_hoare_close))
  else
    unless ← splitCntOrBrkLocal do
      evalTactic (← `(tactic|
        try (first
          | assumption
          | __err_hoare_close
          | (simp only [Hoare, continue_case, break_case, ProgramPO.bot]; done))))

end ErrHoareAutoTactic

elab_rules : tactic
  | `(tactic| err_hoare_auto) => ErrHoareAutoTactic.run

macro "hoare_auto_s" : tactic =>
  `(tactic| err_hoare_auto)

private theorem Hoare_proequiv_from {A Sigma : Type}
    {c1 c2 : program Sigma A} {P : Sigma -> Prop}
    {Q : A -> Sigma -> Prop} :
    Hoare P c1 Q -> equiv c1 c2 -> Hoare P c2 Q := by
  intro h he
  exact Hoare_proequiv c1 c2 P Q he h

syntax "hoare_apply " term:max : tactic

elab_rules : tactic
  | `(tactic| hoare_apply $h:term) => do
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| apply Hoare_proequiv_from $h))
      Lean.Elab.Tactic.pruneSolvedGoals
      unless (← Lean.Elab.Tactic.getGoals).isEmpty do
        Lean.Elab.Tactic.evalTactic (← `(tactic| monad_equiv))

macro "hoare_cons_pre" h:term : tactic =>
  `(tactic|
    apply Hoare_cons_pre <;>
      first | exact $h | try simp_all)

macro "hoare_cons_post" h:term : tactic =>
  `(tactic|
    apply Hoare_cons_post <;>
      first | exact $h | try simp_all)

private theorem hoare_cons_tactic_rule {A Sigma : Type}
    (P P' : Sigma -> Prop) (c : program Sigma A)
    (Q Q' : A -> Sigma -> Prop) :
    (forall s, P' s -> P s) ->
    (forall a s, Q a s -> Q' a s) ->
    Hoare P c Q -> Hoare P' c Q' := by
  intro hpre hpost h
  exact Hoare_cons_pre P P' c Q' hpre
    (Hoare_cons_post P c Q Q' hpost h)

macro "hoare_cons" h:term : tactic =>
  `(tactic|
    apply hoare_cons_tactic_rule <;>
      first | exact $h | (repeat intro; try simp_all))

syntax "err_hoare_fix_nolv_auto " term:max : tactic
syntax "hoare_fix_lv_auto " term:max term:max term:max : tactic
syntax "hoare_fix_lv_auto_conj " term:max term:max term:max : tactic
syntax "hoare_fix_lv_auto_conj' " term:max term:max term:max : tactic

namespace HoareFixTactic

open Lean Meta Elab Tactic

private structure GoalData where
  pre : Expr
  fn : Expr
  arg : Expr
  post : Expr

private def readGoal : TacticM (MVarId × GoalData) := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.consumeMData.getAppFn.isConstOf ``Hoare do
    throwError "hoare_fix_*: expected a Hoare goal"
  let hoareArgs := target.getAppArgs
  unless hoareArgs.size >= 3 do
    throwError "hoare_fix_*: malformed Hoare goal"
  let pre := hoareArgs[hoareArgs.size - 3]!
  let program := hoareArgs[hoareArgs.size - 2]!
  let post := hoareArgs[hoareArgs.size - 1]!
  unless program.consumeMData.getAppFn.isConstOf ``FP.BW_fix do
    throwError "hoare_fix_*: expected BW_fix as the program"
  let fixArgs := program.getAppArgs
  unless fixArgs.size >= 2 do
    throwError "hoare_fix_*: malformed BW_fix application"
  return (goal, {
    pre
    fn := fixArgs[fixArgs.size - 2]!
    arg := fixArgs[fixArgs.size - 1]!
    post
  })

private def checkTypeArgument (stx : Lean.Syntax) (expected : Expr) : TacticM Unit :=
    withMainContext do
  let level ← mkFreshLevelMVar
  let supplied ← elabTerm stx (some (mkSort level))
  unless ← isDefEq supplied expected do
    throwError "hoare_fix_*: supplied type does not match the BW_fix argument type"

private def abstractOne (name : Name) (type term body : Expr) : Expr :=
  mkLambda name BinderInfo.default type (body.abstract #[term])

private def abstractTwo (name1 name2 : Name) (type1 type2 term1 term2 body : Expr) : Expr :=
  mkLambda name1 BinderInfo.default type1 <|
    mkLambda name2 BinderInfo.default type2 (body.abstract #[term1, term2])

private def runNoLogicVar (aTypeSyntax : Lean.Syntax) : TacticM Unit := do
  let (goal, data) ← readGoal
  withMainContext do
    let aType ← inferType data.arg
    checkTypeArgument aTypeSyntax aType
    let preFamily := abstractOne `a aType data.arg data.pre
    let postFamily := abstractOne `a aType data.arg data.post
    let proof ← mkAppM ``Hoare_BW_fix
      #[data.fn, preFamily, postFamily, data.arg]
    replaceMainGoal (← goal.apply proof)

private def runLogicVar (aTypeSyntax cTypeSyntax cSyntax : Lean.Syntax)
    (conj : Bool) : TacticM Unit := do
  let (goal, data) ← readGoal
  withMainContext do
    let aType ← inferType data.arg
    checkTypeArgument aTypeSyntax aType
    let level ← mkFreshLevelMVar
    let cType ← elabTerm cTypeSyntax (some (mkSort level))
    let c ← elabTerm cSyntax (some cType)
    let preFamily := abstractTwo `a `c aType cType data.arg c data.pre
    let postFamily := abstractTwo `a `c aType cType data.arg c data.post
    let theoremName := if conj then ``Hoare_BW_fix_logicv_conj' else ``Hoare_BW_fix_logicv
    let proof ← mkAppM theoremName
      #[data.fn, preFamily, postFamily, data.arg, c]
    replaceMainGoal (← goal.apply proof)

end HoareFixTactic

elab_rules : tactic
  | `(tactic| err_hoare_fix_nolv_auto $A:term) =>
      HoareFixTactic.runNoLogicVar A
  | `(tactic| hoare_fix_lv_auto $A:term $C:term $c:term) =>
      HoareFixTactic.runLogicVar A C c false
  | `(tactic| hoare_fix_lv_auto_conj $A:term $C:term $c:term) =>
      HoareFixTactic.runLogicVar A C c true
  | `(tactic| hoare_fix_lv_auto_conj' $A:term $C:term $c:term) =>
      HoareFixTactic.runLogicVar A C c true

end MonadLib
