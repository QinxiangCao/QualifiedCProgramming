import MonadLib.MonadErr.MonadErrHoare

universe u

namespace MonadLib

open AUXLib
open MonadErr
open scoped MonadNotation

def safe {Sigma A : Type} (s : Sigma) (c : program Sigma A)
    (X : A -> Sigma -> Prop) : Prop :=
  weakestpre c X s

def safeExec {Sigma A : Type} (P : Sigma -> Prop) (c : program Sigma A)
    (X : A -> Sigma -> Prop) : Prop :=
  exists s, P s /\ safe s c X

def result_state {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) : A -> Sigma -> Prop :=
  fun a s1 => exists s0, P s0 /\ c.nrm s0 a s1

def hs_eval {Sigma A : Type} (c : program Sigma A) (P P' : Sigma -> Prop)
    (a : A) : Prop :=
  forall s, P s -> exists s', c.nrm s a s' /\ P' s'

namespace MonadNotation

scoped notation:70 P " -@ " c " -⥅ " P' " ♯ " a =>
  hs_eval c P P' a

scoped notation:70 P " -@ " c " -→ " P' =>
  exists a, hs_eval c P P' a

end MonadNotation

abbrev asrt {Sigma : Type u} : Type u := Sigma -> Prop

theorem hs_eval_equiv_angelic_triple {Sigma A : Type}
    (c : program Sigma A) (P : Sigma -> Prop) (a : A) (Q : Sigma -> Prop) :
    hs_eval c P Q a <->
      valid_angelic_triple P c (fun r s => r = a /\ Q s) := by
  constructor
  · intro h s hs
    rcases h s hs with ⟨s', hn, hq⟩
    exact ⟨a, s', hn, rfl, hq⟩
  · intro h s hs
    rcases h s hs with ⟨r, s', hn, hr, hq⟩
    subst r
    exact ⟨s', hn, hq⟩

theorem ret_eq {Sigma A : Type} (s s0 : Sigma) (a a0 : A) :
    (MonadErr.ret a).nrm s a0 s0 <-> s0 = s /\ a0 = a := by
  constructor
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

theorem highstependret_derive {Sigma A : Type} (c1 : program Sigma A)
    (P : Sigma -> Prop) (a : A) (P' : A -> Sigma -> Prop) :
    hs_eval c1 P (P' a) a ->
    forall X, safeExec P c1 X -> safeExec (P' a) (MonadErr.ret a) X := by
  rintro heval X ⟨s, hp, hsafe⟩
  rcases heval s hp with ⟨s', hn, hp'⟩
  exact ⟨s', hp', (wp_ret a X s').mpr (hsafe.2 a s' hn)⟩

theorem highstepend_derive {Sigma : Type} (c1 : program Sigma Unit)
    (P P' : Sigma -> Prop) :
    (exists a, hs_eval c1 P P' a) ->
    forall X, safeExec P c1 X -> safeExec P' (MonadErr.ret ()) X := by
  rintro ⟨a, heval⟩
  cases a
  exact highstependret_derive c1 P () (fun _ => P') heval

theorem highstepbind_derive {Sigma A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (P : Sigma -> Prop) (a : A)
    (P' : Sigma -> Prop) :
    hs_eval c1 P P' a ->
    forall X, safeExec P (MonadErr.bind c1 c2) X -> safeExec P' (c2 a) X := by
  rintro heval X ⟨s, hp, hsafe⟩
  rcases heval s hp with ⟨s', hn, hp'⟩
  have hbind := (wp_bind c1 c2 X s).mp hsafe
  exact ⟨s', hp', hbind.2 a s' hn⟩

theorem highstepseq_derive {Sigma A B : Type} (c1 : program Sigma A)
    (c2 : program Sigma B) (P P' : Sigma -> Prop) :
    (exists a, hs_eval c1 P P' a) ->
    forall X, safeExec P (c1 ;; c2) X -> safeExec P' c2 X := by
  rintro ⟨a, heval⟩
  exact highstepbind_derive c1 (fun _ => c2) P a P' heval

theorem highret_eval1 {Sigma A : Type} (P : Sigma -> Prop) (a : A) :
    exists r, hs_eval (MonadErr.ret a) P P r := by
  exact ⟨a, fun s hp => ⟨s, ⟨rfl, rfl⟩, hp⟩⟩

theorem highret_eval2 {Sigma A : Type} (P : Sigma -> Prop) (a : A) :
    hs_eval (MonadErr.ret a) P P a := by
  exact fun s hp => ⟨s, ⟨rfl, rfl⟩, hp⟩

theorem hsevalbind_derive {Sigma A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (P : Sigma -> Prop)
    (P' : A -> Sigma -> Prop) (a : A) (Q : B -> Sigma -> Prop) (b : B) :
    hs_eval c1 P (P' a) a -> hs_eval (c2 a) (P' a) (Q b) b ->
    hs_eval (MonadErr.bind c1 c2) P (Q b) b := by
  intro h1 h2 s hp
  rcases h1 s hp with ⟨s1, hn1, hp1⟩
  rcases h2 s1 hp1 with ⟨s2, hn2, hq⟩
  exact ⟨s2, ⟨a, s1, hn1, hn2⟩, hq⟩

theorem hsevalbind_derive' {Sigma A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (P P' : Sigma -> Prop) (a : A)
    (Q : Sigma -> Prop) (b : B) :
    hs_eval c1 P P' a -> hs_eval (c2 a) P' Q b ->
    hs_eval (MonadErr.bind c1 c2) P Q b := by
  intro h1 h2 s hp
  rcases h1 s hp with ⟨s1, hn1, hp1⟩
  rcases h2 s1 hp1 with ⟨s2, hn2, hq⟩
  exact ⟨s2, ⟨a, s1, hn1, hn2⟩, hq⟩

theorem hsevalchoice_left_derive {Sigma A : Type}
    (c1 c2 : program Sigma A) (P Q : Sigma -> Prop) (a : A) :
    hs_eval c1 P Q a -> hs_eval (choice c1 c2) P Q a := by
  intro h s hp
  rcases h s hp with ⟨s', hn, hq⟩
  exact ⟨s', Or.inl hn, hq⟩

theorem hsevalchoice_right_derive {Sigma A : Type}
    (c1 c2 : program Sigma A) (P Q : Sigma -> Prop) (a : A) :
    hs_eval c2 P Q a -> hs_eval (choice c1 c2) P Q a := by
  intro h s hp
  rcases h s hp with ⟨s', hn, hq⟩
  exact ⟨s', Or.inr hn, hq⟩

theorem hsevaltestpure_derive {Sigma : Type} (P : Sigma -> Prop)
    (Q : Prop) (a : Unit) :
    Q -> hs_eval (testPure Q) P P a := by
  intro hq s hp
  cases a
  exact ⟨s, ⟨rfl, hq⟩, hp⟩

theorem hsevalassert_derive {Sigma : Type} (P : Sigma -> Prop)
    (Q : Prop) (a : Unit) :
    Q -> hs_eval (assert Q) P P a := by
  intro hq s hp
  cases a
  exact ⟨s, ⟨rfl, hq⟩, hp⟩

theorem hs_eval_proequiv {Sigma A : Type} (c1 c2 : program Sigma A)
    (P Q : Sigma -> Prop) (a : A) :
    equiv c1 c2 -> hs_eval c1 P Q a -> hs_eval c2 P Q a := by
  intro he h s hp
  rcases h s hp with ⟨s', hn, hq⟩
  exact ⟨s', (he.nrmequiv s a s').mp hn, hq⟩

theorem safeExec_ex {Sigma A B : Type} (P : A -> Sigma -> Prop)
    (c : program Sigma B) (X : B -> Sigma -> Prop) :
    (exists a, safeExec (P a) c X) <->
      safeExec (fun s => exists a, P a s) c X := by
  constructor
  · rintro ⟨a, s, hp, hs⟩
    exact ⟨s, ⟨a, hp⟩, hs⟩
  · rintro ⟨s, ⟨a, hp⟩, hs⟩
    exact ⟨a, s, hp, hs⟩

theorem safeExec_coqprop {Sigma A : Type} (B : Prop) (P : Sigma -> Prop)
    (c : program Sigma A) (X : A -> Sigma -> Prop) :
    safeExec (fun s => B /\ P s) c X <-> B /\ safeExec P c X := by
  constructor
  · rintro ⟨s, ⟨hb, hp⟩, hs⟩
    exact ⟨hb, s, hp, hs⟩
  · rintro ⟨hb, s, hp, hs⟩
    exact ⟨s, ⟨hb, hp⟩, hs⟩

theorem safeExec_pre {Sigma A : Type} (c : program Sigma A)
    (P1 P2 : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    (forall s, P1 s -> P2 s) -> safeExec P1 c X -> safeExec P2 c X := by
  rintro h ⟨s, hp, hs⟩
  exact ⟨s, h s hp, hs⟩

theorem safeExec_X_subset {Sigma A : Type} (c : program Sigma A)
    (P : Sigma -> Prop) (X1 X2 : A -> Sigma -> Prop) :
    (forall a s, X1 a s -> X2 a s) -> safeExec P c X1 -> safeExec P c X2 := by
  rintro h ⟨s, hp, hs⟩
  exact ⟨s, hp, wp_conseq c X1 X2 h s hs⟩

theorem safeExec_proequiv {Sigma A : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    equiv c1 c2 -> safeExec P c1 X -> safeExec P c2 X := by
  rintro he ⟨s, hp, hs⟩
  exact ⟨s, hp, (wp_progequiv c1 c2 X
    (AUXLib.Equivalence.symm _ _ he) s).mp hs⟩

theorem safeExec_choice_l {Sigma A : Type} (c0 c1 : program Sigma A)
    (X : A -> Sigma -> Prop) (P : Sigma -> Prop) :
    safeExec P (choice c0 c1) X -> safeExec P c0 X := by
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, ((wp_choice c0 c1 X) s).mp hs |>.1⟩

theorem safeExec_choice_r {Sigma A : Type} (c0 c1 : program Sigma A)
    (X : A -> Sigma -> Prop) (P : Sigma -> Prop) :
    safeExec P (choice c0 c1) X -> safeExec P c1 X := by
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, ((wp_choice c0 c1 X) s).mp hs |>.2⟩

theorem safeExec_test {Sigma : Type} (Q : Prop) (P : Sigma -> Prop)
    (X : Unit -> Sigma -> Prop) :
    Q -> safeExec P (testPure Q) X -> safeExec P (MonadErr.ret ()) X := by
  rintro hq ⟨s, hp, hs⟩
  exact ⟨s, hp, (wp_ret () X s).mpr ((wp_assume_coqprop Q X hq s).mp hs)⟩

theorem safeExec_testst {Sigma : Type} (Q P : Sigma -> Prop)
    (X : Unit -> Sigma -> Prop) :
    (forall s, P s -> Q s) ->
    safeExec P (test Q) X -> safeExec P (MonadErr.ret ()) X := by
  rintro hq ⟨s, hp, hs⟩
  exact ⟨s, hp, (wp_ret () X s).mpr (((wp_assume Q X) s).mp hs (hq s hp))⟩

theorem safeExec_any {Sigma Q : Type} (P : Sigma -> Prop)
    (X : Q -> Sigma -> Prop) (q : Q) :
    safeExec P (any Q) X -> safeExec P (MonadErr.ret q) X := by
  rintro ⟨s, hp, hs⟩
  exact ⟨s, hp, (wp_ret q X s).mpr (((wp_any X) s).mp hs q)⟩

theorem safeExec_get {Sigma A : Type} (Pa : Sigma -> A -> Prop)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) (a : A) :
    (forall s, P s -> Pa s a) ->
    safeExec P (get Pa) X -> safeExec P (MonadErr.ret a) X := by
  rintro ha ⟨s, hp, hs⟩
  exact ⟨s, hp, (wp_ret a X s).mpr (((wp_get Pa X) s).mp hs a (ha s hp))⟩

theorem safeExec_get' {Sigma A : Type} (f : Sigma -> A)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) (a : A) :
    (forall s, P s -> a = f s) ->
    safeExec P (get' f) X -> safeExec P (MonadErr.ret a) X := by
  rintro ha ⟨s, hp, hs⟩
  exact ⟨s, hp, (wp_ret a X s).mpr (((wp_get' f X) s).mp hs a (ha s hp))⟩

theorem safeExec_update' {Sigma : Type} (f : Sigma -> Sigma)
    (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop) :
    safeExec P (update' f) X ->
    safeExec (fun s => exists s0, s = f s0 /\ P s0) (MonadErr.ret ()) X := by
  rintro ⟨s, hp, hs⟩
  refine ⟨f s, ⟨s, rfl, hp⟩, ?_⟩
  apply (wp_ret () X (f s)).mpr
  exact ((wp_update' f X) s).mp hs (f s) rfl

theorem safeExec_update {Sigma : Type} (R : Sigma -> Sigma -> Prop)
    (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop) :
    (forall s, P s -> exists s', R s s') ->
    safeExec P (update R) X ->
    safeExec (fun s => exists s0, R s0 s /\ P s0) (MonadErr.ret ()) X := by
  rintro hex ⟨s, hp, hs⟩
  rcases hex s hp with ⟨s', hr⟩
  refine ⟨s', ⟨s, hr, hp⟩, ?_⟩
  apply (wp_ret () X s').mpr
  exact ((wp_update R X) s).mp hs s' hr

theorem safeExec_assert_aux {Sigma : Type} (Q : Prop) (P : Sigma -> Prop)
    (X : Unit -> Sigma -> Prop) :
    safeExec P (assert Q) X ->
    safeExec (fun s => Q /\ P s) (MonadErr.ret ()) X := by
  rintro ⟨s, hp, hs⟩
  have h := ((wp_assert Q X) s).mp hs
  exact ⟨s, ⟨h.1, hp⟩, (wp_ret () X s).mpr h.2⟩

theorem safeExec_assert {Sigma : Type} (Q : Prop) (P : Sigma -> Prop)
    (X : Unit -> Sigma -> Prop) :
    safeExec P (assert Q) X -> Q /\ safeExec P (MonadErr.ret ()) X := by
  intro h
  exact (safeExec_coqprop Q P (MonadErr.ret ()) X).mp
    (safeExec_assert_aux Q P X h)

theorem safeExec_assertS {Sigma : Type} (Q P : Sigma -> Prop)
    (X : Unit -> Sigma -> Prop) :
    safeExec P (assertS Q) X ->
    safeExec (fun s => Q s /\ P s) (MonadErr.ret ()) X := by
  rintro ⟨s, hp, hs⟩
  have h := ((wp_assertS Q X) s).mp hs
  exact ⟨s, ⟨h.1, hp⟩, (wp_ret () X s).mpr h.2⟩

theorem safeExec_bind_reta {Sigma A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (P P' : Sigma -> Prop) (a : A) :
    (forall X, safeExec P c1 X -> safeExec P' (MonadErr.ret a) X) ->
    forall X, safeExec P (MonadErr.bind c1 c2) X -> safeExec P' (c2 a) X := by
  intro h X hbind
  have hc1 : safeExec P c1 (fun a => weakestpre (c2 a) X) := by
    rcases hbind with ⟨s, hp, hs⟩
    exact ⟨s, hp, ((wp_bind c1 c2 X) s).mp hs⟩
  rcases h (fun a => weakestpre (c2 a) X) hc1 with ⟨s, hp', hs⟩
  exact ⟨s, hp', (wp_ret a (fun a => weakestpre (c2 a) X) s).mp hs⟩

theorem safeExec_bind' {Sigma A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (P P' : Sigma -> Prop) :
    (forall X, safeExec P c1 X -> exists a, safeExec P' (MonadErr.ret a) X) ->
    forall X, safeExec P (MonadErr.bind c1 c2) X ->
      exists a, safeExec P' (c2 a) X := by
  intro h X hbind
  have hc1 : safeExec P c1 (fun a => weakestpre (c2 a) X) := by
    rcases hbind with ⟨s, hp, hs⟩
    exact ⟨s, hp, ((wp_bind c1 c2 X) s).mp hs⟩
  rcases h (fun a => weakestpre (c2 a) X) hc1 with ⟨a, s, hp', hs⟩
  exact ⟨a, s, hp', (wp_ret a (fun a => weakestpre (c2 a) X) s).mp hs⟩

theorem safeExec_bind {Sigma A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (P : Sigma -> Prop) :
    forall X, safeExec P (MonadErr.bind c1 c2) X ->
    exists X', safeExec P c1 X' /\
      forall P' a, safeExec P' (MonadErr.ret a) X' -> safeExec P' (c2 a) X := by
  rintro X ⟨s, hp, hs⟩
  let X' : A -> Sigma -> Prop := fun r s' => c1.nrm s r s'
  refine ⟨X', ?_, ?_⟩
  · refine ⟨s, hp, ?_⟩
    apply wp_self
    exact ((wp_bind c1 c2 X) s).mp hs |>.1
  · intro P' a
    rintro ⟨s', hp', hret⟩
    have hc1 : c1.nrm s a s' := (wp_ret a X' s').mp hret
    exact ⟨s', hp', (((wp_bind c1 c2 X) s).mp hs).2 a s' hc1⟩

theorem safeExec_conseq {Sigma A : Type} (P' P : Sigma -> Prop)
    (c : program Sigma A) (X : A -> Sigma -> Prop) :
    safeExec P c X -> (forall s, P s -> P' s) -> safeExec P' c X := by
  rintro ⟨s, hp, hs⟩ h
  exact ⟨s, h s hp, hs⟩

theorem safeExec_test_bind {Sigma A : Type} (Q : Prop)
    (c : program Sigma A) (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    Q -> safeExec P (testPure Q ;; c) X -> safeExec P c X := by
  intro hq
  exact safeExec_bind_reta (testPure Q) (fun _ => c) P P ()
    (fun X h => safeExec_test Q P X hq h) X

theorem safeExec_testst_bind {Sigma A : Type} (Q : Sigma -> Prop)
    (c : program Sigma A) (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    (forall s, P s -> Q s) -> safeExec P (test Q ;; c) X -> safeExec P c X := by
  intro hq
  exact safeExec_bind_reta (test Q) (fun _ => c) P P ()
    (fun X h => safeExec_testst Q P X hq h) X

theorem safeExec_any_bind {Sigma A Q : Type} (c : Q -> program Sigma A)
    (P : Sigma -> Prop) (X : A -> Sigma -> Prop) (a : Q) :
    safeExec P (q <- any Q ;; c q) X -> safeExec P (c a) X := by
  exact safeExec_bind_reta (any Q) c P P a
    (fun X h => safeExec_any P X a h) X

theorem safeExec_get_bind {Sigma A B : Type} (a : A)
    (Pa : Sigma -> A -> Prop) (P : Sigma -> Prop)
    (c : A -> program Sigma B) (X : B -> Sigma -> Prop) :
    (forall s, P s -> Pa s a) ->
    safeExec P (a0 <- get Pa ;; c a0) X -> safeExec P (c a) X := by
  intro ha
  exact safeExec_bind_reta (get Pa) c P P a
    (fun X h => safeExec_get Pa P X a ha h) X

theorem safeExec_get'_bind {Sigma A B : Type} (f : Sigma -> A) (a : A)
    (P : Sigma -> Prop) (c : A -> program Sigma B) (X : B -> Sigma -> Prop) :
    (forall s, P s -> a = f s) ->
    safeExec P (a0 <- get' f ;; c a0) X -> safeExec P (c a) X := by
  intro ha
  exact safeExec_bind_reta (get' f) c P P a
    (fun X h => safeExec_get' f P X a ha h) X

theorem safeExec_update'_bind {Sigma B : Type} (f : Sigma -> Sigma)
    (P : Sigma -> Prop) (c : program Sigma B) (X : B -> Sigma -> Prop) :
    safeExec P (update' f ;; c) X ->
    safeExec (fun s => exists s0, s = f s0 /\ P s0) c X := by
  exact safeExec_bind_reta (update' f) (fun _ => c) P
    (fun s => exists s0, s = f s0 /\ P s0) ()
    (fun X h => safeExec_update' f P X h) X

theorem safeExec_update_bind {Sigma B : Type} (R : Sigma -> Sigma -> Prop)
    (P : Sigma -> Prop) (c : program Sigma B) (X : B -> Sigma -> Prop) :
    (forall s, P s -> exists s', R s s') ->
    safeExec P (update R ;; c) X ->
    safeExec (fun s => exists s0, R s0 s /\ P s0) c X := by
  intro hex
  exact safeExec_bind_reta (update R) (fun _ => c) P
    (fun s => exists s0, R s0 s /\ P s0) ()
    (fun X h => safeExec_update R P X hex h) X

theorem safeExec_assert_seq {Sigma A : Type} (B : Prop)
    (c : program Sigma A) (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    safeExec P (assert B ;; c) X -> B /\ safeExec P c X := by
  intro h
  have hs := safeExec_bind_reta (assert B) (fun _ => c) P
    (fun s => B /\ P s) () (fun X h => safeExec_assert_aux B P X h) X h
  exact (safeExec_coqprop B P c X).mp hs

theorem safeExec_assertS_seq {Sigma A : Type} (B : Sigma -> Prop)
    (c : program Sigma A) (P : Sigma -> Prop) (X : A -> Sigma -> Prop) :
    safeExec P (assertS B ;; c) X ->
    safeExec (fun s => B s /\ P s) c X := by
  exact safeExec_bind_reta (assertS B) (fun _ => c) P
    (fun s => B s /\ P s) () (fun X h => safeExec_assertS B P X h) X

theorem safeExec_monad_Atrue_finnal {A : Type} (m : program Unit A) :
    Not (m.err ()) -> safeExec ATrue m (fun r s => m.nrm () r s) := by
  intro he
  exact ⟨(), trivial, wp_self m () he⟩

theorem safeExec_ret_Atrue_finnal {Sigma A : Type} (m : program Sigma A)
    (l : A) (s : Sigma) :
    safeExec ATrue (MonadErr.ret l) (fun r s' => m.nrm s r s') ->
    exists s', m.nrm s l s' := by
  rintro ⟨s', _, hs⟩
  exact ⟨s', (wp_ret l (fun r s' => m.nrm s r s') s').mp hs⟩

instance safeExec_X_subset_impl_Proper {Sigma A : Type} (P : Sigma -> Prop) :
    Proper (Eq ==> Sets.included ==> ImplRel) (@safeExec Sigma A P) where
  proper c1 c2 hc X1 X2 hX := by
    subst c2
    exact safeExec_X_subset c1 P X1 X2 hX

instance safeExec_programequiv_iff_Proper {Sigma A : Type} (P : Sigma -> Prop) :
    Proper (equiv ==> Eq ==> Iff) (@safeExec Sigma A P) where
  proper c1 c2 hc X1 X2 hX := by
    subst X2
    exact ⟨safeExec_proequiv c1 c2 P X1 hc,
      safeExec_proequiv c2 c1 P X1 (AUXLib.Equivalence.symm _ _ hc)⟩

instance hseval_programequiv_Proper {Sigma A : Type} :
    Proper (equiv ==> Eq ==> Eq ==> Eq ==> Iff) (@hs_eval Sigma A) where
  proper c1 c2 hc P1 P2 hP Q1 Q2 hQ a1 a2 ha := by
    subst P2
    subst Q2
    subst a2
    exact ⟨hs_eval_proequiv c1 c2 P1 Q1 a1 hc,
      hs_eval_proequiv c2 c1 P1 Q1 a1 (AUXLib.Equivalence.symm _ _ hc)⟩

theorem program_para_equiv {Sigma A B : Type} (f1 f2 : A -> program Sigma B) :
    equiv f1 f2 -> forall x, equiv (f1 x) (f2 x) := by
  exact fun h x => h x

theorem safeExec_result_state {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) :
    (exists s, P s /\ Not (c.err s)) -> safeExec P c (result_state P c) := by
  rintro ⟨s, hp, he⟩
  refine ⟨s, hp, he, ?_⟩
  intro a s' hn
  exact ⟨s, hp, hn⟩

theorem Hoare_result_state {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P c Q -> forall a s, result_state P c a s -> Q a s := by
  rintro h a s ⟨s0, hp, hn⟩
  exact h.1 a s0 s hp hn

theorem Hoare_safeexec_compose {Sigma A : Type} (P1 : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P1 c Q -> forall (P2 : Sigma -> Prop) (a : A) (s : Sigma),
    safeExec P2 (MonadErr.ret a) (c.nrm s) -> P1 s ->
    exists s', Q a s' /\ P2 s' := by
  rintro h P2 a s ⟨s', hp2, hs⟩ hp1
  have hn : c.nrm s a s' := (wp_ret a (c.nrm s) s').mp hs
  exact ⟨s', h.1 a s s' hp1 hn, hp2⟩

macro "splits" : tactic =>
  `(tactic| repeat apply And.intro)

private theorem highstepbind_from_safe {Sigma A B : Type}
    {c1 : program Sigma A} {c2 : A -> program Sigma B}
    {P P' : Sigma -> Prop} {a : A} {X : B -> Sigma -> Prop} :
    safeExec P (MonadErr.bind c1 c2) X ->
    hs_eval c1 P P' a -> safeExec P' (c2 a) X := by
  intro hsafe heval
  exact highstepbind_derive c1 c2 P a P' heval X hsafe

private theorem safeExec_bind_assoc_nf {Sigma A B C : Type}
    {c0 : program Sigma A} {c1 : A -> program Sigma B}
    {c2 : B -> program Sigma C} {P : Sigma -> Prop}
    {X : C -> Sigma -> Prop} :
    safeExec P (MonadErr.bind (MonadErr.bind c0 c1) c2) X ->
    safeExec P (MonadErr.bind c0 (fun a => MonadErr.bind (c1 a) c2)) X := by
  exact safeExec_proequiv _ _ _ _ (bind_assoc c0 c1 c2)

private theorem safeExec_bind_choice_nf {Sigma A B : Type}
    {c0 c1 : program Sigma A} {c2 : A -> program Sigma B}
    {P : Sigma -> Prop} {X : B -> Sigma -> Prop} :
    safeExec P (MonadErr.bind (choice c0 c1) c2) X ->
    safeExec P (choice (MonadErr.bind c0 c2) (MonadErr.bind c1 c2)) X := by
  exact safeExec_proequiv _ _ _ _ (bind_choice_equiv c0 c1 c2)

private theorem safeExec_bind_ret_l_nf {Sigma A B : Type}
    {a : A} {c : A -> program Sigma B} {P : Sigma -> Prop}
    {X : B -> Sigma -> Prop} :
    safeExec P (MonadErr.bind (MonadErr.ret a) c) X -> safeExec P (c a) X := by
  exact safeExec_proequiv _ _ _ _ (bind_ret_l a c)

private theorem safeExec_bind_ret_r_nf {Sigma A : Type}
    {c : program Sigma A} {P : Sigma -> Prop} {X : A -> Sigma -> Prop} :
    safeExec P (MonadErr.bind c MonadErr.ret) X -> safeExec P c X := by
  exact safeExec_proequiv _ _ _ _ (bind_ret_r c)

syntax "err_prove_by_one_abs_step " term:max : tactic
syntax "__prove_by_one_abs_step " term:max : tactic

namespace AbsStepTactic

open Lean Meta Elab Tactic

private def bindParts? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let head := e.getAppFn
  if head.isConstOf ``MonadErr.bind || head.isConstOf ``MonadLib.bind then
    let args := e.getAppArgs
    if args.size >= 2 then
      some (args[args.size - 2]!, args[args.size - 1]!)
    else
      none
  else
    none

private def run (xSyntax : Syntax) : TacticM Unit := withMainContext do
  let goal <- getMainGoal
  let target <- instantiateMVars (← goal.getType)
  unless target.consumeMData.getAppFn.isConstOf ``safeExec do
    throwError "prove_by_one_abs_step: expected a safeExec goal"
  let targetArgs := target.getAppArgs
  unless targetArgs.size >= 2 do
    throwError "prove_by_one_abs_step: malformed safeExec goal"
  let targetProgram := targetArgs[targetArgs.size - 2]!
  let targetPost := targetArgs[targetArgs.size - 1]!
  let mut candidate : Option (FVarId × Expr × Expr × Expr) := none
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      let type <- instantiateMVars localDecl.type
      if type.consumeMData.getAppFn.isConstOf ``safeExec then
        let args := type.getAppArgs
        if args.size >= 2 then
          let program := args[args.size - 2]!
          let post := args[args.size - 1]!
          if let some (c1, c2) := bindParts? program then
            if ← isDefEq post targetPost then
              let pre := args[args.size - 3]!
              candidate := some (localDecl.fvarId, c1, c2, pre)
  let some (sourceHyp, c1, c2, sourcePre) := candidate
    | throwError "prove_by_one_abs_step: no matching safeExec/bind hypothesis"
  let c2Type <- whnf (← inferType c2)
  let .forallE _ argumentType _ _ := c2Type
    | throwError "prove_by_one_abs_step: malformed bind continuation"
  let x <- elabTerm xSyntax (some argumentType)
  unless ← isDefEq (mkApp c2 x) targetProgram do
    throwError "prove_by_one_abs_step: continuation at the supplied value does not match the goal"
  let sigma := targetArgs[0]!
  let resultType := targetArgs[1]!
  let targetPre := targetArgs[targetArgs.size - 3]!
  let sourceProof := mkFVar sourceHyp
  let rule <- mkAppOptM ``highstepbind_from_safe
    #[some sigma, some argumentType, some resultType, some c1, some c2,
      some sourcePre, some targetPre, some x, some targetPost,
      some sourceProof]
  let nextGoals <- goal.apply rule
  setGoals (← nextGoals.mapM fun nextGoal => nextGoal.tryClear sourceHyp)

end AbsStepTactic

elab_rules : tactic
  | `(tactic| err_prove_by_one_abs_step $x:term) =>
      AbsStepTactic.run x
  | `(tactic| __prove_by_one_abs_step $x:term) =>
      AbsStepTactic.run x

macro "err_abs_choice_left" : tactic =>
  `(tactic| apply hsevalchoice_left_derive)

macro "err_abs_choice_right" : tactic =>
  `(tactic| apply hsevalchoice_right_derive)

macro "err_abs_test_step" : tactic =>
  `(tactic|
    first
      | apply hsevaltestpure_derive
      | (apply hsevalbind_derive' (a := ()) <;>
          first | apply hsevaltestpure_derive | skip))

macro "abs_assert_step" : tactic =>
  `(tactic|
    first
      | apply hsevalassert_derive
      | (apply hsevalbind_derive
            (P' := fun _ => ATrue) (a := ()) (Q := fun _ => ATrue) <;>
          first | apply hsevalassert_derive | skip))

macro "err_abs_ret_step" : tactic =>
  `(tactic| apply highret_eval2)

syntax "err_safe_step " ident : tactic
syntax "__safe_step_once " ident : tactic
syntax "__safe_prog_nf_once " ident : tactic
syntax "__safe_prog_nf " ident : tactic
syntax "__guard_safe " ident ident : tactic

namespace SafeTactic

open Lean Meta Elab Tactic

private def hasHead (e : Expr) (decl : Name) : Bool :=
  e.consumeMData.getAppFn.isConstOf decl

private def bindParts? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if hasHead e ``MonadErr.bind || hasHead e ``MonadLib.bind then
    let args := e.getAppArgs
    if args.size >= 2 then
      some (args[args.size - 2]!, args[args.size - 1]!)
    else
      none
  else
    none

private def safeProgram (hyp : Lean.Syntax) : TacticM Expr := withMainContext do
  let fvarId <- getFVarId hyp
  let type <- instantiateMVars (← fvarId.getType)
  unless type.consumeMData.getAppFn.isConstOf ``safeExec do
    throwError "safe tactic: expected a safeExec hypothesis"
  let args := type.getAppArgs
  unless args.size >= 2 do throwError "safe tactic: malformed safeExec hypothesis"
  return args[args.size - 2]!

private def shapeMatches (kind : Name) (program : Expr) : Bool :=
  match kind with
  | `assoc =>
      match bindParts? program with
      | some (first, _) => (bindParts? first).isSome
      | none => false
  | `bindChoice =>
      match bindParts? program with
      | some (first, _) => hasHead first ``choice
      | none => false
  | `bindRetL =>
      match bindParts? program with
      | some (first, _) => hasHead first ``MonadErr.ret || hasHead first ``MonadLib.ret
      | none => false
  | `bindRetR =>
      match bindParts? program with
      | some (_, second) => hasHead second ``MonadErr.ret || hasHead second ``MonadLib.ret
      | none => false
  | `assert =>
      match bindParts? program with
      | some (first, _) => hasHead first ``MonadLib.assert
      | none => false
  | `testPure =>
      match bindParts? program with
      | some (first, _) => hasHead first ``MonadLib.testPure
      | none => false
  | `test =>
      match bindParts? program with
      | some (first, _) => hasHead first ``MonadLib.test
      | none => false
  | `choice => hasHead program ``MonadLib.choice
  | _ => false

elab_rules : tactic
  | `(tactic| __guard_safe $kind:ident $h:ident) => do
      let program ← safeProgram h
      unless shapeMatches kind.getId.eraseMacroScopes program do
        throwError "safe tactic: hypothesis does not have the requested program shape"

end SafeTactic

macro_rules
  | `(tactic| __safe_prog_nf_once $h:ident) => do
      `(tactic|
        first
          | (__guard_safe assoc $h;
             replace $h := safeExec_bind_assoc_nf $h)
          | (__guard_safe bindChoice $h;
             replace $h := safeExec_bind_choice_nf $h)
          | (__guard_safe bindRetL $h;
             replace $h := safeExec_bind_ret_l_nf $h)
          | (__guard_safe bindRetR $h;
             replace $h := safeExec_bind_ret_r_nf $h))
  | `(tactic| __safe_prog_nf $h:ident) =>
      `(tactic| repeat __safe_prog_nf_once $h)
  | `(tactic| __safe_step_once $h:ident) => do
      `(tactic|
        first
          | (__guard_safe assert $h;
             obtain ⟨hguard, $h⟩ := safeExec_assert_seq _ _ _ _ $h;
             __safe_prog_nf $h)
          | (__guard_safe testPure $h;
             replace $h := safeExec_test_bind _ _ _ _
               (by first | trivial | assumption | simp_all) $h;
             __safe_prog_nf $h)
          | (__guard_safe test $h;
             replace $h := safeExec_testst_bind _ _ _ _
               (by intros; first | trivial | assumption | simp_all) $h;
             __safe_prog_nf $h))
  | `(tactic| err_safe_step $h:ident) => do
      `(tactic|
        (__safe_prog_nf $h;
         __safe_step_once $h;
         repeat __safe_step_once $h))

syntax "err_safe_choice_l " ident : tactic
macro_rules
  | `(tactic| err_safe_choice_l $h:ident) =>
      `(tactic|
        (__safe_prog_nf $h;
         __guard_safe choice $h;
         replace $h := safeExec_choice_l _ _ _ _ $h;
         __safe_prog_nf $h;
         repeat __safe_step_once $h))

syntax "err_safe_choice_r " ident : tactic
macro_rules
  | `(tactic| err_safe_choice_r $h:ident) =>
      `(tactic|
        (__safe_prog_nf $h;
         __guard_safe choice $h;
         replace $h := safeExec_choice_r _ _ _ _ $h;
         __safe_prog_nf $h;
         repeat __safe_step_once $h))

private theorem safeExec_proequiv_from {Sigma A : Type}
    {c1 c2 : program Sigma A} {P : Sigma -> Prop}
    {X : A -> Sigma -> Prop} :
    safeExec P c1 X -> equiv c1 c2 -> safeExec P c2 X := by
  intro h he
  exact safeExec_proequiv c1 c2 P X he h

macro "err_safe_equiv" : tactic =>
  `(tactic|
    apply safeExec_proequiv_from <;>
      first
        | assumption
        | (err_prog_nf; done)
        | (monad_equiv; done)
        | __err_match_bind_equiv)

end MonadLib
