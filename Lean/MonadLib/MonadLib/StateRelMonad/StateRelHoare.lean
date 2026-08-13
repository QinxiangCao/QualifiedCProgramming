import MonadLib.StateRelMonad.FixpointLib

namespace MonadLib.StateRelMonad

open AUXLib FP
open scoped MonadNotation

def Hoare {Sigma A : Type} (P : Sigma -> Prop) (c : program Sigma A)
    (Q : A -> Sigma -> Prop) : Prop :=
  forall s1 a s2, P s1 -> c s1 a s2 -> Q a s2

theorem Hoare_bind {Sigma A B : Type} (P : Sigma -> Prop)
    (f : program Sigma A) (Q : A -> Sigma -> Prop)
    (g : A -> program Sigma B) (R : B -> Sigma -> Prop) :
    Hoare P f Q -> (forall a, Hoare (Q a) (g a) R) ->
      Hoare P (bind f g) R := by
  intro hf hg s b s' hp
  rintro ⟨a, s0, ha, hb⟩
  exact hg a s0 b s' (hf s a s0 hp ha) hb

theorem Hoare_ret {Sigma A : Type} (P : A -> Sigma -> Prop) (a0 : A) :
    Hoare (P a0) (ret a0) P := by
  rintro s _ s' hp ⟨rfl, rfl⟩
  exact hp

theorem Hoare_ret' {Sigma A : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) (a0 : A) :
    (forall s, P s -> Q a0 s) -> Hoare P (ret a0) Q := by
  intro h
  rintro s _ s' hp ⟨rfl, rfl⟩
  exact h s hp

theorem Hoare_step {Sigma A : Type} (P : Sigma -> Prop)
    (f : program Sigma A) :
    Hoare P f (fun a s2 => exists s1, f s1 a s2 /\ P s1) := by
  intro s1 a s2 hp hf
  exact ⟨s1, hf, hp⟩

theorem Hoare_choice {Sigma A : Type} (P : Sigma -> Prop)
    (f g : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P f Q -> Hoare P g Q -> Hoare P (choice f g) Q := by
  intro hf hg s a s' hp
  rintro (h | h)
  · exact hf s a s' hp h
  · exact hg s a s' hp h

theorem Hoare_choice_disj {Sigma A : Type} (P : Sigma -> Prop)
    (f g : program Sigma A) (Q1 Q2 : A -> Sigma -> Prop) :
    Hoare P f Q1 -> Hoare P g Q2 ->
      Hoare P (choice f g) (fun a s => Q1 a s \/ Q2 a s) := by
  intro hf hg s a s' hp
  rintro (h | h)
  · exact Or.inl (hf s a s' hp h)
  · exact Or.inr (hg s a s' hp h)

theorem Hoare_assume_bind {Sigma A : Type} (P Q : Sigma -> Prop)
    (f : program Sigma A) (R : A -> Sigma -> Prop) :
    Hoare (fun s => Q s /\ P s) f R -> Hoare P (test Q ;; f) R := by
  intro hf
  apply Hoare_bind (Q := fun _ s => Q s /\ P s)
  · intro s _ s' hp
    rintro ⟨hq, rfl⟩
    exact ⟨hq, hp⟩
  · intro _
    exact hf

theorem Hoare_assume {Sigma : Type} (P Q : Sigma -> Prop) :
    Hoare P (test Q) (fun _ s => P s /\ Q s) := by
  intro s _ s' hp
  rintro ⟨hq, rfl⟩
  exact ⟨hp, hq⟩

theorem Hoare_assume' {Sigma : Type} (P : Sigma -> Prop) (Q : Prop) :
    Hoare P (test' Q) (fun _ s => P s /\ Q) := by
  intro s _ s' hp
  rintro ⟨hq, rfl⟩
  exact ⟨hp, hq⟩

theorem Hoare_assume_bind' {Sigma A : Type} (P : Sigma -> Prop) (Q : Prop)
    (f : program Sigma A) (R : A -> Sigma -> Prop) :
    (Q -> Hoare P f R) -> Hoare P (test' Q ;; f) R := by
  intro hf
  apply Hoare_bind (Q := fun _ s => P s /\ Q)
  · exact Hoare_assume' P Q
  · intro _ s a s' h hfmem
    exact hf h.2 s a s' h.1 hfmem

theorem Hoare_any {Sigma A : Type} (P : Sigma -> Prop) :
    Hoare P (any A) (fun _ => P) := by
  intro s _ s' hp h
  subst s'
  exact hp

theorem Hoare_any_bind {Sigma A B : Type} (P : Sigma -> Prop)
    (f : A -> program Sigma B) (Q : B -> Sigma -> Prop) :
    (forall a, Hoare P (f a) Q) -> Hoare P (a <- any A ;; f a) Q := by
  intro h
  exact Hoare_bind P (any A) (fun _ => P) f Q (Hoare_any P) h

theorem Hoare_get {Sigma A : Type} (P : Sigma -> Prop)
    (Pa : Sigma -> A -> Prop) :
    Hoare P (get Pa) (fun a s => Pa s a /\ P s) := by
  intro s a s' hp
  rintro ⟨ha, rfl⟩
  exact ⟨ha, hp⟩

theorem Hoare_update {Sigma : Type} (P : Sigma -> Prop)
    (Q : Sigma -> Sigma -> Prop) :
    Hoare P (update Q) (fun _ s2 => exists s1, Q s1 s2 /\ P s1) := by
  intro s _ s' hp hq
  exact ⟨s, hq, hp⟩

private theorem hoare_get_bind_tactic_rule {Sigma A B : Type}
    (P : Sigma -> Prop) (Pa : Sigma -> A -> Prop)
    (g : A -> program Sigma B) (R : B -> Sigma -> Prop) :
    (forall a, Hoare (fun s => Pa s a /\ P s) (g a) R) ->
      Hoare P (bind (get Pa) g) R := by
  intro h
  exact Hoare_bind P (get Pa) (fun a s => Pa s a /\ P s) g R
    (Hoare_get P Pa) h

private theorem hoare_update_bind_tactic_rule {Sigma B : Type}
    (P : Sigma -> Prop) (Q : Sigma -> Sigma -> Prop)
    (g : Unit -> program Sigma B) (R : B -> Sigma -> Prop) :
    (forall s0, Hoare (fun s2 => Q s0 s2 /\ P s0) (g ()) R) ->
      Hoare P (bind (update Q) g) R := by
  intro h
  apply Hoare_bind P (update Q)
    (fun _ s2 => exists s1, Q s1 s2 /\ P s1) g R (Hoare_update P Q)
  intro _ s1 b s2 hpre hg
  rcases hpre with ⟨s0, hq, hp⟩
  exact h s0 s1 b s2 ⟨hq, hp⟩ hg

theorem Hoare_conseq {Sigma A : Type} (P1 P2 : Sigma -> Prop)
    (f : program Sigma A) (Q1 Q2 : A -> Sigma -> Prop) :
    (forall s, P1 s -> P2 s) ->
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P2 f Q2 -> Hoare P1 f Q1 := by
  intro hp hq hf s a s' hs hm
  exact hq a s' (hf s a s' (hp s hs) hm)

theorem Hoare_conseq_pre {Sigma A : Type} (P1 P2 : Sigma -> Prop)
    (f : program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall s, P1 s -> P2 s) -> Hoare P2 f Q -> Hoare P1 f Q := by
  intro hp
  exact Hoare_conseq P1 P2 f Q Q hp (fun _ _ h => h)

theorem Hoare_conseq_post {Sigma A : Type} (P : Sigma -> Prop)
    (f : program Sigma A) (Q1 Q2 : A -> Sigma -> Prop) :
    (forall b s, Q2 b s -> Q1 b s) -> Hoare P f Q2 -> Hoare P f Q1 := by
  exact Hoare_conseq P P f Q1 Q2 (fun _ h => h)

theorem Hoare_conj {Sigma A : Type} (P : Sigma -> Prop)
    (f : program Sigma A) (Q1 Q2 : A -> Sigma -> Prop) :
    Hoare P f Q1 -> Hoare P f Q2 ->
      Hoare P f (fun a s => Q1 a s /\ Q2 a s) := by
  intro h1 h2 s a s' hp hm
  exact ⟨h1 s a s' hp hm, h2 s a s' hp hm⟩

theorem Hoare_conj' {Sigma A : Type} (P1 P2 : Sigma -> Prop)
    (f : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P1 f Q -> Hoare P2 f Q ->
      Hoare (fun s => P1 s /\ P2 s) f Q := by
  intro h1 _ s a s' hp hm
  exact h1 s a s' hp.1 hm

theorem Hoare_disj {Sigma A : Type} (P1 P2 : Sigma -> Prop)
    (f : program Sigma A) (Q : A -> Sigma -> Prop) :
    Hoare P1 f Q -> Hoare P2 f Q ->
      Hoare (fun s => P1 s \/ P2 s) f Q := by
  intro h1 h2 s a s' hp hm
  cases hp with
  | inl h => exact h1 s a s' h hm
  | inr h => exact h2 s a s' h hm

theorem Hoare_forall {Sigma A X : Type} (P : Sigma -> Prop)
    (f : program Sigma A) (Q : X -> A -> Sigma -> Prop) :
    (forall x, Hoare P f (Q x)) ->
      Hoare P f (fun a s => forall x, Q x a s) := by
  intro h s a s' hp hm x
  exact h x s a s' hp hm

theorem Hoare_pre_ex {Sigma A X : Type} (P : X -> Sigma -> Prop)
    (f : program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall x, Hoare (P x) f Q) ->
      Hoare (fun s => exists x, P x s) f Q := by
  intro h s a s'
  rintro ⟨x, hp⟩ hm
  exact h x s a s' hp hm

def continue_case {Sigma A B : Type} : CntOrBrk A B -> program Sigma A
  | .by_continue a => ret a
  | .by_break _ => fun _ _ _ => False

def break_case {Sigma A B : Type} : CntOrBrk A B -> program Sigma B
  | .by_continue _ => fun _ _ _ => False
  | .by_break b => ret b

theorem Hoare_sum {Sigma A B : Type} (P : Sigma -> Prop)
    (c : program Sigma (CntOrBrk A B))
    (Q : A -> Sigma -> Prop) (R : B -> Sigma -> Prop) :
    Hoare P (x <- c ;; continue_case x) Q ->
    Hoare P (x <- c ;; break_case x) R ->
    Hoare P c (fun x s => match x with
      | .by_continue a => Q a s
      | .by_break b => R b s) := by
  intro hc hb s x s' hp hx
  cases x with
  | by_continue a =>
      apply hc s a s' hp
      exact ⟨.by_continue a, s', hx, ⟨rfl, rfl⟩⟩
  | by_break b =>
      apply hb s b s' hp
      exact ⟨.by_break b, s', hx, ⟨rfl, rfl⟩⟩

theorem Hoare_empty {Sigma A : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) : Hoare P (fun _ _ _ => False) Q := by
  intro _ _ _ _ h
  exact False.elim h

theorem Hoare_cnt_cnt {Sigma A B : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) (a : A) :
    (forall s, P s -> Q a s) ->
      Hoare P (@continue_case Sigma A B (.by_continue a)) Q := by
  intro h
  exact Hoare_ret' P Q a h

theorem Hoare_brk_brk {Sigma A B : Type} (P : Sigma -> Prop)
    (Q : B -> Sigma -> Prop) (b : B) :
    (forall s, P s -> Q b s) ->
      Hoare P (@break_case Sigma A B (.by_break b)) Q := by
  intro h
  exact Hoare_ret' P Q b h

theorem Hoare_brk_cnt {Sigma A B : Type} (P : Sigma -> Prop)
    (Q : B -> Sigma -> Prop) (a : A) :
    Hoare P (@break_case Sigma A B (.by_continue a)) Q :=
  Hoare_empty P Q

theorem Hoare_cnt_brk {Sigma A B : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) (b : B) :
    Hoare P (@continue_case Sigma A B (.by_break b)) Q :=
  Hoare_empty P Q

theorem Hoare_proequiv {Sigma A : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (Q : A -> Sigma -> Prop) :
    Sets.equiv c1 c2 -> Hoare P c1 Q -> Hoare P c2 Q := by
  intro he h s a s' hp hm
  exact h s a s' hp ((he s a s').mpr hm)

theorem Hoare_post_true {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) : Hoare P c (fun _ _ => True) := by
  intro _ _ _ _ _
  trivial

theorem Hoare_progrefine {Sigma A : Type} (c1 c2 : program Sigma A)
    (P : Sigma -> Prop) (Q : A -> Sigma -> Prop) :
    Sets.included c2 c1 -> Hoare P c1 Q -> Hoare P c2 Q := by
  intro hi h s a s' hp hm
  exact h s a s' hp (hi s a s' hm)

theorem Hoare_skip {Sigma A B : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (f : A -> program Sigma B)
    (Q : B -> Sigma -> Prop) :
    (forall a, Hoare (fun _ => True) (f a) Q) ->
      Hoare P (bind c f) Q := by
  intro h
  apply Hoare_bind (Q := fun _ _ => True)
  · exact Hoare_post_true P c
  · exact h

theorem Hoare_stateless {Sigma A : Type} (P : Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (P -> Hoare (fun _ => True) c Q) -> Hoare (fun _ => P) c Q := by
  intro h s a s' hp hm
  exact h hp s a s' trivial hm

theorem Hoare_stateless' {Sigma A : Type} (P : Prop)
    (P' : Sigma -> Prop) (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (P -> Hoare P' c Q) <-> Hoare (fun s => P' s /\ P) c Q := by
  constructor
  · intro h s a s' hp hm
    exact h hp.2 s a s' hp.1 hm
  · intro h hp s a s' hp' hm
    exact h s a s' ⟨hp', hp⟩ hm

theorem Hoare_equiv_iff {Sigma A : Type} (P : Sigma -> Prop)
    (c1 c2 : program Sigma A) (Q : A -> Sigma -> Prop) :
    Sets.equiv c1 c2 -> (Hoare P c1 Q <-> Hoare P c2 Q) := by
  intro h
  constructor
  · exact Hoare_proequiv c1 c2 P Q h
  · exact Hoare_proequiv c2 c1 P Q (fun s a s' => (h s a s').symm)

theorem Hoare_state_intro {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) :
    (forall s0, P s0 -> Hoare (fun s => s = s0) c Q) -> Hoare P c Q := by
  intro h s a s' hp hm
  exact h s hp s a s' rfl hm

theorem Hoare_step_s {Sigma A : Type} (s0 : Sigma) (c : program Sigma A) :
    Hoare (fun s => s = s0) c (fun a s1 => c s0 a s1) := by
  intro s a s' hs hm
  subst s
  exact hm

theorem Hoare_update_s {Sigma : Type} (s0 : Sigma)
    (f : Sigma -> Sigma -> Prop) :
    Hoare (fun s => s = s0) (update f) (fun _ s1 => f s0 s1) := by
  intro s _ s' hs hm
  subst s
  exact hm

theorem Hoare_update' {Sigma : Type} (s0 : Sigma) (f : Sigma -> Sigma) :
    Hoare (fun s => s = s0) (update' f) (fun _ s1 => s1 = f s0) := by
  intro s _ s' hs hm
  subst s
  exact hm

theorem Hoare_get_s {Sigma A : Type} (s0 : Sigma)
    (Pa : Sigma -> A -> Prop) :
    Hoare (fun s => s = s0) (get Pa)
      (fun a s1 => s1 = s0 /\ Pa s0 a) := by
  intro s a s' hs
  rintro ⟨ha, hss⟩
  subst s
  subst s'
  exact ⟨rfl, ha⟩

theorem Hoare_get' {Sigma A : Type} (s0 : Sigma) (fa : Sigma -> A) :
    Hoare (fun s => s = s0) (get' fa)
      (fun a s1 => s1 = s0 /\ a = fa s0) := by
  exact Hoare_get_s s0 (fun s a => a = fa s)

theorem Hoare_fix {Sigma A B : Type} (P : A -> Sigma -> Prop)
    (Q : A -> B -> Sigma -> Prop)
    (F : (A -> program Sigma B) -> A -> program Sigma B) (a : A) :
    (forall W : A -> program Sigma B,
      (forall a, Hoare (P a) (W a) (Q a)) ->
      forall a, Hoare (P a) (F W a) (Q a)) ->
    Hoare (P a) (Lfix F a) (Q a) := by
  intro h s b s' hp hm
  change exists n : Nat, FP.nat_iter n F Sets.empty a s b s' at hm
  rcases hm with ⟨n, hn⟩
  have hi : forall n a, Hoare (P a) (FP.nat_iter n F Sets.empty a) (Q a) := by
    intro n
    induction n with
    | zero =>
        intro a _ _ _ _ hempty
        exact False.elim hempty
    | succ n ih =>
        simpa only [FP.nat_iter] using h (FP.nat_iter n F Sets.empty) ih
  exact hi n a s b s' hp hn

theorem Hoare_fix' {Sigma B : Type} (P : Sigma -> Prop)
    (Q : B -> Sigma -> Prop) (F : program Sigma B -> program Sigma B) :
    (forall W : program Sigma B, Hoare P W Q -> Hoare P (F W) Q) ->
      Hoare P (Lfix F) Q := by
  intro h s b s' hp hm
  change exists n : Nat, FP.nat_iter n F Sets.empty s b s' at hm
  rcases hm with ⟨n, hn⟩
  have hi : forall n, Hoare P (FP.nat_iter n F Sets.empty) Q := by
    intro n
    induction n with
    | zero =>
        intro _ _ _ _ hempty
        exact False.elim hempty
    | succ n ih => simpa only [FP.nat_iter] using h _ ih
  exact hi n s b s' hp hn

theorem Hoare_repeat_break {Sigma A B : Type}
    (body : A -> program Sigma (CntOrBrk A B))
    (P : A -> Sigma -> Prop) (Q : B -> Sigma -> Prop) :
    (forall a, Hoare (P a) (body a) (fun x s => match x with
      | .by_continue a' => P a' s
      | .by_break b => Q b s)) ->
    forall a, Hoare (P a) (repeat_break body a) Q := by
  intro h
  unfold repeat_break
  intro a
  apply Hoare_fix P (fun _ => Q) (repeat_break_f body) a
  intro W ih a
  unfold repeat_break_f
  apply Hoare_bind (Q := fun x s => match x with
    | .by_continue a' => P a' s
    | .by_break b => Q b s)
  · exact h a
  · intro x
    cases x with
    | by_continue a' => exact ih a'
    | by_break b => exact Hoare_ret Q b

theorem Hoare_repeat_break' {Sigma A B : Type}
    (body : A -> program Sigma (CntOrBrk A B))
    (P : A -> Sigma -> Prop) (Q : B -> Sigma -> Prop) :
    (forall a, Hoare (P a) (x <- body a ;; continue_case x) P) ->
    (forall a, Hoare (P a) (x <- body a ;; break_case x) Q) ->
    forall a, Hoare (P a) (repeat_break body a) Q := by
  intro hc hb
  apply Hoare_repeat_break
  intro a
  exact Hoare_sum (P a) (body a) P Q (hc a) (hb a)

theorem Hoare_repeat_break_noin {Sigma B : Type}
    (body : program Sigma (CntOrBrk Unit B))
    (P : Sigma -> Prop) (Q : B -> Sigma -> Prop) :
    Hoare P body (fun ab s => match ab with
      | .by_continue _ => P s
      | .by_break b => Q b s) ->
    Hoare P (repeat_break_noin body) Q := by
  intro h
  unfold repeat_break_noin
  apply Hoare_fix'
  intro W ih
  unfold repeat_break_f_noinput
  apply Hoare_bind (Q := fun ab s => match ab with
    | .by_continue _ => P s
    | .by_break b => Q b s)
  · exact h
  · intro ab
    cases ab with
    | by_continue _ => exact ih
    | by_break b => exact Hoare_ret Q b

def weakestpre {Sigma A : Type} (c : program Sigma A)
    (Q : A -> Sigma -> Prop) : Sigma -> Prop :=
  fun s => forall a s', c s a s' -> Q a s'

def valid_angelic_triple {Sigma A : Type} (P : Sigma -> Prop)
    (c : program Sigma A) (Q : A -> Sigma -> Prop) : Prop :=
  forall s, P s -> exists a s', c s a s' /\ Q a s'

theorem wp_spec {Sigma A : Type} (c : program Sigma A)
    (s1 s2 : Sigma) (a : A) (Q : A -> Sigma -> Prop) :
    weakestpre c Q s1 -> c s1 a s2 -> Q a s2 := by
  exact fun h => h a s2

theorem wp_self {Sigma A : Type} (c : program Sigma A) (s : Sigma) :
    weakestpre c (fun a s' => c s a s') s := by
  intro _ _ h
  exact h

theorem wp_Hoare {Sigma A : Type} (c : program Sigma A)
    (Q : A -> Sigma -> Prop) : Hoare (weakestpre c Q) c Q := by
  intro s a s' h
  exact h a s'

theorem wp_Hoare_iff {Sigma A : Type} (P : Sigma -> Prop)
    (Q : A -> Sigma -> Prop) (c : program Sigma A) :
    Sets.included P (weakestpre c Q) <-> Hoare P c Q := by
  constructor
  · intro h s a s' hp hm
    exact h s hp a s' hm
  · intro h s hp a s' hm
    exact h s a s' hp hm

syntax "state_hoare_auto" : tactic
syntax "state_hoare_step" : tactic
syntax "__state_hoare_guard_get_bind" : tactic
syntax "__state_hoare_guard_update_bind" : tactic

namespace HoareDispatchTactic

open Lean Meta Elab Tactic

private def guardBindSource (expected : Name) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    unless target.consumeMData.getAppFn.isConstOf ``Hoare do
      throwError "state_hoare_auto: expected a StateRelMonad.Hoare goal"
    let hoareArgs := target.getAppArgs
    unless hoareArgs.size >= 2 do
      throwError "state_hoare_auto: malformed Hoare goal"
    let programTerm := hoareArgs[hoareArgs.size - 2]!
    unless programTerm.consumeMData.getAppFn.isConstOf ``bind do
      throwError "state_hoare_auto: expected a bind program"
    let bindArgs := programTerm.getAppArgs
    unless bindArgs.size >= 2 do
      throwError "state_hoare_auto: malformed bind program"
    let source := bindArgs[bindArgs.size - 2]!
    unless source.consumeMData.getAppFn.isConstOf expected do
      throwError "state_hoare_auto: bind source has a different constructor"

end HoareDispatchTactic

elab_rules : tactic
  | `(tactic| __state_hoare_guard_get_bind) =>
      HoareDispatchTactic.guardBindSource ``get
  | `(tactic| __state_hoare_guard_update_bind) =>
      HoareDispatchTactic.guardBindSource ``update

macro_rules
  | `(tactic| state_hoare_step) =>
      `(tactic|
        first
          | (__state_hoare_guard_get_bind;
              apply StateRelMonad.hoare_get_bind_tactic_rule;
              intro)
          | (__state_hoare_guard_update_bind;
              apply StateRelMonad.hoare_update_bind_tactic_rule;
              intro)
          | (apply StateRelMonad.Hoare_ret'; repeat intro; simp_all)
          | (rel_rw [StateRelMonad.bind_assoc] <;> try state_hoare_step)
          | (rel_rw [StateRelMonad.bind_choice_equiv] <;> try state_hoare_step)
          | rel_rw [StateRelMonad.bind_ret_left]
          | (apply StateRelMonad.Hoare_any_bind <;> intro)
          | (apply StateRelMonad.Hoare_assume_bind' <;> intro)
          | apply StateRelMonad.Hoare_assume_bind
          | apply StateRelMonad.Hoare_choice
          | (apply StateRelMonad.Hoare_bind <;> first | apply StateRelMonad.Hoare_step | intro)
          | (simp [StateRelMonad.Hoare, StateRelMonad.continue_case,
              StateRelMonad.break_case]; done))

macro_rules
  | `(tactic| state_hoare_auto) =>
      `(tactic|
        first
          | (__state_hoare_guard_get_bind;
              apply StateRelMonad.hoare_get_bind_tactic_rule;
              intro;
              state_hoare_auto)
          | (__state_hoare_guard_update_bind;
              apply StateRelMonad.hoare_update_bind_tactic_rule;
              intro;
              state_hoare_auto)
          | (apply StateRelMonad.Hoare_ret'; repeat intro; simp_all)
          | (rel_rw [StateRelMonad.bind_assoc] <;> state_hoare_auto)
          | (rel_rw [StateRelMonad.bind_choice_equiv] <;> state_hoare_auto)
          | (rel_rw [StateRelMonad.bind_ret_left] <;> state_hoare_auto)
          | (apply StateRelMonad.Hoare_any_bind <;> state_hoare_auto)
          | (apply StateRelMonad.Hoare_assume_bind' <;> state_hoare_auto)
          | (apply StateRelMonad.Hoare_assume_bind <;> state_hoare_auto)
          | (apply StateRelMonad.Hoare_choice <;> state_hoare_auto)
          | (apply StateRelMonad.Hoare_bind <;> state_hoare_auto)
          | (simp [StateRelMonad.Hoare, StateRelMonad.continue_case,
              StateRelMonad.break_case]; done)
          | assumption
          | trivial
          | (intro; state_hoare_auto)
          | simp_all)

syntax "state_hoare_fix_nolv_auto " term:max : tactic

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
    throwError "state_hoare_fix_nolv_auto: expected a StateRelMonad.Hoare goal"
  let hoareArgs := target.getAppArgs
  unless hoareArgs.size >= 3 do
    throwError "state_hoare_fix_nolv_auto: malformed Hoare goal"
  let pre := hoareArgs[hoareArgs.size - 3]!
  let programTerm := hoareArgs[hoareArgs.size - 2]!
  let post := hoareArgs[hoareArgs.size - 1]!
  unless programTerm.consumeMData.getAppFn.isConstOf ``FP.Lfix do
    throwError "state_hoare_fix_nolv_auto: expected Lfix applied to an argument"
  let fixArgs := programTerm.getAppArgs
  unless fixArgs.size >= 2 do
    throwError "state_hoare_fix_nolv_auto: malformed Lfix application"
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
    throwError "state_hoare_fix_nolv_auto: supplied type does not match the Lfix argument type"

private def abstractOne (name : Name) (type term body : Expr) : MetaM Expr := do
  let abstracted <- kabstract body term
  return mkLambda name BinderInfo.default type abstracted

private def runNoLogicVar (aTypeSyntax : Lean.Syntax) : TacticM Unit := do
  let (goal, data) ← readGoal
  withMainContext do
    let aType ← inferType data.arg
    checkTypeArgument aTypeSyntax aType
    let preFamily <- abstractOne `a aType data.arg data.pre
    let postFamily <- abstractOne `a aType data.arg data.post
    let proof ← mkAppM ``Hoare_fix
      #[preFamily, postFamily, data.fn, data.arg]
    replaceMainGoal (← goal.apply proof)

end HoareFixTactic

elab_rules : tactic
  | `(tactic| state_hoare_fix_nolv_auto $A:term) =>
      HoareFixTactic.runNoLogicVar A

end MonadLib.StateRelMonad
