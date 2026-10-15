import MonadLib.StateRelMonad.StateRelMonad

namespace P12Tests.StateRel

open MonadLib.StateRelMonad
open scoped MonadLib.MonadNotation

def rec_body (W : Nat -> program Nat Nat) (n : Nat) : program Nat Nat :=
  choice (ret n) (W n)

theorem rec_body_mono_cont : mono_cont rec_body := by
  unfold rec_body
  mono_cont_auto

theorem rec_unfold_test :
    Sets.equiv (Rec rec_body) (rec_body (Rec rec_body)) := by
  exact Rec_unfold rec_body rec_body_mono_cont

example : mono_cont (fun W : Nat -> program Nat Nat => W) := by
  mono_cont_auto

example : mono_cont (fun _W : Nat -> program Nat Nat =>
    (ret 0 : program Nat Nat)) := by
  mono_cont_auto

example : mono_cont (fun W : Nat -> program Nat Nat => W 0) := by
  mono_cont_auto

example : mono_cont (fun W : Nat -> program Nat Nat =>
    x <- W 0 ;; W x) := by
  mono_cont_auto

example : mono_cont (fun W : Nat -> program Nat Nat =>
    choice (W 0) (W 1)) := by
  mono_cont_auto

example : mono_cont (fun W : Nat -> program Nat Nat =>
    match true with
    | true => W 0
    | false => ret 0) := by
  mono_cont_auto

def nested_rec (W : Nat -> program Nat Nat) : Nat -> program Nat Nat :=
  Rec (fun R n => choice (W n) (R n))

theorem nested_rec_mono_cont : mono_cont nested_rec := by
  unfold nested_rec
  mono_cont_auto

theorem unfold_rec_goal_test :
    Sets.equiv (Rec rec_body) (rec_body (Rec rec_body)) := by
  unfold_rec
  exact Sets_equiv_refl _

theorem unfold_rec_hyp_test (X : Nat -> program Nat Nat) :
    Sets.equiv (Rec rec_body) X -> Sets.equiv (rec_body (Rec rec_body)) X := by
  intro h
  unfold_rec in h
  exact h

theorem unfold_rec_right_goal_test :
    Sets.equiv (rec_body (Rec rec_body)) (Rec rec_body) := by
  unfold_rec
  exact Sets_equiv_refl _

theorem unfold_rec_right_hyp_test (X : Nat -> program Nat Nat) :
    Sets.equiv X (Rec rec_body) -> Sets.equiv X (rec_body (Rec rec_body)) := by
  intro h
  unfold_rec in h
  exact h

def hoare_body (_ : Nat -> program Nat Nat) (n : Nat) : program Nat Nat :=
  ret n

theorem Hoare_Rec_test (n : Nat) :
    Hoare (fun _ => True) (Rec hoare_body n) (fun r _ => r = n) := by
  hoare_rec_nolv_auto Nat
  intro W _ a
  unfold hoare_body
  apply Hoare_ret'
  simp

theorem Hoare_Rec_direct_tactic_test (n : Nat) :
    Hoare (fun _ => True) (Rec hoare_body n) (fun r _ => r = n) := by
  hoare_rec (fun _ _ => True) (fun a r _ => r = a)
  intro W _ a
  unfold hoare_body
  apply Hoare_ret'
  simp

theorem old_hoare_fix_tactic_on_Rec_test (n : Nat) :
    Hoare (fun _ => True) (Rec hoare_body n) (fun r _ => r = n) := by
  hoare_fix_nolv_auto Nat
  intro W _ a
  unfold hoare_body
  apply Hoare_ret'
  simp

theorem old_hoare_fix_tactic_on_Lfix_test (n : Nat) :
    Hoare (fun _ => True) (FP.Lfix hoare_body n) (fun r _ => r = n) := by
  hoare_fix_nolv_auto Nat
  intro W _ a
  unfold hoare_body
  apply Hoare_ret'
  simp

theorem Hoare_Rec_logicv_tactic_test (n c : Nat) :
    Hoare (fun s => s = c) (Rec hoare_body n)
      (fun r s => r = n /\ s = c) := by
  hoare_rec_lv_auto Nat Nat c
  intro W _ a c'
  unfold hoare_body
  apply Hoare_ret'
  intro s hs
  exact ⟨rfl, hs⟩

theorem old_hoare_fix_logicv_tactic_on_Rec_test (n c : Nat) :
    Hoare (fun s => s = c) (Rec hoare_body n)
      (fun r s => r = n /\ s = c) := by
  hoare_fix_lv_auto Nat Nat c
  intro W _ a c'
  unfold hoare_body
  apply Hoare_ret'
  intro s hs
  exact ⟨rfl, hs⟩

theorem old_hoare_fix_logicv_tactic_on_Lfix_test (n c : Nat) :
    Hoare (fun s => s = c) (FP.Lfix hoare_body n)
      (fun r s => r = n /\ s = c) := by
  hoare_fix_lv_auto Nat Nat c
  intro W _ a c'
  unfold hoare_body
  apply Hoare_ret'
  intro s hs
  exact ⟨rfl, hs⟩

example (n c : Nat)
    (P2 : Nat -> Nat -> Nat -> Prop)
    (Q2 : Nat -> Nat -> Nat -> Nat -> Prop)
    (hfixed : forall (a d : Nat), Hoare (P2 a d) (Rec hoare_body a) (Q2 a d))
    (hstep : forall W : Nat -> program Nat Nat,
      (forall (a d : Nat), Hoare (P2 a d) (W a) (Q2 a d)) ->
      (forall (a _c : Nat), Hoare (fun _ => True) (W a) (fun _ _ => True)) ->
      (forall (a d : Nat), Hoare (P2 a d) (hoare_body W a) (Q2 a d)) ->
      forall (a _c : Nat), Hoare (fun _ => True) (hoare_body W a)
        (fun _ _ => True)) :
    Hoare (fun _ => True) (Rec hoare_body n) (fun _ _ => True) := by
  hoare_rec_lv_auto_conj' Nat Nat c
  · exact hfixed
  · exact hstep

example (n c : Nat)
    (P2 : Nat -> Nat -> Nat -> Prop)
    (Q2 : Nat -> Nat -> Nat -> Nat -> Prop)
    (hfixed : forall (a d : Nat), Hoare (P2 a d) (Rec hoare_body a) (Q2 a d))
    (hstep : forall W : Nat -> program Nat Nat,
      (forall (a d : Nat), Hoare (P2 a d) (W a) (Q2 a d)) ->
      (forall (a _c : Nat), Hoare (fun _ => True) (W a) (fun _ _ => True)) ->
      forall (a _c : Nat), Hoare (fun _ => True) (hoare_body W a)
        (fun _ _ => True)) :
    Hoare (fun _ => True) (Rec hoare_body n) (fun _ _ => True) := by
  hoare_fix_lv_auto_conj Nat Nat c
  · exact hfixed
  · exact hstep

example (n c : Nat)
    (P2 : Nat -> Nat -> Nat -> Prop)
    (Q2 : Nat -> Nat -> Nat -> Nat -> Prop)
    (hfixed : forall (a d : Nat), Hoare (P2 a d) (Rec hoare_body a) (Q2 a d))
    (hstep : forall W : Nat -> program Nat Nat,
      (forall (a d : Nat), Hoare (P2 a d) (W a) (Q2 a d)) ->
      (forall (a _c : Nat), Hoare (fun _ => True) (W a) (fun _ _ => True)) ->
      (forall (a d : Nat), Hoare (P2 a d) (hoare_body W a) (Q2 a d)) ->
      forall (a _c : Nat), Hoare (fun _ => True) (hoare_body W a)
        (fun _ _ => True)) :
    Hoare (fun _ => True) (Rec hoare_body n) (fun _ _ => True) := by
  hoare_fix_lv_auto_conj' Nat Nat c
  · exact hfixed
  · exact hstep

example (n c : Nat)
    (P2 : Nat -> Nat -> Nat -> Prop)
    (Q2 : Nat -> Nat -> Nat -> Nat -> Prop)
    (hfixed : forall (a d : Nat), Hoare (P2 a d) (FP.Lfix hoare_body a) (Q2 a d))
    (hstep : forall W : Nat -> program Nat Nat,
      (forall (a d : Nat), Hoare (P2 a d) (W a) (Q2 a d)) ->
      (forall (a _c : Nat), Hoare (fun _ => True) (W a) (fun _ _ => True)) ->
      forall (a _c : Nat), Hoare (fun _ => True) (hoare_body W a)
        (fun _ _ => True)) :
    Hoare (fun _ => True) (FP.Lfix hoare_body n) (fun _ _ => True) := by
  hoare_fix_lv_auto_conj Nat Nat c
  · exact hfixed
  · exact hstep

example (n c : Nat)
    (P2 : Nat -> Nat -> Nat -> Prop)
    (Q2 : Nat -> Nat -> Nat -> Nat -> Prop)
    (hfixed : forall (a d : Nat), Hoare (P2 a d) (FP.Lfix hoare_body a) (Q2 a d))
    (hstep : forall W : Nat -> program Nat Nat,
      (forall (a d : Nat), Hoare (P2 a d) (W a) (Q2 a d)) ->
      (forall (a _c : Nat), Hoare (fun _ => True) (W a) (fun _ _ => True)) ->
      (forall (a d : Nat), Hoare (P2 a d) (hoare_body W a) (Q2 a d)) ->
      forall (a _c : Nat), Hoare (fun _ => True) (hoare_body W a)
        (fun _ _ => True)) :
    Hoare (fun _ => True) (FP.Lfix hoare_body n) (fun _ _ => True) := by
  hoare_fix_lv_auto_conj' Nat Nat c
  · exact hfixed
  · exact hstep

example : True := by
  fail_if_success mono_cont_auto
  fail_if_success unfold_rec
  trivial

end P12Tests.StateRel
