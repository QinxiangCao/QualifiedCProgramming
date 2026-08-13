import MonadLib.Examples.kmp

open MonadLib
open scoped MonadNotation

namespace UnifiedTacticTests

abbrev Sigma := Int

example {A : Type} (a : A) :
    StateRelMonad.Hoare (fun _ : Sigma => True)
      (StateRelMonad.ret a) (fun r _ => r = a) := by
  hoare_auto

example {A : Type} (a : A) :
    Hoare (fun _ : Sigma => True)
      (MonadErr.ret a) (fun r _ => r = a) := by
  hoare_auto

example {A : Type} (a : A) :
    StateRelMonad.Hoare (fun _ : Sigma => True)
      (StateRelMonad.ret a) (fun r _ => r = a) := by
  hoare_step

example {A : Type} (a : A) :
    Hoare (fun _ : Sigma => True)
      (MonadErr.ret a) (fun r _ => r = a) := by
  hoare_step

example (P : Sigma -> Prop) :
    Hoare P
      (MonadLib.assert True ;;
        (MonadErr.ret 3 : program Sigma Int))
      (fun r s => r = 3 /\ P s) := by
  hoare_step
  hoare_step

example (P : Sigma -> Prop) (a b : Int) :
    Hoare P
      (x <-
        (MonadLib.assert True ;;
          choice
            (testPure True ;; MonadLib.continue a)
            (testPure False ;; MonadLib.break b) :
          program Sigma (CntOrBrk Int Int)) ;;
        continue_case x)
      (fun r s => r = a /\ P s) := by
  hoare_auto

example (P : Sigma -> Prop) (a b : Int) :
    Hoare P
      (x <-
        (MonadLib.assert True ;;
          choice
            (testPure False ;; MonadLib.continue a)
            (testPure True ;; MonadLib.break b) :
          program Sigma (CntOrBrk Int Int)) ;;
        break_case x)
      (fun r s => r = b /\ P s) := by
  hoare_auto

private def wrappedConjPost (P : Sigma -> Prop) (_ : Nat) (s : Sigma) : Prop :=
  P s /\ True

example (P : Sigma -> Prop) (c : program Sigma Nat)
    (h : Hoare P c (wrappedConjPost P)) :
    Hoare P c (wrappedConjPost P) := by
  hoare_conj
  exact h

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : StateRelMonad.safeExec P
      (StateRelMonad.choice
        (StateRelMonad.ret 1)
        (StateRelMonad.ret 2)) X) :
    StateRelMonad.safeExec P (StateRelMonad.ret 1) X := by
  safe_choice_l h
  exact h

example (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop)
    (h : StateRelMonad.safeExec P
      (StateRelMonad.test' True ;;
        (StateRelMonad.ret () : StateRelMonad.program Sigma Unit)) X) :
    StateRelMonad.safeExec P (StateRelMonad.ret ()) X := by
  safe_step h
  exact h

example : StateRelMonad.hs_eval
    (StateRelMonad.test' True ;;
      (StateRelMonad.ret () : StateRelMonad.program Sigma Unit))
    (fun _ => True) (fun _ => True) () := by
  state_abs_test_step
  · trivial
  · state_abs_ret_step

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (c : StateRelMonad.program Sigma Nat)
    (h : StateRelMonad.safeExec P
      (StateRelMonad.bind (StateRelMonad.ret ()) (fun _ => c)) X) :
    StateRelMonad.safeExec P c X := by
  prog_nf in h
  exact h

#check StateRelMonad.safeExec_programrefine_impl_Proper
#check StateRelMonad.safeExec_X_subset_impl_Proper
#check StateRelMonad.safeExec_programequiv_iff_Proper
#check StateRelMonad.hseval_programequiv_Proper

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (c1 c2 : StateRelMonad.program Sigma Nat)
    (he : Sets.equiv c1 c2) (h : StateRelMonad.safeExec P c1 X) :
    StateRelMonad.safeExec P c2 X := by
  rel_rw [he] at h
  exact h

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (c : StateRelMonad.program Sigma Nat)
    (h : StateRelMonad.safeExec P
      (MonadLib.bind c (fun x => MonadLib.ret x)) X) :
    StateRelMonad.safeExec P c X := by
  prog_nf in h
  exact h

example (P : Sigma -> Prop) (X : Int -> Sigma -> Prop)
    (body : Int -> program Sigma (CntOrBrk Int Int)) (a : Int)
    (h : safeExec P (repeat_break body a) X) :
    safeExec P
      (res <- body a ;;
        match res with
        | .by_continue a' => repeat_break body a'
        | .by_break b => MonadErr.ret b)
      X := by
  err_unfold_loop in h
  apply safeExec_proequiv _ _ P X _ h
  apply bind_equiv
  · exact AUXLib.Equivalence.refl _
  · intro res
    cases res <;> exact AUXLib.Equivalence.refl _

#check MonadLib.Examples.kmp.inner_loop_prop
#check MonadLib.Examples.kmp.constr_loop_sound
#check MonadLib.Examples.kmp.match_loop_sound

example (r : CntOrBrk Nat Nat) :
    equiv
      (MonadErr.bind
        (match r with
        | .by_continue a => MonadErr.ret a
        | .by_break b => MonadErr.ret b)
        (fun x => MonadErr.ret (x + 1)) : program Sigma Nat)
      (match r with
      | .by_continue a => MonadErr.bind (MonadErr.ret a) (fun x => MonadErr.ret (x + 1))
      | .by_break b => MonadErr.bind (MonadErr.ret b) (fun x => MonadErr.ret (x + 1))) := by
  monad_equiv

-- Every source-style public dispatcher is exercised for both monad families.

example :
    Sets.equiv
      (StateRelMonad.bind (StateRelMonad.ret ())
        (fun _ => StateRelMonad.ret 1) : StateRelMonad.program Sigma Nat)
      (StateRelMonad.ret 1) := by
  prog_nf
  exact Sets_equiv_refl _

example :
    equiv
      (MonadErr.bind (MonadErr.ret ())
        (fun _ => MonadErr.ret 1) : program Sigma Nat)
      (MonadErr.ret 1) := by
  prog_nf

example
    (h : Sets.equiv
      (StateRelMonad.bind (StateRelMonad.ret ())
        (fun _ => StateRelMonad.ret 1) : StateRelMonad.program Sigma Nat)
      (StateRelMonad.ret 1)) : True := by
  prog_nf in h
  trivial

example
    (h : equiv
      (MonadErr.bind (MonadErr.ret ())
        (fun _ => MonadErr.ret 1) : program Sigma Nat)
      (MonadErr.ret 1)) : True := by
  prog_nf in h
  trivial

example : StateRelMonad.mono_cont
    (fun W : StateRelMonad.program Sigma Unit =>
      StateRelMonad.choice W (StateRelMonad.ret ())) := by
  mono_cont_auto

example : mono_cont
    (fun W : program Sigma Unit => choice W (MonadErr.ret ())) := by
  mono_cont_auto

example : StateRelMonad.mono_cont
    (fun W : StateRelMonad.program Sigma Unit =>
      FP.Lfix (fun X => StateRelMonad.choice W X)) := by
  mono_cont_auto

#check StateRelMonad.mono_Lfix
#check StateRelMonad.Lfix_seq_cont_general
#check StateRelMonad.mono_cont_Lfix
#check StateRelMonad.forset_unfold
#print axioms StateRelMonad.mono_cont_Lfix
#print axioms StateRelMonad.forset_unfold

example (body : StateRelMonad.program Sigma Unit) :
    Sets.equiv (StateRelMonad.Repeat body)
      (body ;; StateRelMonad.Repeat body) := by
  unfold_loop

example (body : program Sigma Unit) :
    equiv (whileP (fun _ => False) body)
      (choice
        (test (fun _ => False) ;; body ;; whileP (fun _ => False) body)
        (test (fun _ => Not False) ;; MonadErr.ret ())) := by
  unfold_loop

example (body : StateRelMonad.program Sigma Unit)
    (h : Sets.equiv (StateRelMonad.Repeat body)
      (StateRelMonad.Repeat body)) : True := by
  unfold_loop in h
  trivial

example (body : Nat -> program Sigma (CntOrBrk Nat Bool))
    (h : equiv (repeat_break body) (repeat_break body)) : True := by
  unfold_loop in h
  trivial

example (P : Sigma -> Prop) :
    StateRelMonad.Hoare P (StateRelMonad.ret ())
      (fun _ s => P s) := by
  unfold_loop
  hoare_auto

example (P : Sigma -> Prop) :
    Hoare P (MonadErr.ret ()) (fun _ s => P s) := by
  unfold_loop
  hoare_auto

private def stateConstFixBody
    (_ : Nat -> StateRelMonad.program Sigma Unit) (_ : Nat) :
    StateRelMonad.program Sigma Unit :=
  StateRelMonad.ret ()

example (a : Nat) :
    StateRelMonad.Hoare (fun _ : Sigma => True)
      (FP.Lfix stateConstFixBody a) (fun _ _ => True) := by
  hoare_fix_nolv_auto Nat
  intro W hW a'
  hoare_auto

private def errConstFixBody
    (_ : Nat -> program Sigma Unit) (_ : Nat) : program Sigma Unit :=
  MonadErr.ret ()

example (a : Nat) :
    Hoare (fun _ : Sigma => True) (FP.BW_fix errConstFixBody a)
      (fun _ _ => True) := by
  hoare_fix_nolv_auto Nat
  intro W hW a'
  hoare_auto

example (P P' : Sigma -> Prop)
    (c1 : StateRelMonad.program Sigma Nat)
    (c2 : Nat -> StateRelMonad.program Sigma Nat)
    (X : Nat -> Sigma -> Prop) (a : Nat)
    (hsafe : StateRelMonad.safeExec P (StateRelMonad.bind c1 c2) X)
    (heval : StateRelMonad.hs_eval c1 P P' a) :
    StateRelMonad.safeExec P' (c2 a) X := by
  prove_by_one_abs_step a
  fail_if_success clear hsafe
  exact heval

example (P P' : Sigma -> Prop) (c1 : program Sigma Nat)
    (c2 : Nat -> program Sigma Nat) (X : Nat -> Sigma -> Prop) (a : Nat)
    (hsafe : safeExec P (MonadErr.bind c1 c2) X)
    (heval : hs_eval c1 P P' a) : safeExec P' (c2 a) X := by
  prove_by_one_abs_step a
  fail_if_success clear hsafe
  exact heval

example (P : Sigma -> Prop) :
    StateRelMonad.hs_eval
      (StateRelMonad.bind (StateRelMonad.ret ()) (fun _ =>
        StateRelMonad.choice (StateRelMonad.ret 1) (StateRelMonad.ret 2)))
      P P 1 := by
  abs_choice_left
  abs_ret_step

example (P : Sigma -> Prop) :
    hs_eval (choice (MonadErr.ret 1) (MonadErr.ret 2) : program Sigma Nat)
      P P 1 := by
  abs_choice_left
  abs_ret_step

example (P : Sigma -> Prop) :
    StateRelMonad.hs_eval
      (StateRelMonad.bind (StateRelMonad.ret ()) (fun _ =>
        StateRelMonad.choice (StateRelMonad.ret 1) (StateRelMonad.ret 2)))
      P P 2 := by
  abs_choice_right
  abs_ret_step

example (P : Sigma -> Prop) :
    hs_eval (choice (MonadErr.ret 1) (MonadErr.ret 2) : program Sigma Nat)
      P P 2 := by
  abs_choice_right
  abs_ret_step

example (P : Sigma -> Prop) :
    StateRelMonad.hs_eval
      (StateRelMonad.test' True ;;
        (StateRelMonad.ret () : StateRelMonad.program Sigma Unit))
      P P () := by
  abs_test_step
  · trivial
  · abs_ret_step

example (P : Sigma -> Prop) :
    hs_eval (testPure True ;; (MonadErr.ret () : program Sigma Unit))
      P P () := by
  abs_test_step
  · trivial
  · abs_ret_step

example (P : Sigma -> Prop) :
    StateRelMonad.hs_eval (StateRelMonad.ret ()) P P () := by
  abs_ret_step

example (P : Sigma -> Prop) :
    hs_eval (MonadErr.ret ()) P P () := by
  abs_ret_step

example (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop)
    (h : StateRelMonad.safeExec P
      (StateRelMonad.test' True ;;
        (StateRelMonad.ret () : StateRelMonad.program Sigma Unit)) X) :
    StateRelMonad.safeExec P (StateRelMonad.ret ()) X := by
  safe_step h
  exact h

example (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop)
    (h : safeExec P
      (testPure True ;; (MonadErr.ret () : program Sigma Unit)) X) :
    safeExec P (MonadErr.ret ()) X := by
  safe_step h
  exact h

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : StateRelMonad.safeExec P
      (StateRelMonad.choice (StateRelMonad.ret 1) (StateRelMonad.ret 2)) X) :
    StateRelMonad.safeExec P (StateRelMonad.ret 1) X := by
  safe_choice_l h
  exact h

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : safeExec P
      (choice (MonadErr.ret 1) (MonadErr.ret 2) : program Sigma Nat) X) :
    safeExec P (MonadErr.ret 1) X := by
  safe_choice_l h
  exact h

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : StateRelMonad.safeExec P
      (StateRelMonad.choice (StateRelMonad.ret 1) (StateRelMonad.ret 2)) X) :
    StateRelMonad.safeExec P (StateRelMonad.ret 2) X := by
  safe_choice_r h
  exact h

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : safeExec P
      (choice (MonadErr.ret 1) (MonadErr.ret 2) : program Sigma Nat) X) :
    safeExec P (MonadErr.ret 2) X := by
  safe_choice_r h
  exact h

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : StateRelMonad.safeExec P (StateRelMonad.ret 1) X) :
    StateRelMonad.safeExec P
      (StateRelMonad.bind (StateRelMonad.ret ())
        (fun _ => StateRelMonad.ret 1)) X := by
  safe_equiv
  exact Sets_equiv_refl _

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : safeExec P (MonadErr.ret 1 : program Sigma Nat) X) :
    safeExec P
      (MonadErr.bind (MonadErr.ret ()) (fun _ => MonadErr.ret 1)) X := by
  safe_equiv

example (P : Sigma -> Prop) (R : Sigma -> Nat -> Prop)
    (g : Nat -> StateRelMonad.program Sigma Unit)
    (Q : Unit -> Sigma -> Prop)
    (h : forall a, StateRelMonad.Hoare
      (fun s => R s a /\ P s) (g a) Q) :
    StateRelMonad.Hoare P
      (StateRelMonad.bind (StateRelMonad.get R) g) Q := by
  hoare_step
  exact h _

example (P : Sigma -> Prop) (R : Sigma -> Sigma -> Prop)
    (g : Unit -> StateRelMonad.program Sigma Unit)
    (Q : Unit -> Sigma -> Prop)
    (h : forall s0, StateRelMonad.Hoare
      (fun s2 => R s0 s2 /\ P s0) (g ()) Q) :
    StateRelMonad.Hoare P
      (StateRelMonad.bind (StateRelMonad.update R) g) Q := by
  hoare_step
  exact h _

example {A : Type} (a : A) :
    Hoare
      (fun s : Sigma => StateRelMonad.ret () s () s)
      (MonadErr.ret a)
      (fun r s => r = a /\ StateRelMonad.ret () s () s) := by
  hoare_auto

example {A : Type} (a : A) :
    StateRelMonad.Hoare
      (fun s : Sigma => (MonadErr.ret () : program Sigma Unit).nrm s () s)
      (StateRelMonad.ret a)
      (fun r s => r = a /\
        (MonadErr.ret () : program Sigma Unit).nrm s () s) := by
  hoare_auto

example : True := by
  fail_if_success hoare_auto
  trivial

example (h : True) : True := by
  fail_if_success safe_step h
  exact h

end UnifiedTacticTests
