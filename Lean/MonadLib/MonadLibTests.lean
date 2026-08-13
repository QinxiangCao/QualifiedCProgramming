import MonadLib.MonadErr.StateRelMonadErr

universe u v

open MonadLib
open AUXLib
open MonadLib.MonadNotation
open scoped MonadNotation

inductive TestM (A : Type) where
  | mk (value : A)

instance : MonadLib.Monad TestM where
  bind x f := match x with | .mk a => f a
  ret := TestM.mk

instance : MonadLib.FMap TestM where
  fmap f x := match x with | .mk a => .mk (f a)

#check MonadLib.Monad.bind
#check MonadLib.Monad.ret
#check MonadLib.FMap.fmap
#check MonadLib.CntOrBrk
#check MonadLib.by_continue
#check MonadLib.by_break

example {A : Type u} {B : Type v} (a : A) : CntOrBrk A B := by_continue a

example : (return 3 : TestM Nat) = .mk 3 := rfl
example : (x <- TestM.mk 3 ;; return (x + 1)) = .mk 4 := rfl
example : (TestM.mk 3 ;; return 4 : TestM Nat) = .mk 4 := rfl
example : ((fun x => x + 1) <$> TestM.mk 3) = .mk 4 := rfl
example : (((fun x : Nat => TestM.mk (x + 1)) ≫=.) (TestM.mk 3)) = .mk 4 := rfl
example : ((.≫= TestM.mk 3) (fun x => TestM.mk (x + 1))) = .mk 4 := rfl
example : ((≫=) (fun x : Nat => TestM.mk (x + 1)) (TestM.mk 3)) = .mk 4 := rfl
example : ((x, y) <- TestM.mk (3, 4) ;; return (x + y)) = .mk 7 := rfl

namespace MonadErrTests

abbrev State := Int

example : MONAD Nat = program Unit Nat := rfl

def fail {A : Type} : program State A where
  nrm _ _ _ := False
  err _ := True

example : (MonadErr.ret 7 : program State Nat).nrm 3 7 3 := ⟨rfl, rfl⟩
example : (MonadErr.bind (MonadErr.ret 7 : program State Nat)
    (fun n => MonadErr.ret (n + 1))).nrm 3 8 3 :=
  ⟨7, 3, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
example : (MonadErr.bind (MonadErr.ret 7 : program State Nat)
    (fun _ => (fail : program State Nat))).err 3 :=
  Or.inr ⟨7, 3, ⟨rfl, rfl⟩, trivial⟩

example : FP.equiv
    (MonadErr.bind (MonadErr.ret 2 : program State Nat) fun x => MonadErr.ret (x + 1))
    (MonadErr.ret 3) := by
  exact bind_ret_l 2 (fun x => MonadErr.ret (x + 1))

example (c : program State Nat) :
    FP.equiv (MonadErr.bind (MonadErr.ret 2) fun _ => c) c := by
  prog_nf

example (c0 : program State Nat) (c1 : Nat -> program State Nat)
    (c2 : Nat -> program State Nat) :
    FP.equiv (MonadErr.bind (MonadErr.bind c0 c1) c2)
      (MonadErr.bind c0 fun x => MonadErr.bind (c1 x) c2) := by
  prog_nf

example (c0 c1 : program State Nat) (c2 : Nat -> program State Nat) :
    FP.equiv (MonadErr.bind (choice c0 c1) c2)
      (choice (MonadErr.bind c0 c2) (MonadErr.bind c1 c2)) := by
  prog_nf

example (c : program State Nat) :
    FP.equiv (MonadErr.bind c MonadErr.ret) c := by
  prog_nf

example (f : Nat -> Nat) (c : Nat -> Nat -> program State Nat) :
    FP.equiv (fun k => MonadErr.bind (MonadErr.ret (f k)) (c k))
      (fun k => c k (f k)) := by
  prog_nf

example (c0 c1 : program State Nat) (c2 : Nat -> program State Nat)
    (h : FP.equiv (MonadErr.bind (choice c0 c1) c2)
      (choice (MonadErr.bind c0 c2) (MonadErr.bind c1 c2))) : True := by
  prog_nf in h
  trivial

end MonadErrTests

namespace StateRelMonadErrTests

open MonadErr

abbrev Sigma := Int

example : MonadErr.bind (MonadErr.ret 1 : program Sigma Nat)
    (fun x => MonadErr.ret (x + 1)) =
    MonadErr.bind (MonadErr.ret 1) (fun x => MonadErr.ret (x + 1)) := by
  unfold_monad

example (h : MonadErr.bind (MonadErr.ret 1 : program Sigma Nat)
    (fun x => MonadErr.ret (x + 1)) =
    MonadErr.bind (MonadErr.ret 1) (fun x => MonadErr.ret (x + 1))) : True := by
  unfold_monad in h
  trivial

example (P : Sigma -> Prop) :
    Hoare P (MonadErr.ret 3) (fun r s => r = 3 /\ P s) := by
  hoare_auto

example (P : Sigma -> Prop) :
    Hoare P (MonadErr.ret 3) (fun r s => r = 3 /\ P s) := by
  hoare_auto_s

example (P : Sigma -> Prop) :
    Hoare P (MonadErr.ret 3) (fun r s => r = 3 /\ P s) := by
  hoare_step

example (P : Sigma -> Prop) (c : program Sigma Nat)
    (Q : Nat -> Sigma -> Prop) (h : Hoare P c Q) :
    Hoare P (testPure True ;; c) Q := by
  hoare_step

example (P R : Sigma -> Prop) (c : program Sigma Nat)
    (Q : Nat -> Sigma -> Prop)
    (h : Hoare (fun s => P s /\ R s) c Q) :
    Hoare P (test R ;; c) Q := by
  hoare_step

example (P : Sigma -> Prop) (c : program Sigma Nat)
    (Q : Nat -> Sigma -> Prop) (h : Hoare P c Q) :
    Hoare P (assert True ;; c) Q := by
  hoare_step

example (P : Sigma -> Prop) (c1 c2 : program Sigma Nat)
    (Q : Nat -> Sigma -> Prop) (h1 : Hoare P c1 Q)
    (h2 : Hoare P c2 Q) :
    Hoare P (choice c1 c2) Q := by
  hoare_step

example (P : Sigma -> Prop) (a : Nat) :
    Hoare P
      (@continue_case Nat Bool Sigma (.by_continue a))
      (fun r s => r = a /\ P s) := by
  hoare_step

example (P : Sigma -> Prop) (b : Bool) :
    Hoare P
      (@continue_case Nat Bool Sigma (.by_break b))
      (fun _ _ => False) := by
  hoare_step

example (P : Sigma -> Prop) (a : Nat) :
    Hoare P
      (@break_case Nat Bool Sigma
        (.by_continue a : CntOrBrk Nat Bool))
      (fun (_ : Bool) (_ : Sigma) => False) := by
  hoare_auto

example (P : Sigma -> Prop) (b : Bool) :
    Hoare P
      (@break_case Nat Bool Sigma (.by_break b : CntOrBrk Nat Bool))
      (fun r s => r = b /\ P s) := by
  hoare_auto

example (P : Sigma -> Prop) (ab : CntOrBrk Nat Bool) :
    Hoare P
      (match ab with
      | .by_continue a =>
          @continue_case Nat Bool Sigma (.by_continue a)
      | .by_break b =>
          @continue_case Nat Bool Sigma (.by_break b))
      (fun _ s => P s) := by
  hoare_auto

example (P : Sigma -> Prop) :
    Hoare P (x <- (MonadErr.ret 3 : program Sigma Int) ;;
      MonadErr.ret (x + 1)) (fun r s => r = 4 /\ P s) := by
  hoare_auto

example (P : Sigma -> Prop)
    (h1 : Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun _ s => P s))
    (h2 : Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun _ s => True)) :
    Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun r s => P s /\ True) := by
  hoare_conj
  all_goals first | (intro s hs; exact hs) | assumption

example (P : Sigma -> Prop)
    (h1 : Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun _ s => P s))
    (h2 : Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun _ _ => True)) :
    Hoare P (MonadErr.ret 1 : program Sigma Nat)
      (fun _ s => P s /\ (True /\ True)) := by
  hoare_conj
  all_goals first | (intro s hs; exact hs) | assumption

example (P : Nat -> Sigma -> Prop)
    (h : forall n, Hoare (P n) (MonadErr.ret () : program Sigma Unit)
      (fun _ _ => True)) :
    Hoare (fun s => exists n, P n s) (MonadErr.ret ()) (fun _ _ => True) := by
  hoare_intros
  exact h _

example (P : Prop) (hP : P) :
    Hoare (fun _ : Sigma => P) (MonadErr.ret ()) (fun _ _ => True) := by
  stateless_intros
  hoare_auto

example (P : Sigma -> Prop) :
    Hoare P
      (choice (MonadErr.ret true) (MonadErr.ret false) : program Sigma Bool)
      (fun _ s => P s) := by
  hoare_auto

example : FP.equiv
    (MonadErr.bind (MonadErr.ret 1 : program Sigma Nat) MonadErr.ret)
    (MonadErr.ret 1) := by
  monad_law

example : Sets.equiv (fun x : Nat => x = x) (fun x => True) := by
  intro_bound

example : FP.equiv
    (MonadErr.bind (MonadErr.ret 1 : program Sigma Nat) MonadErr.ret)
    (MonadErr.ret 1) := by
  monad_equiv

example (P : Sigma -> Prop) :
    Hoare P (testPure True ;; (MonadErr.ret () : program Sigma Unit))
      (fun _ s => P s) := by
  hoare_auto

example (P P' : Sigma -> Prop) (hpre : forall s, P' s -> P s)
    (h : Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun _ s => P s)) :
    Hoare P' (MonadErr.ret 1 : program Sigma Nat) (fun _ s => P s) := by
  hoare_cons_pre h
  exact hpre

example (P : Sigma -> Prop)
    (h : Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun _ s => P s)) :
    Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun _ s => True) := by
  hoare_cons_post h

example (P P' : Sigma -> Prop) (hpre : forall s, P' s -> P s)
    (h : Hoare P (MonadErr.ret 1 : program Sigma Nat) (fun _ s => P s)) :
    Hoare P' (MonadErr.ret 1 : program Sigma Nat) (fun _ s => True) := by
  hoare_cons h
  exact hpre _ ‹P' _›

example (P : Sigma -> Prop) :
    Hoare P (assert True ;; (MonadErr.ret () : program Sigma Unit))
      (fun _ s => P s) := by
  hoare_auto

example (P Q : Sigma -> Prop) (hPQ : forall s, P s -> Q s) :
    Hoare P (assertS Q ;; (MonadErr.ret () : program Sigma Unit))
      (fun _ s => P s) := by
  hoare_auto

example (P : Sigma -> Prop) :
    Hoare P ((MonadErr.ret () : program Sigma Unit) ;;
      (MonadErr.ret 1 : program Sigma Nat)) (fun _ s => P s) := by
  hoare_bind (Hoare_ret P () (fun _ s => P s) (fun _ => id))
  hoare_auto

example (P : Sigma -> Prop) :
    Hoare P ((MonadErr.ret () : program Sigma Unit) ;;
      (MonadErr.ret 1 : program Sigma Nat)) (fun _ s => P s) := by
  hoare_bind' (Hoare_ret P () (fun _ s => P s) (fun _ => id))
  hoare_auto

example (P : Sigma -> Prop) :
    hs_eval (choice (MonadErr.ret 1) (MonadErr.ret 2) : program Sigma Nat)
      P P 1 := by
  abs_choice_left
  abs_ret_step

example (P : Sigma -> Prop) :
    hs_eval (choice (MonadErr.ret 1) (MonadErr.ret 2) : program Sigma Nat)
      P P 2 := by
  abs_choice_right
  abs_ret_step

example (P P' : Sigma -> Prop) (c1 : program Sigma Nat)
    (c2 : Nat -> program Sigma Nat) (X : Nat -> Sigma -> Prop) (a : Nat)
    (hsafe : safeExec P (MonadErr.bind c1 c2) X)
    (heval : hs_eval c1 P P' a) : safeExec P' (c2 a) X := by
  prove_by_one_abs_step a
  fail_if_success clear hsafe
  exact heval

example (P : Sigma -> Prop) (Q : Nat -> Sigma -> Prop)
    (h : Hoare P (MonadErr.ret 1 : program Sigma Nat) Q) :
    Hoare P (MonadErr.bind (MonadErr.ret ()) (fun _ => MonadErr.ret 1)) Q := by
  hoare_apply h

example (P : Sigma -> Prop) :
    hs_eval (testPure True : program Sigma Unit) P P () := by
  abs_test_step
  trivial

example (P : Sigma -> Prop) :
    hs_eval (testPure True ;; (MonadErr.ret () : program Sigma Unit)) P P () := by
  abs_test_step
  · trivial
  · abs_ret_step

example : hs_eval
    (assert True ;; (MonadErr.ret () : program Sigma Unit))
    (ATrue : Sigma -> Prop) ATrue () := by
  abs_assert_step
  · trivial
  · abs_ret_step

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : safeExec P
      (choice (MonadErr.ret 1) (MonadErr.ret 2) : program Sigma Nat) X) :
    safeExec P (MonadErr.ret 1) X := by
  safe_choice_l h
  exact h

example (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop)
    (h : safeExec P (testPure True ;; (MonadErr.ret () : program Sigma Unit)) X) :
    safeExec P (MonadErr.ret ()) X := by
  safe_step h
  exact h

example (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop)
    (h : safeExec P
      (testPure True ;; assert True ;; test (fun _ => True) ;;
        (MonadErr.ret () : program Sigma Unit)) X) :
    safeExec P (MonadErr.ret ()) X := by
  safe_step h
  exact h

example (P : Sigma -> Prop) (X : Unit -> Sigma -> Prop)
    (h : safeExec P
      (choice
        (testPure True ;; (MonadErr.ret () : program Sigma Unit))
        (MonadErr.ret ())) X) :
    safeExec P (MonadErr.ret ()) X := by
  safe_choice_l h
  exact h

example (P : Sigma -> Prop) (body : program Sigma Unit)
    (hbody : Hoare P body (fun _ s => P s)) :
    Hoare P (whileP (fun _ => False) body)
    (fun _ s => P s /\ Not False) := by
  apply Hoare_whileP
  exact Hoare_cons_pre P (fun s => False /\ P s) body
    (fun _ s => P s) (fun _ h => h.2) hbody

example (body : program Sigma Unit) :
    FP.equiv (whileP (fun _ => False) body)
      (choice (test (fun _ => False) ;; body ;; whileP (fun _ => False) body)
        (test (fun s => Not False) ;; MonadErr.ret ())) := by
  unfold_loop

example (cond : program Sigma Bool) (body : program Sigma Unit) :
    FP.equiv («while» cond body)
      (x <- cond ;;
        if x then body ;; «while» cond body else MonadErr.ret ()) := by
  unfold_loop

example (cond : Nat -> program Sigma Bool)
    (body : Nat -> program Sigma Nat)
    (h : FP.equiv (whileret cond body) (whileret cond body)) : True := by
  unfold_loop in h
  trivial

example (body : Nat -> program Sigma (CntOrBrk Nat Bool))
    (h : FP.equiv (repeat_break body) (repeat_break body)) : True := by
  unfold_loop in h
  trivial

example (body : program Sigma (CntOrBrk Unit Bool))
    (h : FP.equiv (repeat_break_noin body) (repeat_break_noin body)) : True := by
  unfold_loop in h
  trivial

example (body : Int -> Nat -> program Sigma Nat) (lo hi : Int) (a : Nat) :
    FP.equiv (range_iter lo hi body a)
      (choice
        (testPure (lo < hi) ;; b <- body lo a ;;
          range_iter (lo + 1) hi body b)
        (testPure (lo >= hi) ;; MonadErr.ret a)) := by
  unfold_loop

example (body : Int -> Nat -> program Sigma (CntOrBrk Nat Bool))
    (lo hi : Int) (a : Nat)
    (h : FP.equiv (range_iter_break lo hi body a)
      (range_iter_break lo hi body a)) : True := by
  unfold_loop in h
  trivial

example (uPred : Nat -> Prop) (body : Nat -> program Sigma Unit) :
    FP.equiv (forset uPred body)
      (choice
        (a <- get (fun _ a => uPred a) ;; body a ;;
          forset (fun x => uPred x /\ x ≠ a) body)
        (testPure (forall x, Not (uPred x)) ;; MonadErr.ret ())) := by
  unfold_loop

example (body : program Sigma Unit)
    (h : FP.equiv (whileP (fun _ => False) body)
      (whileP (fun _ => False) body)) : True := by
  unfold_loop in h
  trivial

example : mono_cont (fun W : program Sigma Unit =>
    (MonadErr.ret () : program Sigma Unit) ;; W) := by
  mono_cont_auto

example (a : Nat) :
    mono_cont (fun W : Nat -> program Sigma Unit => W a) := by
  mono_cont_auto

example : mono_cont (fun W : program Sigma Unit =>
    choice W (MonadErr.ret ())) := by
  mono_cont_auto

example : mono_cont (fun (W : Nat -> program Sigma Unit) (a : Nat) =>
    W a ;; (MonadErr.ret () : program Sigma Unit)) := by
  mono_cont_auto

example (b : Bool) :
    mono_cont (fun W : program Sigma Unit =>
      match b with
      | true => W
      | false => MonadErr.ret ()) := by
  mono_cont_auto

example (a : Option Nat) :
    mono_cont (fun W : Nat -> program Sigma Unit =>
      match a with
      | some n => W n
      | none => MonadErr.ret ()) := by
  mono_cont_auto

example (b c : Bool) :
    mono_cont (fun W : program Sigma Unit =>
      match b && c with
      | true => W
      | false => MonadErr.ret ()) := by
  mono_cont_auto

private def constFixBody
    (_ : Nat -> program Sigma Unit) (_ : Nat) : program Sigma Unit :=
  MonadErr.ret ()

example (a : Nat) :
    Hoare (fun _ : Sigma => True) (FP.BW_fix constFixBody a)
      (fun _ _ => True) := by
  hoare_fix_nolv_auto Nat
  intro W hW a'
  hoare_auto

example (a c : Nat) :
    Hoare (fun _ : Sigma => True) (FP.BW_fix constFixBody a)
      (fun _ _ => True) := by
  hoare_fix_lv_auto Nat Nat c
  intro W hW a' c'
  hoare_auto

example (a c : Nat) (hfalse : False) :
    Hoare (fun _ : Sigma => True) (FP.BW_fix constFixBody a)
      (fun _ _ => True) := by
  hoare_fix_lv_auto_conj Nat Nat c <;> contradiction

example (a c : Nat) (hfalse : False) :
    Hoare (fun _ : Sigma => True) (FP.BW_fix constFixBody a)
      (fun _ _ => True) := by
  hoare_fix_lv_auto_conj' Nat Nat c <;> contradiction

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : safeExec P
      (choice (MonadErr.ret 1) (MonadErr.ret 2) : program Sigma Nat) X) :
    safeExec P (MonadErr.ret 2) X := by
  safe_choice_r h
  exact h

example (P : Sigma -> Prop) (X : Nat -> Sigma -> Prop)
    (h : safeExec P (MonadErr.ret 1 : program Sigma Nat) X) :
    safeExec P (MonadErr.bind (MonadErr.ret ())
      (fun _ => MonadErr.ret 1)) X := by
  safe_equiv

example (P : Sigma -> Prop) :
    hs_eval (assert True : program Sigma Unit) P P () := by
  abs_assert_step
  trivial

example (P Q : Prop) (hP : P) (hQ : Q) : P /\ Q := by
  splits <;> assumption

example (P : Sigma -> Prop) : (show asrt from P) = P := rfl

#check Hoare_range_iter
#check Hoare_forset
#check Hoare_fix_logicv_fspecs
#check mono_BW_fix
#check BW_fix_seq_cont_general
#check mono_cont_BW_fix
#check safeExec_bind
#check Hoare_safeexec_compose

#synth Proper (equiv ==> Eq ==> Iff)
  (@safeExec Sigma Nat (fun _ => True))

#print axioms Hoare_range_iter
#print axioms Hoare_forset
#print axioms safeExec_bind

end StateRelMonadErrTests
