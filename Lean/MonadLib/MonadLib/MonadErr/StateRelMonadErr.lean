import MonadLib.MonadErr.MonadErrBasic
import MonadLib.MonadErr.MonadErrHoare
import MonadLib.MonadErr.MonadErrLoop
import MonadLib.MonadErr.monadesafe_lib

macro "prog_nf" : tactic => `(tactic| err_prog_nf)
macro "prog_nf" " in " loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic| err_prog_nf in $loc)
macro "mono_cont_auto" : tactic => `(tactic| err_mono_cont_auto)
macro "unfold_loop" : tactic => `(tactic| err_unfold_loop)
macro "unfold_loop" " in " loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic| err_unfold_loop in $loc)
macro "hoare_step" : tactic => `(tactic| err_hoare_step)
macro "hoare_auto" : tactic => `(tactic| err_hoare_auto)
macro "hoare_fix_nolv_auto " A:term : tactic =>
  `(tactic| err_hoare_fix_nolv_auto $A)
macro "prove_by_one_abs_step " x:term : tactic =>
  `(tactic| err_prove_by_one_abs_step $x)
macro "abs_choice_left" : tactic => `(tactic| err_abs_choice_left)
macro "abs_choice_right" : tactic => `(tactic| err_abs_choice_right)
macro "abs_test_step" : tactic => `(tactic| err_abs_test_step)
macro "abs_ret_step" : tactic => `(tactic| err_abs_ret_step)
macro "safe_step " h:ident : tactic => `(tactic| err_safe_step $h)
macro "safe_choice_l " h:ident : tactic => `(tactic| err_safe_choice_l $h)
macro "safe_choice_r " h:ident : tactic => `(tactic| err_safe_choice_r $h)
macro "safe_equiv" : tactic => `(tactic| err_safe_equiv)
