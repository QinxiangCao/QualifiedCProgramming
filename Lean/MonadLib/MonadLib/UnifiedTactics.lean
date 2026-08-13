import MonadLib.StateRelMonad.StateRelBasic
import MonadLib.StateRelMonad.FixpointLib
import MonadLib.StateRelMonad.StateRelHoare
import MonadLib.StateRelMonad.safeexec_lib
import MonadLib.MonadErr.MonadErrBasic
import MonadLib.MonadErr.MonadErrHoare
import MonadLib.MonadErr.MonadErrLoop
import MonadLib.MonadErr.monadesafe_lib

syntax "__guard_monad_family_target " ident : tactic
syntax "__guard_monad_family_hyp " ident ident : tactic
syntax "__dispatch_monad_hyp " ident ident : tactic

namespace MonadLib.UnifiedTactics

open Lean Meta Elab Tactic

private inductive MonadFamily where
  | state
  | err
  deriving BEq

private def containsPrefix (ns : Name) : Expr -> Bool
  | .const name _ => ns.isPrefixOf name
  | .app fn arg => containsPrefix ns fn || containsPrefix ns arg
  | .lam _ type body _ => containsPrefix ns type || containsPrefix ns body
  | .forallE _ type body _ => containsPrefix ns type || containsPrefix ns body
  | .letE _ type value body _ =>
      containsPrefix ns type || containsPrefix ns value || containsPrefix ns body
  | .mdata _ body => containsPrefix ns body
  | .proj _ _ body => containsPrefix ns body
  | _ => false

private def isErrProgramName (name : Name) : Bool :=
  let errNamespace := Name.str (Name.str .anonymous "MonadLib") "MonadErr"
  errNamespace.isPrefixOf name ||
    name == ``MonadLib.state_rel_monad ||
    name == ``MonadLib.choice ||
    name == ``MonadLib.testPure ||
    name == ``MonadLib.test ||
    name == ``MonadLib.assert ||
    name == ``MonadLib.assertS ||
    name == ``MonadLib.put ||
    name == ``MonadLib.any ||
    name == ``MonadLib.get ||
    name == ``MonadLib.update ||
    name == ``MonadLib.whileP ||
    name == ``MonadLib.«while» ||
    name == ``MonadLib.whileret ||
    name == ``MonadLib.Repeat ||
    name == ``MonadLib.repeat_break ||
    name == ``MonadLib.repeat_break_noin ||
    name == ``MonadLib.range_iter ||
    name == ``MonadLib.range_iter_break ||
    name == ``MonadLib.forset

private def containsErrProgram : Expr -> Bool
  | .const name _ => isErrProgramName name
  | .app fn arg => containsErrProgram fn || containsErrProgram arg
  | .lam _ type body _ => containsErrProgram type || containsErrProgram body
  | .forallE _ type body _ => containsErrProgram type || containsErrProgram body
  | .letE _ type value body _ =>
      containsErrProgram type || containsErrProgram value ||
        containsErrProgram body
  | .mdata _ body => containsErrProgram body
  | .proj _ _ body => containsErrProgram body
  | _ => false

private def outerFamily? (type : Expr) : Option MonadFamily :=
  let head := type.consumeMData.getAppFn.constName?
  if head == some ``MonadLib.StateRelMonad.Hoare ||
      head == some ``MonadLib.StateRelMonad.safeExec ||
      head == some ``MonadLib.StateRelMonad.hs_eval ||
      head == some ``MonadLib.StateRelMonad.mono_cont then
    some .state
  else if head == some ``MonadLib.Hoare ||
      head == some ``MonadLib.safeExec ||
      head == some ``MonadLib.hs_eval ||
      head == some ``MonadLib.mono_cont then
    some .err
  else
    none

private def inferFamily? (type : Expr) : Option MonadFamily :=
  if let some family := outerFamily? type then
    some family
  else
    let stateNamespace := Name.str (Name.str .anonymous "MonadLib") "StateRelMonad"
    let hasState := containsPrefix stateNamespace type
    let hasErr := containsErrProgram type
    match hasState, hasErr with
    | true, _ => some .state
    | false, true => some .err
    | _, _ => none

private def guardFamily (family : Name) (type : Expr) : TacticM Unit := do
  let expected ← match family.eraseMacroScopes with
    | `state => pure MonadFamily.state
    | `err => pure MonadFamily.err
    | _ => throwError "unknown monad family"
  match inferFamily? type with
  | some actual =>
      unless actual == expected do
        throwError "target belongs to the other monad family"
  | none =>
      throwError "cannot determine the monad family from the target structure"

elab_rules : tactic
  | `(tactic| __guard_monad_family_target $family:ident) => withMainContext do
      let target <- instantiateMVars (← getMainTarget)
      guardFamily family.getId target
  | `(tactic| __guard_monad_family_hyp $family:ident $h:ident) => withMainContext do
      let fvarId <- getFVarId h
      let type <- instantiateMVars (← fvarId.getType)
      guardFamily family.getId type
  | `(tactic| __dispatch_monad_hyp $operation:ident $h:ident) => withMainContext do
      let fvarId <- getFVarId h
      let type <- instantiateMVars (← fvarId.getType)
      let some family := inferFamily? type |
        throwError "cannot determine the monad family from hypothesis {h.getId}"
      let tacticName <- match operation.getId.eraseMacroScopes, family with
        | `prog_nf, .state => pure "state_prog_nf"
        | `prog_nf, .err => pure "err_prog_nf"
        | `unfold_loop, .state => pure "state_unfold_loop"
        | `unfold_loop, .err => pure "err_unfold_loop"
        | _, _ => throwError "unknown monad hypothesis operation"
      let source := s!"{tacticName} in {h.getId.eraseMacroScopes}"
      match Lean.Parser.runParserCategory (← getEnv) `tactic source with
      | .ok tactic => evalTactic tactic
      | .error message => throwError message

end MonadLib.UnifiedTactics

macro "prog_nf" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_prog_nf)
      | (__guard_monad_family_target err; err_prog_nf))
macro "prog_nf" " in " h:ident : tactic =>
  `(tactic| __dispatch_monad_hyp prog_nf $h)
macro "mono_cont_auto" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_mono_cont_auto)
      | (__guard_monad_family_target err; err_mono_cont_auto))
macro "unfold_loop" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_unfold_loop)
      | (__guard_monad_family_target err; err_unfold_loop))
macro "unfold_loop" " in " h:ident : tactic =>
  `(tactic| __dispatch_monad_hyp unfold_loop $h)
macro "hoare_step" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_hoare_step)
      | (__guard_monad_family_target err; err_hoare_step))
macro "hoare_auto" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_hoare_auto)
      | (__guard_monad_family_target err; err_hoare_auto))
macro "hoare_fix_nolv_auto " A:term : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_hoare_fix_nolv_auto $A)
      | (__guard_monad_family_target err; err_hoare_fix_nolv_auto $A))
macro "prove_by_one_abs_step " x:term : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_prove_by_one_abs_step $x)
      | (__guard_monad_family_target err; err_prove_by_one_abs_step $x))
macro "abs_choice_left" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_abs_choice_left)
      | (__guard_monad_family_target err; err_abs_choice_left))
macro "abs_choice_right" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_abs_choice_right)
      | (__guard_monad_family_target err; err_abs_choice_right))
macro "abs_test_step" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_abs_test_step)
      | (__guard_monad_family_target err; err_abs_test_step))
macro "abs_ret_step" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_abs_ret_step)
      | (__guard_monad_family_target err; err_abs_ret_step))
macro "safe_step " h:ident : tactic =>
  `(tactic| first
      | (__guard_monad_family_hyp state $h; state_safe_step $h)
      | (__guard_monad_family_hyp err $h; err_safe_step $h))
macro "safe_choice_l " h:ident : tactic =>
  `(tactic| first
      | (__guard_monad_family_hyp state $h; state_safe_choice_l $h)
      | (__guard_monad_family_hyp err $h; err_safe_choice_l $h))
macro "safe_choice_r " h:ident : tactic =>
  `(tactic| first
      | (__guard_monad_family_hyp state $h; state_safe_choice_r $h)
      | (__guard_monad_family_hyp err $h; err_safe_choice_r $h))
macro "safe_equiv" : tactic =>
  `(tactic| first
      | (__guard_monad_family_target state; state_safe_equiv)
      | (__guard_monad_family_target err; err_safe_equiv))
