import MonadLib.StateRelMonad.StateRelMonad
import MonadLib.MonadErr.StateRelMonadErr

namespace P12Tests.SafeExecStateRel

open MonadLib.StateRelMonad

def zeroP (s : Nat) : Prop := s = 0

def resultQ (r s : Nat) : Prop := r = 2 /\ s = 0

def oneQ (r s : Nat) : Prop := r = 1 /\ s = 0

def next (_ : Nat) : program Nat Nat := ret 2

private theorem bind_safe :
    safeExec zeroP (MonadLib.StateRelMonad.bind (ret 1) next) resultQ := by
  refine ⟨0, rfl, ?_⟩
  intro r s hrun
  rcases hrun with ⟨a, s', ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  exact ⟨rfl, rfl⟩

theorem reta_target_behavior : safeExec zeroP (ret 2) resultQ := by
  exact safeExec_bind_reta_target (ret 1) next zeroP zeroP 1 (ret 2)
    (fun _ h => h) resultQ bind_safe rfl

theorem partial_target_behavior :
    safeExec zeroP (MonadLib.StateRelMonad.bind (ret 1) next) resultQ := by
  exact safeExec_bind_partial_target (ret 1) (ret 1) next zeroP zeroP
    (MonadLib.StateRelMonad.bind (ret 1) next) (fun _ h => h)
    resultQ bind_safe rfl

private theorem ret_hoare : Hoare zeroP (ret 1) oneQ := by
  apply Hoare_ret'
  intro s hs
  exact ⟨rfl, hs⟩

theorem vertical_composition_behavior :
    exists s, oneQ 1 s /\ zeroP s := by
  exact vertical_composition_rule zeroP zeroP (ret 1) oneQ 1
    (fun _ h => h) ret_hoare ⟨0, rfl⟩

theorem hoare_safeexec_compose_behavior :
    exists s, oneQ 1 s /\ zeroP s := by
  exact Hoare_safeexec_imply_compose zeroP zeroP (ret 1) oneQ 1
    ret_hoare (fun h => h) ⟨0, rfl⟩

end P12Tests.SafeExecStateRel

namespace P12Tests.SafeExecMonadErr

open MonadLib
open MonadLib.MonadErr

def zeroP (s : Nat) : Prop := s = 0

def resultQ (r s : Nat) : Prop := r = 2 /\ s = 0

def oneQ (r s : Nat) : Prop := r = 1 /\ s = 0

def next (_ : Nat) : program Nat Nat := MonadErr.ret 2

private theorem bind_safe :
    safeExec zeroP (MonadErr.bind (MonadErr.ret 1) next) resultQ := by
  refine ⟨0, rfl, ?_⟩
  apply ((wp_bind (MonadErr.ret 1) next resultQ) 0).mpr
  apply (wp_ret 1 (fun a => weakestpre (next a) resultQ) 0).mpr
  apply (wp_ret 2 resultQ 0).mpr
  exact ⟨rfl, rfl⟩

theorem reta_target_behavior : safeExec zeroP (MonadErr.ret 2) resultQ := by
  exact safeExec_bind_reta_target (MonadErr.ret 1) next zeroP zeroP 1
    (MonadErr.ret 2) (fun _ h => h) resultQ bind_safe rfl

theorem partial_target_behavior :
    safeExec zeroP (MonadErr.bind (MonadErr.ret 1) next) resultQ := by
  exact safeExec_bind_partial_target (MonadErr.ret 1) (MonadErr.ret 1) next
    zeroP zeroP (MonadErr.bind (MonadErr.ret 1) next) (fun _ h => h)
    resultQ bind_safe rfl

private theorem ret_hoare : Hoare zeroP (MonadErr.ret 1) oneQ := by
  apply Hoare_ret
  intro s hs
  exact ⟨rfl, hs⟩

theorem vertical_composition_behavior :
    exists s, oneQ 1 s /\ zeroP s := by
  exact vertical_composition_rule zeroP zeroP (MonadErr.ret 1) oneQ 1
    (fun _ h => h) ret_hoare ⟨0, rfl⟩

theorem hoare_safeexec_compose_behavior :
    exists s, oneQ 1 s /\ zeroP s := by
  exact Hoare_safeexec_imply_compose zeroP zeroP (MonadErr.ret 1) oneQ 1
    ret_hoare (fun h => h) ⟨0, rfl⟩

end P12Tests.SafeExecMonadErr
