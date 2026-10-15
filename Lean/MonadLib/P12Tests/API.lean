import MonadLib.StateRelMonad.StateRelMonad
import MonadLib.MonadErr.StateRelMonadErr

#check MonadLib.StateRelMonad.Rec
#check MonadLib.StateRelMonad.Rec_unfold
#check MonadLib.StateRelMonad.Rec_mono
#check MonadLib.StateRelMonad.Rec_continuous
#check MonadLib.StateRelMonad.mono_cont_Rec
#check MonadLib.StateRelMonad.mono_intro
#check MonadLib.StateRelMonad.mono_bind
#check MonadLib.StateRelMonad.mono_choice
#check MonadLib.StateRelMonad.continuous_intro
#check MonadLib.StateRelMonad.continuous_const
#check MonadLib.StateRelMonad.continuous_bind
#check MonadLib.StateRelMonad.continuous_choice
#check MonadLib.StateRelMonad.mono_cont_pointwise
#check MonadLib.StateRelMonad.mono_cont_at
#check MonadLib.StateRelMonad.mono_cont_id
#check MonadLib.StateRelMonad.mono_cont_intro
#check MonadLib.StateRelMonad.mono_cont_const
#check MonadLib.StateRelMonad.mono_cont_bind
#check MonadLib.StateRelMonad.mono_cont_choice
#check MonadLib.StateRelMonad.Hoare_assume'
#check MonadLib.StateRelMonad.Hoare_Rec
#check MonadLib.StateRelMonad.Hoare_Rec_prog
#check MonadLib.StateRelMonad.Hoare_Rec_logicv
#check MonadLib.StateRelMonad.Hoare_Rec_logicv_conj'
#check MonadLib.StateRelMonad.Hoare_Rec_fspecs
#check MonadLib.StateRelMonad.Hoare_fix_logicv_conj
#check MonadLib.StateRelMonad.Hoare_fix_logicv_conj'
#check MonadLib.StateRelMonad.safeExec_bind_reta_target
#check MonadLib.StateRelMonad.safeExec_bind_partial_target
#check MonadLib.StateRelMonad.vertical_composition_rule
#check MonadLib.StateRelMonad.Hoare_safeexec_imply_compose

#check MonadLib.Rec
#check MonadLib.Rec_unfold
#check MonadLib.Rec_mono
#check MonadLib.Rec_continuous
#check MonadLib.mono_cont_Rec
#check MonadLib.mono_intro
#check MonadLib.mono_bind
#check MonadLib.mono_choice
#check MonadLib.continuous_intro
#check MonadLib.continuous_const
#check MonadLib.continuous_bind
#check MonadLib.continuous_choice
#check MonadLib.mono_cont_pointwise
#check MonadLib.mono_cont_at
#check MonadLib.mono_cont_id
#check MonadLib.mono_cont_intro
#check MonadLib.mono_cont_const
#check MonadLib.mono_cont_bind
#check MonadLib.mono_cont_choice
#check MonadLib.Hoare_assume'
#check MonadLib.Hoare_Rec
#check MonadLib.Hoare_Rec_prog
#check MonadLib.Hoare_Rec_logicv
#check MonadLib.Hoare_Rec_logicv_conj'
#check MonadLib.Hoare_Rec_fspecs
#check MonadLib.safeExec_bind_reta_target
#check MonadLib.safeExec_bind_partial_target
#check MonadLib.vertical_composition_rule
#check MonadLib.Hoare_safeexec_imply_compose

-- The candidate MonadErr theorem no longer requires a separate proof of `Q`.
example {Sigma : Type} (P : Sigma -> Prop) (Q : Prop) :
    MonadLib.Hoare P (MonadLib.testPure Q) (fun _ s => P s /\ Q) :=
  MonadLib.Hoare_assume' P Q

-- Instantiate the generalized carrier at a program directly, rather than at
-- the old continuation-only carrier shape.
#check MonadLib.StateRelMonad.mono_intro
  (X := MonadLib.StateRelMonad.program Unit Unit) (I := Unit)
  (Y := MonadLib.StateRelMonad.program Unit Unit)
#check MonadLib.mono_intro
  (X := MonadLib.program Unit Unit) (I := Unit)
  (Y := MonadLib.program Unit Unit)

#print axioms MonadLib.StateRelMonad.Rec_unfold
#print axioms MonadLib.StateRelMonad.Hoare_fix_logicv_conj
#print axioms MonadLib.StateRelMonad.Hoare_Rec_fspecs
#print axioms MonadLib.StateRelMonad.vertical_composition_rule
#print axioms MonadLib.Rec_unfold
#print axioms MonadLib.Hoare_Rec_fspecs
#print axioms MonadLib.vertical_composition_rule
