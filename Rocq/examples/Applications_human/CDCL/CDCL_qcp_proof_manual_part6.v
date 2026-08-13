Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_goal.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_auto.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_lib.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_common.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_bcp_entail_wit_9 : bcp_entail_wit_9.
Proof.
  aggressive_pre_process.
  unfold variable_arrays_rep.
  bind_fact (coherent_snapshot F n live original_count snap) as Hcoh.
  assert (Hrow_bound : 0 <= i < Zlength (snap_rows snap)).
  { pose proof Hcoh as Hcoherent.
    unfold coherent_snapshot in Hcoherent.
    destruct Hcoherent as (_ & _ & Hlengths & _ & _ & _).
    destruct Hlengths as (_ & _ & _ & Hrows_length & _ & _ & _).
    lia. }
  assert (Hrow_length : Zlength (Znth i (snap_rows snap) (@nil Z)) = n).
  { pose proof Hcoh as Hcoherent.
    unfold coherent_snapshot in Hcoherent.
    destruct Hcoherent as (_ & _ & _ & Hcells & _ & _).
    destruct Hcells as (_ & Hrows_wf).
    rewrite Forall_forall in Hrows_wf.
    apply Hrows_wf.
    unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrow_bound.
    lia. }
  Exists value_cell_2 b_2 new_snap_2 ranks1_2 cur_states_2.
  unfold bcp_clause_scan, bcp_ready.
  repeat match goal with
  | Hs : bcp_clause_scan _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold bcp_clause_scan in Hs
  end.
  entailer!.
  rewrite (Znth_indep (snap_rows snap) i __default__List_Z (@nil Z))
    by exact Hrow_bound.
  try rewrite (IntArray.seg_shape_empty values n).
  entailer!.
Qed.
