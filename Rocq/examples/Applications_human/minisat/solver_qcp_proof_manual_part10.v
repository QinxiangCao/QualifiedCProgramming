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
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_goal.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_common.
Local Open Scope sac.

(* Keep this large entailment proof in its own compilation unit.
   Coq 8.20 can reject its Qed with an unbound reference when it follows
   the other proofs in part7; the statement and proof are unchanged. *)
Lemma proof_of_solver_solve_which_implies_wit_9 : solver_solve_which_implies_wit_9.
Proof.
  unfold solver_solve_which_implies_wit_9.
  intros A_arr F n solve_wl_solver_solve_spec M0
    levels_ptr endvar begin values s.
  intros.
  bind_fact ( solver_query_ready n F M0 ) as Hquery.
  destruct Hquery as [Hbase [Hlim [Hqhead Hpending]]].
  pose proof (msas_weak Hbase) as Hinv.
  pose proof (msa_shape Hinv) as Hshape.
  unfold assumptions_array.
  Intros raw.
  lazymatch goal with
  | Harray : endvar = _ /\ A_arr = lits_denote raw /\ _ |- _ =>
      destruct Harray as [Hend [HA [Hrawwf Hempty]]]
  end.
  assert (HAwf : Forall (literal_wf n) A_arr).
  { rewrite HA. apply lits_denote_wf. exact Hrawwf. }
  pose proof (solver_query_assumptions__solve n F M0 A_arr Hbase HAwf) as Hstrong.
  assert (Hprefix : A_arr = assumption_prefix raw (Zlength raw)).
  { unfold assumption_prefix.
    rewrite (sublist_self raw (Zlength raw) eq_refl).
    exact HA. }
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
    solver_var_arrays_rep, solver_assigns_focus_frame_wl_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  destruct raw as [|z raw'].
  - assert (Hvalid : valid_int_position begin).
    { apply Hempty. reflexivity. }
    Right. Exists (@nil Z) act opos rsn trl tgs.
    pose proof (msa_size Hinv) as Hsize.
    subst n.
    unfold solver_shape in Hshape.
    unfold solver_scalars_rep, solver_vecs_rep.
    msat_manual_entailer_with ltac:(lia).
  - Left. Exists (z :: raw') act opos rsn trl tgs.
    entailer_with ltac:(lia);
      try discriminate;
      rewrite (msa_size Hinv);
      unfold solver_shape in Hshape;
      entailer_with ltac:(lia);
      unfold solver_scalars_rep, solver_vecs_rep;
      entailer_with ltac:(lia).
Qed.
