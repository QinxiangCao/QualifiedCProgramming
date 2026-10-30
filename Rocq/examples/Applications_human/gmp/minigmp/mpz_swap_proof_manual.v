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
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_swap_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_swap_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_swap_entail_wit_1_u_read0 : mpz_swap_entail_wit_1_u_read0.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_Z_read0, store_Z.
  Intros uptr usize ucap vptr vsize vcap.
  Intros.
  Exists vptr uptr vcap vsize ucap usize.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - repeat split_pures; dump_pre_spatial; assumption.
Qed. 

Lemma proof_of_mpz_swap_entail_wit_2_u_read0_split_goal_spatial : mpz_swap_entail_wit_2_u_read0_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  cancel (mpd_store_Z_compact UINT_MOD vptr (Zabs m_u_read0) (Zabs vsize)).
  unfold store_Z_read0.
  Exists uptr usize ucap.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - repeat split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_mpz_swap_entail_wit_2_u_read0 : mpz_swap_entail_wit_2_u_read0.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_swap_entail_wit_2_u_read0_split_goal_spatial.
Qed. 

