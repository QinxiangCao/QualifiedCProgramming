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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P011_765A_neverending_competitions_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P011_765A_neverending_competitions_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib.
Local Open Scope sac.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst n_pre.
  unfold Pre in PreH6.
  destruct PreH6 as (_ & _ & Hflights & current & Hitinerary).
  assert (Hflight_parity : Forall (fun f =>
      (fst f = home_data /\ snd f <> home_data) \/
      (fst f <> home_data /\ snd f = home_data)) flights_data).
  {
    rewrite Forall_forall in *.
    intros f Hin.
    specialize (Hflights f Hin).
    tauto.
  }
  pose proof (itinerary_endpoint_parity__return_parity
    home_data flights_data current Hflight_parity Hitinerary) as Hendpoint.
  assert (Hland_mod :
      Z.land (Zlength flights_data) 1 = Zlength flights_data mod 2).
  {
    change (Z.land (Zlength flights_data) (Z.ones 1) =
            Zlength flights_data mod 2).
    rewrite Z.land_ones by lia.
    reflexivity.
  }
  assert (Hcurrent : current <> home_data).
  {
    intro Heq.
    apply (proj1 Hendpoint) in Heq.
    apply PreH1.
    rewrite Hland_mod.
    exact Heq.
  }
  unfold Spec.
  right.
  split; [reflexivity |].
  exists current.
  tauto.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst n_pre.
  unfold Pre in PreH6.
  destruct PreH6 as (_ & _ & Hflights & current & Hitinerary).
  assert (Hflight_parity : Forall (fun f =>
      (fst f = home_data /\ snd f <> home_data) \/
      (fst f <> home_data /\ snd f = home_data)) flights_data).
  {
    rewrite Forall_forall in *.
    intros f Hin.
    specialize (Hflights f Hin).
    tauto.
  }
  pose proof (itinerary_endpoint_parity__return_parity
    home_data flights_data current Hflight_parity Hitinerary) as Hendpoint.
  assert (Hland_mod :
      Z.land (Zlength flights_data) 1 = Zlength flights_data mod 2).
  {
    change (Z.land (Zlength flights_data) (Z.ones 1) =
            Zlength flights_data mod 2).
    rewrite Z.land_ones by lia.
    reflexivity.
  }
  assert (Hcurrent : current = home_data).
  {
    apply (proj2 Hendpoint).
    rewrite <- Hland_mod.
    exact PreH1.
  }
  unfold Spec.
  left.
  split; [reflexivity |].
  subst current.
  exact Hitinerary.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.
