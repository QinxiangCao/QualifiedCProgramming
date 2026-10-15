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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P051_986A_fair_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P051_986A_fair_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P051_986A_fair_lib.
Local Open Scope sac.

Lemma proof_of_bfs_type_entail_wit_1_split_goal_1 : bfs_type_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_bfs_type_entail_wit_1 : bfs_type_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_bfs_type_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_bfs_type_entail_wit_2_split_goal_1 : bfs_type_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_2 : bfs_type_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_bfs_type_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_bfs_type_entail_wit_3_split_goal_1 : bfs_type_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply BfsInit_nil__g2_bfs_init.
  intros w Hw. apply PreH16. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_3_split_goal_2 : bfs_type_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_bfs_type_entail_wit_3 : bfs_type_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_bfs_type_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_bfs_type_entail_wit_4_1_split_goal_1 : bfs_type_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply BfsInit_push__g2_bfs_init;
    [exact PreH21 | lia | lia | exact PreH1].
Qed.

Lemma proof_of_bfs_type_entail_wit_4_1_split_goal_2 : bfs_type_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_4_1_split_goal_3 : bfs_type_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_4_1 : bfs_type_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_bfs_type_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_bfs_type_entail_wit_4_1_split_goal_3.
Qed.

Lemma proof_of_bfs_type_entail_wit_4_2_split_goal_1 : bfs_type_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply BfsInit_skip__g2_bfs_init;
    [exact PreH21 | lia | exact PreH1].
Qed.

Lemma proof_of_bfs_type_entail_wit_4_2 : bfs_type_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_bfs_type_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_bfs_type_entail_wit_5_split_goal_1 : bfs_type_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (BfsInit_head_dist__g2_bfs_init n_pre goods c_pre Q_2 dl_2 v PreH20 ltac:(lia)).
  apply (BfsInit_BfsBounded__g2_bfs_init n_pre goods c_pre Q_2 dl_2 v);
    [exact PreH20 | lia].
Qed.

Lemma proof_of_bfs_type_entail_wit_5_split_goal_2 : bfs_type_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros i w Hi Hw He. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_5_split_goal_3 : bfs_type_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hv : v = n_pre + 1) by lia. subst v.
  exact (proj1 (BfsInit_BfsCore n_pre edges goods c_pre Q_2 dl_2 PreH20)).
Qed.

Lemma proof_of_bfs_type_entail_wit_5 : bfs_type_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_bfs_type_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_bfs_type_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_bfs_type_entail_wit_6_split_goal_1 : bfs_type_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (qh - 0) with qh by lia.
  apply PreH20. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_6_split_goal_2 : bfs_type_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (qh + 1 - 1) with qh by lia.
  exact PreH19.
Qed.

Lemma proof_of_bfs_type_entail_wit_6_split_goal_3 : bfs_type_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (qh - 0) with qh by lia.
  pose proof PreH18 as Hc.
  destruct Hc as (_ & _ & _ & _ & _ & _ & Hidx & _).
  specialize (Hidx qh ltac:(lia)). lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_6_split_goal_4 : bfs_type_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (qh - 0) with qh by lia.
  pose proof PreH18 as Hc.
  destruct Hc as (_ & _ & _ & _ & _ & _ & Hidx & _).
  specialize (Hidx qh ltac:(lia)). lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_6_split_goal_5 : bfs_type_entail_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (qh - 0) with qh by lia.
  pose proof PreH18 as Hc.
  destruct Hc as (Hb1 & _).
  specialize (Hb1 qh ltac:(lia)). lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_6_split_goal_6 : bfs_type_entail_wit_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (qh - 0) with qh by lia.
  pose proof PreH18 as Hc.
  destruct Hc as (Hb1 & _).
  specialize (Hb1 qh ltac:(lia)). lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_6_split_goal_7 : bfs_type_entail_wit_6_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (qh - 0) with (qh + 1 - 1) by lia.
  reflexivity.
Qed.

Lemma proof_of_bfs_type_entail_wit_6 : bfs_type_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_bfs_type_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_bfs_type_entail_wit_6_split_goal_3.
  - Goal_apply proof_of_bfs_type_entail_wit_6_split_goal_4.
  - Goal_apply proof_of_bfs_type_entail_wit_6_split_goal_5.
  - Goal_apply proof_of_bfs_type_entail_wit_6_split_goal_6.
  - Goal_apply proof_of_bfs_type_entail_wit_6_split_goal_7.
Qed. 

Lemma proof_of_bfs_type_entail_wit_7_split_goal_1 : bfs_type_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (BfsScan_entry n_pre m edges hd nx tlst Q_2 dl_2 u PreH9 ltac:(lia)).
Qed.

Lemma proof_of_bfs_type_entail_wit_7_split_goal_2 : bfs_type_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct H as [Hne Hneg].
  pose proof PreH9 as Hb.
  destruct Hb as (_ & _ & _ & _ & _ & Hhd & _).
  specialize (Hhd u ltac:(lia)).
  destruct Hhd as [Hh | Hh]; [lia |].
  assert (Hwr : 1 <= Znth (Znth (u - 1) hd 0) tlst 0 <= n_pre)
    by (apply PreH11; lia).
  pose proof (queue_room_core__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                (Znth (Znth (u - 1) hd 0) tlst 0) PreH22 Hwr Hneg) as Hres.
  lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_7_split_goal_3 : bfs_type_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename H into Hne.
  pose proof PreH9 as Hb.
  destruct Hb as (_ & _ & _ & _ & _ & Hhd & _).
  specialize (Hhd u ltac:(lia)).
  destruct Hhd as [Hh | Hh]; [lia |].
  apply PreH11. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_7_split_goal_4 : bfs_type_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH9 as Hb.
  destruct Hb as (_ & _ & _ & _ & _ & Hhd & _).
  specialize (Hhd u ltac:(lia)).
  destruct Hhd as [Hh | Hh]; lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_7_split_goal_5 : bfs_type_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof PreH9 as Hb.
  destruct Hb as (_ & _ & _ & _ & _ & Hhd & _).
  specialize (Hhd u ltac:(lia)).
  destruct Hhd as [Hh | Hh]; lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_7 : bfs_type_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_bfs_type_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_bfs_type_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_bfs_type_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_bfs_type_entail_wit_7_split_goal_5.
Qed. 

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_1 : bfs_type_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).

  assert (Hw : 1 <= Znth e tlst 0 <= n_pre) by (apply PreH26; exact PreH2).
  assert (Hlen : n_pre < Zlength dl_2) by lia.
  assert (Hu : In u Q_2).
  { rewrite PreH18. apply In_Znth_Q__g3_bfs_scan_core. lia. }
  assert (Hufix : Znth u (replace_Znth (Znth e tlst 0) (Znth u dl_2 0 + 1) dl_2) 0
                  = Znth u dl_2 0)
    by (exact (dl_push_frame__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                 (Znth e tlst 0) u (Znth u dl_2 0 + 1) Hlen PreH28 Hw PreH1 Hu)).

  apply (BfsScan_step m edges nx tlst Q_2 dl_2
           (Q_2 ++ Znth e tlst 0 :: nil)
           (replace_Znth (Znth e tlst 0) (Znth u dl_2 0 + 1) dl_2)
           u e PreH2 PreH31).
  - intros w0 Hw0. apply In_push__g3_bfs_scan_core. left. exact Hw0.
  - intros w0 Hw0.
    exact (dl_push_frame__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
             (Znth e tlst 0) w0 (Znth u dl_2 0 + 1) Hlen PreH28 Hw PreH1 Hw0).
  - exact Hufix.
  - apply In_push__g3_bfs_scan_core. right. reflexivity.
  - rewrite Hufix. rewrite Znth_replace_Znth_Same by lia. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_2 : bfs_type_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).

  assert (Hw : 1 <= Znth e tlst 0 <= n_pre) by (apply PreH26; exact PreH2).
  assert (Hlen : n_pre < Zlength dl_2) by lia.
  assert (Hu : In u Q_2).
  { rewrite PreH18. apply In_Znth_Q__g3_bfs_scan_core. lia. }
  assert (Hufix : Znth u (replace_Znth (Znth e tlst 0) (Znth u dl_2 0 + 1) dl_2) 0
                  = Znth u dl_2 0)
    by (exact (dl_push_frame__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                 (Znth e tlst 0) u (Znth u dl_2 0 + 1) Hlen PreH28 Hw PreH1 Hu)).

  exact (BfsBounded_push__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2 u
           (Znth e tlst 0) Hlen PreH28 PreH30 Hu Hw PreH1).
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_3 : bfs_type_entail_wit_8_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).

  assert (Hw : 1 <= Znth e tlst 0 <= n_pre) by (apply PreH26; exact PreH2).
  assert (Hlen : n_pre < Zlength dl_2) by lia.
  assert (Hu : In u Q_2).
  { rewrite PreH18. apply In_Znth_Q__g3_bfs_scan_core. lia. }
  assert (Hufix : Znth u (replace_Znth (Znth e tlst 0) (Znth u dl_2 0 + 1) dl_2) 0
                  = Znth u dl_2 0)
    by (exact (dl_push_frame__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                 (Znth e tlst 0) u (Znth u dl_2 0 + 1) Hlen PreH28 Hw PreH1 Hu)).

  exact (BfsExpanded_push__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2 u
           (Znth e tlst 0) (qh - 1) Hlen PreH28 PreH29 ltac:(lia) Hw PreH1).
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_4 : bfs_type_entail_wit_8_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).

  assert (Hw : 1 <= Znth e tlst 0 <= n_pre) by (apply PreH26; exact PreH2).
  assert (Hlen : n_pre < Zlength dl_2) by lia.
  assert (Hu : In u Q_2).
  { rewrite PreH18. apply In_Znth_Q__g3_bfs_scan_core. lia. }
  assert (Hufix : Znth u (replace_Znth (Znth e tlst 0) (Znth u dl_2 0 + 1) dl_2) 0
                  = Znth u dl_2 0)
    by (exact (dl_push_frame__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                 (Znth e tlst 0) u (Znth u dl_2 0 + 1) Hlen PreH28 Hw PreH1 Hu)).

  assert (Hfrom : 0 <= e < 2 * m /\ ArcFrom edges e = u).
  { pose proof PreH31 as Hs.
    destruct Hs as [lrem [Hchain [Hmem2 _]]].
    destruct (AdjChain_cons_inv nx e lrem PreH2 Hchain) as [l' [Heq _]].
    subst lrem. apply Hmem2. left. reflexivity. }
  assert (Hto : Znth e tlst 0 = ArcTo edges e).
  { pose proof PreH11 as Hb.
    destruct Hb as (_ & _ & _ & Htl & _).
    apply Htl. lia. }
  assert (Hedge : In (u, Znth e tlst 0) edges \/ In (Znth e tlst 0, u) edges).
  { apply (proj2 (arc_edge_iff edges m (eq_sym PreH10) u (Znth e tlst 0))).
    exists e. split; [lia | split; [tauto | symmetry; exact Hto]]. }
  assert (HmrU : MReach n_pre edges goods c_pre u (Znth u dl_2 0)).
  { pose proof PreH28 as Hc.
    destruct Hc as (_ & _ & _ & _ & Hreal & _).
    specialize (Hreal (qh - 1) ltac:(lia)).
    rewrite <- PreH18 in Hreal. exact Hreal. }
  assert (Hmr : MReach n_pre edges goods c_pre (Znth e tlst 0) (Znth u dl_2 0 + 1))
    by (exact (MReach_step__g3_bfs_scan_core n_pre edges goods c_pre u
                 (Znth e tlst 0) (Znth u dl_2 0) HmrU Hedge ltac:(lia) Hw)).
  assert (Hroom : Znth u dl_2 0 + 1 <= Zlength Q_2).
  { pose proof PreH28 as Hc.
    destruct Hc as (_ & _ & _ & _ & _ & _ & Hidx & _).
    specialize (Hidx (qh - 1) ltac:(lia)).
    rewrite <- PreH18 in Hidx. lia. }
  exact (BfsCore_push__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2 u
           (Znth e tlst 0) Hlen PreH28 PreH30 Hu Hw PreH1 Hroom Hmr).
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_5 : bfs_type_entail_wit_8_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct H as [Hne Hneg].
  assert (Hw : 1 <= Znth e tlst 0 <= n_pre) by (apply PreH26; exact PreH2).
  pose proof (PreH12 e ltac:(lia)) as He1.
  assert (Hw1 : 1 <= Znth (Znth e nx 0) tlst 0 <= n_pre) by (apply PreH13; lia).
  assert (Hdlw : Znth (Znth e tlst 0)
                   (replace_Znth (Znth e tlst 0) (Znth u dl_2 0 + 1) dl_2) 0
                 = Znth u dl_2 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hne2 : Znth (Znth e nx 0) tlst 0 <> Znth e tlst 0).
  { intros Heq. rewrite Heq, Hdlw in Hneg. lia. }
  rewrite (Znth_replace_Znth_Diff 0 dl_2 (Znth e tlst 0)
             (Znth (Znth e nx 0) tlst 0) (Znth u dl_2 0 + 1)) in Hneg
    by lia.
  pose proof (queue_room_push__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                (Znth e tlst 0) (Znth (Znth e nx 0) tlst 0)
                PreH28 Hw PreH1 Hw1 Hneg Hne2) as Hres.
  lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_6 : bfs_type_entail_wit_8_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename H into Hne.
  pose proof (PreH12 e ltac:(lia)) as He1.
  apply PreH13. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_7 : bfs_type_entail_wit_8_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth. exact PreH25.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_8 : bfs_type_entail_wit_8_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 e ltac:(lia)) as He1. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_9 : bfs_type_entail_wit_8_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 e ltac:(lia)) as He1. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_10 : bfs_type_entail_wit_8_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).

  assert (Hw : 1 <= Znth e tlst 0 <= n_pre) by (apply PreH26; exact PreH2).
  assert (Hlen : n_pre < Zlength dl_2) by lia.
  assert (Hu : In u Q_2).
  { rewrite PreH18. apply In_Znth_Q__g3_bfs_scan_core. lia. }
  assert (Hufix : Znth u (replace_Znth (Znth e tlst 0) (Znth u dl_2 0 + 1) dl_2) 0
                  = Znth u dl_2 0)
    by (exact (dl_push_frame__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                 (Znth e tlst 0) u (Znth u dl_2 0 + 1) Hlen PreH28 Hw PreH1 Hu)).

  rewrite Hufix. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_11 : bfs_type_entail_wit_8_1_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).

  assert (Hw : 1 <= Znth e tlst 0 <= n_pre) by (apply PreH26; exact PreH2).
  assert (Hlen : n_pre < Zlength dl_2) by lia.
  assert (Hu : In u Q_2).
  { rewrite PreH18. apply In_Znth_Q__g3_bfs_scan_core. lia. }
  assert (Hufix : Znth u (replace_Znth (Znth e tlst 0) (Znth u dl_2 0 + 1) dl_2) 0
                  = Znth u dl_2 0)
    by (exact (dl_push_frame__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                 (Znth e tlst 0) u (Znth u dl_2 0 + 1) Hlen PreH28 Hw PreH1 Hu)).

  rewrite Hufix. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_12 : bfs_type_entail_wit_8_1_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Znth_prefix_push__g3_bfs_scan_core by lia.
  exact PreH18.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1_split_goal_13 : bfs_type_entail_wit_8_1_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_push__g3_bfs_scan_core. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_1 : bfs_type_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_2.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_3.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_4.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_5.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_6.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_7.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_8.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_9.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_10.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_11.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_12.
  - Goal_apply proof_of_bfs_type_entail_wit_8_1_split_goal_13.
Qed. 

Lemma proof_of_bfs_type_entail_wit_8_2_split_goal_1 : bfs_type_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hw : 1 <= Znth e tlst 0 <= n_pre) by (apply PreH26; exact PreH2).
  assert (HinQ : In (Znth e tlst 0) Q_2).
  { pose proof PreH28 as Hc.
    destruct Hc as (_ & _ & Hmem & _).
    apply (proj2 (Hmem (Znth e tlst 0) Hw)). lia. }
  apply (BfsScan_step m edges nx tlst Q_2 dl_2 Q_2 dl_2 u e PreH2 PreH31).
  - intros w0 Hw0. exact Hw0.
  - intros w0 Hw0. reflexivity.
  - reflexivity.
  - exact HinQ.
  - apply In_Znth_Z in HinQ as [i [Hi Hnth]].
    rewrite <- Hnth. apply PreH30. exact Hi.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_2_split_goal_2 : bfs_type_entail_wit_8_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct H as [Hne Hneg].
  pose proof (PreH12 e ltac:(lia)) as He1.
  assert (Hw1 : 1 <= Znth (Znth e nx 0) tlst 0 <= n_pre) by (apply PreH13; lia).
  pose proof (queue_room_core__g3_bfs_scan_core n_pre edges goods c_pre Q_2 dl_2
                (Znth (Znth e nx 0) tlst 0) PreH28 Hw1 Hneg) as Hres.
  lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_2_split_goal_3 : bfs_type_entail_wit_8_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename H into Hne.
  pose proof (PreH12 e ltac:(lia)) as He1.
  apply PreH13. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_2_split_goal_4 : bfs_type_entail_wit_8_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 e ltac:(lia)) as He1. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_2_split_goal_5 : bfs_type_entail_wit_8_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 e ltac:(lia)) as He1. lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_8_2 : bfs_type_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_bfs_type_entail_wit_8_2_split_goal_2.
  - Goal_apply proof_of_bfs_type_entail_wit_8_2_split_goal_3.
  - Goal_apply proof_of_bfs_type_entail_wit_8_2_split_goal_4.
  - Goal_apply proof_of_bfs_type_entail_wit_8_2_split_goal_5.
Qed. 

Lemma proof_of_bfs_type_entail_wit_9_split_goal_1 : bfs_type_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold BfsBounded in *.
  intros j Hj.
  specialize (PreH29 j Hj).
  destruct PreH27 as (_ & _ & _ & _ & _ & Hmono & _).
  specialize (Hmono (qh - 1) qh ltac:(lia) ltac:(lia) ltac:(lia)).
  subst u.
  lia.
Qed.

Lemma proof_of_bfs_type_entail_wit_9_split_goal_2 : bfs_type_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  apply (BfsScan_expand n_pre m edges hd nx tlst Q_2 dl_2 qh u).
  - lia.
  - exact PreH10.
  - lia.
  - exact PreH17.
  - exact PreH28.
  - exact PreH30.
Qed.

Lemma proof_of_bfs_type_entail_wit_9 : bfs_type_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_bfs_type_entail_wit_9_split_goal_2.
Qed.

Lemma proof_of_bfs_type_return_wit_1_split_goal_1 : bfs_type_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  apply (BfsCore_expanded_result n_pre edges goods c_pre Q dl).
  - lia.
  - exact PreH18.
  - replace (Zlength Q) with qh by lia.
    exact PreH19.
Qed.

Lemma proof_of_bfs_type_return_wit_1_split_goal_spatial : bfs_type_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.seg_to_undef_seg (&( "queue_" )) 0 qt Q).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "queue_" )) 0 qt n_pre ltac:(lia)).
  rewrite Z.mul_0_l, Z.add_0_r, Z.sub_0_r.
  cancel (IntArray.undef_full (&( "queue_" )) n_pre).
Qed.

Lemma proof_of_bfs_type_return_wit_1 : bfs_type_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_bfs_type_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_bfs_type_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_1 : solver_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hs : 0 <= ZSum (sublist 0 i l1) <= i * (n_pre - 1)).
  { apply ZSum_sublist_bound__g7_fair_sum; try lia.
    intros j Hj. apply PreH35. lia. }
  assert (He : 0 <= Znth i l1 0 <= n_pre - 1) by (apply PreH35; lia).
  assert (Hb : i * (n_pre - 1) <= 100 * 100000) by nia.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_29_split_goal_2 : solver_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hs : 0 <= ZSum (sublist 0 i l1) <= i * (n_pre - 1)).
  { apply ZSum_sublist_bound__g7_fair_sum; try lia.
    intros j Hj. apply PreH35. lia. }
  assert (He : 0 <= Znth i l1 0 <= n_pre - 1) by (apply PreH35; lia).
  lia.
Qed.

Lemma proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_29_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH18; tauto.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (exfalso; lia).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH16; tauto.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_5 : solver_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH11; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_6 : solver_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH10; tauto.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hv : v = n_pre + 1) by lia. subst v.
  Exists (@nil Z) (@nil Z) hd0.
  replace (2 * 0) with 0 by lia.
  rewrite (IntArray.undef_seg_empty (&( "head_")) (n_pre+1)).
  rewrite (IntArray.seg_empty (&( "nxt_")) 0 0).
  rewrite (IntArray.seg_empty (&( "to_")) 0 0).
  sep_apply (IntArray.undef_full_to_undef_seg (&( "nxt_")) (2*m_pre)).
  sep_apply (IntArray.undef_full_to_undef_seg (&( "to_")) (2*m_pre)).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try (rewrite Zlength_nil; lia).
    all: try lia.
    + intros Hm.
      destruct (PreH17 0 ltac:(lia)) as [Hu0 Hv0].
      pose proof (PreH12 0 ltac:(lia)) as Hb.
      rewrite Hu0, Hv0. lia.
    + unfold AdjBuild.
      split; [lia | ].
      split; [rewrite Zlength_nil; lia | ].
      split; [rewrite Zlength_nil; lia | ].
      split; [intros j Hj; exfalso; lia | ].
      split; [intros j Hj; exfalso; lia | ].
      split; [intros u Hu; left; apply PreH21; lia | ].
      intros u Hu. exists nil. unfold AdjListAt.
      assert (Hh : Znth (u - 1) hd0 0 = -1) by (apply PreH21; lia).
      rewrite Hh.
      split; [apply AdjChain_nil | ].
      split; [apply NoDup_nil | ].
      split; [intros j Hj; contradiction | intros j Hj; exfalso; lia].
    + unfold NxtRange. intros j Hj. exfalso. lia.
    + unfold ArcToRange. intros j Hj. exfalso. lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH20 PreH1) as Hrng.
  assert (Hidx : Znth i_4 tree_edges __default__Prod_Z_Z = Znth i_4 tree_edges (0, 0))
    by (apply Znth_indep; lia).
  destruct (PreH17 i_4 ltac:(lia)) as [Heu Hev].
  rewrite Hidx in Heu, Hev.
  pose proof (PreH12 i_4 ltac:(lia)) as Hbnd.
  rewrite Hidx in Hbnd. destruct Hbnd as [_ Hne].
  assert (Hdiff : Znth i_4 edge_u 0 - 1 <> Znth i_4 edge_v 0 - 1) by (rewrite Heu, Hev; lia).
  assert (Hlen1 : Zlength (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2) = n_pre)
    by (rewrite Zlength_replace_Znth; lia).
  assert (Hlen2 : Zlength (replace_Znth (Znth i_4 edge_v 0 - 1) (2 * i_4 + 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2)) = n_pre)
    by (rewrite Zlength_replace_Znth; lia).
  assert (Hbmid : Znth (Znth i_4 edge_v 0 - 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2) 0 = Znth (Znth i_4 edge_v 0 - 1) hd_2 0).
  { apply (Znth_replace_Znth_Diff 0 hd_2 (Znth i_4 edge_u 0 - 1) (Znth i_4 edge_v 0 - 1) (2 * i_4)); lia. }
  assert (Hhdu : Znth (Znth i_4 edge_u 0 - 1) (replace_Znth (Znth i_4 edge_v 0 - 1) (2 * i_4 + 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2)) 0 = 2 * i_4).
  { rewrite (Znth_replace_Znth_Diff 0 (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2) (Znth i_4 edge_v 0 - 1) (Znth i_4 edge_u 0 - 1) (2 * i_4 + 1))
       by lia.
     apply Znth_replace_Znth_Same. lia. }
  assert (Hhdv : Znth (Znth i_4 edge_v 0 - 1) (replace_Znth (Znth i_4 edge_v 0 - 1) (2 * i_4 + 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2)) 0 = 2 * i_4 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hhdo : forall x, 1 <= x <= n_pre -> x <> Znth i_4 edge_u 0 -> x <> Znth i_4 edge_v 0 ->
            Znth (x - 1) (replace_Znth (Znth i_4 edge_v 0 - 1) (2 * i_4 + 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2)) 0 = Znth (x - 1) hd_2 0).
  { intros x Hx Hxu Hxv.
     rewrite (Znth_replace_Znth_Diff 0 (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2) (Znth i_4 edge_v 0 - 1) (x - 1) (2 * i_4 + 1))
       by lia.
     apply (Znth_replace_Znth_Diff 0 hd_2 (Znth i_4 edge_u 0 - 1) (x - 1) (2 * i_4)); lia. }
  assert (HAB : AdjBuild n_pre (i_4 + 1) tree_edges (replace_Znth (Znth i_4 edge_v 0 - 1) (2 * i_4 + 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2)) ((nx_2 ++ (Znth (Znth i_4 edge_u 0 - 1) hd_2 0 :: nil)) ++ (Znth (Znth i_4 edge_v 0 - 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2) 0 :: nil)) ((tlst_2 ++ (Znth i_4 edge_v 0 :: nil)) ++ (Znth i_4 edge_u 0 :: nil))).
  { apply AdjBuild_insert__g1_adjacency_build with (hd := hd_2); try lia.
     - exact PreH24.
     - exact Hhdo. }
  assert (HNX : NxtRange (i_4 + 1) ((nx_2 ++ (Znth (Znth i_4 edge_u 0 - 1) hd_2 0 :: nil)) ++ (Znth (Znth i_4 edge_v 0 - 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2) 0 :: nil))).
  { unfold NxtRange. intros j Hj.
     pose proof HAB as HB'. unfold AdjBuild in HB'.
     destruct HB' as [_ [_ [_ [_ [Hr _]]]]].
     destruct (Hr j Hj); lia. }
  assert (HTL : ArcToRange n_pre (i_4 + 1) ((tlst_2 ++ (Znth i_4 edge_v 0 :: nil)) ++ (Znth i_4 edge_u 0 :: nil))).
  { unfold ArcToRange. intros j Hj.
     destruct (Z.lt_ge_cases j (2 * i_4)) as [Hlt | Hge].
     - rewrite app2_Znth_lt__g1_adjacency_build by lia.
       apply PreH26. lia.
     - destruct (Z.eq_dec j (2 * i_4)) as [He | He].
       + subst j. replace (2 * i_4) with (Zlength tlst_2) by lia.
         rewrite app2_Znth_fst__g1_adjacency_build. lia.
       + assert (Hj1 : j = 2 * i_4 + 1) by lia. subst j.
         replace (2 * i_4 + 1) with (Zlength tlst_2 + 1) by lia.
         rewrite app2_Znth_snd__g1_adjacency_build. lia. }
  Exists ((tlst_2 ++ (Znth i_4 edge_v 0 :: nil)) ++ (Znth i_4 edge_u 0 :: nil)) ((nx_2 ++ (Znth (Znth i_4 edge_u 0 - 1) hd_2 0 :: nil)) ++ (Znth (Znth i_4 edge_v 0 - 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2) 0 :: nil)) (replace_Znth (Znth i_4 edge_v 0 - 1) (2 * i_4 + 1) (replace_Znth (Znth i_4 edge_u 0 - 1) (2 * i_4) hd_2)).
  replace (2 * i_4 + 1 + 1) with (2 * (i_4 + 1)) by lia.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    all: try (rewrite !Zlength_replace_Znth; lia).
    all: try (rewrite !Zlength_app_cons; lia).
    intros Hlt.
    destruct (PreH17 (i_4 + 1) ltac:(lia)) as [Hu1 Hv1].
    pose proof (PreH12 (i_4 + 1) ltac:(lia)) as Hb1.
    rewrite Hu1, Hv1. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (unfold BfsRows; intros c v Hc Hv; exfalso; lia).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH28; tauto.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (replace m_pre with i_7 by lia; exact PreH26).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (replace m_pre with i_7 by lia; exact PreH25).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_5 : solver_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (replace m_pre with i_7 by lia; exact PreH24).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_6 : solver_entail_wit_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH17; tauto.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_7 : solver_entail_wit_5_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH12; tauto.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_8 : solver_entail_wit_5_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH11; tauto.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_7.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_8.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists rows_2 tlst_2 nx_2 hd_2.
  rewrite (Znth_indep__g5_dist_rows rows_2 c __default__List_Z nil) by lia.
  assert (Haddr : ( &( "dist_" ) ) + c * (sizeof(INT) * 100005) + 0 * sizeof(INT)
                  = IntArray2.row_addr ( &( "dist_" ) ) 100005 c).
  { unfold IntArray2.row_addr. ring. }
  rewrite Haddr.
  sep_apply (IntArray2.full_split_to_missing_i ( &( "dist_" ) ) c 105 100005 rows_2).
  2: lia.
  change IntArray2.ElemArray.full with IntArray.full.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; solve [ lia | assumption | auto ].
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Haddr : ( &( "dist_" ) ) + c * (sizeof(INT) * 100005) + 0 * sizeof(INT)
                  = IntArray2.row_addr ( &( "dist_" ) ) 100005 c).
  { unfold IntArray2.row_addr. ring. }
  rewrite Haddr.
  Exists (replace_Znth c dist_after rows_2) tlst_2 nx_2 hd_2.
  change IntArray.full with IntArray2.ElemArray.full.
  sep_apply (IntArray2.missing_i_merge_to_full ( &( "dist_" ) ) c 105 100005 rows_2 dist_after).
  2: lia.
  assert (Hrow : forall cc : Z, 0 <= cc < 105 ->
            Zlength (Znth cc (replace_Znth c dist_after rows_2) __default__List_Z) = 100005).
  { intros cc Hcc. destruct (Z.eq_dec cc c) as [Heq | Hne].
    - subst cc. rewrite Znth_replace_Znth_Same by lia. exact PreH1.
    - rewrite Znth_replace_Znth_Diff by lia. apply PreH28. lia. }
  assert (Hbfs : BfsRows n_pre tree_edges goods (replace_Znth c dist_after rows_2) (c + 1)).
  { unfold BfsRows. intros c2 v Hc2 Hv. destruct (Z.eq_dec c2 c) as [Heq | Hne].
    - subst c2. rewrite Znth_replace_Znth_Same by lia.
      apply (BfsRowResult_total k_pre s_pre n_pre tree_edges goods c dist_after v);
        [ exact PreH3 | exact PreH14 | lia | lia | exact PreH2 ].
    - rewrite Znth_replace_Znth_Diff by lia. apply PreH29; lia. }
  assert (Hlen : Zlength (replace_Znth c dist_after rows_2) = 105).
  { rewrite Zlength_replace_Znth. exact PreH27. }
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; solve [ lia | assumption | auto ].
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: unfold OutPrefix; intros i Hi; lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: replace (k_pre + 1) with c by lia.
  all: exact PreH28.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: exact PreH27.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH17; assumption.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_6 : solver_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH12; assumption.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_7 : solver_entail_wit_8_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH11; assumption.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (@nil Z) rows_2 tlst_2 nx_2 hd_2 out_2.
  replace (1 - 1) with 0 by lia.
  sep_apply (IntArray.undef_full_to_undef_seg ( &( "tmp_" ) ) k_pre).
  rewrite (IntArray.seg_empty ( &( "tmp_" ) ) 0 0).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      solve [ lia | assumption | auto
            | unfold TmpPrefix; intros j Hj; lia ].
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (@nil Z) rows_2 tlst_2 nx_2 hd_2 out_2.
  replace (1 - 1) with 0 by lia.
  sep_apply (IntArray.full_to_undef_full ( &( "tmp_" ) ) k_pre tmpl).
  sep_apply (IntArray.undef_full_to_undef_seg ( &( "tmp_" ) ) k_pre).
  rewrite (IntArray.seg_empty ( &( "tmp_" ) ) 0 0).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      solve [ lia | assumption | auto
            | unfold TmpPrefix; intros j Hj; lia ].
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (tp_2 ++ ((Znth v (Znth c rows_2 __default__List_Z) 0) :: nil))
         rows_2 tlst_2 nx_2 hd_2 out_2.
  assert (Hdef : Znth c rows_2 __default__List_Z = Znth c rows_2 nil).
  { apply Znth_indep__g6_tmp_prefix. lia. }
  assert (Hrow : (0 <= Znth v (Znth c rows_2 nil) 0 <= n_pre - 1) /\
                 (BfsDist n_pre tree_edges goods c v (Znth v (Znth c rows_2 nil) 0))).
  { apply PreH28; lia. }
  assert (Hlen : Zlength (tp_2 ++ ((Znth v (Znth c rows_2 __default__List_Z) 0) :: nil)) = c).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Htmp : TmpPrefix n_pre tree_edges goods v
                   (tp_2 ++ ((Znth v (Znth c rows_2 __default__List_Z) 0) :: nil)) c).
  { unfold TmpPrefix. intros j Hj.
    destruct (Z_lt_dec j (c - 1)) as [Hlt | Hge].
    - rewrite Znth_app_left__g6_tmp_prefix by lia.
      apply PreH31. lia.
    - assert (Hj0 : j = c - 1) by lia. subst j.
      rewrite Znth_app_right__g6_tmp_prefix by lia.
      rewrite PreH30. replace (c - 1 - (c - 1)) with 0 by lia.
      rewrite Hdef. unfold Znth. simpl.
      replace (c - 1 + 1) with c by lia.
      exact Hrow. }
  replace (c + 1 - 1) with c by lia.
  replace (c - 1 + 1) with c by lia.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      solve [ lia | assumption | auto ].
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists tp_2 rows_2 tlst_2 nx_2 hd_2 out_2.
  assert (Hc : c - 1 = k_pre) by lia.
  rewrite Hc in PreH30, PreH31 |- *.
  rewrite (IntArray.undef_seg_empty ( &( "tmp_" ) ) k_pre).
  assert (Hfull : IntArray.seg ( &( "tmp_" ) ) 0 k_pre tp_2
                  |-- IntArray.full (( &( "tmp_" ) ) + 0 * sizeof(INT)) k_pre tp_2).
  { pose proof (IntArray.seg_to_full ( &( "tmp_" ) ) 0 k_pre tp_2) as Hsf.
    replace (k_pre - 0) with k_pre in Hsf by lia.
    exact Hsf. }
  sep_apply Hfull.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      solve [ lia | assumption | auto ].
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((&( "tmp_")) + 0 * sizeof ( INT )) with (&( "tmp_")) by lia.
  prop_apply_p (IntArray.full_Zlength (&( "tmp_")) k_pre l1_2).
  Intros_p Hl1len.
  assert (Htp := PreH29). unfold TmpPrefix in Htp.
  assert (Hlen : Zlength tp = k_pre)
    by (rewrite (perm_Zlength tp l1_2 PreH1); lia).
  assert (Hbnd : forall j, 0 <= j < k_pre -> 0 <= Znth j l1_2 0 <= n_pre - 1).
  { intros j Hj.
    apply (Permutation_bound__g7_fair_sum tp l1_2 0 (n_pre - 1) PreH1).
    - intros j2 Hj2. apply (proj1 (Htp j2 ltac:(lia))).
    - lia. }
  Exists tp l1_2 rows_2 tlst_2 nx_2 hd_2 out_2.
  split_pure_spatial.
  - cancel (IntArray.full (&( "tmp_")) k_pre l1_2). cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia; try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hstep : sum + Znth i_4 l1_2 0 = ZSum (sublist 0 (i_4 + 1) l1_2)).
  { rewrite ZSum_sublist_succ__g7_fair_sum by lia. lia. }
  Exists tp0_2 l1_2 rows_2 tlst_2 nx_2 hd_2 out_2.
  split_pure_spatial.
  - cancel (IntArray.full (&( "tmp_")) k_pre l1_2). cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia; try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_1 : solver_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i_10 = s_pre) by lia. subst i_10.
  unfold OutPrefix. intros i2 Hi2.
  destruct (Z.eq_dec i2 (v - 1)) as [He | Hne].
  - subst i2. rewrite app_Znth2 by lia.
    replace (v - 1 - Zlength out_3) with 0 by lia.
    replace (Znth 0 (cons sum nil) 0) with sum by reflexivity.
    replace (v - 1 + 1) with v by lia.
    rewrite PreH36.
    apply (fair_cost_min n_pre s_pre k_pre tree_edges goods v tp0 l1);
      try assumption; try lia.
    + intros j Hj. apply (proj2 ((fun H => H) PreH33 j Hj)).
  - rewrite app_Znth1 by lia. apply PreH29. lia.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_2 : solver_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_3 : solver_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_4 : solver_entail_wit_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH17; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_5 : solver_entail_wit_14_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH12; lia.
Qed.

Lemma proof_of_solver_entail_wit_14_split_goal_6 : solver_entail_wit_14_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11; lia.
Qed.

Lemma proof_of_solver_entail_wit_14 : solver_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_14_split_goal_6.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hv : v = n_pre + 1) by lia. subst v.
  replace (n_pre + 1 - 1) with n_pre in PreH27 by lia.
  assert (HSpec : Spec k_pre s_pre tree_edges goods out_2).
  { apply (OutPrefix_Spec n_pre s_pre k_pre tree_edges goods out_2);
      try lia. exact PreH27. }
  rewrite (Int64Array.undef_seg_empty cost_pre (n_pre + 1)).
  Exists tmpl tlst nx hd rows out_2.
  split_pure_spatial.
  - cancel (IntArray.seg a_pre 1 (n_pre + 1) goods). cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed. 

