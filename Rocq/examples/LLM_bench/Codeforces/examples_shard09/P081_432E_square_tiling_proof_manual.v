From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P081_432E_square_tiling_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P081_432E_square_tiling_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib.
Local Open Scope sac.

Lemma proof_of_conflicts_entail_wit_1_split_goal_1 : conflicts_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_conflicts_entail_wit_1_split_goal_2 : conflicts_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_conflicts_entail_wit_1_split_goal_3 : conflicts_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_conflicts_entail_wit_1_split_goal_4 : conflicts_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_conflicts_entail_wit_1 : conflicts_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_conflicts_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_conflicts_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_conflicts_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_conflicts_return_wit_1_split_goal_1 : conflicts_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  destruct (Z.eq_dec left_override_pre 0); simpl in *; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_1 : conflicts_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_2_split_goal_1 : conflicts_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsigned :
      signed_last_nbits
        (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { assert (Hbounds :
        0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
    { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
      nia. }
    match goal with Hcanonical : CanonicalGrid flat |- _ =>
      specialize (Hcanonical _ Hbounds)
    end.
    match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict; simpl; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_2 : conflicts_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_3_split_goal_1 : conflicts_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  destruct (Z.eq_dec left_override_pre 0); simpl in *; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_3 : conflicts_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_4_split_goal_1 : conflicts_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsigned :
      signed_last_nbits
        (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { assert (Hbounds :
        0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
    { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
      nia. }
    match goal with Hcanonical : CanonicalGrid flat |- _ =>
      specialize (Hcanonical _ Hbounds)
    end.
    match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict; simpl; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_4 : conflicts_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_5_split_goal_1 : conflicts_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  destruct (Z.eq_dec left_override_pre 0); simpl in *; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_5 : conflicts_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_6_split_goal_1 : conflicts_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsigned :
      signed_last_nbits
        (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { assert (Hbounds :
        0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
    { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
      nia. }
    match goal with Hcanonical : CanonicalGrid flat |- _ =>
      specialize (Hcanonical _ Hbounds)
    end.
    match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict; simpl; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_6 : conflicts_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_7_split_goal_1 : conflicts_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  destruct (Z.eq_dec left_override_pre 0); simpl in *; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_7 : conflicts_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_8_split_goal_1 : conflicts_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsigned :
      signed_last_nbits
        (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { assert (Hbounds :
        0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
    { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
      nia. }
    match goal with Hcanonical : CanonicalGrid flat |- _ =>
      specialize (Hcanonical _ Hbounds)
    end.
    match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict; simpl; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_8 : conflicts_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_8_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_9_split_goal_1 : conflicts_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  destruct (Z.eq_dec left_override_pre 0); simpl in *; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_9 : conflicts_return_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_9_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_10_split_goal_1 : conflicts_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsigned :
      signed_last_nbits
        (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { assert (Hbounds :
        0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
    { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
      nia. }
    match goal with Hcanonical : CanonicalGrid flat |- _ =>
      specialize (Hcanonical _ Hbounds)
    end.
    match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict; simpl; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_10 : conflicts_return_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_10_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_11_split_goal_1 : conflicts_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  destruct (Z.eq_dec left_override_pre 0); simpl in *; intuition nia.
Qed.

Lemma proof_of_conflicts_return_wit_11 : conflicts_return_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_11_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_12_split_goal_1 : conflicts_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] |
       [[Hdown_bound Hdown] |
        [[Hright_bound Hright] |
         [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c,
         Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c,
         Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_12 : conflicts_return_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_12_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_13_split_goal_1 : conflicts_return_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_13 : conflicts_return_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_13_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_14_split_goal_1 : conflicts_return_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_14 : conflicts_return_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_14_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_15_split_goal_1 : conflicts_return_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_15 : conflicts_return_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_15_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_16_split_goal_1 : conflicts_return_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_16 : conflicts_return_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_16_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_17_split_goal_1 : conflicts_return_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_17 : conflicts_return_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_17_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_18_split_goal_1 : conflicts_return_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_18 : conflicts_return_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_18_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_19_split_goal_1 : conflicts_return_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_19 : conflicts_return_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_19_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_20_split_goal_1 : conflicts_return_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_20 : conflicts_return_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_20_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_21_split_goal_1 : conflicts_return_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_21 : conflicts_return_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_21_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_22_split_goal_1 : conflicts_return_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_22 : conflicts_return_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_22_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_23_split_goal_1 : conflicts_return_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intro Hconf.
  destruct Hconf as
      [[Hi Hup] | [[Hdown_bound Hdown] | [[Hright_bound Hright] |
       [[Hj Hleft] | [Hj0 Hover]]]]].
  all: try lia.
  all: try congruence.
  all: try (destruct (Z.eq_dec left_override_pre 0) as [Hoverride | Hoverride];
            subst; simpl in *; try lia; try congruence).
  all: try match goal with
       | Hneq : signed_last_nbits ?x 8 <> ?x |- False =>
           apply Hneq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?x = ?c |- False =>
           apply Hneq; rewrite Heq; apply signed_last_nbits_eq; lia
       | Hneq : signed_last_nbits ?x 8 <> ?c, Heq : ?c = ?x |- False =>
           apply Hneq; rewrite <- Heq; apply signed_last_nbits_eq; lia
       end.
Qed.

Lemma proof_of_conflicts_return_wit_23 : conflicts_return_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_23_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_24_split_goal_1 : conflicts_return_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  intuition lia.
Qed.

Lemma proof_of_conflicts_return_wit_24 : conflicts_return_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_24_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_25_split_goal_1 : conflicts_return_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; right.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_conflicts_return_wit_25 : conflicts_return_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_25_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_26_split_goal_1 : conflicts_return_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; right.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_conflicts_return_wit_26 : conflicts_return_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_26_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_27_split_goal_1 : conflicts_return_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; right.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_conflicts_return_wit_27 : conflicts_return_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_27_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_28_split_goal_1 : conflicts_return_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; right.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_conflicts_return_wit_28 : conflicts_return_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_28_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_29_split_goal_1 : conflicts_return_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; right.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_conflicts_return_wit_29 : conflicts_return_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_29_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_30_split_goal_1 : conflicts_return_wit_30_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; right.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_conflicts_return_wit_30 : conflicts_return_wit_30.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_30_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_31_split_goal_1 : conflicts_return_wit_31_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; right.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_conflicts_return_wit_31 : conflicts_return_wit_31.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_31_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_32_split_goal_1 : conflicts_return_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; right.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_conflicts_return_wit_32 : conflicts_return_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_32_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_33_split_goal_1 : conflicts_return_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia |].
  destruct (Z.eq_dec c_pre 0) as [Hzero | Hnonzero].
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_conflicts_return_wit_33 : conflicts_return_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_33_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_34_split_goal_1 : conflicts_return_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbounds :
      0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
  { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
    nia. }
  match goal with Hcanonical : CanonicalGrid flat |- _ =>
    specialize (Hcanonical _ Hbounds)
  end.
  assert (Hsigned :
      signed_last_nbits (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia | simpl; exact PreH1].
Qed.

Lemma proof_of_conflicts_return_wit_34 : conflicts_return_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_34_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_35_split_goal_1 : conflicts_return_wit_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia |].
  destruct (Z.eq_dec c_pre 0) as [Hzero | Hnonzero].
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_conflicts_return_wit_35 : conflicts_return_wit_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_35_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_36_split_goal_1 : conflicts_return_wit_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbounds :
      0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
  { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
    nia. }
  match goal with Hcanonical : CanonicalGrid flat |- _ =>
    specialize (Hcanonical _ Hbounds)
  end.
  assert (Hsigned :
      signed_last_nbits (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia | simpl; exact PreH1].
Qed.

Lemma proof_of_conflicts_return_wit_36 : conflicts_return_wit_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_36_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_37_split_goal_1 : conflicts_return_wit_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia |].
  destruct (Z.eq_dec c_pre 0) as [Hzero | Hnonzero].
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_conflicts_return_wit_37 : conflicts_return_wit_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_37_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_38_split_goal_1 : conflicts_return_wit_38_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbounds :
      0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
  { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
    nia. }
  match goal with Hcanonical : CanonicalGrid flat |- _ =>
    specialize (Hcanonical _ Hbounds)
  end.
  assert (Hsigned :
      signed_last_nbits (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia | simpl; exact PreH1].
Qed.

Lemma proof_of_conflicts_return_wit_38 : conflicts_return_wit_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_38_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_39_split_goal_1 : conflicts_return_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia |].
  destruct (Z.eq_dec c_pre 0) as [Hzero | Hnonzero].
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_conflicts_return_wit_39 : conflicts_return_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_39_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_40_split_goal_1 : conflicts_return_wit_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbounds :
      0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
  { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
    nia. }
  match goal with Hcanonical : CanonicalGrid flat |- _ =>
    specialize (Hcanonical _ Hbounds)
  end.
  assert (Hsigned :
      signed_last_nbits (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia | simpl; exact PreH1].
Qed.

Lemma proof_of_conflicts_return_wit_40 : conflicts_return_wit_40.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_40_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_41_split_goal_1 : conflicts_return_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia |].
  destruct (Z.eq_dec c_pre 0) as [Hzero | Hnonzero].
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_conflicts_return_wit_41 : conflicts_return_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_41_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_42_split_goal_1 : conflicts_return_wit_42_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbounds :
      0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
  { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
    nia. }
  match goal with Hcanonical : CanonicalGrid flat |- _ =>
    specialize (Hcanonical _ Hbounds)
  end.
  assert (Hsigned :
      signed_last_nbits (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia | simpl; exact PreH1].
Qed.

Lemma proof_of_conflicts_return_wit_42 : conflicts_return_wit_42.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_42_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_43_split_goal_1 : conflicts_return_wit_43_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia |].
  destruct (Z.eq_dec c_pre 0) as [Hzero | Hnonzero].
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_conflicts_return_wit_43 : conflicts_return_wit_43.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_43_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_44_split_goal_1 : conflicts_return_wit_44_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbounds :
      0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
  { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
    nia. }
  match goal with Hcanonical : CanonicalGrid flat |- _ =>
    specialize (Hcanonical _ Hbounds)
  end.
  assert (Hsigned :
      signed_last_nbits (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia | simpl; exact PreH1].
Qed.

Lemma proof_of_conflicts_return_wit_44 : conflicts_return_wit_44.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_44_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_45_split_goal_1 : conflicts_return_wit_45_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia |].
  destruct (Z.eq_dec c_pre 0) as [Hzero | Hnonzero].
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_conflicts_return_wit_45 : conflicts_return_wit_45.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_45_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_46_split_goal_1 : conflicts_return_wit_46_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbounds :
      0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
  { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
    nia. }
  match goal with Hcanonical : CanonicalGrid flat |- _ =>
    specialize (Hcanonical _ Hbounds)
  end.
  assert (Hsigned :
      signed_last_nbits (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia | simpl; exact PreH1].
Qed.

Lemma proof_of_conflicts_return_wit_46 : conflicts_return_wit_46.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_46_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_47_split_goal_1 : conflicts_return_wit_47_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia |].
  destruct (Z.eq_dec c_pre 0) as [Hzero | Hnonzero].
  - lia.
  - reflexivity.
Qed.

Lemma proof_of_conflicts_return_wit_47 : conflicts_return_wit_47.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_47_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_48_split_goal_1 : conflicts_return_wit_48_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbounds :
      0 <= i_pre * m_pre + j_pre - 1 < Zlength flat).
  { match goal with Hlength : Zlength flat = _ |- _ => rewrite Hlength end.
    nia. }
  match goal with Hcanonical : CanonicalGrid flat |- _ =>
    specialize (Hcanonical _ Hbounds)
  end.
  assert (Hsigned :
      signed_last_nbits (Znth (i_pre * m_pre + j_pre - 1) flat 0) 8 =
      Znth (i_pre * m_pre + j_pre - 1) flat 0).
  { match goal with
    | Hcanonical : _ = 0 \/ _ |- _ =>
        destruct Hcanonical as [Hzero | Hrange]
    end.
    - rewrite Hzero. apply signed_last_nbits_eq; lia.
    - apply signed_last_nbits_eq; lia. }
  rewrite Hsigned in PreH1.
  unfold NeighborConflict.
  right; right; right; left.
  split; [lia | simpl; exact PreH1].
Qed.

Lemma proof_of_conflicts_return_wit_48 : conflicts_return_wit_48.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_48_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_49_split_goal_1 : conflicts_return_wit_49_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; left.
  split; assumption.
Qed.

Lemma proof_of_conflicts_return_wit_49 : conflicts_return_wit_49.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_49_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_50_split_goal_1 : conflicts_return_wit_50_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; left.
  split; assumption.
Qed.

Lemma proof_of_conflicts_return_wit_50 : conflicts_return_wit_50.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_50_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_51_split_goal_1 : conflicts_return_wit_51_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; left.
  split; assumption.
Qed.

Lemma proof_of_conflicts_return_wit_51 : conflicts_return_wit_51.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_conflicts_return_wit_51_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_52_split_goal_1 : conflicts_return_wit_52_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; right; left.
  split; assumption.
Qed.

Lemma proof_of_conflicts_return_wit_52 : conflicts_return_wit_52.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_conflicts_return_wit_52_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_53_split_goal_1 : conflicts_return_wit_53_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; left.
  split; assumption.
Qed.

Lemma proof_of_conflicts_return_wit_53 : conflicts_return_wit_53.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_conflicts_return_wit_53_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_54_split_goal_1 : conflicts_return_wit_54_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  right; left.
  split; assumption.
Qed.

Lemma proof_of_conflicts_return_wit_54 : conflicts_return_wit_54.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_conflicts_return_wit_54_split_goal_1.
Qed.

Lemma proof_of_conflicts_return_wit_55_split_goal_1 : conflicts_return_wit_55_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NeighborConflict.
  left.
  split; [lia | congruence].
Qed.

Lemma proof_of_conflicts_return_wit_55 : conflicts_return_wit_55.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_conflicts_return_wit_55_split_goal_1.
Qed.

Lemma proof_of_cell_colour_entail_wit_1_split_goal_1 : cell_colour_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NoConflictBelow.
  intros color Hcolor.
  lia.
Qed.

Lemma proof_of_cell_colour_entail_wit_1 : cell_colour_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cell_colour_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_cell_colour_entail_wit_2_split_goal_1 : cell_colour_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NoConflictBelow in *.
  intros color Hcolor.
  destruct (Z_lt_ge_dec color c) as [Hlt | Hge].
  - apply PreH20.
    lia.
  - replace color with c by lia.
    exact PreH3.
Qed.

Lemma proof_of_cell_colour_entail_wit_2 : cell_colour_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cell_colour_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_cell_colour_return_wit_1_split_goal_1 : cell_colour_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (neighbor_conflict_five_colour_choice__colour_selection
    flat n_pre m_pre i_pre j_pre left_override_pre)
    as (color & Hcolor & Hfree).
  exfalso.
  apply Hfree.
  apply PreH16.
  lia.
Qed.

Lemma proof_of_cell_colour_return_wit_1 : cell_colour_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cell_colour_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cell_colour_return_wit_2_split_goal_1 : cell_colour_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold LeastLegalColor, LegalColor.
  split.
  - split.
    + lia.
    + exact PreH3.
  - intros color Hcolor (_ & Hfree).
    apply Hfree.
    apply PreH20.
    exact Hcolor.
Qed.

Lemma proof_of_cell_colour_return_wit_2 : cell_colour_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cell_colour_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_can_place_entail_wit_1_split_goal_1 : can_place_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold EmptySquarePrefix.
  intros off Hoff.
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_1 : can_place_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_can_place_entail_wit_2_split_goal_1 : can_place_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold EmptySquarePrefix in *.
  intros off Hoff.
  apply PreH20.
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_2_split_goal_2 : can_place_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_2 : can_place_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_can_place_entail_wit_3_split_goal_1 : can_place_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold EmptySquarePrefix in *.
  intros off Hoff.
  apply PreH23.
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_3 : can_place_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_can_place_entail_wit_4_split_goal_1 : can_place_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold EmptySquarePrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off ((r - i_pre) * s_pre + (q - j_pre)))
    as [Hold | Hnew].
  - apply PreH23. nia.
  - assert (off = (r - i_pre) * s_pre + (q - j_pre)) by nia.
    subst off.
    replace (((r - i_pre) * s_pre + (q - j_pre)) / s_pre)
      with (r - i_pre).
    2: { rewrite Z.div_add_l by lia.
         rewrite Z.div_small by lia.
         lia. }
    replace (((r - i_pre) * s_pre + (q - j_pre)) mod s_pre)
      with (q - j_pre).
    2: { rewrite Z.add_comm, Z.mod_add, Z.mod_small by lia.
         reflexivity. }
    replace ((i_pre + (r - i_pre)) * m_pre +
             (j_pre + (q - j_pre))) with (r * m_pre + q) by lia.
    exact PreH24.
Qed.

Lemma proof_of_can_place_entail_wit_4_split_goal_2 : can_place_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_4 : can_place_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_can_place_entail_wit_5_split_goal_1 : can_place_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HorizontalBoundaryClearPrefix.
  intros off Hoff.
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_5_split_goal_2 : can_place_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold EmptySquarePrefix in *.
  intros off Hoff.
  apply PreH20.
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_5_split_goal_3 : can_place_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_5_split_goal_4 : can_place_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - apply Z.add_nonneg_nonneg.
    + apply Z.mul_nonneg_nonneg; lia.
    + lia.
  - transitivity (i_pre * m_pre).
    + replace (i_pre * m_pre) with ((i_pre - 1) * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_lt_mono_pos_r; lia.
Qed.

Lemma proof_of_can_place_entail_wit_5 : can_place_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_can_place_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_can_place_entail_wit_5_split_goal_4.
Qed.

Lemma proof_of_can_place_entail_wit_6_1_split_goal_1 : can_place_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HorizontalBoundaryClearPrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off (q - j_pre)) as [Hold | Hnew].
  - apply PreH26. lia.
  - assert (off = q - j_pre) by lia.
    subst off.
    split; intro Hboundary.
    + replace (j_pre + (q - j_pre)) with q by lia.
      exact PreH2.
    + lia.
Qed.

Lemma proof_of_can_place_entail_wit_6_1_split_goal_2 : can_place_entail_wit_6_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_6_1 : can_place_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_6_1_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_6_1_split_goal_2.
Qed.

Lemma proof_of_can_place_entail_wit_6_2_split_goal_1 : can_place_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HorizontalBoundaryClearPrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off (q - j_pre)) as [Hold | Hnew].
  - apply PreH25. lia.
  - assert (off = q - j_pre) by lia.
    subst off.
    split; intro Hboundary; lia.
Qed.

Lemma proof_of_can_place_entail_wit_6_2 : can_place_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_6_2_split_goal_1.
Qed.

Lemma proof_of_can_place_entail_wit_6_3_split_goal_1 : can_place_entail_wit_6_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HorizontalBoundaryClearPrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off (q - j_pre)) as [Hold | Hnew].
  - apply PreH26. lia.
  - assert (off = q - j_pre) by lia.
    subst off.
    split; intro Hboundary.
    + lia.
    + replace (j_pre + (q - j_pre)) with q by lia.
      exact PreH1.
Qed.

Lemma proof_of_can_place_entail_wit_6_3_split_goal_2 : can_place_entail_wit_6_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.

Lemma proof_of_can_place_entail_wit_6_3 : can_place_entail_wit_6_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_6_3_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_6_3_split_goal_2.
Qed.

Lemma proof_of_can_place_entail_wit_6_4_split_goal_1 : can_place_entail_wit_6_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HorizontalBoundaryClearPrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off (q - j_pre)) as [Hold | Hnew].
  - apply PreH27. lia.
  - assert (off = q - j_pre) by lia.
    subst off.
    split; intro Hboundary.
    + replace (j_pre + (q - j_pre)) with q by lia.
      exact PreH3.
    + replace (j_pre + (q - j_pre)) with q by lia.
      exact PreH1.
Qed.

Lemma proof_of_can_place_entail_wit_6_4_split_goal_2 : can_place_entail_wit_6_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - apply Z.add_nonneg_nonneg.
    + apply Z.mul_nonneg_nonneg; lia.
    + lia.
  - apply Z.lt_le_trans with (m := (i_pre + s_pre + 1) * m_pre).
    + replace ((i_pre + s_pre + 1) * m_pre) with
        ((i_pre + s_pre) * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_can_place_entail_wit_6_4_split_goal_3 : can_place_entail_wit_6_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_can_place_entail_wit_6_4 : can_place_entail_wit_6_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_6_4_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_6_4_split_goal_2.
  - Goal_apply proof_of_can_place_entail_wit_6_4_split_goal_3.
Qed.

Lemma proof_of_can_place_entail_wit_7_split_goal_1 : can_place_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold VerticalBoundaryClearPrefix.
  intros off Hoff.
  lia.
Qed.

Lemma proof_of_can_place_entail_wit_7_split_goal_2 : can_place_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HorizontalBoundaryClearPrefix in *.
  intros off Hoff.
  apply PreH23.
  lia.
Qed.

Lemma proof_of_can_place_entail_wit_7_split_goal_3 : can_place_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= i_pre * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (i_pre + 1) * m_pre).
    + replace ((i_pre + 1) * m_pre) with
        (i_pre * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_can_place_entail_wit_7_split_goal_4 : can_place_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= i_pre * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (i_pre + 1) * m_pre).
    + replace ((i_pre + 1) * m_pre) with
        (i_pre * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_can_place_entail_wit_7 : can_place_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_can_place_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_can_place_entail_wit_7_split_goal_4.
Qed.

Lemma proof_of_can_place_entail_wit_8_1_split_goal_1 : can_place_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold VerticalBoundaryClearPrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off (r - i_pre)) as [Hold | Hnew].
  - apply PreH27. lia.
  - assert (off = r - i_pre) by lia.
    subst off.
    split; intro Hboundary.
    + replace (i_pre + (r - i_pre)) with r by lia.
      exact PreH2.
    + lia.
Qed.

Lemma proof_of_can_place_entail_wit_8_1_split_goal_2 : can_place_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= (r + 1) * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (r + 2) * m_pre).
    + replace ((r + 2) * m_pre) with
        ((r + 1) * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_can_place_entail_wit_8_1 : can_place_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_8_1_split_goal_2.
Qed.

Lemma proof_of_can_place_entail_wit_8_2_split_goal_1 : can_place_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold VerticalBoundaryClearPrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off (r - i_pre)) as [Hold | Hnew].
  - apply PreH26. lia.
  - assert (off = r - i_pre) by lia.
    subst off.
    split; intro Hboundary; lia.
Qed.

Lemma proof_of_can_place_entail_wit_8_2 : can_place_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_8_2_split_goal_1.
Qed.

Lemma proof_of_can_place_entail_wit_8_3_split_goal_1 : can_place_entail_wit_8_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold VerticalBoundaryClearPrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off (r - i_pre)) as [Hold | Hnew].
  - apply PreH27. lia.
  - assert (off = r - i_pre) by lia.
    subst off.
    split; intro Hboundary.
    + lia.
    + replace (i_pre + (r - i_pre)) with r by lia.
      exact PreH1.
Qed.

Lemma proof_of_can_place_entail_wit_8_3_split_goal_2 : can_place_entail_wit_8_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= (r + 1) * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (r + 2) * m_pre).
    + replace ((r + 2) * m_pre) with
        ((r + 1) * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_can_place_entail_wit_8_3 : can_place_entail_wit_8_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_8_3_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_8_3_split_goal_2.
Qed.

Lemma proof_of_can_place_entail_wit_8_4_split_goal_1 : can_place_entail_wit_8_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold VerticalBoundaryClearPrefix in *.
  intros off Hoff.
  destruct (Z_lt_ge_dec off (r - i_pre)) as [Hold | Hnew].
  - apply PreH28. lia.
  - assert (off = r - i_pre) by lia.
    subst off.
    split; intro Hboundary.
    + replace (i_pre + (r - i_pre)) with r by lia.
      exact PreH3.
    + replace (i_pre + (r - i_pre)) with r by lia.
      exact PreH1.
Qed.

Lemma proof_of_can_place_entail_wit_8_4_split_goal_2 : can_place_entail_wit_8_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= (r + 1) * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (r + 2) * m_pre).
    + replace ((r + 2) * m_pre) with
        ((r + 1) * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_can_place_entail_wit_8_4_split_goal_3 : can_place_entail_wit_8_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= (r + 1) * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (r + 2) * m_pre).
    + replace ((r + 2) * m_pre) with
        ((r + 1) * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_can_place_entail_wit_8_4 : can_place_entail_wit_8_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_entail_wit_8_4_split_goal_1.
  - Goal_apply proof_of_can_place_entail_wit_8_4_split_goal_2.
  - Goal_apply proof_of_can_place_entail_wit_8_4_split_goal_3.
Qed.

Lemma proof_of_can_place_return_wit_1_split_goal_1 : can_place_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  split; [exact PreH10 |].
  split; [exact PreH14 |].
  split; [exact PreH15 |].
  split.
  - intros row column Hrow Hcolumn.
    specialize (PreH22 ((row - i_pre) * s_pre + (column - j_pre))).
    assert (Hoff :
      0 <= (row - i_pre) * s_pre + (column - j_pre) <
        s_pre * s_pre) by nia.
    specialize (PreH22 Hoff).
    replace ((row - i_pre) * s_pre + (column - j_pre))
      with ((column - j_pre) + (row - i_pre) * s_pre) in PreH22 by ring.
    rewrite Z.div_add in PreH22 by lia.
    rewrite Z.div_small in PreH22 by lia.
    rewrite Z.mod_add in PreH22 by lia.
    rewrite Z.mod_small in PreH22 by lia.
    replace (i_pre + (0 + (row - i_pre))) with row in PreH22 by ring.
    replace (j_pre + (column - j_pre)) with column in PreH22 by ring.
    exact PreH22.
  - split.
    + intros column Hcolumn.
      specialize (PreH23 (column - j_pre)).
      replace (j_pre + (column - j_pre)) with column in PreH23 by ring.
      apply PreH23.
      lia.
    + intros row Hrow.
      specialize (PreH24 (row - i_pre)).
      replace (i_pre + (row - i_pre)) with row in PreH24 by ring.
      apply PreH24.
      lia.
Qed.

Lemma proof_of_can_place_return_wit_1 : can_place_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_2_split_goal_1 : can_place_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & _ & _ & _ & _ & Hvertical).
  specialize (Hvertical r ltac:(lia)) as (_ & Hright).
  apply (Hright ltac:(lia)).
  exact PreH1.
Qed.

Lemma proof_of_can_place_return_wit_2 : can_place_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_3_split_goal_1 : can_place_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & _ & _ & _ & _ & Hvertical).
  specialize (Hvertical r ltac:(lia)) as (_ & Hright).
  apply (Hright ltac:(lia)).
  exact PreH1.
Qed.

Lemma proof_of_can_place_return_wit_3 : can_place_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_4_split_goal_1 : can_place_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & _ & _ & _ & _ & Hvertical).
  specialize (Hvertical r ltac:(lia)) as (Hleft & _).
  apply (Hleft ltac:(lia)).
  exact PreH1.
Qed.

Lemma proof_of_can_place_return_wit_4 : can_place_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_5_split_goal_1 : can_place_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & _ & _ & _ & Hhorizontal & _).
  specialize (Hhorizontal q ltac:(lia)) as (_ & Hbottom).
  apply (Hbottom ltac:(lia)).
  exact PreH1.
Qed.

Lemma proof_of_can_place_return_wit_5 : can_place_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_6_split_goal_1 : can_place_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & _ & _ & _ & Hhorizontal & _).
  specialize (Hhorizontal q ltac:(lia)).
  destruct Hhorizontal as [_ Hdown].
  apply (Hdown PreH2).
  exact PreH1.
Qed.

Lemma proof_of_can_place_return_wit_6 : can_place_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_7_split_goal_1 : can_place_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & _ & _ & _ & Hhorizontal & _).
  specialize (Hhorizontal q ltac:(lia)).
  destruct Hhorizontal as [Hup _].
  apply (Hup ltac:(lia)).
  exact PreH1.
Qed.

Lemma proof_of_can_place_return_wit_7 : can_place_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_8_split_goal_1 : can_place_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & _ & _ & Hempty & _).
  apply PreH24.
  apply Hempty; lia.
Qed.

Lemma proof_of_can_place_return_wit_8 : can_place_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_8_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_9_split_goal_1 : can_place_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & Hrow_bound & _).
  lia.
Qed.

Lemma proof_of_can_place_return_wit_9 : can_place_return_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_9_split_goal_1.
Qed.

Lemma proof_of_can_place_return_wit_10_split_goal_1 : can_place_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace.
  intros (_ & _ & Hcolumn_bound & _).
  lia.
Qed.

Lemma proof_of_can_place_return_wit_10 : can_place_return_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_can_place_return_wit_10_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NoPlaceableColorBelow in PreH17.
  specialize (PreH17 available ltac:(lia)).
  contradiction.
Qed.

Lemma proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshape_rec :
    forall (storeA : addr -> Z -> Z -> Assertion) k x lo hi,
      store_undef_array_rec (fun x lo => EX a : Z, storeA x lo a)
        x lo hi k
      |-- EX l : list Z, store_array_rec storeA x lo hi l).
  {
    intros storeA k.
    induction k as [|k IH]; intros x lo hi; simpl.
    - Exists (@nil Z).
      simpl.
      split_pure_spatial.
      + Intros_p Hlohi.
        cancel.
      + Intros_p Hlohi2.
        split_pures; dump_pre_spatial; auto.
    - Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      Intros l.
      Exists (a :: l).
      simpl.
      cancel.
  }
  assert (Hshape_full :
    forall x n,
      CharArray.full_shape x n
      |-- EX l : list Z, CharArray.full x n l).
  {
    intros x n.
    unfold CharArray.full_shape, CharArray.full,
      store_undef_array, store_array.
    apply Hshape_rec.
  }
  sep_apply_l_atomic (Hshape_full g_pre (n_pre * m_pre)).
  Intros flat.
  prop_apply_p (CharArray.full_Zlength g_pre (n_pre * m_pre) flat).
  Intros_p Hflat_length.
  Exists flat.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold ZeroPrefix; intros; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i * m_pre + 0) with (i * m_pre) by lia.
  exact PreH9.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (i * m_pre + 0) with (i * m_pre) by lia.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - apply Z.mul_lt_mono_pos_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i + 1) * m_pre) with (i * m_pre + j) by nia.
  exact PreH12.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ZeroPrefix in *.
  intros k Hk.
  destruct (Z.eq_dec k (i * m_pre + j)) as [Heq | Hneq].
  - subst k.
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - rewrite Znth_replace_Znth_Diff.
    + apply PreH12. lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= i * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (i + 1) * m_pre).
    + replace ((i + 1) * m_pre) with (i * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (0 * m_pre) with 0 by lia.
  apply GreedyTrace_zero.
  - exact PreH8.
  - replace (n_pre * m_pre) with (i * m_pre) by nia.
    exact PreH9.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanonicalGrid.
  intros k Hk.
  left.
  apply PreH9.
  replace (i * m_pre) with (n_pre * m_pre) by nia.
  rewrite <- PreH8.
  exact Hk.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i * m_pre + 0) with (i * m_pre) by lia.
  exact PreH10.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (i * m_pre + 0) with (i * m_pre) by lia.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - apply Z.mul_lt_mono_pos_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (PreH10 PreH1) as [Hindex_lo Hindex_hi].
  eapply GreedyTrace_skip.
  - exact PreH13.
  - split; assumption.
  - specialize (PreH12 (i * m_pre + j)).
    destruct (PreH12 ltac:(lia)) as [Hzero | Hcolor].
    + contradiction.
    + exact Hcolor.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (five_colour_neighbour_available__solver_colour_search
    grid_2 n_pre m_pre i j PreH2 PreH4
    ltac:(lia) ltac:(lia) PreH14) as [available [[Havlo Havhi] Hplace]].
  assert (Hnone : NoPlaceableColorBelow grid_2 n_pre m_pre i j 65).
  { unfold NoPlaceableColorBelow.
    intros color Hcolor.
    lia. }
  Exists available grid_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption || lia.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proj1
    (can_place_one_iff_legal_color__solver_colour_search
       grid_2 n_pre m_pre i j t PreH5 PreH7
       ltac:(lia) ltac:(lia) PreH18 ltac:(lia)) PreH2) as Hlegal.
  split; [exact Hlegal |].
  unfold NoPlaceableColorBelow in PreH20.
  intros d Hd Hlegal_d.
  apply (PreH20 d Hd).
  apply (proj2
    (can_place_one_iff_legal_color__solver_colour_search
       grid_2 n_pre m_pre i j d PreH5 PreH7
       ltac:(lia) ltac:(lia) PreH18 ltac:(lia))).
  exact Hlegal_d.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold NoPlaceableColorBelow in PreH17.
  exfalso.
  apply (PreH17 available).
  - lia.
  - exact PreH20.
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnone_next :
      NoPlaceableColorBelow grid_2 n_pre m_pre i j (t + 1)).
  { unfold NoPlaceableColorBelow in *.
    intros color Hcolor.
    destruct (Z_lt_ge_dec color t) as [Hlt | Hge].
    - apply (PreH20 color). lia.
    - assert (color = t) by lia.
      subst color.
      exact PreH2. }
  Exists available_2 grid_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption || lia.
Qed.

Lemma proof_of_solver_entail_wit_14_colour_found_split_goal_1 : solver_entail_wit_14_colour_found_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ChosenSquareState, GreedySideState.
  intuition lia.
Qed.

Lemma proof_of_solver_entail_wit_14_colour_found_split_goal_2 : solver_entail_wit_14_colour_found_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedySideState.
  intuition lia.
Qed.

Lemma proof_of_solver_entail_wit_14_colour_found_split_goal_3 : solver_entail_wit_14_colour_found_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold LeastLegalColor, LegalColor in *.
  intuition lia.
Qed.

Lemma proof_of_solver_entail_wit_14_colour_found_split_goal_4 : solver_entail_wit_14_colour_found_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold LeastLegalColor, LegalColor in *.
  intuition lia.
Qed.

Lemma proof_of_solver_entail_wit_14_colour_found : solver_entail_wit_14_colour_found.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_colour_found_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_colour_found_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_colour_found_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_colour_found_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_17_colour_found_split_goal_1 : solver_entail_wit_17_colour_found_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ChosenSquareState in *.
  split; [assumption |].
  eapply greedy_side_extend__solver_greedy_side; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_colour_found_split_goal_2 : solver_entail_wit_17_colour_found_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply greedy_side_extend__solver_greedy_side; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_17_colour_found_split_goal_3 : solver_entail_wit_17_colour_found_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CanPlace in *.
  intuition lia.
Qed.

Lemma proof_of_solver_entail_wit_17_colour_found : solver_entail_wit_17_colour_found.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_17_colour_found_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_17_colour_found_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_17_colour_found_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_18_1_colour_found_split_goal_1 : solver_entail_wit_18_1_colour_found_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SettledSquareState.
  split.
  - assumption.
  - left. lia.
Qed.

Lemma proof_of_solver_entail_wit_18_1_colour_found : solver_entail_wit_18_1_colour_found.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_18_1_colour_found_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_18_2_colour_found_split_goal_1 : solver_entail_wit_18_2_colour_found_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SettledSquareState.
  split.
  - assumption.
  - right. left. assumption.
Qed.

Lemma proof_of_solver_entail_wit_18_2_colour_found : solver_entail_wit_18_2_colour_found.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_18_2_colour_found_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_18_3_colour_found_split_goal_1 : solver_entail_wit_18_3_colour_found_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SettledSquareState.
  split.
  - assumption.
  - right. right. eexists. split; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_18_3_colour_found : solver_entail_wit_18_3_colour_found.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_18_3_colour_found_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_19_colour_found : solver_entail_wit_19_colour_found.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists grid grid.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try (intros; nia).
    unfold PaintRectanglePrefix.
    split; [reflexivity |].
    intros index Hindex.
    right.
    split.
    + intros off Hoff. lia.
    + reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_20_colour_found : solver_entail_wit_20_colour_found.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists current_2 before_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try (intros; nia).
    replace (((r - i) * size) + (j - j)) with ((r - i) * size) by lia.
    exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_21_colour_found : solver_entail_wit_21_colour_found.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists current_2 before_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    replace (((r + 1) - i) * size)
      with (((r - i) * size) + (q - j)) by nia.
    exact PreH27.
Qed.

Lemma proof_of_solver_entail_wit_22_colour_found : solver_entail_wit_22_colour_found.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hindex :
      0 <= r * m_pre + q < Zlength current_2).
  { rewrite PreH21. apply PreH19. exact PreH1. }
  Exists (replace_Znth (r * m_pre + q) c current_2) before_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia; try (intros; nia).
    + rewrite zlength_replace_Znth__solver_paint. exact PreH21.
    + apply canonical_grid_replace__solver_paint; try assumption; lia.
    + apply paint_prefix_replace__solver_paint; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_23_split_goal_1 : solver_entail_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace ((i + 1) * m_pre) with (i * m_pre + j) by lia.
  exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_23 : solver_entail_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_23_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_24_colour_found_split_goal_1 : solver_entail_wit_24_colour_found_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i * m_pre + (j + 1)) with ((i * m_pre + j) + 1) by lia.
  eapply GreedyTrace_place with
      (before := before) (i := i) (j := j)
      (color := c) (side := size).
  - exact PreH22.
  - reflexivity.
  - lia.
  - lia.
  - exact PreH21.
  - exact PreH23.
  - replace (size * size) with ((r - i) * size) by nia.
    exact PreH24.
Qed.

Lemma proof_of_solver_entail_wit_24_colour_found_split_goal_2 : solver_entail_wit_24_colour_found_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= i * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (i + 1) * m_pre).
    + replace ((i + 1) * m_pre) with (i * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_24_colour_found : solver_entail_wit_24_colour_found.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_24_colour_found_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_24_colour_found_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_25_split_goal_1 : solver_entail_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i * m_pre + (j + 1)) with ((i * m_pre + j) + 1) by lia.
  exact PreH11.
Qed.

Lemma proof_of_solver_entail_wit_25_split_goal_2 : solver_entail_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split.
  - assert (Hprod : 0 <= i * m_pre) by
      (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - apply Z.lt_le_trans with (m := (i + 1) * m_pre).
    + replace ((i + 1) * m_pre) with (i * m_pre + m_pre) by ring.
      lia.
    + apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma proof_of_solver_entail_wit_25 : solver_entail_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_25_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_25_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  assert (Hpartial : PartialTilingState n_pre m_pre (n_pre * m_pre) grid).
  { apply (greedy_trace_implies_partial_tiling__solver_final n_pre m_pre
      (n_pre * m_pre) grid PreH2 PreH4).
    replace (n_pre * m_pre) with (i * m_pre) by lia. exact PreH10. }
  destruct (complete_partial_tiling_implies_spec__solver_final n_pre m_pre grid
    PreH2 PreH4 PreH8 Hpartial) as [out [Hflat Hspec]].
  Exists out.
  split_pure_spatial.
  - unfold Flatten in Hflat. rewrite Hflat. cancel.
  - entailer!.
Qed.
