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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P056_65B_harry_potter_and_the_history_of_magic_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P056_65B_harry_potter_and_the_history_of_magic_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P056_65B_harry_potter_and_the_history_of_magic_lib.
Local Open Scope sac.

Lemma proof_of_next_year_safety_wit_22_split_goal_1 : next_year_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_22_split_goal_2 : next_year_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: unfold DigitLower in PreH14; simpl in PreH14.
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_22 : next_year_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_23_split_goal_1 : next_year_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_23_split_goal_2 : next_year_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: unfold DigitLower in PreH14; simpl in PreH14.
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_23 : next_year_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_24_split_goal_1 : next_year_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_24_split_goal_2 : next_year_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: unfold DigitLower in PreH14; simpl in PreH14.
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_24 : next_year_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_25_split_goal_1 : next_year_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_25_split_goal_2 : next_year_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: unfold DigitLower in PreH14; simpl in PreH14.
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_25 : next_year_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_25_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_26_split_goal_1 : next_year_safety_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_26_split_goal_2 : next_year_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: unfold DigitLower in PreH14; simpl in PreH14.
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_26 : next_year_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_27_split_goal_1 : next_year_safety_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_27_split_goal_2 : next_year_safety_wit_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen : Zlength digits = 4) by (rewrite PreH15; reflexivity).
  dump_pre_spatial.
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]].
  all: unfold DigitLower in PreH14; simpl in PreH14.
  all: repeat rewrite Znth_replace_Znth_Same by lia.
  all: repeat rewrite Znth_replace_Znth_Diff by lia.
  all: lia.
Qed.

Lemma proof_of_next_year_safety_wit_27 : next_year_safety_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_27_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_27_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_35_split_goal_1 : next_year_safety_wit_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_35_split_goal_2 : next_year_safety_wit_35_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_35 : next_year_safety_wit_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_35_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_35_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_36_split_goal_1 : next_year_safety_wit_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_36_split_goal_2 : next_year_safety_wit_36_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_36 : next_year_safety_wit_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_36_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_36_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_37_split_goal_1 : next_year_safety_wit_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_37_split_goal_2 : next_year_safety_wit_37_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_37 : next_year_safety_wit_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_37_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_37_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_38_split_goal_1 : next_year_safety_wit_38_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_38_split_goal_2 : next_year_safety_wit_38_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_38 : next_year_safety_wit_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_38_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_38_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_39_split_goal_1 : next_year_safety_wit_39_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_39_split_goal_2 : next_year_safety_wit_39_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_39 : next_year_safety_wit_39.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_39_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_39_split_goal_2.
Qed.

Lemma proof_of_next_year_safety_wit_40_split_goal_1 : next_year_safety_wit_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_40_split_goal_2 : next_year_safety_wit_40_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength digits = 4).
  { subst digits. rewrite Zlength_replace_Znth. reflexivity. }
  assert (Hv : 0 <= v).
  { unfold DigitLower in PreH9. destruct (Z.eq_dec pos 0); lia. }
  assert (Hpos : pos = 0 \/ pos = 1 \/ pos = 2 \/ pos = 3) by lia.
  destruct Hpos as [-> | [-> | [-> | ->]]];
    repeat rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia);
    repeat rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia);
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_next_year_safety_wit_40 : next_year_safety_wit_40.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_safety_wit_40_split_goal_1.
  - Goal_apply proof_of_next_year_safety_wit_40_split_goal_2.
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_1 : next_year_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  apply (proj1 (Z.lt_succ_r _ _)).
  change (y_pre mod 10 < 10).
  apply Z.mod_pos_bound; lia.
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_2 : next_year_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  apply (proj1 (Z.mod_pos_bound y_pre 10 ltac:(lia))).
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_3 : next_year_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  apply (proj1 (Z.lt_succ_r _ _)).
  change ((y_pre / 10) mod 10 < 10).
  apply Z.mod_pos_bound; lia.
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_4 : next_year_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  apply (proj1 (Z.mod_pos_bound (y_pre / 10) 10 ltac:(lia))).
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_5 : next_year_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  apply (proj1 (Z.lt_succ_r _ _)).
  change ((y_pre / 100) mod 10 < 10).
  apply Z.mod_pos_bound; lia.
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_6 : next_year_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  apply (proj1 (Z.mod_pos_bound (y_pre / 100) 10 ltac:(lia))).
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_7 : next_year_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  apply (proj1 (Z.lt_succ_r _ _)).
  change (y_pre / 1000 < 10).
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_8 : next_year_entail_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  apply Z.div_pos; lia.
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_9 : next_year_entail_wit_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold BestScanned.
  left; split; [reflexivity |].
  intros cand Hcursor.
  unfold CursorCandidate in Hcursor.
  destruct Hcursor as (p & v & Hp & Hv & Hbefore & Hcand).
  destruct Hbefore as [Hp0 | [Hpeq Hvlt]]; [lia |].
  subst p.
  unfold DigitLower in Hv, Hvlt; simpl in Hv, Hvlt.
  lia.
Qed.

Lemma proof_of_next_year_entail_wit_1_split_goal_10 : next_year_entail_wit_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hy100 : 0 <= y_pre / 100) by (apply Z.div_pos; lia).
  assert (Hy10 : 0 <= y_pre / 10) by (apply Z.div_pos; lia).
  unfold YearDigits.
  repeat rewrite Z.quot_div_nonneg by lia.
  rewrite (Z.rem_mod_nonneg y_pre 10) by lia.
  rewrite (Z.rem_mod_nonneg (y_pre / 10) 10) by lia.
  rewrite (Z.rem_mod_nonneg (y_pre / 100) 10) by lia.
  reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_1 : next_year_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_7.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_8.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_9.
  - Goal_apply proof_of_next_year_entail_wit_1_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_2_1 : next_year_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  Exists (YearDigits y_pre).
  subst pos.
  unfold DigitLower in *; simpl in *.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption; lia.
Qed.

Lemma proof_of_next_year_entail_wit_2_2 : next_year_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  Exists (YearDigits y_pre).
  unfold DigitLower in *.
  destruct (Z.eq_dec pos 0); [contradiction |].
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try reflexivity; try assumption; lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_1 : next_year_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_2 : next_year_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_3 : next_year_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_4 : next_year_entail_wit_3_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_5 : next_year_entail_wit_3_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_6 : next_year_entail_wit_3_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_7 : next_year_entail_wit_3_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_8 : next_year_entail_wit_3_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_9 : next_year_entail_wit_3_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) cand).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_accept_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  unfold LegalNext. split; [lia |]. split; [lia |].
  rewrite Hcand_value.
  apply at_most_one_digit_candidate__candidate_scan; try lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_1_split_goal_10 : next_year_entail_wit_3_1_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_1 : next_year_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_1_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_1 : next_year_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_2 : next_year_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_3 : next_year_entail_wit_3_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_4 : next_year_entail_wit_3_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_5 : next_year_entail_wit_3_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_6 : next_year_entail_wit_3_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_7 : next_year_entail_wit_3_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_8 : next_year_entail_wit_3_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_9 : next_year_entail_wit_3_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) cand).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_accept_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  unfold LegalNext. split; [lia |]. split; [lia |].
  rewrite Hcand_value.
  apply at_most_one_digit_candidate__candidate_scan; try lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_2_split_goal_10 : next_year_entail_wit_3_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_2 : next_year_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_2_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_1 : next_year_entail_wit_3_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_2 : next_year_entail_wit_3_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_3 : next_year_entail_wit_3_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_4 : next_year_entail_wit_3_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_5 : next_year_entail_wit_3_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_6 : next_year_entail_wit_3_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_7 : next_year_entail_wit_3_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_8 : next_year_entail_wit_3_3_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_9 : next_year_entail_wit_3_3_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) cand).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_accept_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  unfold LegalNext. split; [lia |]. split; [lia |].
  rewrite Hcand_value.
  apply at_most_one_digit_candidate__candidate_scan; try lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_3_split_goal_10 : next_year_entail_wit_3_3_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_3 : next_year_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_3_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_1 : next_year_entail_wit_3_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_2 : next_year_entail_wit_3_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_3 : next_year_entail_wit_3_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_4 : next_year_entail_wit_3_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_5 : next_year_entail_wit_3_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_6 : next_year_entail_wit_3_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_7 : next_year_entail_wit_3_4_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_8 : next_year_entail_wit_3_4_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_9 : next_year_entail_wit_3_4_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) cand).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_accept_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  unfold LegalNext. split; [lia |]. split; [lia |].
  rewrite Hcand_value.
  apply at_most_one_digit_candidate__candidate_scan; try lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_4_split_goal_10 : next_year_entail_wit_3_4_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_4 : next_year_entail_wit_3_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_4_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_1 : next_year_entail_wit_3_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_2 : next_year_entail_wit_3_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_3 : next_year_entail_wit_3_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_4 : next_year_entail_wit_3_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_5 : next_year_entail_wit_3_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_6 : next_year_entail_wit_3_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_7 : next_year_entail_wit_3_5_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_8 : next_year_entail_wit_3_5_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_9 : next_year_entail_wit_3_5_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) best).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_reject_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  left. unfold LegalNext. intros [[_ _] [Hprev _]]. unfold cand in *. lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_5_split_goal_10 : next_year_entail_wit_3_5_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_5 : next_year_entail_wit_3_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_5_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_1 : next_year_entail_wit_3_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_2 : next_year_entail_wit_3_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_3 : next_year_entail_wit_3_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_4 : next_year_entail_wit_3_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_5 : next_year_entail_wit_3_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_6 : next_year_entail_wit_3_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_7 : next_year_entail_wit_3_6_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_8 : next_year_entail_wit_3_6_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_9 : next_year_entail_wit_3_6_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) best).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_reject_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  left. unfold LegalNext. intros [[_ _] [Hprev _]]. unfold cand in *. lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_6_split_goal_10 : next_year_entail_wit_3_6_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_6 : next_year_entail_wit_3_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_6_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_1 : next_year_entail_wit_3_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_2 : next_year_entail_wit_3_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_3 : next_year_entail_wit_3_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_4 : next_year_entail_wit_3_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_5 : next_year_entail_wit_3_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_6 : next_year_entail_wit_3_7_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_7 : next_year_entail_wit_3_7_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_8 : next_year_entail_wit_3_7_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_9 : next_year_entail_wit_3_7_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) best).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_reject_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  left. unfold LegalNext. intros [[Hmin _] _]. unfold cand in *. lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_7_split_goal_10 : next_year_entail_wit_3_7_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_7 : next_year_entail_wit_3_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_7_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_1 : next_year_entail_wit_3_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_2 : next_year_entail_wit_3_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_3 : next_year_entail_wit_3_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_4 : next_year_entail_wit_3_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_5 : next_year_entail_wit_3_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_6 : next_year_entail_wit_3_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_7 : next_year_entail_wit_3_8_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_8 : next_year_entail_wit_3_8_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_9 : next_year_entail_wit_3_8_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) best).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_reject_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  left. unfold LegalNext. intros [[Hmin _] _]. unfold cand in *. lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_8_split_goal_10 : next_year_entail_wit_3_8_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_8 : next_year_entail_wit_3_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_8_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_1 : next_year_entail_wit_3_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_2 : next_year_entail_wit_3_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_3 : next_year_entail_wit_3_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_4 : next_year_entail_wit_3_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_5 : next_year_entail_wit_3_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_6 : next_year_entail_wit_3_9_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_7 : next_year_entail_wit_3_9_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_8 : next_year_entail_wit_3_9_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_9 : next_year_entail_wit_3_9_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) best).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_reject_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  left. unfold LegalNext. intros [[_ Hmax] _]. unfold cand in *. lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_9_split_goal_10 : next_year_entail_wit_3_9_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_9 : next_year_entail_wit_3_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_9_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_1 : next_year_entail_wit_3_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_2 : next_year_entail_wit_3_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_3 : next_year_entail_wit_3_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_4 : next_year_entail_wit_3_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_5 : next_year_entail_wit_3_10_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_6 : next_year_entail_wit_3_10_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_7 : next_year_entail_wit_3_10_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_8 : next_year_entail_wit_3_10_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_9 : next_year_entail_wit_3_10_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) best).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_reject_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
  left. unfold LegalNext. intros [[_ Hmax] _]. unfold cand in *. lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_10_split_goal_10 : next_year_entail_wit_3_10_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_10 : next_year_entail_wit_3_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_10_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_1 : next_year_entail_wit_3_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_2 : next_year_entail_wit_3_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_3 : next_year_entail_wit_3_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_4 : next_year_entail_wit_3_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_5 : next_year_entail_wit_3_11_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_6 : next_year_entail_wit_3_11_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_7 : next_year_entail_wit_3_11_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_8 : next_year_entail_wit_3_11_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_9 : next_year_entail_wit_3_11_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) best).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_reject_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_11_split_goal_10 : next_year_entail_wit_3_11_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_11 : next_year_entail_wit_3_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_11_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_1 : next_year_entail_wit_3_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_2 : next_year_entail_wit_3_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 3) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 3 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_3 : next_year_entail_wit_3_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_4 : next_year_entail_wit_3_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 2) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 2 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_5 : next_year_entail_wit_3_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_6 : next_year_entail_wit_3_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 1 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_7 : next_year_entail_wit_3_12_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_8 : next_year_entail_wit_3_12_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with
  | H : digits_2 = replace_Znth pos ?old (YearDigits y_pre) |- _ =>
      rewrite <- (replace_Znth_overwrite__candidate_scan pos v old (YearDigits y_pre));
      rewrite <- H
  | _ => idtac
  end.
  assert (Zlength digits_2 = 4) as Hlen.
  { match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite Zlength_replace_Znth. reflexivity. }
  destruct (Z.eq_dec pos 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    unfold DigitLower in *. destruct (Z.eq_dec 0 0); lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_9 : next_year_entail_wit_3_12_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  set (cand := Znth 0 (replace_Znth pos v digits_2) 0 * 1000 +
    Znth 1 (replace_Znth pos v digits_2) 0 * 100 +
    Znth 2 (replace_Znth pos v digits_2) 0 * 10 +
    Znth 3 (replace_Znth pos v digits_2) 0).
  change (BestScanned y_pre prev_pre pos (v + 1) best).
  assert (Hcand_value : cand = CandidateValue y_pre pos v).
  { unfold cand, CandidateValue, DigitsValue.
    match goal with H : digits_2 = _ |- _ => rewrite H end.
    repeat rewrite replace_Znth_overwrite__candidate_scan. ring. }
  eapply (best_scanned_reject_candidate__candidate_scan
            y_pre prev_pre pos v best cand); try eassumption; try lia.
Qed.

Lemma proof_of_next_year_entail_wit_3_12_split_goal_10 : next_year_entail_wit_3_12_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (v + 1 - 1) with v by lia.
  match goal with H : digits_2 = _ |- _ => rewrite H end.
  repeat rewrite replace_Znth_overwrite__candidate_scan. reflexivity.
Qed.

Lemma proof_of_next_year_entail_wit_3_12 : next_year_entail_wit_3_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_1.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_2.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_3.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_4.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_5.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_6.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_7.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_8.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_9.
  Goal_apply proof_of_next_year_entail_wit_3_12_split_goal_10.
Qed.

Lemma proof_of_next_year_entail_wit_4_1_split_goal_1 : next_year_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold DigitLower in PreH14.
  destruct (Z.eq_dec pos 0); lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_1_split_goal_2 : next_year_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold DigitLower in PreH14.
  destruct (Z.eq_dec pos 0); lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_1 : next_year_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_next_year_entail_wit_4_1_split_goal_2.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_1 : next_year_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  change (y_pre mod 10 <= 9).
  destruct (Z.mod_pos_bound y_pre 10 ltac:(lia)); lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_2 : next_year_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  change (0 <= y_pre mod 10).
  destruct (Z.mod_pos_bound y_pre 10 ltac:(lia)); lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_3 : next_year_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  change (y_pre / 10 mod 10 <= 9).
  destruct (Z.mod_pos_bound (y_pre / 10) 10 ltac:(lia)); lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_4 : next_year_entail_wit_4_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  change (0 <= y_pre / 10 mod 10).
  destruct (Z.mod_pos_bound (y_pre / 10) 10 ltac:(lia)); lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_5 : next_year_entail_wit_4_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  change (y_pre / 100 mod 10 <= 9).
  destruct (Z.mod_pos_bound (y_pre / 100) 10 ltac:(lia)); lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_6 : next_year_entail_wit_4_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  change (0 <= y_pre / 100 mod 10).
  destruct (Z.mod_pos_bound (y_pre / 100) 10 ltac:(lia)); lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_7 : next_year_entail_wit_4_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  change (y_pre / 1000 <= 9).
  pose proof (Z.div_lt_upper_bound y_pre 1000 10 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_8 : next_year_entail_wit_4_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold YearDigits; simpl.
  change (0 <= y_pre / 1000).
  pose proof (Z.div_pos y_pre 1000 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_9 : next_year_entail_wit_4_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (v = 10) by lia; subst v.
  unfold BestScanned in *.
  destruct PreH13 as [[Hbest Hnone] | [Hcursor [Hlegal Hmin]]].
  - left; split; [exact Hbest|].
    intros cand Hcand.
    apply Hnone.
    apply (proj2 (cursor_finished_position_equiv__cursor_completion y_pre pos cand ltac:(lia))).
    exact Hcand.
  - right; split.
    + apply (proj1 (cursor_finished_position_equiv__cursor_completion y_pre pos best ltac:(lia))).
      exact Hcursor.
    + split; [exact Hlegal|].
      intros cand Hcand Hcandlegal.
      apply Hmin; [|exact Hcandlegal].
      apply (proj2 (cursor_finished_position_equiv__cursor_completion y_pre pos cand ltac:(lia))).
      exact Hcand.
Qed.

Lemma proof_of_next_year_entail_wit_4_2_split_goal_10 : next_year_entail_wit_4_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst digits.
  subst old.
  apply replace_Znth_restore_original__cursor_completion.
Qed.

Lemma proof_of_next_year_entail_wit_4_2 : next_year_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_3.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_4.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_5.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_6.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_7.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_8.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_9.
  - Goal_apply proof_of_next_year_entail_wit_4_2_split_goal_10.
Qed.

Lemma proof_of_next_year_return_wit_1_split_goal_1 : next_year_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (pos = 4) by lia; subst pos.
  apply best_scanned_full_cursor_result__cursor_completion.
  exact PreH10.
Qed.

Lemma proof_of_next_year_return_wit_1 : next_year_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_next_year_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold GreedyPrefix.
  split.
  - simpl. apply Zlength_nonneg.
  - intros k Hk.
    rewrite Zlength_nil in Hk.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (IntArray.full_shape_to_seg_shape out_pre n_pre).
  cancel (IntArray.seg_shape out_pre 0 n_pre).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_spatial : solver_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (IntArray.missing_i_shape_unfold out_pre i i n_pre) by lia.
  Left.
  split_pure_spatial.
  - cancel (IntArray.seg_shape out_pre (i + 1) n_pre).
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst i prev.
  assert (Hreplace :
    replace_Znth (Zlength done_2) retval (done_2 ++ (old_out :: nil)) =
    done_2 ++ (retval :: nil)).
  {
    apply replace_Znth_at_snoc_slot__solver_prefix_extension.
  }
  rewrite Hreplace in PreH1 |-.
  assert (Hretval_nonneg : 0 <= retval).
  {
    rewrite (app_Znth2 0 done_2 (retval :: nil) (Zlength done_2)) in PreH1 by lia.
    replace (Zlength done_2 - Zlength done_2) with 0 in PreH1 by lia.
    change (retval >= 0) in PreH1.
    lia.
  }
  assert (Hminimal :
    MinimalNext (Znth (Zlength done_2) input_years 0)
      (PreviousYear done_2) retval).
  {
    unfold NextYearResult in PreH2.
    destruct PreH2 as [[Hminus _] | Hminimal]; [lia | exact Hminimal].
  }
  assert (Hgreedy : GreedyPrefix input_years (done_2 ++ (retval :: nil))).
  {
    apply greedy_prefix_snoc__solver_prefix_extension; auto.
    rewrite <- PreH5.
    lia.
  }
  assert (Hlen : Zlength (done_2 ++ (retval :: nil)) = Zlength done_2 + 1).
  {
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  }
  assert (Hprevious : PreviousYear (done_2 ++ (retval :: nil)) = retval).
  {
    apply previous_year_snoc__solver_prefix_extension.
  }
  assert (Hlast :
    Znth (Zlength done_2) (done_2 ++ (retval :: nil)) 0 = retval).
  {
    rewrite (app_Znth2 0 done_2 (retval :: nil) (Zlength done_2)) by lia.
    replace (Zlength done_2 - Zlength done_2) with 0 by lia.
    reflexivity.
  }
  rewrite Hreplace.
  Exists (done_2 ++ (retval :: nil)).
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.full_to_seg out_pre (Zlength done_2 + 1)
         (done_2 ++ (retval :: nil))).
    sep_apply_l_atomic
      (IntArray.missing_i_shape_to_seg_shape_head
         out_pre (Zlength done_2) n_pre).
    + dump_pre_spatial. lia.
    + cancel (IntArray.full years_pre n_pre input_years).
      cancel (IntArray.seg out_pre 0 (Zlength done_2 + 1)
        (done_2 ++ (retval :: nil))).
      cancel (IntArray.seg_shape out_pre (Zlength done_2 + 1) n_pre).
  - split_pures.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact PreH5.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. rewrite Hlast, Hprevious. reflexivity.
    + dump_pre_spatial. exact Hgreedy.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hvalid : ValidYears input_years done).
  { eapply greedy_prefix_full_valid_years__solver_results; eauto; lia. }
  assert (Hspec : Spec input_years (Some done)).
  { unfold Spec. right. exists done. auto. }
  Exists done.
  split_pure_spatial.
  - rewrite Hi.
    rewrite IntArray.seg_shape_empty.
    sep_apply_l_atomic (IntArray.seg_to_full out_pre 0 n_pre done).
    replace (out_pre + 0 * sizeof(INT)) with out_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full out_pre n_pre done).
    cancel (IntArray.full years_pre n_pre input_years).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hidx : 0 <= i < Zlength (done ++ old_out :: nil)).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  rewrite Znth_replace_Znth_Same in PreH1 by exact Hidx.
  unfold NextYearResult in PreH2.
  destruct PreH2 as [[Hretval Hnone] | Hminimal].
  - assert (Hblocked : ~ exists out, ValidYears input_years out).
    { eapply greedy_prefix_no_extension_blocks_valid_years__solver_results.
      - exact PreH11.
      - exact PreH9.
      - lia.
      - intros cand. rewrite <- PreH10. apply Hnone. }
    dump_pre_spatial.
    unfold Spec. left. auto.
  - unfold MinimalNext, LegalNext in Hminimal.
    lia.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_spatial : solver_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape out_pre (i + 1)
      (replace_Znth i retval (done ++ old_out :: nil))).
  sep_apply_l_atomic
    (IntArray.missing_i_shape_to_seg_shape_head out_pre i n_pre ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_shape_to_seg_shape out_pre (i + 1)).
  sep_apply_l_atomic
    (IntArray.seg_shape_merge_to_seg_shape out_pre 0 (i + 1) n_pre
      ltac:(lia)).
  sep_apply_l_atomic (IntArray.seg_shape_to_full_shape out_pre 0 n_pre).
  replace (out_pre + 0 * sizeof(INT)) with out_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  cancel (IntArray.full_shape out_pre n_pre).
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_1 : solver_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst prev.
  pose proof (greedy_prefix_previous_year_bounds__solver_setup input_years done PreH15).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure_split_goal_2 : solver_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst prev.
  pose proof (greedy_prefix_previous_year_bounds__solver_setup input_years done PreH15).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_2_pure_split_goal_2.
Qed.
