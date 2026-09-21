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
From SimpleC.EE.LLM_bench.Algorithms.magic_items Require Import magic_items_goal.
From SimpleC.EE.LLM_bench.Algorithms.magic_items Require Import magic_items_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.magic_items.magic_items_lib.
Local Open Scope sac.

Lemma proof_of_magic_items_safety_wit_5_split_goal_1 : magic_items_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_5_split_goal_2 : magic_items_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_5 : magic_items_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_5_split_goal_1 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as H; sepcon_assoc_change_in H; exact H)).
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_5_split_goal_2 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as H; sepcon_assoc_change_in H; exact H)).
Qed. 

Lemma proof_of_magic_items_safety_wit_6_split_goal_1 : magic_items_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_6_split_goal_2 : magic_items_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_6 : magic_items_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_6_split_goal_1 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as H; sepcon_assoc_change_in H; exact H)).
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_6_split_goal_2 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as H; sepcon_assoc_change_in H; exact H)).
Qed. 

Lemma proof_of_magic_items_safety_wit_7_split_goal_1 : magic_items_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_7_split_goal_2 : magic_items_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_7 : magic_items_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_7_split_goal_1 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as H; sepcon_assoc_change_in H; exact H)).
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_7_split_goal_2 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as H; sepcon_assoc_change_in H; exact H)).
Qed. 

Lemma proof_of_magic_items_safety_wit_8_split_goal_1 : magic_items_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_8_split_goal_2 : magic_items_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_8 : magic_items_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_8_split_goal_1 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as H; sepcon_assoc_change_in H; exact H)).
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_8_split_goal_2 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) as H; sepcon_assoc_change_in H; exact H)).
Qed. 

Lemma proof_of_magic_items_safety_wit_10_split_goal_1 : magic_items_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_10_split_goal_2 : magic_items_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_10 : magic_items_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_10_split_goal_1 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) as H; sepcon_assoc_change_in H; exact H)).
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_10_split_goal_2 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) as H; sepcon_assoc_change_in H; exact H)).
Qed. 

Lemma proof_of_magic_items_safety_wit_11_split_goal_1 : magic_items_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_11_split_goal_2 : magic_items_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hlen.
  dump_pre_spatial.
  assert (Hbnds : 1 <= Znth i al 0 /\ Znth i al 0 <= Znth i bl 0 /\ Znth i bl 0 <= 10000).
  { apply item_bounds__prefix_safety; auto; lia. }
  lia.
Qed.

Lemma proof_of_magic_items_safety_wit_11 : magic_items_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_11_split_goal_1 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) as H; sepcon_assoc_change_in H; exact H)).
  - Goal_apply (ltac:(let H := fresh "Hsplit" in pose proof (proof_of_magic_items_safety_wit_11_split_goal_2 b_pre a_pre c_pre n_pre bl al ans s t i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) as H; sepcon_assoc_change_in H; exact H)).
Qed. 

Lemma proof_of_magic_items_safety_wit_21_split_goal_1 : magic_items_safety_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH15 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH16 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH17 ltac:(lia)) as Hb;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_21_split_goal_2 : magic_items_safety_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH15 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH16 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH17 ltac:(lia)) as Hb;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_21 : magic_items_safety_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_safety_wit_21_split_goal_1.
  - Goal_apply proof_of_magic_items_safety_wit_21_split_goal_2.
Qed. 

Lemma proof_of_magic_items_safety_wit_22_split_goal_1 : magic_items_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH15 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH16 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH17 ltac:(lia)) as Hb;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_22_split_goal_2 : magic_items_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH15 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH16 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH17 ltac:(lia)) as Hb;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_22 : magic_items_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_magic_items_safety_wit_22_split_goal_2.
Qed. 

Lemma proof_of_magic_items_safety_wit_25_split_goal_1 : magic_items_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH20 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH21 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH22 ltac:(lia)) as Hb;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_25_split_goal_2 : magic_items_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH20 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH21 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH22 ltac:(lia)) as Hb;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_25 : magic_items_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_magic_items_safety_wit_25_split_goal_2.
Qed. 

Lemma proof_of_magic_items_safety_wit_28_split_goal_1 : magic_items_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH21 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH22 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH23 ltac:(lia)) as Hb;
  pose proof (forall_Znth__dp_safety (Z.le 0) dl 0 PreH24 ltac:(lia)) as Hdlo;
  pose proof (forall_Znth__dp_safety (Z.ge 10000001) dl 0 PreH25 ltac:(lia)) as Hdhi;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_28_split_goal_2 : magic_items_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH21 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH22 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH23 ltac:(lia)) as Hb;
  pose proof (forall_Znth__dp_safety (Z.le 0) dl 0 PreH24 ltac:(lia)) as Hdlo;
  pose proof (forall_Znth__dp_safety (Z.ge 10000001) dl 0 PreH25 ltac:(lia)) as Hdhi;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_28 : magic_items_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_magic_items_safety_wit_28_split_goal_2.
Qed. 

Lemma proof_of_magic_items_safety_wit_29_split_goal_1 : magic_items_safety_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH21 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH22 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH23 ltac:(lia)) as Hb;
  pose proof (forall_Znth__dp_safety (Z.le 0) dl (j - Znth i al 0) PreH24 ltac:(lia)) as Hdlo;
  pose proof (forall_Znth__dp_safety (Z.ge 10000001) dl (j - Znth i al 0) PreH25 ltac:(lia)) as Hdhi;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_29_split_goal_2 : magic_items_safety_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 1) al i PreH21 ltac:(lia)) as Ha;
  pose proof (forall2_Znth__dp_safety al bl i PreH22 ltac:(lia)) as Hab;
  pose proof (forall_Znth__dp_safety (Z.ge 10000) bl i PreH23 ltac:(lia)) as Hb;
  pose proof (forall_Znth__dp_safety (Z.le 0) dl (j - Znth i al 0) PreH24 ltac:(lia)) as Hdlo;
  pose proof (forall_Znth__dp_safety (Z.ge 10000001) dl (j - Znth i al 0) PreH25 ltac:(lia)) as Hdhi;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_29 : magic_items_safety_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_safety_wit_29_split_goal_1.
  - Goal_apply proof_of_magic_items_safety_wit_29_split_goal_2.
Qed. 

Lemma proof_of_magic_items_safety_wit_36_split_goal_1 : magic_items_safety_wit_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 0) dl k PreH18 ltac:(lia)) as Hdlo;
  pose proof (forall_Znth__dp_safety (Z.ge 10000001) dl k PreH19 ltac:(lia)) as Hdhi;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_36_split_goal_2 : magic_items_safety_wit_36_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al);
  Intros_p Halen;
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl);
  Intros_p Hblen;
  prop_apply_p (IntArray.full_Zlength ( &("dp") ) (k + 1) dl);
  Intros_p Hdlen;
  dump_pre_spatial;
  pose proof (forall_Znth__dp_safety (Z.le 0) dl k PreH18 ltac:(lia)) as Hdlo;
  pose proof (forall_Znth__dp_safety (Z.ge 10000001) dl k PreH19 ltac:(lia)) as Hdhi;
  try change INT_MAX with 2147483647;
  try change INT_MIN with (-2147483648); lia
  ).
Qed.

Lemma proof_of_magic_items_safety_wit_36 : magic_items_safety_wit_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_safety_wit_36_split_goal_1.
  - Goal_apply proof_of_magic_items_safety_wit_36_split_goal_2.
Qed. 

Lemma proof_of_magic_items_entail_wit_1_split_goal_1 : magic_items_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_magic_items_entail_wit_1_split_goal_2 : magic_items_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_magic_items_entail_wit_1_split_goal_3 : magic_items_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_magic_items_entail_wit_1 : magic_items_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_magic_items_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_magic_items_entail_wit_1_split_goal_3.
Qed. 

Lemma proof_of_magic_items_entail_wit_2_1_split_goal_1 : magic_items_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_1_split_goal_2 : magic_items_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_1_split_goal_3 : magic_items_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_1_split_goal_4 : magic_items_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_1_split_goal_5 : magic_items_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_prefix_step__prefix_totals c_pre al bl i ltac:(lia) ltac:(lia) ltac:(assumption)) as [Ht [Hr Hs]].
  rewrite Z.max_r in Hr by lia.
  assert (Z.leb (Znth i bl 0 - Znth i al 0 - c_pre) 0 = false) as Hd by (apply Z.leb_gt; lia).
  rewrite Hd in Hs.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_1_split_goal_6 : magic_items_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_prefix_step__prefix_totals c_pre al bl i ltac:(lia) ltac:(lia) ltac:(assumption)) as [Ht [Hr Hs]].
  rewrite Z.max_r in Hr by lia.
  assert (Z.leb (Znth i bl 0 - Znth i al 0 - c_pre) 0 = false) as Hd by (apply Z.leb_gt; lia).
  rewrite Hd in Hs.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_1_split_goal_7 : magic_items_entail_wit_2_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_prefix_step__prefix_totals c_pre al bl i ltac:(lia) ltac:(lia) ltac:(assumption)) as [Ht [Hr Hs]].
  rewrite Z.max_r in Hr by lia.
  assert (Z.leb (Znth i bl 0 - Znth i al 0 - c_pre) 0 = false) as Hd by (apply Z.leb_gt; lia).
  rewrite Hd in Hs.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_1 : magic_items_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_magic_items_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_magic_items_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_magic_items_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_magic_items_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_magic_items_entail_wit_2_1_split_goal_6.
  - Goal_apply proof_of_magic_items_entail_wit_2_1_split_goal_7.
Qed. 

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_1 : magic_items_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_2 : magic_items_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_3 : magic_items_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_4 : magic_items_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_5 : magic_items_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_6 : magic_items_entail_wit_2_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_default_bounds__prefix_totals al bl i ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hb.
  lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_7 : magic_items_entail_wit_2_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_prefix_step__prefix_totals c_pre al bl i ltac:(lia) ltac:(lia) ltac:(assumption)) as [Ht [Hr Hs]].
  rewrite Z.max_l in Hr by lia.
  assert (Z.leb (Znth i bl 0 - Znth i al 0 - c_pre) 0 = true) as Hd by (apply Z.leb_le; lia).
  rewrite Hd in Hs. lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_8 : magic_items_entail_wit_2_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_prefix_step__prefix_totals c_pre al bl i ltac:(lia) ltac:(lia) ltac:(assumption)) as [Ht [Hr Hs]].
  rewrite Z.max_l in Hr by lia.
  assert (Z.leb (Znth i bl 0 - Znth i al 0 - c_pre) 0 = true) as Hd by (apply Z.leb_le; lia).
  rewrite Hd in Hs. lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2_split_goal_9 : magic_items_entail_wit_2_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (magic_prefix_step__prefix_totals c_pre al bl i ltac:(lia) ltac:(lia) ltac:(assumption)) as [Ht [Hr Hs]].
  rewrite Z.max_l in Hr by lia.
  assert (Z.leb (Znth i bl 0 - Znth i al 0 - c_pre) 0 = true) as Hd by (apply Z.leb_le; lia).
  rewrite Hd in Hs. lia.
Qed.

Lemma proof_of_magic_items_entail_wit_2_2 : magic_items_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_5.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_6.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_7.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_8.
  - Goal_apply proof_of_magic_items_entail_wit_2_2_split_goal_9.
Qed. 

Lemma proof_of_magic_items_entail_wit_3 : magic_items_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.full_Zlength a_pre n_pre al).
  Intros_p Hal.
  prop_apply_p (IntArray.full_Zlength b_pre n_pre bl).
  Intros_p Hbl.
  assert (Hi : i = n_pre) by lia. subst i.
  rewrite (sublist_self al n_pre) in * by lia.
  rewrite (sublist_self bl n_pre) in * by lia.
  Exists (0 :: nil).
  split_pure_spatial.
  - sep_apply_l_atomic (store_int_undef_store_int (&("s")) s).
    sep_apply_l_atomic (store_int_undef_store_int (&("t")) t).
    sep_apply_l_atomic (IntArray.seg_single (&("dp")) 0 0).
    replace (0+1) with 1 by lia. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia; try reflexivity.
    change (Forall (eq 10000001) nil). constructor.
Qed. 

Lemma proof_of_magic_items_entail_wit_4_split_goal_1 : magic_items_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_magic_items_entail_wit_4_split_goal_2 : magic_items_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_magic_items_entail_wit_4 : magic_items_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.seg_Zlength (&("dp")) 0 (j+1) (dl_2 ++ (10000001 :: nil))).
  Intros_p Hlen.
  assert (Hdl : Zlength dl_2 = j).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen. lia. }
  destruct (magic_init_tail__dp_initialization dl_2 j Hdl PreH8 PreH18 PreH19) as [tail [Heq Htail]].
  Exists (dl_2 ++ (10000001 :: nil)).
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite app_Znth1 by lia. assumption.
    + subst dl_2. simpl app.
      rewrite sublist_cons2 by (rewrite ?Zlength_cons, ?Zlength_app, ?Zlength_cons, ?Zlength_nil in *; lia).
      replace (1-1) with 0 by lia.
      rewrite sublist_self.
      * apply Forall_app. split; [assumption|repeat constructor].
      * rewrite Zlength_app, Zlength_cons, Zlength_nil.
        rewrite Zlength_cons in Hdl. lia.
Qed. 

Lemma proof_of_magic_items_entail_wit_5 : magic_items_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (IntArray.seg_Zlength (&("dp")) 0 j dl_2).
  Intros_p Hlen.
  assert (Hj : j = k+1) by lia.
  assert (Hdl : Zlength dl_2 = j) by lia.
  destruct (magic_init_tail__dp_initialization dl_2 j Hdl PreH8 PreH18 PreH19) as [tail [Heq Htail]].
  Exists dl_2.
  split_pure_spatial.
  - rewrite Hj. unfold IntArray.full, IntArray.seg, store_array. repeat progress cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + rewrite Heq. constructor; [lia|].
      eapply Forall_impl; [|exact Htail]. intros x Hx. subst x. lia.
    + rewrite Heq. constructor; [lia|].
      eapply Forall_impl; [|exact Htail]. intros x Hx. subst x. lia.
    + intros q Hq.
      destruct (Z.eq_dec q 0) as [Hz|Hz].
      * subst q. rewrite PreH18.
        pose proof (magic_empty_minimum__dp_initialization c_pre al bl 0 ltac:(lia)) as Hmin.
        simpl in Hmin. exact Hmin.
      * assert (Hval : Znth q dl_2 0 = 10000001).
        { pose proof (magic_Forall_nth__dp_initialization (eq 10000001) (sublist 1 j dl_2) (q-1) PreH19) as Hnth.
          rewrite Zlength_sublist in Hnth by lia.
          specialize (Hnth ltac:(lia)). rewrite Znth_sublist in Hnth by lia.
          replace (q-1+1) with q in Hnth by lia. symmetry. exact Hnth. }
        rewrite Hval.
        pose proof (magic_empty_minimum__dp_initialization c_pre al bl q ltac:(lia)) as Hmin.
        destruct (Z.eq_dec q 0); [contradiction|exact Hmin].
Qed. 

Lemma proof_of_magic_items_entail_wit_6_split_goal_1 : magic_items_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_magic_items_entail_wit_6_split_goal_2 : magic_items_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_magic_items_entail_wit_6_split_goal_3 : magic_items_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hlen : length al = length bl) by (eapply Forall2_length; eauto).
  destruct (lt_dec (Z.to_nat i) (length al)) as [Hi | Hi].
  - apply Forall_forall with (x := Znth i al 0) in PreH16; auto.
    unfold Znth. apply nth_In. exact Hi.
  - unfold Znth in PreH1. rewrite !nth_overflow in PreH1; lia.
Qed.

Lemma proof_of_magic_items_entail_wit_6 : magic_items_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_magic_items_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_magic_items_entail_wit_6_split_goal_3.
Qed. 

Lemma proof_of_magic_items_entail_wit_7_1_split_goal_1 : magic_items_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (magic_forall_read__dp_projections (Z.ge 10000001) dl_2 0 j PreH26 ltac:(lia)).
  apply magic_forall_write__dp_projections; auto; lia.
Qed.

Lemma proof_of_magic_items_entail_wit_7_1_split_goal_2 : magic_items_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (magic_forall_read__dp_projections (Z.le 0) dl_2 0 0 PreH25 ltac:(lia)).
  apply magic_forall_write__dp_projections; auto; lia.
Qed.

Lemma proof_of_magic_items_entail_wit_7_1 : magic_items_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_magic_items_entail_wit_7_1_split_goal_2.
Qed. 

Lemma proof_of_magic_items_entail_wit_7_2_split_goal_1 : magic_items_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (magic_forall_read__dp_projections (Z.ge 10000001) dl_2 0 j PreH26 ltac:(lia)).
  apply magic_forall_write__dp_projections; auto; lia.
Qed.

Lemma proof_of_magic_items_entail_wit_7_2_split_goal_2 : magic_items_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  pose proof (magic_forall_read__dp_projections (Z.le 0) dl_2 0 (j - Znth i al 0) PreH25 ltac:(lia)).
  apply magic_forall_write__dp_projections; auto; lia.
Qed.

Lemma proof_of_magic_items_entail_wit_7_2 : magic_items_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_magic_items_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_magic_items_entail_wit_7_2_split_goal_2.
Qed. 

Lemma proof_of_magic_items_entail_wit_8_1_split_goal_1 : magic_items_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  assert (Hj : j = 0) by lia. subst j.
  destruct (Z.eq_dec q 0) as [-> | Hq].
  - apply (proj2 (magic_zero_minimum__dp_projections c_pre al bl (i+1) (Znth 0 dl_2 0) ltac:(lia))).
    apply (proj1 (magic_zero_minimum__dp_projections c_pre al bl i (Znth 0 dl_2 0) ltac:(lia))).
    apply PreH25. lia.
  - apply PreH26. lia.
Qed.

Lemma proof_of_magic_items_entail_wit_8_1 : magic_items_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_magic_items_entail_wit_8_1_split_goal_1.
Qed. 

Lemma proof_of_magic_items_entail_wit_9_split_goal_1 : magic_items_entail_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_magic_items_entail_wit_9_split_goal_spatial : magic_items_entail_wit_9_split_goal_spatial.
Proof. Abort.

Lemma proof_of_magic_items_entail_wit_9 : magic_items_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength a_pre n_pre al). Intros_p Hla.
  prop_apply (IntArray.full_Zlength b_pre n_pre bl). Intros_p Hlb.
  assert (Hi : i = Zlength al) by lia.
  assert (Hmin : MinimumSacrifice c_pre al bl (Zlength al)
    (c_pre-FreeCash c_pre al bl) (Znth k dl 0)).
  { rewrite <- Hi, <- PreH10. apply PreH20. lia. }
  assert (Hopt : MaximumMagicRevenue c_pre al bl (ans-Znth k dl 0)).
  { rewrite PreH12. apply magic_capital_optimum__maximum_revenue; auto; lia. }
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_undef_full (&("dp")) (k+1) dl).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("dp")) (k+1)).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("dp")) 0 (k+1) 5001 ltac:(lia)).
    sep_apply_l_atomic (store_int_undef_store_int (&("ans")) ans).
    sep_apply_l_atomic (store_int_undef_store_int (&("k")) k).
    replace (5001-0) with 5001 by lia.
    rewrite Z.mul_0_l, Z.add_0_r.
    cancel.
  - dump_pre_spatial. exact Hopt.
Qed. 

Lemma proof_of_magic_items_return_wit_2_split_goal_1 : magic_items_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_magic_items_return_wit_2 : magic_items_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength a_pre n_pre al). Intros_p Hla.
  prop_apply (IntArray.full_Zlength b_pre n_pre bl). Intros_p Hlb.
  assert (Hi : i = Zlength al) by lia.
  assert (Hib : i = Zlength bl) by lia.
  assert (Hsa : sublist 0 i al = al) by (apply sublist_self; exact Hi).
  assert (Hsb : sublist 0 i bl = bl) by (apply sublist_self; exact Hib).
  rewrite Hsa, Hsb in PreH14, PreH15.
  subst s ans.
  assert (Hopt : MaximumMagicRevenue c_pre al bl (UnconstrainedRevenue c_pre al bl)).
  { apply magic_free_optimum__maximum_revenue; auto; lia. }
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact Hopt.
Qed. 

Lemma proof_of_magic_items_return_wit_3_split_goal_1 : magic_items_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_magic_items_return_wit_3 : magic_items_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength a_pre n_pre al). Intros_p Hla.
  prop_apply (IntArray.full_Zlength b_pre n_pre bl). Intros_p Hlb.
  assert (Hi : i = Zlength al) by lia.
  rewrite Hi, sublist_self in PreH12 by reflexivity.
  subst t.
  assert (Hopt : MaximumMagicRevenue c_pre al bl (ListLib.sum al)).
  { apply magic_no_capital_optimum__maximum_revenue.
    - eapply Forall_impl; [|exact PreH9]. intros z Hz. lia.
    - rewrite Zlength_correct in Hla, Hlb. lia.
    - exact PreH1. }
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact Hopt.
Qed. 

