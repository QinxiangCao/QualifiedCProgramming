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
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_goal.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib.
Local Open Scope sac.

Lemma proof_of_hashtbl_free_blist_return_wit_1_split_goal_spatial : hashtbl_free_blist_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst ks.
  simpl KP.remove_keys.
  cancel.
Qed.

Lemma proof_of_hashtbl_free_blist_return_wit_1 : hashtbl_free_blist_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_hashtbl_free_blist_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_hashtbl_free_blist_return_wit_2_split_goal_1 : hashtbl_free_blist_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_hashtbl_free_blist_return_wit_2_split_goal_spatial : hashtbl_free_blist_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_hashtbl_free_blist_return_wit_2 : hashtbl_free_blist_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst bl_pre.
  destruct l as [|x l1].
  - simpl sll.
    Intros_p Hnull.
    destruct ks as [|k1 ks1].
    + simpl KP.remove_keys.
      cancel.
    + simpl key_list_for_addrs in PreH2.
      contradiction.
  - simpl sll.
    Intros bl_next.
    contradiction.
Qed.

Lemma proof_of_hashtbl_free_blist_which_implies_wit_1 : hashtbl_free_blist_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct l as [|x l1].
  - simpl sll.
    Intros_p Hblnull.
    contradiction.
  - simpl sll.
    Intros bl_next.
    subst x.
    destruct ks as [|k1 ks1].
    + simpl key_list_for_addrs in PreH1.
      contradiction.
    + simpl key_list_for_addrs in PreH1.
      destruct PreH1 as [Hmap Hkeys].
      sep_apply_l_atomic (store_map_split store_name k1 bl m1 Hmap).
      assert (Houtside : forall key, key <> k1 ->
                m1 key = KP.remove_map m1 k1 key).
      { intros key Hkey.
        symmetry.
        apply KP.remove_map_diff.
        congruence. }
      destruct
        (store_map_missing_i_equiv
          store_name m1 (KP.remove_map m1 k1) k1 Houtside)
        as [Hto_removed _].
      sep_apply_l_atomic Hto_removed.
      sep_apply_l_atomic
        (store_map_missing_equiv_store_map
          store_name (KP.remove_map m1 k1) k1
          (KP.remove_map_same m1 k1)).
      unfold store_name.
      Intros bl_key.
      Exists bl_key bl_next k1 ks1 l1.
      split_pure_spatial.
      * normalize; repeat cancel.
      * split_pures.
        all: dump_pre_spatial.
        all: first [reflexivity | assumption].
Qed.

