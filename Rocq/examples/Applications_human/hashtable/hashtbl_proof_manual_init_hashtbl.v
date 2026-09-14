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

Lemma proof_of_init_hashtbl_return_wit_1_split_goal_spatial : init_hashtbl_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_hash_skeleton.
  Exists (@empty_map (list Z) addr) (@nil addr) (zeros 211)
    0 bucks_base b_init.
  split_pure_spatial.
  - unfold NBUCK.
    rewrite dll_null.
    rewrite (store_map_empty store_name).
    sep_apply_r_atomic store_sll_null.
    normalize.
    repeat cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold node_value_map, map_fun, empty_map.
      reflexivity.
    + dump_pre_spatial.
      exact empty_contain_all_addrs.
    + dump_pre_spatial.
      exact empty_repr_all_heads.
    + dump_pre_spatial.
      exact empty_contain_all_correct_addrs.
    + dump_pre_spatial.
      exact PreH1.
Qed.

Lemma proof_of_init_hashtbl_return_wit_1 : init_hashtbl_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_init_hashtbl_return_wit_1_split_goal_spatial.
Qed.

