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
From SimpleC.EE.LLM_bench.Engineering.minisat Require Import vec_goal.
From SimpleC.EE.LLM_bench.Engineering.minisat Require Import vec_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import vec_lib.
Local Open Scope sac.

Lemma proof_of_veci_new_return_wit_1 : veci_new_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vec_alloc_ok in PreH2.
  destruct PreH2 as [Hstride [Hcap [Halloc_lo Halloc_hi]]].
  Exists retval.
  unfold veci_raw, veci_header, veci_buffer.
  rewrite Zlength_nil.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval 4).
  rewrite (IntArray.full_empty retval 0).
  split_pure_spatial.
  - cancel (IntArray.undef_seg retval 0 4).
    cancel (&(v_pre # "veci_t" ->ₛ "size") # Int |-> 0).
    cancel (&(v_pre # "veci_t" ->ₛ "cap") # Int |-> 4).
    cancel (&(v_pre # "veci_t" ->ₛ "ptr") # Ptr |-> retval).
  - split_pures.
    + dump_pre_spatial.
      repeat split; try assumption; try lia; try (compute; lia).
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_veci_new_which_implies_wit_1 : veci_new_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_shell.
  Intros_p Hneq.
  split_pure_spatial.
  - cancel (&(v # "veci_t" ->ₛ "size") # Int |->_).
    cancel (&(v # "veci_t" ->ₛ "cap") # Int |->_).
    cancel (&(v # "veci_t" ->ₛ "ptr") # Ptr |->_).
  - dump_pre_spatial. exact Hneq.
Qed.

Lemma proof_of_veci_delete_return_wit_1_split_goal_spatial : veci_delete_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_shell.
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_int_undef_store_int
        (&((v_pre) # "veci_t" ->ₛ "size")) (Zlength xs)).
    sep_apply_l_atomic
      (store_int_undef_store_int
        (&((v_pre) # "veci_t" ->ₛ "cap")) cap).
    sep_apply_l_atomic
      (store_ptr_undef_store_ptr
        (&((v_pre) # "veci_t" ->ₛ "ptr")) buf).
    cancel (&((v_pre) # "veci_t" ->ₛ "size") # Int |->_).
    cancel (&((v_pre) # "veci_t" ->ₛ "cap") # Int |->_).
    cancel (&((v_pre) # "veci_t" ->ₛ "ptr") # Ptr |->_).
  - dump_pre_spatial.
    exact PreH5.
Qed.

Lemma proof_of_veci_delete_return_wit_1 : veci_delete_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_veci_delete_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_veci_delete_which_implies_wit_1 : veci_delete_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_veci, veci_raw, veci_header, veci_buffer.
  Intros buf cap.
  Exists cap buf.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_veci_begin_return_wit_1 : veci_begin_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cap_2.
  unfold veci_raw, veci_header, veci_buffer.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    split; [exact PreH1 |].
    split; [exact PreH2 |].
    split; [exact PreH3 |].
    split; [exact PreH4 |].
    split; [exact PreH5 |].
    split.
    + int_auto.
    + exact PreH7.
Qed.

Lemma proof_of_veci_begin_which_implies_wit_1 : veci_begin_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_veci, veci_raw, veci_header, veci_buffer.
  Intros buf cap.
  Exists cap buf.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_veci_size_return_wit_1_split_goal_spatial : veci_size_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_veci.
  Exists buf cap.
  unfold veci_raw, veci_header, veci_buffer.
  split_pure_spatial.
  - cancel (&((v_pre) # "veci_t" ->ₛ "size") # Int |-> Zlength xs).
    cancel (&((v_pre) # "veci_t" ->ₛ "cap") # Int |-> cap).
    cancel (&((v_pre) # "veci_t" ->ₛ "ptr") # Ptr |-> buf).
    cancel (IntArray.full buf (Zlength xs) xs).
    cancel (IntArray.undef_seg buf (Zlength xs) cap).
  - dump_pre_spatial.
    split; [exact PreH5 |].
    split; [exact PreH6 |].
    split; [exact PreH7 |].
    split; [exact PreH8 |].
    split; [exact PreH9 |].
    split; [exact PreH10 | exact PreH11].
Qed.

Lemma proof_of_veci_size_return_wit_1 : veci_size_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_veci_size_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_veci_size_which_implies_wit_1 : veci_size_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_veci, veci_raw, veci_header, veci_buffer.
  Intros buf cap.
  Exists cap buf.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_veci_resize_return_wit_1_split_goal_spatial : veci_resize_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw, veci_header, veci_buffer.
  rewrite Zlength_sublist by lia.
  sep_apply_l_atomic
    (veci_buffer_truncate__resize_prefix
      buf xs cap k_pre ltac:(lia) ltac:(lia)).
  replace (k_pre - 0) with k_pre by lia.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    unfold vec_alloc_ok in PreH11.
    destruct PreH11 as [Hstride [Hcap [Hmul0 Hmulmax]]].
    repeat split; try lia; try assumption.
Qed.

Lemma proof_of_veci_resize_return_wit_1 : veci_resize_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_veci_resize_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1_split_goal_1 : veci_resize_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Halloc.
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1_split_goal_2 : veci_resize_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hcapmax.
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1_split_goal_3 : veci_resize_which_implies_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hcap4.
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1_split_goal_4 : veci_resize_which_implies_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hlencap.
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1_split_goal_5 : veci_resize_which_implies_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hlen0.
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1_split_goal_6 : veci_resize_which_implies_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hbuf.
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1_split_goal_7 : veci_resize_which_implies_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hv.
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1_split_goal_spatial : veci_resize_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold veci_raw.
  Intros_p Hraw.
  unfold veci_header, veci_buffer.
  cancel (&(v # "veci_t" ->ₛ "size") # Int |-> Zlength xs).
  cancel (&(v # "veci_t" ->ₛ "cap") # Int |-> cap).
  cancel (&(v # "veci_t" ->ₛ "ptr") # Ptr |-> buf).
  cancel (IntArray.full buf (Zlength xs) xs).
  cancel (IntArray.undef_seg buf (Zlength xs) cap).
Qed.

Lemma proof_of_veci_resize_which_implies_wit_1 : veci_resize_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_veci_resize_which_implies_wit_1_split_goal_spatial cap buf xs v).
  - Goal_apply (proof_of_veci_resize_which_implies_wit_1_split_goal_1 cap buf xs v).
  - Goal_apply (proof_of_veci_resize_which_implies_wit_1_split_goal_2 cap buf xs v).
  - Goal_apply (proof_of_veci_resize_which_implies_wit_1_split_goal_3 cap buf xs v).
  - Goal_apply (proof_of_veci_resize_which_implies_wit_1_split_goal_4 cap buf xs v).
  - Goal_apply (proof_of_veci_resize_which_implies_wit_1_split_goal_5 cap buf xs v).
  - Goal_apply (proof_of_veci_resize_which_implies_wit_1_split_goal_6 cap buf xs v).
  - Goal_apply (proof_of_veci_resize_which_implies_wit_1_split_goal_7 cap buf xs v).
Qed.

Lemma proof_of_veci_push_entail_wit_1_2_split_goal_1 : veci_push_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_veci_push_entail_wit_1_2_split_goal_2 : veci_push_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_veci_push_entail_wit_1_2 : veci_push_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_veci_push_entail_wit_1_2_split_goal_1.
  - Goal_apply proof_of_veci_push_entail_wit_1_2_split_goal_2.
Qed.

Lemma proof_of_veci_push_partial_solve_wit_2_pure_split_goal_1 : veci_push_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH18 PreH9).
  destruct PreH18 as [[Hgrowth Hcap_limit] Huint_limit].
  unfold vec_growth_ok in Hgrowth.
  destruct Hgrowth as
      [Hstride [Hcap_nonneg
        [Htwocap_signed [Hgcap_signed [Hgalloc Haddr]]]]].
  unfold vec_alloc_ok.
  dump_pre_spatial.
  repeat split; lia.
Qed.

Lemma proof_of_veci_push_partial_solve_wit_2_pure : veci_push_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply
    (reassociate_sepcon_7_entail__push_nongrowth
      (@proof_of_veci_push_partial_solve_wit_2_pure_split_goal_1
        e_pre v_pre cap buf xs
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
        PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1_split_goal_1 : veci_push_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_veci_resize_which_implies_wit_1_split_goal_1 as Hresize.
  unfold veci_resize_which_implies_wit_1_split_goal_1 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1_split_goal_2 : veci_push_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_veci_resize_which_implies_wit_1_split_goal_2 as Hresize.
  unfold veci_resize_which_implies_wit_1_split_goal_2 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1_split_goal_3 : veci_push_which_implies_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_veci_resize_which_implies_wit_1_split_goal_3 as Hresize.
  unfold veci_resize_which_implies_wit_1_split_goal_3 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1_split_goal_4 : veci_push_which_implies_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_veci_resize_which_implies_wit_1_split_goal_4 as Hresize.
  unfold veci_resize_which_implies_wit_1_split_goal_4 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1_split_goal_5 : veci_push_which_implies_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_veci_resize_which_implies_wit_1_split_goal_5 as Hresize.
  unfold veci_resize_which_implies_wit_1_split_goal_5 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1_split_goal_6 : veci_push_which_implies_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_veci_resize_which_implies_wit_1_split_goal_6 as Hresize.
  unfold veci_resize_which_implies_wit_1_split_goal_6 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1_split_goal_7 : veci_push_which_implies_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_veci_resize_which_implies_wit_1_split_goal_7 as Hresize.
  unfold veci_resize_which_implies_wit_1_split_goal_7 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1_split_goal_spatial : veci_push_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_veci_resize_which_implies_wit_1_split_goal_spatial as Hresize.
  unfold veci_resize_which_implies_wit_1_split_goal_spatial in Hresize.
  sep_apply (Hresize cap buf xs v).
  cancel (&(v # "veci_t" ->ₛ "size") # Int |-> Zlength xs).
  cancel (&(v # "veci_t" ->ₛ "cap") # Int |-> cap).
  cancel (&(v # "veci_t" ->ₛ "ptr") # Ptr |-> buf).
  cancel (IntArray.full buf (Zlength xs) xs).
  cancel (IntArray.undef_seg buf (Zlength xs) cap).
Qed.

Lemma proof_of_veci_push_which_implies_wit_1 : veci_push_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_veci_push_which_implies_wit_1_split_goal_spatial cap buf xs v).
  - Goal_apply (proof_of_veci_push_which_implies_wit_1_split_goal_1 cap buf xs v).
  - Goal_apply (proof_of_veci_push_which_implies_wit_1_split_goal_2 cap buf xs v).
  - Goal_apply (proof_of_veci_push_which_implies_wit_1_split_goal_3 cap buf xs v).
  - Goal_apply (proof_of_veci_push_which_implies_wit_1_split_goal_4 cap buf xs v).
  - Goal_apply (proof_of_veci_push_which_implies_wit_1_split_goal_5 cap buf xs v).
  - Goal_apply (proof_of_veci_push_which_implies_wit_1_split_goal_6 cap buf xs v).
  - Goal_apply (proof_of_veci_push_which_implies_wit_1_split_goal_7 cap buf xs v).
Qed.

Lemma proof_of_veci_push_which_implies_wit_2 : veci_push_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists curbuf_2 curcap_2.
  unfold veci_raw, veci_header, veci_buffer.
  assert (Hlen : Zlength (xs +:: e) = Zlength xs + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite Hlen.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial.
    all: repeat first [assumption | split].
    all: try (pose proof (Zlength_nonneg xs); lia).
    eapply vec_push_result_from_branches__push_final; eauto.
Qed.

Lemma proof_of_vecp_new_return_wit_1 : vecp_new_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vec_alloc_ok in PreH2.
  destruct PreH2 as [Hstride [Hcap [Halloc_lo Halloc_hi]]].
  Exists retval.
  unfold vecp_raw, vecp_header, vecp_buffer.
  rewrite Zlength_nil.
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval 4).
  rewrite (PtrArray.full_empty retval 0).
  split_pure_spatial.
  - cancel (PtrArray.undef_seg retval 0 4).
    cancel (&(v_pre # "vecp_t" ->ₛ "size") # Int |-> 0).
    cancel (&(v_pre # "vecp_t" ->ₛ "cap") # Int |-> 4).
    cancel (&(v_pre # "vecp_t" ->ₛ "ptr") # Ptr |-> retval).
  - split_pures.
    + dump_pre_spatial.
      repeat split; try assumption; try lia; try (compute; lia).
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_vecp_new_which_implies_wit_1 : vecp_new_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_shell.
  Intros_p Hneq.
  split_pure_spatial.
  - cancel (&(v # "vecp_t" ->ₛ "size") # Int |->_).
    cancel (&(v # "vecp_t" ->ₛ "cap") # Int |->_).
    cancel (&(v # "vecp_t" ->ₛ "ptr") # Ptr |->_).
  - dump_pre_spatial. exact Hneq.
Qed.

Lemma proof_of_vecp_delete_return_wit_1_split_goal_spatial : vecp_delete_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_shell.
  split_pure_spatial.
  - sep_apply_l_atomic
      (store_int_undef_store_int
        (&((v_pre) # "vecp_t" ->ₛ "size")) (Zlength xs)).
    sep_apply_l_atomic
      (store_int_undef_store_int
        (&((v_pre) # "vecp_t" ->ₛ "cap")) cap).
    sep_apply_l_atomic
      (store_ptr_undef_store_ptr
        (&((v_pre) # "vecp_t" ->ₛ "ptr")) buf).
    cancel (&((v_pre) # "vecp_t" ->ₛ "size") # Int |->_).
    cancel (&((v_pre) # "vecp_t" ->ₛ "cap") # Int |->_).
    cancel (&((v_pre) # "vecp_t" ->ₛ "ptr") # Ptr |->_).
  - dump_pre_spatial.
    exact PreH5.
Qed.

Lemma proof_of_vecp_delete_return_wit_1 : vecp_delete_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_vecp_delete_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_vecp_delete_which_implies_wit_1 : vecp_delete_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_vecp, vecp_raw, vecp_header, vecp_buffer.
  Intros buf cap.
  Exists cap buf.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_vecp_begin_return_wit_1 : vecp_begin_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists cap_2.
  unfold vecp_raw, vecp_header, vecp_buffer.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    split; [exact PreH1 |].
    split; [exact PreH2 |].
    split; [exact PreH3 |].
    split; [exact PreH4 |].
    split; [exact PreH5 |].
    split.
    + int_auto.
    + exact PreH7.
Qed.

Lemma proof_of_vecp_begin_which_implies_wit_1 : vecp_begin_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_vecp, vecp_raw, vecp_header, vecp_buffer.
  Intros buf cap.
  Exists cap buf.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_vecp_size_return_wit_1_split_goal_spatial : vecp_size_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_vecp.
  Exists buf cap.
  unfold vecp_raw, vecp_header, vecp_buffer.
  split_pure_spatial.
  - cancel (&((v_pre) # "vecp_t" ->ₛ "size") # Int |-> Zlength xs).
    cancel (&((v_pre) # "vecp_t" ->ₛ "cap") # Int |-> cap).
    cancel (&((v_pre) # "vecp_t" ->ₛ "ptr") # Ptr |-> buf).
    cancel (PtrArray.full buf (Zlength xs) xs).
    cancel (PtrArray.undef_seg buf (Zlength xs) cap).
  - dump_pre_spatial.
    split; [exact PreH5 |].
    split; [exact PreH6 |].
    split; [exact PreH7 |].
    split; [exact PreH8 |].
    split; [exact PreH9 |].
    split; [exact PreH10 | exact PreH11].
Qed.

Lemma proof_of_vecp_size_return_wit_1 : vecp_size_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_vecp_size_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_vecp_size_which_implies_wit_1 : vecp_size_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold store_vecp, vecp_raw, vecp_header, vecp_buffer.
  Intros buf cap.
  Exists cap buf.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_vecp_resize_return_wit_1_split_goal_spatial : vecp_resize_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw, vecp_header, vecp_buffer.
  rewrite Zlength_sublist by lia.
  sep_apply_l_atomic
    (vecp_buffer_truncate__resize_prefix
      buf xs cap k_pre ltac:(lia) ltac:(lia)).
  replace (k_pre - 0) with k_pre by lia.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    unfold vec_alloc_ok in PreH11.
    destruct PreH11 as [Hstride [Hcap [Hmul0 Hmulmax]]].
    repeat split; try lia; try assumption.
Qed.

Lemma proof_of_vecp_resize_return_wit_1 : vecp_resize_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_vecp_resize_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1_split_goal_1 : vecp_resize_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Halloc.
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1_split_goal_2 : vecp_resize_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hcapmax.
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1_split_goal_3 : vecp_resize_which_implies_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hcap4.
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1_split_goal_4 : vecp_resize_which_implies_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hlencap.
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1_split_goal_5 : vecp_resize_which_implies_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hlen0.
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1_split_goal_6 : vecp_resize_which_implies_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hbuf.
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1_split_goal_7 : vecp_resize_which_implies_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw.
  Intros_p Hraw.
  destruct Hraw as [Hv [Hbuf [Hlen0 [Hlencap [Hcap4 [Hcapmax Halloc]]]]]].
  dump_pre_spatial.
  exact Hv.
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1_split_goal_spatial : vecp_resize_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold vecp_raw.
  Intros_p Hraw.
  unfold vecp_header, vecp_buffer.
  cancel (&(v # "vecp_t" ->ₛ "size") # Int |-> Zlength xs).
  cancel (&(v # "vecp_t" ->ₛ "cap") # Int |-> cap).
  cancel (&(v # "vecp_t" ->ₛ "ptr") # Ptr |-> buf).
  cancel (PtrArray.full buf (Zlength xs) xs).
  cancel (PtrArray.undef_seg buf (Zlength xs) cap).
Qed.

Lemma proof_of_vecp_resize_which_implies_wit_1 : vecp_resize_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_vecp_resize_which_implies_wit_1_split_goal_spatial cap buf xs v).
  - Goal_apply (proof_of_vecp_resize_which_implies_wit_1_split_goal_1 cap buf xs v).
  - Goal_apply (proof_of_vecp_resize_which_implies_wit_1_split_goal_2 cap buf xs v).
  - Goal_apply (proof_of_vecp_resize_which_implies_wit_1_split_goal_3 cap buf xs v).
  - Goal_apply (proof_of_vecp_resize_which_implies_wit_1_split_goal_4 cap buf xs v).
  - Goal_apply (proof_of_vecp_resize_which_implies_wit_1_split_goal_5 cap buf xs v).
  - Goal_apply (proof_of_vecp_resize_which_implies_wit_1_split_goal_6 cap buf xs v).
  - Goal_apply (proof_of_vecp_resize_which_implies_wit_1_split_goal_7 cap buf xs v).
Qed.

Lemma proof_of_vecp_push_entail_wit_1_2_split_goal_1 : vecp_push_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_vecp_push_entail_wit_1_2_split_goal_2 : vecp_push_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_vecp_push_entail_wit_1_2 : vecp_push_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_vecp_push_entail_wit_1_2_split_goal_1.
  - Goal_apply proof_of_vecp_push_entail_wit_1_2_split_goal_2.
Qed.

Lemma proof_of_vecp_push_partial_solve_wit_2_pure_split_goal_1 : vecp_push_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH16 PreH7).
  destruct PreH16 as [[Hgrowth Hcap_limit] Huint_limit].
  unfold vec_growth_ok in Hgrowth.
  destruct Hgrowth as
      [Hstride [Hcap_nonneg
        [Htwocap_signed [Hgcap_signed [Hgalloc Haddr]]]]].
  unfold vec_alloc_ok.
  dump_pre_spatial.
  repeat split; lia.
Qed.

Lemma proof_of_vecp_push_partial_solve_wit_2_pure : vecp_push_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply
    (reassociate_sepcon_7_entail__push_nongrowth
      (@proof_of_vecp_push_partial_solve_wit_2_pure_split_goal_1
        e_pre v_pre cap buf xs
        PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
        PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16)).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1_split_goal_1 : vecp_push_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_vecp_resize_which_implies_wit_1_split_goal_1 as Hresize.
  unfold vecp_resize_which_implies_wit_1_split_goal_1 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1_split_goal_2 : vecp_push_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_vecp_resize_which_implies_wit_1_split_goal_2 as Hresize.
  unfold vecp_resize_which_implies_wit_1_split_goal_2 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1_split_goal_3 : vecp_push_which_implies_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_vecp_resize_which_implies_wit_1_split_goal_3 as Hresize.
  unfold vecp_resize_which_implies_wit_1_split_goal_3 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1_split_goal_4 : vecp_push_which_implies_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_vecp_resize_which_implies_wit_1_split_goal_4 as Hresize.
  unfold vecp_resize_which_implies_wit_1_split_goal_4 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1_split_goal_5 : vecp_push_which_implies_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_vecp_resize_which_implies_wit_1_split_goal_5 as Hresize.
  unfold vecp_resize_which_implies_wit_1_split_goal_5 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1_split_goal_6 : vecp_push_which_implies_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_vecp_resize_which_implies_wit_1_split_goal_6 as Hresize.
  unfold vecp_resize_which_implies_wit_1_split_goal_6 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1_split_goal_7 : vecp_push_which_implies_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_vecp_resize_which_implies_wit_1_split_goal_7 as Hresize.
  unfold vecp_resize_which_implies_wit_1_split_goal_7 in Hresize.
  exact (Hresize cap buf xs v).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1_split_goal_spatial : vecp_push_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof proof_of_vecp_resize_which_implies_wit_1_split_goal_spatial as Hresize.
  unfold vecp_resize_which_implies_wit_1_split_goal_spatial in Hresize.
  sep_apply (Hresize cap buf xs v).
  cancel (&(v # "vecp_t" ->ₛ "size") # Int |-> Zlength xs).
  cancel (&(v # "vecp_t" ->ₛ "cap") # Int |-> cap).
  cancel (&(v # "vecp_t" ->ₛ "ptr") # Ptr |-> buf).
  cancel (PtrArray.full buf (Zlength xs) xs).
  cancel (PtrArray.undef_seg buf (Zlength xs) cap).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_1 : vecp_push_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_vecp_push_which_implies_wit_1_split_goal_spatial cap buf xs v).
  - Goal_apply (proof_of_vecp_push_which_implies_wit_1_split_goal_1 cap buf xs v).
  - Goal_apply (proof_of_vecp_push_which_implies_wit_1_split_goal_2 cap buf xs v).
  - Goal_apply (proof_of_vecp_push_which_implies_wit_1_split_goal_3 cap buf xs v).
  - Goal_apply (proof_of_vecp_push_which_implies_wit_1_split_goal_4 cap buf xs v).
  - Goal_apply (proof_of_vecp_push_which_implies_wit_1_split_goal_5 cap buf xs v).
  - Goal_apply (proof_of_vecp_push_which_implies_wit_1_split_goal_6 cap buf xs v).
  - Goal_apply (proof_of_vecp_push_which_implies_wit_1_split_goal_7 cap buf xs v).
Qed.

Lemma proof_of_vecp_push_which_implies_wit_2 : vecp_push_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists curbuf_2 curcap_2.
  unfold vecp_raw, vecp_header, vecp_buffer.
  assert (Hlen : Zlength (xs +:: e) = Zlength xs + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite Hlen.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial.
    all: repeat first [assumption | split].
    all: try (pose proof (Zlength_nonneg xs); lia).
    eapply vec_push_result_from_branches__push_final; eauto.
Qed.
