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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_add_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_add_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_mpz_add_safety_wit_3 : mpz_add_safety_wit_3.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_add_safety_wit_5 : mpz_add_safety_wit_5.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_add_entail_wit_1 : mpz_add_entail_wit_1.
Proof.
  pre_process.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Intros ptr old_size cap bptr bsize bcap.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  replace (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) with (Zabs za_r_eq_a + Zabs zb_r_eq_a) by lia.
  Exists bptr ptr old_size bcap bsize cap.
  entailer!.
  unfold same_sign in *.
  pose proof (proj1 (Z.lxor_nonneg size size_2) ltac:(lia)).
  assert (0 <= Z.lxor old_size bsize) by (rewrite Z.lxor_nonneg; lia).
  lia.
Qed.

Lemma proof_of_mpz_add_entail_wit_2 : mpz_add_entail_wit_2.
Proof.
  pre_process.
  subst r_pre.
  unfold store_Z_with_old_size, store_Z.
  Intros ptr old_size cap bptr bsize bcap.
  prop_apply (store_int_range (&(a_pre # "__mpz_struct" ->ₛ "_mp_alloc")) cap).
  Intros.
  change Int.min_signed with (-2147483648) in *.
  change Int.max_signed with 2147483647 in *.
  Exists bptr ptr old_size bcap bsize cap.
  entailer!.
  unfold same_sign in *.
  assert (~ 0 <= Z.lxor old_size bsize).
  { rewrite Z.lxor_nonneg.
    destruct (lxor_negative_implies_opposite_signs_simple size size_2 ltac:(lia)); lia. }
  lia.
Qed.

Lemma proof_of_mpz_add_return_wit_1 : mpz_add_return_wit_1.
Proof.
  pre_process.
  subst r_pre.
  assert (za_r_eq_a >= 0 /\ zb_r_eq_a >= 0) as Hnm.
  { unfold same_sign in *.
    pose proof (proj1 (Z.lxor_nonneg old_size bsize) ltac:(lia)).
    lia. }
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with (Zabs (za_r_eq_a + zb_r_eq_a)) in * by lia.
  unfold store_Z at 1.
  Exists ptr; Exists rn_v; Exists cap.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  entailer!.
  unfold same_sign in *; lia.
Qed.

Lemma proof_of_mpz_add_return_wit_2 : mpz_add_return_wit_2.
Proof.
  pre_process.
  subst r_pre.
  assert (za_r_eq_a < 0 /\ zb_r_eq_a < 0) as Hnm.
  { unfold same_sign in *.
    destruct (lxor_nonneg_implies_same_sign old_size bsize ltac:(lia)); lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs za_r_eq_a + Zabs zb_r_eq_a) (Zabs rn_v)).
  Intros.
  assert (same_sign (za_r_eq_a + zb_r_eq_a) (- rn_v)) as Hsg.
  { replace (za_r_eq_a + zb_r_eq_a) with (-(Zabs za_r_eq_a + Zabs zb_r_eq_a)) by lia.
    replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with (Zabs (Zabs za_r_eq_a + Zabs zb_r_eq_a)) in H by lia.
    eapply same_sign_opp_compact_abs; eauto. }
  replace (Zabs za_r_eq_a + Zabs zb_r_eq_a) with (Zabs (za_r_eq_a + zb_r_eq_a)) in * by lia.
  unfold store_Z at 1.
  Exists ptr; Exists (- rn_v); Exists cap.
  replace (Zabs (- rn_v)) with (Zabs rn_v) by lia.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  entailer!.
Qed.

Lemma proof_of_mpz_add_return_wit_3 : mpz_add_return_wit_3.
Proof.
  pre_process.
  subst r_pre.
  assert (za_r_eq_a >= 0 /\ zb_r_eq_a < 0) as Hnm.
  { unfold same_sign in *.
    destruct (lxor_negative_implies_opposite_signs_simple old_size bsize ltac:(lia)); lia. }
  replace (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) with (Zabs (za_r_eq_a + zb_r_eq_a)) in * by lia.
  replace (Zabs za_r_eq_a - Zabs zb_r_eq_a) with (za_r_eq_a + zb_r_eq_a) in * by lia.
  unfold store_Z at 1.
  Exists ptr; Exists rn_v; Exists cap.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  entailer!.
Qed.

Lemma proof_of_mpz_add_return_wit_4 : mpz_add_return_wit_4.
Proof.
  pre_process.
  subst r_pre.
  assert (za_r_eq_a < 0 /\ zb_r_eq_a >= 0) as Hnm.
  { unfold same_sign in *.
    destruct (lxor_negative_implies_opposite_signs_simple old_size bsize ltac:(lia)); lia. }
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) (Zabs rn_v)).
  Intros.
  assert (same_sign (za_r_eq_a + zb_r_eq_a) (- rn_v)) as Hsg.
  { replace (za_r_eq_a + zb_r_eq_a) with (-(Zabs za_r_eq_a - Zabs zb_r_eq_a)) by lia.
    apply same_sign_opp_compact_abs; assumption. }
  replace (Zabs (Zabs za_r_eq_a - Zabs zb_r_eq_a)) with (Zabs (za_r_eq_a + zb_r_eq_a)) in * by lia.
  unfold store_Z at 1.
  Exists ptr; Exists (- rn_v); Exists cap.
  replace (Zabs (- rn_v)) with (Zabs rn_v) by lia.
  unfold store_Z at 1.
  Exists bptr; Exists bsize; Exists bcap.
  entailer!.
Qed.
