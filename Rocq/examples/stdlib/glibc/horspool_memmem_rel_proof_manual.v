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
From SimpleC.EE.stdlib.glibc Require Import horspool_memmem_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.horspool_memmem_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Require SimpleC.EE.stdlib.glibc.horspool_memmem_rel_legacy_proof.

Lemma proof_of_hp_hash2_entail_wit_1 : hp_hash2_entail_wit_1.
Proof.
unfold hp_hash2_entail_wit_1; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_hp_hash2_entail_wit_1 pointer_pre index bytes length base) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.hp_hash2_entail_wit_1 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros ;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_hp_hash2_return_wit_1 : hp_hash2_return_wit_1.
Proof.
unfold hp_hash2_return_wit_1; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_hp_hash2_return_wit_1 pointer_pre index bytes length base) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.hp_hash2_return_wit_1 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros ;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_2 : horspool_memmem_refinement_entail_wit_2.
Proof.
unfold horspool_memmem_refinement_entail_wit_2; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_2 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec ne m1 search_end hs offset tmp shift1) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_2 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0;
      Exists migration_witness0;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_3 : horspool_memmem_refinement_entail_wit_3.
Proof.
unfold horspool_memmem_refinement_entail_wit_3; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_3 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec shift1 tmp table_2 i offset hs search_end m1 ne retval) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_3 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0;
      Exists migration_witness0;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_4 : horspool_memmem_refinement_entail_wit_4.
Proof.
unfold horspool_memmem_refinement_entail_wit_4; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_4 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec shift1 tmp table i offset hs search_end m1 ne retval retval_2) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_4 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_5 : horspool_memmem_refinement_entail_wit_5.
Proof.
unfold horspool_memmem_refinement_entail_wit_5; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_5 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec tmp hs offset table_2 shift1 search_end m1 ne position_2) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_5 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_6 : horspool_memmem_refinement_entail_wit_6.
Proof.
unfold horspool_memmem_refinement_entail_wit_6; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_6 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec tmp hs offset table_2 shift1 search_end ne m1 position_2) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_6 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_7 : horspool_memmem_refinement_entail_wit_7.
Proof.
unfold horspool_memmem_refinement_entail_wit_7; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_7 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table position_2 m1 ne search_end shift1 offset hs tmp retval) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_7 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_8_1 : horspool_memmem_refinement_entail_wit_8_1.
Proof.
unfold horspool_memmem_refinement_entail_wit_8_1; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_8_2 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec tmp hs offset table_2 shift1 search_end ne m1 position_2) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_8_2 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_8_2 : horspool_memmem_refinement_entail_wit_8_2.
Proof.
unfold horspool_memmem_refinement_entail_wit_8_2; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_8_1 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec tmp hs offset table_2 shift1 search_end ne m1 position_2) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_8_1 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_1 : horspool_memmem_refinement_entail_wit_9_1.
Proof.
unfold horspool_memmem_refinement_entail_wit_9_1; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_9_1 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table_2 position_2 ne m1 search_end shift1 offset hs tmp retval) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_9_1 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_2 : horspool_memmem_refinement_entail_wit_9_2.
Proof.
unfold horspool_memmem_refinement_entail_wit_9_2; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_9_2 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table_2 position_2 ne m1 search_end shift1 offset hs tmp retval) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_9_2 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_3 : horspool_memmem_refinement_entail_wit_9_3.
Proof.
unfold horspool_memmem_refinement_entail_wit_9_3; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_9_3 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table_2 position_2 ne m1 search_end shift1 offset hs tmp retval retval_2) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_9_3 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_4 : horspool_memmem_refinement_entail_wit_9_4.
Proof.
unfold horspool_memmem_refinement_entail_wit_9_4; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_9_4 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table_2 position_2 ne m1 search_end shift1 offset hs tmp retval retval_2) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_9_4 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_9_5 : horspool_memmem_refinement_entail_wit_9_5.
Proof.
unfold horspool_memmem_refinement_entail_wit_9_5; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_entail_wit_9_5 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table_2 position_2 ne m1 search_end shift1 offset hs tmp retval) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_entail_wit_9_5 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros migration_witness0 migration_witness1;
      Exists migration_witness0 migration_witness1;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_10_1 : horspool_memmem_refinement_entail_wit_10_1.
Proof.
unfold horspool_memmem_refinement_entail_wit_10_1; left; intros.
  Exists table_2 (position_2 + shift1).
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring].
Qed.

Lemma proof_of_horspool_memmem_refinement_entail_wit_10_2 : horspool_memmem_refinement_entail_wit_10_2.
Proof.
unfold horspool_memmem_refinement_entail_wit_10_2; left; intros.
  Exists table_2 position_2.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring].
Qed.

Lemma proof_of_horspool_memmem_refinement_return_wit_1 : horspool_memmem_refinement_return_wit_1.
Proof.
unfold horspool_memmem_refinement_return_wit_1; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_return_wit_1 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec tmp hs offset table shift1 search_end m1 ne position) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_return_wit_1 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros ;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_return_wit_2 : horspool_memmem_refinement_return_wit_2.
Proof.
unfold horspool_memmem_refinement_return_wit_2; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_return_wit_3 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table position ne m1 search_end shift1 offset hs tmp retval) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_return_wit_3 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros ;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_return_wit_3 : horspool_memmem_refinement_return_wit_3.
Proof.
unfold horspool_memmem_refinement_return_wit_3; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_return_wit_2 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table position ne m1 search_end shift1 offset hs tmp retval retval_2) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_return_wit_2 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros ;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_return_wit_4 : horspool_memmem_refinement_return_wit_4.
Proof.
unfold horspool_memmem_refinement_return_wit_4; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_return_wit_4 ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_return_wit_4 in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros ;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_partial_solve_wit_2_pure : horspool_memmem_refinement_partial_solve_wit_2_pure.
Proof.
unfold horspool_memmem_refinement_partial_solve_wit_2_pure; try left; intros.
  entailer!.
Qed.

Lemma proof_of_horspool_memmem_refinement_partial_solve_wit_4_pure : horspool_memmem_refinement_partial_solve_wit_4_pure.
Proof.
unfold horspool_memmem_refinement_partial_solve_wit_4_pure; try left; intros.
  entailer!.
Qed.

Lemma proof_of_horspool_memmem_refinement_partial_solve_wit_6_pure : horspool_memmem_refinement_partial_solve_wit_6_pure.
Proof.
unfold horspool_memmem_refinement_partial_solve_wit_6_pure; try left; intros.
  entailer!.
Qed.

Lemma proof_of_horspool_memmem_refinement_partial_solve_wit_8_pure : horspool_memmem_refinement_partial_solve_wit_8_pure.
Proof.
unfold horspool_memmem_refinement_partial_solve_wit_8_pure; left; intros.
  repeat rewrite sizeof_uchar in *.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_horspool_memmem_refinement_partial_solve_wit_10_pure : horspool_memmem_refinement_partial_solve_wit_10_pure.
Proof.
unfold horspool_memmem_refinement_partial_solve_wit_10_pure; try left; intros.
  pose proof (horspool_memmem_rel_legacy_proof.proof_of_horspool_memmem_refinement_partial_solve_wit_10_pure ne_len_pre needle_pre hs_len_pre haystack_pre X_low_level_spec needleoff_low_level_spec hayoff_low_level_spec bytes_low_level_spec length_low_level_spec base_low_level_spec table position ne m1 search_end shift1 offset hs tmp) as Hlegacy;
      unfold horspool_memmem_rel_legacy_goal.horspool_memmem_refinement_partial_solve_wit_10_pure in Hlegacy; repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *;
      try match goal with H : hp_filter_offset ?m ?off |- _ =>
        let Hb := fresh "filter_bounds" in
        assert (Hb : 0 <= off /\ off + 8 <= m) by (apply H; lia)
      end;
      repeat match type of Hlegacy with context [unsigned_last_nbits ?x 64] =>
        let E := fresh in assert (E : unsigned_last_nbits x 64 = x) by
          (unfold unsigned_last_nbits; apply Z.mod_small; cbn; lia);
        rewrite E in Hlegacy; clear E end;
      repeat multimatch type of Hlegacy with
        | context [hp_memcmp_result ?b ?l ?r ?n ?ret] =>
          multimatch goal with H : hp_memcmp_result b ?l0 ?r0 n ret |- _ =>
            tryif (constr_eq l0 l; constr_eq r0 r) then fail else
              (replace l0 with l in H by ring; replace r0 with r in H by ring)
          end
        end;
      first [solve [eapply derivable1_trans;
        [|eapply derivable1_trans; [exact Hlegacy |]];
        [(first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]) | repeat match goal with |- (exp _) |-- (exp _) =>
           let w := fresh "migration_witness" in Intros w; Exists w end;
           (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)]]
      |       let T := type of Hlegacy in
      let rec spatial P := lazymatch P with
        | ?B && ?Q => spatial Q | _ => constr:(P) end in
      lazymatch T with ?P |-- ?Q =>
        let S := spatial P in
        assert (Hcore : S |-- Q) by
          (eapply derivable1_trans; [|exact Hlegacy]; (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]));
        sep_apply Hcore
      end;
      Intros ;
      (first [solve [split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; try lia; try ring]] | entailer!]); try (unfold hp_filter_offset; lia)].
Qed.

Lemma proof_of_horspool_memmem_refinement_partial_solve_wit_11_pure : horspool_memmem_refinement_partial_solve_wit_11_pure.
Proof.
unfold horspool_memmem_refinement_partial_solve_wit_11_pure; left; intros.
  repeat rewrite sizeof_uchar in *.
  match goal with H : tmp = m1 -> _ /\ _ |- _ =>
    specialize (H ltac:(lia)); destruct H as [Hwindow Hhash]
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_horspool_memmem_refinement_partial_solve_wit_12_pure : horspool_memmem_refinement_partial_solve_wit_12_pure.
Proof.
unfold horspool_memmem_refinement_partial_solve_wit_12_pure; left; intros.
  repeat rewrite sizeof_uchar in *.
  match goal with H : tmp = m1 -> _ /\ _ |- _ =>
    specialize (H ltac:(lia)); destruct H as [Hwindow Hhash]
  end.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_horspool_memmem_refinement_low_level_spec_entail_high_level_spec : horspool_memmem_refinement_low_level_spec_entail_high_level_spec.
Proof.
unfold horspool_memmem_refinement_low_level_spec_entail_high_level_spec; intros.
  Intros.
  Exists base_high_level_spec; Exists length_high_level_spec; Exists bytes_high_level_spec.
  Exists hayoff_high_level_spec; Exists needleoff_high_level_spec.
  Exists (MonadErr.nrm (hp_search_from bytes_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre 0) tt).
  split_pure_spatial.
  - cancel; Intros_r retval; apply derivable1_wand_sepcon_adjoint; Intros.
    split_pure_spatial; [cancel | split_pures; dump_pre_spatial].
    pose proof (Hoare_safeexec_compose _ _ _
      (hp_rel_g0_search_entry_correct bytes_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre)
      _ _ _ H12 I) as [st [Hpost _]].
    unfold hp_ptr_result in Hpost; destruct (Z.eq_dec retval 0) as [Hz|Hz].
    + left; split; assumption.
    + right; exists (retval - (base_high_level_spec + hayoff_high_level_spec)).
      split; [lia | exact Hpost].
  - split_pures; dump_pre_spatial; auto.
    apply safeExec_monad_Atrue_finnal.
    exact (proj2 (hp_rel_g0_search_entry_correct bytes_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre) tt I).
Qed.

