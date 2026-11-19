From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.glibc Require Import memmove_bytes_goal memmove_lib.
Import Snaive_C_Rules64.
Local Open Scope sac.

Ltac mm_addr := repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *.

Lemma proof_of_mm_load_byte_entail_wit_1 : mm_load_byte_entail_wit_1.
Proof.
 unfold mm_load_byte_entail_wit_1; intros. mm_addr.
 destruct PreH4 as [v Hv]. destruct PreH3 as [H1|H2].
 - eapply derivable1_trans; [|apply derivable1_orp_intros2]. Exists v.
   sep_apply (mm_extract_byte b1 n1 m p_pre v H1 Hv).
   split_pure_spatial; [cancel|].
   split_pures; dump_pre_spatial; try assumption; try lia.
   replace (p_pre + -b1) with (p_pre-b1) by ring.
   rewrite mm_cells_nth by lia. replace (b1+(p_pre-b1)) with p_pre by ring. exact Hv.
 - eapply derivable1_trans; [|apply derivable1_orp_intros1]. Exists v.
   sep_apply (mm_extract_byte b2 n2 m p_pre v H2 Hv).
   split_pure_spatial; [cancel|].
   split_pures; dump_pre_spatial; try assumption; try lia.
   replace (p_pre + -b2) with (p_pre-b2) by ring.
   rewrite mm_cells_nth by lia. replace (b2+(p_pre-b2)) with p_pre by ring. exact Hv.
Qed.

Lemma proof_of_mm_load_byte_return_wit_1 : mm_load_byte_return_wit_1.
Proof.
 unfold mm_load_byte_return_wit_1; left; intros.
 prop_apply (store_uchar_range p_pre v). Intros.
 sep_apply (mm_restore_byte b1 n1 m p_pre v ltac:(lia) PreH1).
 entailer!.
Qed.

Lemma proof_of_mm_load_byte_return_wit_2 : mm_load_byte_return_wit_2.
Proof.
 unfold mm_load_byte_return_wit_2; left; intros.
 prop_apply (store_uchar_range p_pre v). Intros.
 sep_apply (mm_restore_byte b2 n2 m p_pre v ltac:(lia) PreH1).
 entailer!.
Qed.

Lemma proof_of_mm_store_byte_entail_wit_1 : mm_store_byte_entail_wit_1.
Proof.
 unfold mm_store_byte_entail_wit_1; intros.
 destruct PreH3 as [H1|H2].
 - eapply derivable1_trans; [|apply derivable1_orp_intros1].
   sep_apply (mm_extract_writable b1 n1 m p_pre H1). entailer!.
 - eapply derivable1_trans; [|apply derivable1_orp_intros2].
   sep_apply (mm_extract_writable b2 n2 m p_pre H2). entailer!.
Qed.

Lemma proof_of_mm_store_byte_return_wit_1 : mm_store_byte_return_wit_1.
Proof.
 unfold mm_store_byte_return_wit_1; left; intros.
 assert (E : mm_cells b2 n2 (mm_write m p_pre (Some value_pre)) = mm_cells b2 n2 m).
 { destruct (Z.eq_dec n2 0) as [->|Hnz]; [reflexivity|].
   apply mm_cells_write_outside; [lia|]. unfold mm_separated in PreH3; lia. }
 rewrite E.
 sep_apply (mm_restore_written b1 n1 m p_pre value_pre ltac:(lia)). cancel.
Qed.

Lemma proof_of_mm_store_byte_return_wit_2 : mm_store_byte_return_wit_2.
Proof.
 unfold mm_store_byte_return_wit_2; left; intros.
 assert (E : mm_cells b1 n1 (mm_write m p_pre (Some value_pre)) = mm_cells b1 n1 m).
 { destruct (Z.eq_dec n1 0) as [->|Hnz]; [reflexivity|].
   apply mm_cells_write_outside; [lia|]. unfold mm_separated in PreH3; lia. }
 rewrite E.
 sep_apply (mm_restore_written b2 n2 m p_pre value_pre ltac:(lia)). cancel.
Qed.
