(* glibc strstr entry and short-needle refinement. All names refer to the
   current generated VCs. Algorithm component contracts are linked through
   strstr_tw_bridge and the completed dynamic Horspool case. *)
From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.glibc Require Import strstr_goal strstr_short_lib.
Require Import SimpleC.EE.stdlib.musl.strstr_rel_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Ltac gs_addresses := repeat rewrite sizeof_uchar in *; repeat rewrite Z.mul_1_r in *.
Ltac gs_context :=
 match goal with H : gs_inputs ?b ?len ?ho ?hl ?no ?nl |- _ =>
  pose proof H as Inputs;
  destruct H as (Len & LengthBound & Ho & Hl & HEnd & No & Nl & NEnd & Bytes & Hay & Needle & Sep);
  pose proof Hay as (Hnonzero & Hzero); pose proof Needle as (Nnonzero & Nzero);
  try assert (N0 : nl <> 0) by (let E := fresh "LenEq" in intro E; rewrite E, Z.add_0_r in Nzero; congruence);
  try assert (N1 : nl <> 1) by (let E := fresh "LenEq" in intro E; rewrite E in Nzero; congruence);
  try assert (N2 : nl <> 2) by (let E := fresh "LenEq" in intro E; rewrite E in Nzero; congruence);
  try assert (N3 : nl <> 3) by (let E := fresh "LenEq" in intro E; rewrite E in Nzero; congruence);
  try assert (Z0 : nl = 0) by
   (symmetry; apply (proj1 (gs_read_zero b no nl 0 Needle ltac:(lia))); rewrite Z.add_0_r; congruence);
  try assert (Z1 : nl = 1) by
   (symmetry; apply (proj1 (gs_read_zero b no nl 1 Needle ltac:(lia))); congruence);
  try assert (Z2 : nl = 2) by
   (symmetry; apply (proj1 (gs_read_zero b no nl 2 Needle ltac:(lia))); congruence);
  try assert (Z3 : nl = 3) by
   (symmetry; apply (proj1 (gs_read_zero b no nl 3 Needle ltac:(lia))); congruence)
 end.
Ltac gs_loop_bound :=
 try match goal with Hc : ?c <> 0, Ec : ?c = Znth (?ho+?pos) ?b 0,
                      Hz : Znth (?ho+?hl) ?b 0 = 0 |- _ =>
 assert (PosEnd : pos < hl) by (destruct (Z.eq_dec pos hl); [subst;congruence|lia]) end.
Ltac gs_pure := split_pures; dump_pre_spatial; try assumption; try lia; try ring.
Ltac gs_finish := split_pure_spatial; [entailer!|gs_pure].

Ltac gs_suffix_normal :=
 match goal with P : ?hs = ?base + ?ho + ?start, I : gs_inputs ?b ?len ?ho ?hl ?no ?nl |- _ =>
 replace (hs+-base) with (ho+start) in * by lia;
 replace (base+ho+start+-base) with (ho+start) in * by ring;
 replace (ho+hl-(ho+start)) with (hl-start) in * by ring end.
Ltac gs_signed := repeat rewrite signed_last_nbits_eq in * by (cbn; lia).
Ltac gs_probe_facts :=
 match goal with H : gs_probe ?total ?limit ?res |- _ =>
  unfold gs_probe in H;
  pose proof (Z.le_min_l total limit) as ProbeUpper;
  pose proof (Z.le_min_r total limit) as ProbeLimit
 end.

Lemma proof_of_gs_read_entail_wit_1 : gs_read_entail_wit_1.
Proof.
unfold gs_read_entail_wit_1; left; intros.
subst p_pre. split_pure_spatial.
- replace (base+index) with (base+index*sizeof(UCHAR)) by (rewrite sizeof_uchar; ring).
  rewrite <- UCharArray.seg_shift. replace (index+(0-index)) with 0 by ring.
  replace (index+(length-index)) with length by ring.
  apply UCharArray.full_to_seg.
- gs_pure.
Qed.

Lemma proof_of_gs_read_return_wit_1 : gs_read_return_wit_1.
Proof.
unfold gs_read_return_wit_1; left; intros.
subst p. pose proof (gs_byte_bound bytes index PreH4) as Bound.
split_pure_spatial.
- sep_apply UCharArray.seg_to_full.
  gs_addresses. replace (base+index+(0-index)) with base by ring.
  replace (length-index-(0-index)) with length by ring. entailer!.
- replace (0-(0-index)) with index by ring. gs_pure.
Qed.

Lemma proof_of_strstr2_safety_wit_1 : strstr2_safety_wit_1.
Proof.
unfold strstr2_safety_wit_1; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_signed. gs_pure.
Qed.

Lemma proof_of_strstr2_entail_wit_1 : strstr2_entail_wit_1.
Proof.
unfold strstr2_entail_wit_1; left; intros. gs_addresses. gs_context.
Exists 0. repeat rewrite Z.add_0_r. gs_finish.
unfold gs_short. split.
- unfold gs_word, gs_lag. cbn [Z.eqb Pos.eqb Z.ltb Z.compare Pos.compare Pos.compare_cont].
  unfold unsigned_last_nbits.
  rewrite Z.mod_small by (rewrite Z.shiftl_mul_pow2 by lia; change (2^16) with 65536; lia).
  rewrite lor_high_low__proof_of_threebyte_2 by (try lia; change (2^16) with 65536; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536.
  replace (no+2-2) with no by ring. replace (no+2-1) with (no+1) by ring. lia.
- split; [reflexivity|]. unfold hp_no_match_before; intros; lia.
Qed.

Lemma proof_of_strstr2_entail_wit_2 : strstr2_entail_wit_2.
Proof.
unfold strstr2_entail_wit_2; left; intros. gs_addresses. gs_context. gs_loop_bound.
Exists (pos_2+1).
replace (hs+1+-base) with (ho+(pos_2+1)) in * by lia.
gs_finish.
pose proof PreH11 as (A & B & Before).
unfold gs_short. split; [exact A|]. split.
- rewrite B. unfold unsigned_last_nbits.
apply gs_word2_step; auto.
- eapply gs_short_before_step; eauto; lia.
Qed.

Lemma proof_of_strstr2_return_wit_1 : strstr2_return_wit_1.
Proof.
unfold strstr2_return_wit_1; left; intros. gs_addresses. gs_context.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_short_return; try exact Bytes; try exact Needle; try exact Hay; try eassumption; try lia.
Qed.

Lemma proof_of_strstr2_return_wit_2 : strstr2_return_wit_2.
Proof.
unfold strstr2_return_wit_2; left; intros. gs_addresses. gs_context.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_short_return; try exact Bytes; try exact Needle; try exact Hay; try eassumption; try lia.
Qed.

Lemma proof_of_strstr2_partial_solve_wit_1_pure : strstr2_partial_solve_wit_1_pure.
Proof.
unfold strstr2_partial_solve_wit_1_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr2_partial_solve_wit_2_pure : strstr2_partial_solve_wit_2_pure.
Proof.
unfold strstr2_partial_solve_wit_2_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr2_partial_solve_wit_3_pure : strstr2_partial_solve_wit_3_pure.
Proof.
unfold strstr2_partial_solve_wit_3_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr2_partial_solve_wit_4_pure : strstr2_partial_solve_wit_4_pure.
Proof.
unfold strstr2_partial_solve_wit_4_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr3_safety_wit_1 : strstr3_safety_wit_1.
Proof.
unfold strstr3_safety_wit_1; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_signed. gs_pure.
Qed.

Lemma proof_of_strstr3_safety_wit_2 : strstr3_safety_wit_2.
Proof.
unfold strstr3_safety_wit_2; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_signed. gs_pure.
Qed.

Lemma proof_of_strstr3_entail_wit_1 : strstr3_entail_wit_1.
Proof.
unfold strstr3_entail_wit_1; left; intros. gs_addresses. gs_context.
Exists 0. repeat rewrite Z.add_0_r. gs_finish.
unfold gs_short. split.
- unfold gs_word, gs_lag. cbn [Z.eqb Pos.eqb Z.ltb Z.compare Pos.compare Pos.compare_cont].
  unfold unsigned_last_nbits.
  rewrite packed3__proof_of_threebyte_2 by lia.
  replace (no+3-3) with no by ring. replace (no+3-2) with (no+1) by ring.
  replace (no+3-1) with (no+2) by ring. lia.
- split; [reflexivity|]. unfold hp_no_match_before; intros; lia.
Qed.

Lemma proof_of_strstr3_entail_wit_2 : strstr3_entail_wit_2.
Proof.
unfold strstr3_entail_wit_2; left; intros. gs_addresses. gs_context. gs_loop_bound.
Exists (pos_2+1).
replace (hs+1+-base) with (ho+(pos_2+1)) in * by lia.
gs_finish.
pose proof PreH11 as (A & B & Before).
unfold gs_short. split; [exact A|]. split.
- rewrite B. unfold unsigned_last_nbits.
apply gs_word3_step; auto.
- eapply gs_short_before_step; eauto; lia.
Qed.

Lemma proof_of_strstr3_return_wit_1 : strstr3_return_wit_1.
Proof.
unfold strstr3_return_wit_1; left; intros. gs_addresses. gs_context.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_short_return; try exact Bytes; try exact Needle; try exact Hay; try eassumption; try lia.
Qed.

Lemma proof_of_strstr3_return_wit_2 : strstr3_return_wit_2.
Proof.
unfold strstr3_return_wit_2; left; intros. gs_addresses. gs_context.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_short_return; try exact Bytes; try exact Needle; try exact Hay; try eassumption; try lia.
Qed.

Lemma proof_of_strstr3_partial_solve_wit_1_pure : strstr3_partial_solve_wit_1_pure.
Proof.
unfold strstr3_partial_solve_wit_1_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr3_partial_solve_wit_2_pure : strstr3_partial_solve_wit_2_pure.
Proof.
unfold strstr3_partial_solve_wit_2_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr3_partial_solve_wit_3_pure : strstr3_partial_solve_wit_3_pure.
Proof.
unfold strstr3_partial_solve_wit_3_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr3_partial_solve_wit_4_pure : strstr3_partial_solve_wit_4_pure.
Proof.
unfold strstr3_partial_solve_wit_4_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr3_partial_solve_wit_5_pure : strstr3_partial_solve_wit_5_pure.
Proof.
unfold strstr3_partial_solve_wit_5_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr_entail_wit_1 : strstr_entail_wit_1.
Proof.
unfold strstr_entail_wit_1; left; intros. gs_addresses. gs_context.
match goal with H : gs_strchr bytes base ho hl ?c ?r |- _ =>
 assert (N : 0 < nl) by lia;
 replace c with (Znth no bytes 0) in H by congruence;
 destruct (gs_chr_before bytes base ho hl no nl r N H ltac:(lia))
 as (start & Bound & Ptr & First & Before)
end.
Exists start. gs_finish.
Qed.

Lemma proof_of_strstr_return_wit_1 : strstr_return_wit_1.
Proof.
unfold strstr_return_wit_1; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_result_suffix with (start := start); try eassumption; try lia.
all: try congruence.
Qed.

Lemma proof_of_strstr_return_wit_2 : strstr_return_wit_2.
Proof.
unfold strstr_return_wit_2; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_result_suffix with (start := start); try eassumption; try lia.
all: try congruence.
Qed.

Lemma proof_of_strstr_return_wit_3 : strstr_return_wit_3.
Proof.
unfold strstr_return_wit_3; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
replace hs with (base+ho+start) by lia.
apply gs_match_return; [|assumption].
unfold hp_match_at. split; [lia|]. split; [lia|].
intros j Hj. unfold hp_memcmp_result in PreH2.
pose proof ((proj1 PreH2) PreH1 j ltac:(lia)).
replace (ho+start+j) with (ho+start+j) by ring. assumption.
Qed.

Lemma proof_of_strstr_return_wit_4 : strstr_return_wit_4.
Proof.
unfold strstr_return_wit_4; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_result_suffix with (start := start); try eassumption; try lia.
apply gs_no_room.
replace retval_4 with nl in * by lia.
pose proof (gs_or_budget nl Nl).
pose proof (Z.min_spec (hl-start) (Z.lor nl 512)) as [[B E]|[B E]]; lia.
Qed.

Lemma proof_of_strstr_return_wit_5 : strstr_return_wit_5.
Proof.
unfold strstr_return_wit_5; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_result_suffix with (start := start); try eassumption; try lia.
all: try congruence.
Qed.

Lemma proof_of_strstr_return_wit_6 : strstr_return_wit_6.
Proof.
unfold strstr_return_wit_6; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
eapply gs_result_suffix with (start := start); try eassumption; try lia.
all: try congruence.
Qed.

Lemma proof_of_strstr_return_wit_7 : strstr_return_wit_7.
Proof.
unfold strstr_return_wit_7; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
replace hs with (base+ho+start) by lia.
apply gs_match_return; [|assumption].
unfold hp_match_at. split; [lia|]. split; [lia|].
intros j Hj. assert (j=0) by lia. subst j. repeat rewrite Z.add_0_r. assumption.
Qed.

Lemma proof_of_strstr_return_wit_8 : strstr_return_wit_8.
Proof.
unfold strstr_return_wit_8; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
subst retval. eapply gs_chr_none; [lia|].
replace (Znth no bytes 0) with retval_3 by congruence. exact PreH2.
Qed.

Lemma proof_of_strstr_return_wit_9 : strstr_return_wit_9.
Proof.
unfold strstr_return_wit_9; left; intros. gs_addresses. gs_context.
try gs_suffix_normal. gs_signed. try gs_probe_facts.
split_pure_spatial; [cancel|]. dump_pre_spatial.
replace nl with 0 by lia. replace haystack_pre with (base+ho) by lia.
apply gs_empty; lia.
Qed.

Lemma proof_of_strstr_partial_solve_wit_1_pure : strstr_partial_solve_wit_1_pure.
Proof.
unfold strstr_partial_solve_wit_1_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr_partial_solve_wit_2_pure : strstr_partial_solve_wit_2_pure.
Proof.
unfold strstr_partial_solve_wit_2_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr_partial_solve_wit_3_pure : strstr_partial_solve_wit_3_pure.
Proof.
unfold strstr_partial_solve_wit_3_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr_partial_solve_wit_4_pure : strstr_partial_solve_wit_4_pure.
Proof.
unfold strstr_partial_solve_wit_4_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr_partial_solve_wit_5_pure : strstr_partial_solve_wit_5_pure.
Proof.
unfold strstr_partial_solve_wit_5_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr_partial_solve_wit_6_pure : strstr_partial_solve_wit_6_pure.
Proof.
unfold strstr_partial_solve_wit_6_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_suffix_normal.
pose proof (gs_suffix_inputs bytes length ho hl no nl start Inputs ltac:(lia)) as Suffix.
try gs_probe_facts. gs_signed.
try subst nl.
gs_pure;
try solve [congruence | unfold gs_inputs in Suffix; tauto
          | unfold hp_inputs; unfold gs_inputs in Suffix; intuition lia].
Qed.

Lemma proof_of_strstr_partial_solve_wit_7_pure : strstr_partial_solve_wit_7_pure.
Proof.
unfold strstr_partial_solve_wit_7_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr_partial_solve_wit_8_pure : strstr_partial_solve_wit_8_pure.
Proof.
unfold strstr_partial_solve_wit_8_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_suffix_normal.
pose proof (gs_suffix_inputs bytes length ho hl no nl start Inputs ltac:(lia)) as Suffix.
try gs_probe_facts. gs_signed.
try subst nl.
gs_pure;
try solve [congruence | unfold gs_inputs in Suffix; tauto
          | unfold hp_inputs; unfold gs_inputs in Suffix; intuition lia].
Qed.

Lemma proof_of_strstr_partial_solve_wit_9_pure : strstr_partial_solve_wit_9_pure.
Proof.
unfold strstr_partial_solve_wit_9_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_pure.
Qed.

Lemma proof_of_strstr_partial_solve_wit_10_pure : strstr_partial_solve_wit_10_pure.
Proof.
unfold strstr_partial_solve_wit_10_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_suffix_normal.
pose proof (gs_suffix_inputs bytes length ho hl no nl start Inputs ltac:(lia)) as Suffix.
try gs_probe_facts. gs_signed.
gs_pure;
try solve [congruence | unfold gs_inputs in Suffix; tauto
          | unfold hp_inputs; unfold gs_inputs in Suffix; intuition lia].
Qed.

Lemma proof_of_strstr_partial_solve_wit_11_pure : strstr_partial_solve_wit_11_pure.
Proof.
unfold strstr_partial_solve_wit_11_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_suffix_normal.
pose proof (gs_suffix_inputs bytes length ho hl no nl start Inputs ltac:(lia)) as Suffix.
try gs_probe_facts. gs_signed.
gs_pure;
try solve [congruence | unfold gs_inputs in Suffix; tauto
          | unfold hp_inputs; unfold gs_inputs in Suffix; intuition lia].
Qed.

Lemma proof_of_strstr_partial_solve_wit_12_pure : strstr_partial_solve_wit_12_pure.
Proof.
unfold strstr_partial_solve_wit_12_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_suffix_normal.
pose proof (gs_suffix_inputs bytes length ho hl no nl start Inputs ltac:(lia)) as Suffix.
try gs_probe_facts. gs_signed.
gs_pure;
try solve [congruence | unfold gs_inputs in Suffix; tauto
          | unfold hp_inputs; unfold gs_inputs in Suffix; intuition lia].
Qed.

Lemma proof_of_strstr_partial_solve_wit_13_pure : strstr_partial_solve_wit_13_pure.
Proof.
unfold strstr_partial_solve_wit_13_pure; try left; intros. gs_addresses. gs_context. gs_loop_bound.
gs_suffix_normal.
pose proof (gs_suffix_inputs bytes length ho hl no nl start Inputs ltac:(lia)) as Suffix.
try gs_probe_facts. gs_signed.
gs_pure;
try solve [congruence | unfold gs_inputs in Suffix; tauto
          | unfold hp_inputs; unfold gs_inputs in Suffix; intuition lia].
Qed.
