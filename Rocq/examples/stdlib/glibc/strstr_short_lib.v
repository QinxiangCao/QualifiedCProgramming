From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.stdlib.glibc.strstr_lib.
Require Import SimpleC.EE.stdlib.musl.strstr_rel_lib.
Local Open Scope Z_scope.

Lemma gs_lag_bound : forall b ho pos lag, gs_bytes b -> 0 <= gs_lag b ho pos lag <= 255.
Proof. intros. unfold gs_lag. destruct (pos <? lag); [lia|apply gs_byte_bound;assumption]. Qed.

Lemma gs_lag_step : forall b ho pos lag,
 gs_lag b ho (pos+1) (lag+1) = gs_lag b ho pos lag.
Proof.
 intros. unfold gs_lag. destruct (pos+1 <? lag+1) eqn:A, (pos <? lag) eqn:B;
 try reflexivity; try (apply Z.ltb_lt in A); try (apply Z.ltb_lt in B);
 try (apply Z.ltb_ge in A); try (apply Z.ltb_ge in B); try lia.
 f_equal; ring.
Qed.

Lemma gs_lag_current : forall b ho pos,
 0 <= pos -> gs_lag b ho (pos+1) 1 = Znth (ho+pos) b 0.
Proof. intros. unfold gs_lag. destruct (pos+1 <? 1) eqn:E; [apply Z.ltb_lt in E; lia|]. f_equal; ring. Qed.

Lemma gs_word2_step : forall b ho pos c,
 gs_bytes b -> 0 <= pos -> c = Znth (ho+pos) b 0 ->
 Z.lor ((Z.shiftl (gs_word b ho 2 pos) 16) mod 4294967296) c = gs_word b ho 2 (pos+1).
Proof.
 intros b ho pos c B P C.
 pose proof (gs_lag_bound b ho pos 2 B) as A.
 pose proof (gs_lag_bound b ho pos 1 B) as D.
 pose proof (gs_byte_bound b (ho+pos) B) as E.
 unfold gs_word. cbn [Z.eqb Pos.eqb].
 rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536.
 replace ((65536 * gs_lag b ho pos 2 + gs_lag b ho pos 1)*65536)
  with (65536 * gs_lag b ho pos 1 + gs_lag b ho pos 2*4294967296) by ring.
 rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
 replace (65536*gs_lag b ho pos 1) with (Z.shiftl (gs_lag b ho pos 1) 16)
  by (rewrite Z.shiftl_mul_pow2 by lia; change (2^16) with 65536; ring).
 rewrite lor_high_low__proof_of_threebyte_2 by (try lia; change (2^16) with 65536; lia).
 rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536.
 assert (L2 : gs_lag b ho (pos+1) 2 = gs_lag b ho pos 1) by (exact (gs_lag_step b ho pos 1)); rewrite L2, gs_lag_current by lia. lia.
Qed.

Lemma gs_word3_step : forall b ho pos c,
 gs_bytes b -> 0 <= pos -> c = Znth (ho+pos) b 0 ->
 (Z.shiftl (Z.lor (gs_word b ho 3 pos) c) 8) mod 4294967296 = gs_word b ho 3 (pos+1).
Proof.
 intros b ho pos c B P C.
 pose proof (gs_lag_bound b ho pos 3 B) as A.
 pose proof (gs_lag_bound b ho pos 2 B) as D.
 pose proof (gs_lag_bound b ho pos 1 B) as E.
 pose proof (gs_byte_bound b (ho+pos) B) as F.
 unfold gs_word. cbn [Z.eqb Pos.eqb].
 replace c with (c mod 4294967296) at 1 by (rewrite Z.mod_small; lia).
 rewrite packed3_step__proof_of_threebyte_2 by lia.
 assert (L3 : gs_lag b ho (pos+1) 3 = gs_lag b ho pos 2) by (exact (gs_lag_step b ho pos 2)); rewrite L3.
 assert (L2 : gs_lag b ho (pos+1) 2 = gs_lag b ho pos 1) by (exact (gs_lag_step b ho pos 1)); rewrite L2.
 rewrite gs_lag_current by lia. lia.
Qed.

Lemma gs_word2_equal : forall b ho hl no pos,
 gs_bytes b -> hp_cstring b no 2 -> 0 <= pos <= hl ->
 (gs_word b no 2 2 = gs_word b ho 2 pos <->
  2 <= pos /\ hp_match_at b ho hl no 2 (pos-2)).
Proof.
 intros b ho hl no pos Bytes [Nnz Nz] P.
 pose proof (Nnz 0 ltac:(lia)) as N0. rewrite Z.add_0_r in N0.
 pose proof (gs_byte_bound b no Bytes) as B0.
 pose proof (gs_byte_bound b (no+1) Bytes) as B1.
 pose proof (gs_byte_bound b (ho+pos-2) Bytes) as C0.
 pose proof (gs_byte_bound b (ho+pos-1) Bytes) as C1.
 unfold gs_word, gs_lag; cbn [Z.eqb Pos.eqb Z.ltb Z.compare Pos.compare Pos.compare_cont].
 replace (no+2-2) with no by ring. replace (no+2-1) with (no+1) by ring.
 destruct (pos <? 2) eqn:A; destruct (pos <? 1) eqn:D;
 try (apply Z.ltb_lt in A); try (apply Z.ltb_ge in A);
 try (apply Z.ltb_lt in D); try (apply Z.ltb_ge in D); try (split; intros; lia).
 split.
 - intros Eq. split; [lia|]. unfold hp_match_at. split; [lia|]. split; [lia|].
   intros i I. assert (i=0 \/ i=1) by lia. destruct H; subst i;
   replace (ho+(pos-2)+0) with (ho+pos-2) by ring;
   replace (ho+(pos-2)+1) with (ho+pos-1) by ring;
   replace (no+0) with no by ring; lia.
 - intros [_ (_ & _ & M)]. pose proof (M 0 ltac:(lia)). pose proof (M 1 ltac:(lia)).
   replace (ho+(pos-2)+0) with (ho+pos-2) in * by ring.
   replace (ho+(pos-2)+1) with (ho+pos-1) in * by ring.
   replace (no+0) with no in * by ring. lia.
Qed.

Lemma gs_word3_equal : forall b ho hl no pos,
 gs_bytes b -> hp_cstring b no 3 -> 0 <= pos <= hl ->
 (gs_word b no 3 3 = gs_word b ho 3 pos <->
  3 <= pos /\ hp_match_at b ho hl no 3 (pos-3)).
Proof.
 intros b ho hl no pos Bytes [Nnz Nz] P.
 pose proof (Nnz 0 ltac:(lia)) as N0. rewrite Z.add_0_r in N0.
 pose proof (gs_byte_bound b no Bytes) as B0.
 pose proof (gs_byte_bound b (no+1) Bytes) as B1.
 pose proof (gs_byte_bound b (no+2) Bytes) as B2.
 pose proof (gs_byte_bound b (ho+pos-3) Bytes) as C0.
 pose proof (gs_byte_bound b (ho+pos-2) Bytes) as C1.
 pose proof (gs_byte_bound b (ho+pos-1) Bytes) as C2.
 unfold gs_word, gs_lag; cbn [Z.eqb Pos.eqb Z.ltb Z.compare Pos.compare Pos.compare_cont].
 replace (no+3-3) with no by ring. replace (no+3-2) with (no+1) by ring.
 replace (no+3-1) with (no+2) by ring.
 destruct (pos <? 3) eqn:A; destruct (pos <? 2) eqn:D; destruct (pos <? 1) eqn:E;
 try (apply Z.ltb_lt in A); try (apply Z.ltb_ge in A);
 try (apply Z.ltb_lt in D); try (apply Z.ltb_ge in D);
 try (apply Z.ltb_lt in E); try (apply Z.ltb_ge in E); try (split; intros; lia).
 split.
 - intros Eq. split; [lia|]. unfold hp_match_at. split; [lia|]. split; [lia|].
   intros i I. assert (i=0 \/ i=1 \/ i=2) by lia. destruct H as [H|[H|H]]; subst i;
   replace (ho+(pos-3)+0) with (ho+pos-3) by ring;
   replace (ho+(pos-3)+1) with (ho+pos-2) by ring;
   replace (ho+(pos-3)+2) with (ho+pos-1) by ring;
   replace (no+0) with no by ring; lia.
 - intros [_ (_ & _ & M)]. pose proof (M 0 ltac:(lia)). pose proof (M 1 ltac:(lia)). pose proof (M 2 ltac:(lia)).
   replace (ho+(pos-3)+0) with (ho+pos-3) in * by ring.
   replace (ho+(pos-3)+1) with (ho+pos-2) in * by ring.
   replace (ho+(pos-3)+2) with (ho+pos-1) in * by ring.
   replace (no+0) with no in * by ring. lia.
Qed.

Lemma gs_short_before_step : forall b ho hl no k pos h1 h2,
 (k=2 \/ k=3) -> gs_bytes b -> hp_cstring b no k -> 0 <= pos <= hl ->
 gs_short b ho hl no k pos h1 h2 -> h1 <> h2 ->
 hp_no_match_before b ho hl no k (pos+1-k).
Proof.
 intros b ho hl no k pos h1 h2 K Bytes Ns P [A [B Before]] Ne.
 assert (E : gs_word b no k k = gs_word b ho k pos <->
 k <= pos /\ hp_match_at b ho hl no k (pos-k)).
 { destruct K; subst k; [apply gs_word2_equal|apply gs_word3_equal]; auto. }
 intros i I M. destruct (Z_lt_ge_dec i (pos-k)).
 - apply (Before i); auto; lia.
 - assert (i=pos-k) by lia. subst i. apply Ne. rewrite A,B. apply E; split; auto; lia.
Qed.

Lemma gs_short_return : forall b base ho hl no k pos h1 h2 r,
 (k=2 \/ k=3) -> gs_bytes b -> hp_cstring b no k -> hp_cstring b ho hl ->
 0 <= pos <= hl -> gs_short b ho hl no k pos h1 h2 ->
 ((h1=h2 /\ r=base+ho+pos-k) \/
  (h1<>h2 /\ Znth (ho+pos) b 0=0 /\ r=0)) ->
 hp_result b base ho hl no k r.
Proof.
 intros b base ho hl no k pos h1 h2 r K Bytes Ns Hs P Short End.
 pose proof Short as [A [B Before]].
 destruct End as [[Eq R]|[Ne [Zero R]]].
 - assert (W : k<=pos /\ hp_match_at b ho hl no k (pos-k)).
   { destruct K; subst k; [apply gs_word2_equal|apply gs_word3_equal]; auto; congruence. }
   right. exists (pos-k). split; [lia|]. tauto.
 - subst r. left. split; auto. intros i M.
   pose proof (gs_short_before_step b ho hl no k pos h1 h2 K Bytes Ns P Short Ne) as All.
   apply (All i); auto. pose proof (proj1 (gs_read_zero b ho hl pos Hs P) Zero).
   unfold hp_match_at in M. lia.
Qed.
