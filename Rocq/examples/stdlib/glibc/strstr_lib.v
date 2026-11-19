From Coq Require Import ZArith List Lia Classical_Prop.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.stdlib.glibc.horspool_dynamic_lib.
Require Import SimpleC.EE.stdlib.musl.strstr_rel_lib.
Local Open Scope Z_scope.

Definition gs_bytes (b : list Z) := Forall (fun x => 0 <= x <= 255) b.
Definition gs_inputs (b : list Z) (len ho hl no nl : Z) : Prop :=
 Zlength b = len /\ 0 <= len <= 2147483647 /\
 0 <= ho /\ 0 <= hl /\ ho+hl < len /\
 0 <= no /\ 0 <= nl /\ no+nl < len /\
 gs_bytes b /\ hp_cstring b ho hl /\ hp_cstring b no nl /\
 (256 < nl -> ho+hl < no \/ no+nl < ho).
Definition gs_strchr (b : list Z) (base ho hl c r : Z) : Prop :=
 (r = 0 /\ forall i, 0 <= i < hl -> Znth (ho+i) b 0 <> c) \/
 exists i, 0 <= i < hl /\ r = base+ho+i /\ r <> 0 /\
 Znth (ho+i) b 0 = c /\ (forall j, 0 <= j < i -> Znth (ho+j) b 0 <> c).
Definition gs_probe (total limit result : Z) := result = Z.min total limit.
Definition gs_lag (b : list Z) (ho pos lag : Z) :=
 if pos <? lag then 0 else Znth (ho+pos-lag) b 0.
Definition gs_word (b : list Z) (ho k pos : Z) :=
 if k =? 2 then 65536 * gs_lag b ho pos 2 + gs_lag b ho pos 1
 else 16777216 * gs_lag b ho pos 3 + 65536 * gs_lag b ho pos 2 + 256 * gs_lag b ho pos 1.
Definition gs_short (b : list Z) (ho hl no k pos h1 h2 : Z) : Prop :=
 h1 = gs_word b no k k /\ h2 = gs_word b ho k pos /\
 hp_no_match_before b ho hl no k (pos-k).

Lemma gs_byte_bound : forall b i, gs_bytes b -> 0 <= Znth i b 0 <= 255.
Proof.
 intros b i H. unfold gs_bytes, Znth in *.
 destruct (lt_dec (Z.to_nat i) (length b)).
 - exact (proj1 (Forall_nth _ _) H _ 0 l).
 - rewrite nth_overflow by lia. lia.
Qed.

Lemma gs_read_zero : forall b off len i,
 hp_cstring b off len -> 0 <= i <= len ->
 (Znth (off+i) b 0 = 0 <-> i = len).
Proof. intros b off len i [Hnz Hz] Hi; split; intros; [|subst;assumption].
 destruct (Z.eq_dec i len); auto. exfalso. apply (Hnz i ltac:(lia)); assumption.
Qed.

Lemma gs_suffix_inputs : forall b len ho hl no nl start,
 gs_inputs b len ho hl no nl -> 0 <= start <= hl ->
 gs_inputs b len (ho+start) (hl-start) no nl.
Proof.
 intros b len ho hl no nl start (L & B & Ho & Hl & He & No & Nl & Ne & Bytes & [Hnz Hz] & [Nnz Nz] & Sep) S.
 unfold gs_inputs. repeat split; try assumption; try lia.
 - intros i Hi. replace (ho+start+i) with (ho+(start+i)) by ring. apply Hnz; lia.
 - replace (ho+start+(hl-start)) with (ho+hl) by ring. exact Hz.
Qed.

Lemma gs_match_suffix : forall b ho hl no nl start pos,
 0 <= start -> 0 <= pos ->
 (hp_match_at b (ho+start) (hl-start) no nl pos <->
  hp_match_at b ho hl no nl (start+pos)).
Proof. unfold hp_match_at; intros. split; intros (A & B & C); repeat split; try lia;
 intros i Hi; specialize (C i Hi);
 replace (ho+start+pos+i) with (ho+(start+pos)+i) in * by ring; assumption.
Qed.

Lemma gs_result_suffix : forall b base ho hl no nl start r,
 0 <= start -> hp_no_match_before b ho hl no nl start ->
 hp_result b base (ho+start) (hl-start) no nl r ->
 hp_result b base ho hl no nl r.
Proof.
 intros b base ho hl no nl start r S Before [[R None]|(pos & R & Match & Prior)].
 - left. split; auto. intros pos M.
   destruct (Z_lt_ge_dec pos start).
   + apply (Before pos); [unfold hp_match_at in M; lia|exact M].
   + apply (None (pos-start)). apply gs_match_suffix; try lia.
     replace (start+(pos-start)) with pos by ring. exact M.
 - right. exists (start+pos). split; [lia|]. split.
   + apply gs_match_suffix; try lia. unfold hp_match_at in Match; lia.
     exact Match.
   + intros j Hj M. destruct (Z_lt_ge_dec j start).
     * apply (Before j); auto; lia.
     * apply (Prior (j-start)); [lia|]. apply gs_match_suffix; try lia.
       replace (start+(j-start)) with j by ring. exact M.
Qed.

Lemma gs_no_room : forall b base ho hl no nl,
 hl < nl -> hp_result b base ho hl no nl 0.
Proof. intros. left. split; auto. unfold hp_match_at; intros; lia. Qed.

Lemma gs_empty : forall b base ho hl no,
 0 <= hl -> hp_result b base ho hl no 0 (base+ho).
Proof.
 intros. right. exists 0. split; [lia|]. split.
 - unfold hp_match_at; repeat split; intros; lia.
 - unfold hp_no_match_before; intros; lia.
Qed.

Lemma gs_chr_before : forall b base ho hl no nl r,
 0 < nl -> gs_strchr b base ho hl (Znth no b 0) r -> r <> 0 ->
 exists start, 0 <= start < hl /\ r = base+ho+start /\
 Znth (ho+start) b 0 = Znth no b 0 /\ hp_no_match_before b ho hl no nl start.
Proof.
 intros b base ho hl no nl r N [[R None]|(i & I & R & NZ & E & Before)] Not; [contradiction|].
 exists i. split; [exact I|]. split; [exact R|]. split; [exact E|].
 unfold hp_no_match_before; intros p Hp (P & Fit & Match).
 apply (Before p Hp). specialize (Match 0 ltac:(lia)).
 replace (ho+p+0) with (ho+p) in Match by ring.
 replace (no+0) with no in Match by ring. exact Match.
Qed.

Lemma gs_chr_none : forall b base ho hl no nl,
 0 < nl -> gs_strchr b base ho hl (Znth no b 0) 0 ->
 hp_result b base ho hl no nl 0.
Proof.
 intros b base ho hl no nl N [[_ None]|(i & I & R & NZ & Rest)]; [|contradiction].
 left. split; auto. intros p (P & Fit & Match).
 apply (None p); [lia|]. specialize (Match 0 ltac:(lia)).
 replace (ho+p+0) with (ho+p) in Match by ring.
 replace (no+0) with no in Match by ring. exact Match.
Qed.

Lemma gs_match_return : forall b base ho hl no nl pos,
 hp_match_at b ho hl no nl pos -> hp_no_match_before b ho hl no nl pos ->
 hp_result b base ho hl no nl (base+ho+pos).
Proof. intros. right. exists pos. auto. Qed.

Lemma gs_or_budget : forall n, 0 <= n -> n <= Z.lor n 512.
Proof.
 intros n Hn.
 assert (B : Z.land n 512 <= 512).
 { destruct n as [|p|p]; try (simpl; lia).
   change (Z.of_N (N.land (N.pos p) 512) <= Z.of_N 512).
   apply N2Z.inj_le. apply N.land_le_r. }
 pose proof (Z.add_lor_land n 512). lia.
Qed.
