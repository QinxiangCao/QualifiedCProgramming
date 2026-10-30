From SimpleC.Verification Require Import VCPrelude.
Require Import Coq.setoid_ring.Field.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
From Coq Require Reals SpecFloat.
From Flocq.Core Require Core.
From Flocq.IEEE754 Require Import Binary.
From CDCLLib Require Export cdcl_shared_lib.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_model_tactics.

Lemma binary_scratch_initialized : forall c words,
  words <> [] -> binary_scratch_rep c words = MiniSatClause.rep c false words.
Proof. intros c [|x xs] H; [contradiction|reflexivity]. Qed.

Lemma binary_scratch_forget : forall c words,
  (words = [] \/ Zlength words = 2) ->
  binary_scratch_rep c words |-- binary_scratch_rep c [].
Proof.
  intros c [|x xs] Hshape; [cancel|].
  assert (Hlen : Zlength (x :: xs) = 2) by (destruct Hshape; congruence).
  cbn [binary_scratch_rep]. unfold MiniSatClause.rep. rewrite Hlen. Intros.
  sep_apply_l_atomic (IntArray.seg_to_undef_seg (clause_lits_addr c) 0 2 (x :: xs)).
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.

Lemma binary_scratch_positive : forall c words,
  binary_scratch_rep c words |-- “ 0 < c ”.
Proof.
  intros c [|x xs]; cbn [binary_scratch_rep];
    unfold MiniSatClause.rep; (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
Qed.

Lemma binary_scratch_open_for_write : forall c words,
  (words = [] \/ Zlength words = 2) ->
  binary_scratch_rep c words |--
  “ 0 < c /\ c mod 2 = 0 ” &&
  (clause_hdr_addr c # Int |-> 4 **
   clause_lits_addr c # Int |->_ **
   (clause_lits_addr c + sizeof(INT)) # Int |->_).
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct words as [|x xs].
  all: unfold binary_scratch_rep, activity_state, clause_hdr_word,
    MiniSatClause.rep, IntArray.undef_seg, IntArray.full,
    store_undef_array_rec, store_array_rec;
    simpl; rewrite ?Z.add_0_r.
  - entailer!.
  - assert (Hlen : Zlength (x :: xs) = 2) by
      (destruct H; congruence).
    rewrite Hlen; unfold clause_hdr_word; simpl; Intros.
    sep_apply_l_atomic
      (IntArray.seg_to_undef_seg (clause_lits_addr c) 0 2 (x :: xs)).
    unfold IntArray.undef_seg, store_undef_array_rec;
      simpl; rewrite ?Z.add_0_r; entailer!.
Qed.

Lemma solver_binary_open_for_write : forall M,
  solver_shape M ->
  solver_binary_rep M |--
  “ 0 < ms_binary M /\ ms_binary M mod 2 = 0 ” &&
  (clause_hdr_addr (ms_binary M) # Int |-> 4 **
   clause_lits_addr (ms_binary M) # Int |->_ **
   (clause_lits_addr (ms_binary M) + sizeof(INT)) # Int |->_).
Proof.
  intros M Hshape. unfold solver_binary_rep.
  apply binary_scratch_open_for_write.
  unfold solver_shape in Hshape. tauto.
Qed.

Module MiniSatTarget.

Definition two31 : Z := 2147483648.
Definition two32 : Z := 4294967296.
Definition two64 : Z := 18446744073709551616.
Definition lo64 (x : Z) : Z := x mod two64.
Definition lo32 (x : Z) : Z := x mod two32.
Definition signed_low32 (x : Z) : Z :=
  let y := lo32 x in
  if y <? two31 then y else y - two32.
Definition uint64_sum_to_int (left right : Z) : Z :=
  signed_low32 (lo64 (left + right)).

End MiniSatTarget.

Lemma minisat_signed32_cast_eq_signed_low32 : forall x,
  signed_last_nbits x 32 = MiniSatTarget.signed_low32 x.
Proof.
  intros x.
  unfold signed_last_nbits, MiniSatTarget.signed_low32,
    MiniSatTarget.lo32, MiniSatTarget.two31, MiniSatTarget.two32.
  change
    ((if Coqlib.zlt (x mod 4294967296) 2147483648
      then x mod 4294967296
      else x mod 4294967296 - 4294967296) =
     (if (x mod 4294967296 <? 2147483648)
      then x mod 4294967296
      else x mod 4294967296 - 4294967296)).
  destruct (Coqlib.zlt (x mod 4294967296) 2147483648)
    as [Hlt | Hge].
  - assert (Htest : (x mod 4294967296 <? 2147483648) = true).
    { apply Z.ltb_lt. lia. }
    rewrite Htest. reflexivity.
  - assert (Htest : (x mod 4294967296 <? 2147483648) = false).
    { apply Z.ltb_ge. lia. }
    rewrite Htest. reflexivity.
Qed.

Lemma minisat_signed32_sum_cast_eq_uint64_sum_to_int : forall x y,
  signed_last_nbits (x + y) 32 = MiniSatTarget.uint64_sum_to_int x y.
Proof.
  intros x y.
  unfold MiniSatTarget.uint64_sum_to_int.
  rewrite <- minisat_signed32_cast_eq_signed_low32.
  change
    (signed_last_nbits (x + y) 32 =
     signed_last_nbits (unsigned_last_nbits (x + y) 64) 32).
  symmetry.
  apply signed_unsigned_revolutive_less; lia.
Qed.


(** Type-only carrier for opaque or intentionally abstracted double results.
    Unlike IEEE equality, this remains true for NaNs as well as ordinary values. *)
Definition msat_fp64_value (_ : fp64) : Prop := True.

(** Structural identity for binary32 values.  IEEE [fp32_eq] is deliberately
    not used here: it is false when both operands are the same NaN payload. *)
Definition msat_fp32_same (x y : fp32) : Prop := x = y.

Definition double_Znth (i : Z) (values : list fp64) : fp64 :=
  Znth i values msat_fp64_zero.

(** The part of a concrete double array left after focusing two distinct
    live indices.  The two omitted cells remain explicit in C annotations so
    symbolic execution can read them; this predicate owns every other cell. *)
Definition double_array_missing2
    (base i j n : Z) (values : list fp64) : Assertion :=
  “ Zlength values = n ” &&
  (if i <? j then
     DoubleArray.seg base 0 i (sublist 0 i values) **
     DoubleArray.seg base (i + 1) j (sublist (i + 1) j values) **
     DoubleArray.seg base (j + 1) n (sublist (j + 1) n values)
   else
     DoubleArray.seg base 0 j (sublist 0 j values) **
     DoubleArray.seg base (j + 1) i (sublist (j + 1) i values) **
     DoubleArray.seg base (i + 1) n (sublist (i + 1) n values)).

Definition lit_encode (l : literal) : Z :=
  match l with
  | Pos x => 2 * x
  | Neg x => 2 * x + 1
  end.

Definition lit_sign_c (l : Z) : Z := if Z.odd l then 1 else 0.

(** ----- parity toolbox for [lit_neg_c] ----- *)

Lemma land_1_mod2 : forall l, Z.land l 1 = l mod 2.
Proof.
  intros l.
  assert (H : Z.land l (Z.ones 1) = l mod 2 ^ 1) by (apply Z.land_ones; lia).
  replace (Z.ones 1) with 1 in H by reflexivity.
  replace (2 ^ 1) with 2 in H by reflexivity.
  exact H.
Qed.

Lemma one_div_two : 1 / 2 = 0.
Proof. reflexivity. Qed.

Lemma lit_neg_c_even : forall l, Z.even l = true -> lit_neg_c l = l + 1.
Proof.
  intros l Hev. unfold lit_neg_c. symmetry.
  apply Z.add_nocarry_lxor.
  rewrite land_1_mod2.
  apply Z.even_spec in Hev. destruct Hev as [k ->].
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma lit_neg_c_odd : forall l, Z.odd l = true -> lit_neg_c l = l - 1.
Proof.
  intros l Hod.
  assert (Hev : Z.even (l - 1) = true).
  { apply Z.odd_spec in Hod. destruct Hod as [k ->].
    apply Z.even_spec. exists k. lia. }
  apply lit_neg_c_even in Hev.
  unfold lit_neg_c in *.
  assert (Hrw : Z.lxor (Z.lxor (l - 1) 1) 1 = l - 1).
  { rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity. }
  rewrite Hev in Hrw.
  replace (l - 1 + 1) with l in Hrw by lia.
  exact Hrw.
Qed.

Lemma lit_neg_c_involutive : forall l, lit_neg_c (lit_neg_c l) = l.
Proof.
  intros l. unfold lit_neg_c.
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
Qed.

Lemma lit_neg_c_odd_parity : forall l,
  Z.odd (lit_neg_c l) = negb (Z.odd l).
Proof.
  intros l. destruct (Z.odd l) eqn:Hod.
  - rewrite lit_neg_c_odd by assumption. simpl.
    apply Z.odd_spec in Hod. destruct Hod as [k ->].
    replace (2 * k + 1 - 1) with (0 + 2 * k) by lia.
    rewrite Z.odd_add_mul_2. reflexivity.
  - assert (Hev : Z.even l = true).
    { rewrite <- Z.negb_odd, Hod. reflexivity. }
    rewrite lit_neg_c_even by assumption. simpl.
    apply Z.even_spec in Hev. destruct Hev as [k ->].
    replace (2 * k + 1) with (1 + 2 * k) by lia.
    rewrite Z.odd_add_mul_2. reflexivity.
Qed.

Lemma lit_var_c_neg : forall l, lit_var_c (lit_neg_c l) = lit_var_c l.
Proof.
  intros l. unfold lit_var_c. destruct (Z.odd l) eqn:Hod.
  - rewrite lit_neg_c_odd by assumption.
    apply Z.odd_spec in Hod. destruct Hod as [k ->].
    replace (2 * k + 1 - 1) with (k * 2) by lia.
    replace (2 * k + 1) with (k * 2 + 1) by lia.
    rewrite Z.div_add_l by lia. rewrite Z_div_mult_full by lia.
    rewrite one_div_two. lia.
  - assert (Hev : Z.even l = true).
    { rewrite <- Z.negb_odd, Hod. reflexivity. }
    rewrite lit_neg_c_even by assumption.
    apply Z.even_spec in Hev. destruct Hev as [k ->].
    replace (2 * k) with (k * 2) by lia.
    replace (k * 2 + 1) with (k * 2 + 1) by lia.
    rewrite Z.div_add_l by lia. rewrite Z_div_mult_full by lia.
    rewrite one_div_two. lia.
Qed.

Lemma lit_denote_neg : forall l,
  0 <= l -> lit_denote (lit_neg_c l) = literal_neg (lit_denote l).
Proof.
  intros l _. unfold lit_denote, literal_neg.
  rewrite lit_neg_c_odd_parity.
  assert (Hv : lit_var_c (lit_neg_c l) = lit_var_c l) by apply lit_var_c_neg.
  unfold lit_var_c in Hv.
  destruct (Z.odd l); simpl; rewrite Hv; reflexivity.
Qed.

Lemma lit_var_c_denote : forall l, literal_var (lit_denote l) = lit_var_c l.
Proof.
  intros l. unfold lit_denote, lit_var_c, literal_var.
  destruct (Z.odd l); reflexivity.
Qed.

Lemma lit_denote_wf : forall n l, lit_wf_c n l -> literal_wf n (lit_denote l).
Proof.
  intros n l [Hlo Hhi].
  unfold literal_wf, var_in_range. rewrite lit_var_c_denote.
  unfold lit_var_c. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma lit_encode_wf : forall n l,
  literal_wf n l -> lit_wf_c n (lit_encode l).
Proof.
  intros n [x|x] Hwf;
    unfold literal_wf, var_in_range, literal_var in Hwf;
    unfold lit_wf_c, lit_encode;
    lia.
Qed.

Lemma lit_denote_encode : forall n l,
  literal_wf n l -> lit_denote (lit_encode l) = l.
Proof.
  intros n [x|x] Hwf;
    unfold literal_wf, var_in_range, literal_var in Hwf.
  - unfold lit_encode, lit_denote.
    assert (Ho : Z.odd (2 * x) = false)
      by (rewrite Z.odd_mul; reflexivity).
    assert (Hd : (2 * x) / 2 = x).
    { replace (2 * x) with (x * 2) by lia.
      apply Z_div_mult_full. lia. }
    rewrite Ho, Hd. reflexivity.
  - unfold lit_encode, lit_denote.
    assert (Ho : Z.odd (2 * x + 1) = true).
    { replace (2 * x + 1) with (Z.succ (2 * x)) by lia.
      rewrite Z.odd_succ, Z.even_mul. reflexivity. }
    assert (Hd : (2 * x + 1) / 2 = x).
    { replace (2 * x + 1) with (1 + x * 2) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
    rewrite Ho, Hd. reflexivity.
Qed.

Lemma lit_encode_denote : forall n l,
  lit_wf_c n l -> lit_encode (lit_denote l) = l.
Proof.
  intros n l Hwf. unfold lit_encode, lit_denote.
  destruct (Z.odd l) eqn:Hodd.
  - apply Z.odd_spec in Hodd. destruct Hodd as [k Hk]. subst l.
    replace ((2 * k + 1) / 2) with k.
    + lia.
    + replace (2 * k + 1) with (1 + k * 2) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
  - assert (Heven : Z.even l = true).
    { rewrite <- Z.negb_odd, Hodd. reflexivity. }
    apply Z.even_spec in Heven. destruct Heven as [k Hk]. subst l.
    replace ((2 * k) / 2) with k.
    + lia.
    + replace (2 * k) with (k * 2) by lia.
      symmetry. apply Z_div_mult_full. lia.
Qed.

Lemma lit_neg_c_wf : forall n l, lit_wf_c n l -> lit_wf_c n (lit_neg_c l).
Proof.
  intros n l [Hlo Hhi]. unfold lit_wf_c. destruct (Z.odd l) eqn:Hod.
  - rewrite lit_neg_c_odd by assumption.
    apply Z.odd_spec in Hod. destruct Hod as [k Hk]. lia.
  - assert (Hev : Z.even l = true).
    { rewrite <- Z.negb_odd, Hod. reflexivity. }
    rewrite lit_neg_c_even by assumption.
    apply Z.even_spec in Hev. destruct Hev as [k Hk]. lia.
Qed.

Lemma lit_sign_c_range : forall l, 0 <= lit_sign_c l <= 1.
Proof. intros l. unfold lit_sign_c. destruct (Z.odd l); lia. Qed.

Lemma lit_pack_unpack : forall l,
  0 <= l -> 2 * lit_var_c l + lit_sign_c l = l.
Proof.
  intros l _. unfold lit_var_c, lit_sign_c.
  destruct (Z.odd l) eqn:Hod.
  - apply Z.odd_spec in Hod. destruct Hod as [k ->].
    replace (2 * k + 1) with (k * 2 + 1) by lia.
    rewrite Z.div_add_l by lia. rewrite one_div_two. lia.
  - assert (Hev : Z.even l = true).
    { rewrite <- Z.negb_odd, Hod. reflexivity. }
    apply Z.even_spec in Hev. destruct Hev as [k ->].
    replace (2 * k) with (k * 2) by lia.
    rewrite Z_div_mult_full by lia. lia.
Qed.

Lemma lbool_val_true : forall v, lbool_val v = Some true <-> v = 1.
Proof.
  intros v. unfold lbool_val. split; intros H.
  - destruct (v =? 1) eqn:H1; [ apply Z.eqb_eq in H1; assumption |].
    destruct (v =? -1); discriminate.
  - subst. reflexivity.
Qed.

Lemma lbool_val_false : forall v, lbool_val v = Some false <-> v = -1.
Proof.
  intros v. unfold lbool_val. split; intros H.
  - destruct (v =? 1) eqn:H1; [discriminate|].
    destruct (v =? -1) eqn:H2; [ apply Z.eqb_eq in H2; assumption | discriminate].
  - subst. reflexivity.
Qed.

Lemma eval_denote : forall assigns l, 0 <= l ->
  eval_partial_literal (assigns_pv assigns) (lit_denote l)
  = match lbool_val (Znth (lit_var_c l) assigns 0) with
    | None => None
    | Some b => Some (if Z.odd l then negb b else b)
    end.
Proof.
  intros assigns l _.
  unfold eval_partial_literal, assigns_pv, assigns_val, lit_denote, lit_var_c.
  destruct (Z.odd l); simpl;
    destruct (lbool_val (Znth (l / 2) assigns 0)) as [b|]; reflexivity.
Qed.

Lemma lit_true_iff : forall assigns l, 0 <= l ->
  Znth (lit_var_c l) assigns 0 = lit_sig l
  <-> eval_partial_literal (assigns_pv assigns) (lit_denote l) = Some true.
Proof.
  intros assigns l Hl. rewrite eval_denote by assumption.
  unfold lit_sig. split; intros H.
  - rewrite H. destruct (Z.odd l).
    + rewrite (proj2 (lbool_val_false _) eq_refl). reflexivity.
    + rewrite (proj2 (lbool_val_true _) eq_refl). reflexivity.
  - destruct (lbool_val (Znth (lit_var_c l) assigns 0)) as [b|] eqn:Hb;
      [|discriminate].
    destruct (Z.odd l).
    + destruct b; simpl in H; [discriminate|].
      apply lbool_val_false. exact Hb.
    + destruct b; simpl in H; [|discriminate].
      apply lbool_val_true. exact Hb.
Qed.

Lemma lit_false_iff : forall assigns l, 0 <= l ->
  Znth (lit_var_c l) assigns 0 = - lit_sig l
  <-> eval_partial_literal (assigns_pv assigns) (lit_denote l) = Some false.
Proof.
  intros assigns l Hl. rewrite eval_denote by assumption.
  unfold lit_sig. split; intros H.
  - destruct (Z.odd l).
    + assert (Hv : Znth (lit_var_c l) assigns 0 = 1) by lia.
      rewrite Hv. reflexivity.
    + assert (Hv : Znth (lit_var_c l) assigns 0 = -1) by lia.
      rewrite Hv. reflexivity.
  - destruct (lbool_val (Znth (lit_var_c l) assigns 0)) as [b|] eqn:Hb;
      [|discriminate].
    destruct (Z.odd l).
    + destruct b; simpl in H; [|discriminate].
      apply lbool_val_true in Hb. lia.
    + destruct b; simpl in H; [discriminate|].
      apply lbool_val_false in Hb. lia.
Qed.

Lemma lit_neg_true_iff_false : forall assigns l, 0 <= l ->
  eval_partial_literal (assigns_pv assigns) (lit_denote (lit_neg_c l)) = Some true
  <-> eval_partial_literal (assigns_pv assigns) (lit_denote l) = Some false.
Proof.
  intros assigns l Hl.
  rewrite lit_denote_neg by assumption.
  rewrite eval_partial_literal_neg.
  destruct (eval_partial_literal (assigns_pv assigns) (lit_denote l)) as [b|];
    simpl.
  - destruct b; simpl; split; intros H; try reflexivity; discriminate.
  - split; intros H; discriminate.
Qed.

(** ----- watcher tag codec ----- *)

Lemma tag_lit_of : forall l, tag_lit (tag_of_lit l) = l.
Proof.
  intros l. unfold tag_lit, tag_of_lit.
  replace (2 * l + 1) with (l * 2 + 1) by lia.
  rewrite Z.div_add_l by lia. rewrite one_div_two. lia.
Qed.

Lemma tag_of_lit_odd : forall l, Z.odd (tag_of_lit l) = true.
Proof.
  intros l. unfold tag_of_lit.
  replace (2 * l + 1) with (1 + 2 * l) by lia.
  rewrite Z.odd_add_mul_2. reflexivity.
Qed.

Lemma is_tag_of : forall l, is_tag (tag_of_lit l) = true.
Proof. intros l. unfold is_tag. apply tag_of_lit_odd. Qed.

Lemma even_not_tag : forall p, Z.even p = true -> is_tag p = false.
Proof.
  intros p H. unfold is_tag.
  rewrite <- Z.negb_even, H. reflexivity.
Qed.

Lemma is_tag_odd_inv : forall w, is_tag w = true -> tag_of_lit (tag_lit w) = w.
Proof.
  intros w H. unfold is_tag in H. unfold tag_of_lit, tag_lit.
  apply Z.odd_spec in H. destruct H as [k ->].
  replace (2 * k + 1) with (k * 2 + 1) by lia.
  rewrite Z.div_add_l by lia. rewrite one_div_two. lia.
Qed.

(** A tagged word with an in-range decoded literal is positive:
    an odd nonpositive word decodes to a negative literal. *)
Lemma tag_pos_of_lit_wf : forall n w,
  is_tag w = true -> lit_wf_c n (tag_lit w) -> 0 < w.
Proof.
  intros n w Ht [Hlo _].
  rewrite <- (is_tag_odd_inv w Ht). unfold tag_of_lit. lia.
Qed.

Lemma tag_of_lit_reason_wf : forall n p,
  lit_wf_c n p -> 0 < tag_of_lit p /\ lit_wf_c n (tag_lit (tag_of_lit p)).
Proof.
  intros n p Hp. rewrite tag_lit_of.
  destruct Hp as [Hlo Hhi].
  split; [unfold tag_of_lit; lia | split; lia].
Qed.

(** ----- clause-level denotation ----- *)

Lemma lits_denote_cons : forall l ls,
  lits_denote (l :: ls) = lit_denote l :: lits_denote ls.
Proof. reflexivity. Qed.

Lemma lits_denote_app : forall ls ms,
  lits_denote (ls ++ ms) = lits_denote ls ++ lits_denote ms.
Proof. intros. unfold lits_denote. apply map_app. Qed.

Lemma lits_denote_length : forall ls,
  Zlength (lits_denote ls) = Zlength ls.
Proof.
  intros ls. unfold lits_denote.
  rewrite !Zlength_correct, length_map. reflexivity.
Qed.

Lemma lits_denote_in : forall l ls,
  In l ls -> In (lit_denote l) (lits_denote ls).
Proof. intros l ls H. unfold lits_denote. apply in_map. exact H. Qed.

Lemma lits_denote_in_inv : forall L ls,
  In L (lits_denote ls) -> exists l, In l ls /\ lit_denote l = L.
Proof.
  intros L ls H. unfold lits_denote in H.
  apply in_map_iff in H. destruct H as [l [Heq Hin]].
  exists l. split; assumption.
Qed.

Lemma lits_denote_wf : forall n ls,
  Forall (lit_wf_c n) ls -> Forall (literal_wf n) (lits_denote ls).
Proof.
  intros n ls H. unfold lits_denote. rewrite Forall_map.
  eapply Forall_impl; [|exact H].
  intros l Hl. apply lit_denote_wf. exact Hl.
Qed.

Lemma map_literal_var_lits_denote : forall ls,
  map literal_var (lits_denote ls) = map lit_var_c ls.
Proof.
  intros ls. unfold lits_denote. rewrite map_map.
  apply map_ext. intros l. apply lit_var_c_denote.
Qed.

Lemma lits_denote_nodup_vars : forall ls,
  NoDup (map lit_var_c ls) -> NoDup (map literal_var (lits_denote ls)).
Proof.
  intros ls H. rewrite map_literal_var_lits_denote. exact H.
Qed.

(** ----- clause status through the bridge ----- *)

Lemma lits_denote_false_iff : forall assigns ls,
  Forall (fun l => 0 <= l) ls ->
  Forall (fun l => Znth (lit_var_c l) assigns 0 = - lit_sig l) ls ->
  clause_false (assigns_pv assigns) (lits_denote ls).
Proof.
  intros assigns ls Hpos Hval.
  rewrite Forall_forall in Hpos. rewrite Forall_forall in Hval.
  unfold clause_false. intros L Hin.
  apply lits_denote_in_inv in Hin. destruct Hin as [l [Hin Heq]].
  subst L. apply lit_false_iff; auto.
Qed.

Lemma ztake_ztake : forall a b l, 0 <= a <= b -> ztake a (ztake b l) = ztake a l.
Proof.
  intros a b l H. unfold ztake. rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma Forall_ztake : forall (P : Z -> Prop) k l, Forall P l -> Forall P (ztake k l).
Proof.
  intros P k l H. rewrite Forall_forall in *. intros x Hx.
  apply H. eapply In_ztake; eauto.
Qed.

Lemma Znth_zdrop : forall k l j d,
  0 <= k -> 0 <= j -> Znth j (zdrop k l) d = Znth (k + j) l d.
Proof.
  intros k l j d Hk Hj. unfold Znth, zdrop.
  rewrite nth_skipn.
  f_equal. lia.
Qed.

Lemma NoDup_snoc : forall (xs : list Z) y, NoDup xs -> ~ In y xs -> NoDup (xs ++ [y]).
Proof.
  induction xs as [|a xs IH]; intros y Hnd Hnin; simpl.
  - constructor; [intros []|constructor].
  - inversion Hnd as [|? ? Hna Hnd']; subst.
    constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|[Hin|[]]].
      * apply Hna; exact Hin.
      * apply Hnin. left. symmetry. exact Hin.
    + apply IH; [exact Hnd'|]. intro Hin. apply Hnin. right. exact Hin.
Qed.

Lemma In_Znth_index : forall (l : list Z) x,
  In x l -> exists j, 0 <= j < Zlength l /\ Znth j l 0 = x.
Proof.
  induction l as [|a l IH]; intros x Hin; simpl in Hin.
  - contradiction.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg l).
    destruct Hin as [<-|Hin].
    + exists 0. split; [lia|apply Znth0_cons].
    + destruct (IH x Hin) as [j [Hj Hval]].
      exists (j + 1). split; [lia|].
      rewrite Znth_cons by lia. replace (j + 1 - 1) with j by lia. exact Hval.
Qed.

Lemma Zlength_map_Z : forall (f : Z -> Z) l, Zlength (map f l) = Zlength l.
Proof. intros. rewrite !Zlength_correct, length_map. reflexivity. Qed.

Lemma count_le_app : forall i l1 l2,
  count_le i (l1 ++ l2) = count_le i l1 + count_le i l2.
Proof.
  intros i l1 l2; induction l1 as [|x l1 IH]; simpl; [lia|].
  rewrite IH. lia.
Qed.

Lemma count_le_length : forall i l, count_le i l <= Zlength l.
Proof.
  intros i l; induction l as [|x l IH]; simpl; [rewrite Zlength_nil; lia|].
  rewrite Zlength_cons. destruct (x <=? i); lia.
Qed.

Lemma count_le_none : forall i l, Forall (fun x => i < x) l -> count_le i l = 0.
Proof.
  intros i l H; induction H as [|x l Hx Hl IH]; simpl; [reflexivity|].
  assert (Hb : (x <=? i) = false) by (apply Z.leb_gt; lia).
  rewrite Hb, IH. lia.
Qed.

Lemma count_le_all : forall i l, Forall (fun x => x <= i) l -> count_le i l = Zlength l.
Proof.
  intros i l H; induction H as [|x l Hx Hl IH]; simpl;
    [rewrite Zlength_nil; reflexivity|].
  assert (Hb : (x <=? i) = true) by (apply Z.leb_le; lia).
  rewrite Hb, IH, Zlength_cons. lia.
Qed.

Lemma count_le_all_inv : forall i l,
  count_le i l = Zlength l -> Forall (fun x => x <= i) l.
Proof.
  intros i l; induction l as [|x l IH]; intros Hcount; constructor.
  - simpl in Hcount. rewrite Zlength_cons in Hcount.
    destruct (x <=? i) eqn:Hx.
    + apply Z.leb_le in Hx. exact Hx.
    + pose proof (count_le_length i l). lia.
  - apply IH. simpl in Hcount. rewrite Zlength_cons in Hcount.
    destruct (x <=? i); [lia|].
    pose proof (count_le_length i l). lia.
Qed.

Lemma strict_sorted_ztake : forall k l, strict_sorted l -> strict_sorted (ztake k l).
Proof.
  intros k l; revert k; induction l as [|a l IH]; intros k Hs.
  - unfold ztake; rewrite firstn_nil; exact I.
  - unfold ztake. destruct (Z.to_nat k) as [|m] eqn:Hm; [exact I|].
    simpl. destruct Hs as [Hall Hs]. split.
    + apply (Forall_ztake _ (Z.of_nat m)) in Hall.
      unfold ztake in Hall. rewrite Nat2Z.id in Hall. exact Hall.
    + apply (IH (Z.of_nat m)) in Hs. unfold ztake in Hs.
      rewrite Nat2Z.id in Hs. exact Hs.
Qed.

Lemma strict_sorted_snoc : forall l y,
  strict_sorted l -> Forall (fun x => x < y) l -> strict_sorted (l ++ [y]).
Proof.
  induction l as [|a l IH]; intros y Hs Hall; simpl.
  - split; [constructor|exact I].
  - destruct Hs as [Hfa Hs].
    inversion Hall as [|? ? Hay Hall']; subst.
    split.
    + apply Forall_app. split; [exact Hfa|constructor; [exact Hay|constructor]].
    + apply IH; assumption.
Qed.

Lemma strict_sorted_Znth : forall l i j,
  strict_sorted l -> 0 <= i -> i < j -> j < Zlength l -> Znth i l 0 < Znth j l 0.
Proof.
  induction l as [|a l IH]; intros i j Hs Hi Hij Hj.
  - rewrite Zlength_nil in Hj; lia.
  - rewrite Zlength_cons in Hj. pose proof (Zlength_nonneg l).
    destruct Hs as [Hall Hs].
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons, Znth_cons by lia.
      rewrite Forall_forall in Hall. apply Hall.
      apply Znth_In. lia.
    + rewrite !Znth_cons by lia. apply IH; try lia. exact Hs.
Qed.

Lemma strict_sorted_count_prefix : forall l i k,
  strict_sorted l -> 0 <= k < count_le i l -> Znth k l 0 <= i.
Proof.
  induction l as [|a l IH]; intros i k Hs [Hk0 Hk]; simpl in Hk.
  - lia.
  - destruct Hs as [Hall Hs].
    destruct (a <=? i) eqn:Ha.
    + apply Z.leb_le in Ha.
      destruct (Z.eq_dec k 0) as [->|Hk0'].
      * rewrite Znth0_cons; exact Ha.
      * rewrite Znth_cons by lia. apply IH; [exact Hs|lia].
    + apply Z.leb_gt in Ha.
      assert (Hz : count_le i l = 0).
      { apply count_le_none. revert Hall. apply Forall_impl. intros y Hy; lia. }
      lia.
Qed.

Lemma count_le_ztake : forall l i k,
  strict_sorted l -> 0 <= k -> count_le i l <= k ->
  count_le i (ztake k l) = count_le i l.
Proof.
  induction l as [|a l IH]; intros i k Hs Hk Hcnt.
  - unfold ztake; rewrite firstn_nil; reflexivity.
  - destruct Hs as [Hall Hs]. simpl in Hcnt.
    destruct (Z.eq_dec k 0) as [->|Hk0].
    + unfold ztake; simpl.
      pose proof (count_le_nonneg i l).
      destruct (a <=? i); [lia|]. simpl. lia.
    + unfold ztake. replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia.
      simpl.
      assert (Hrest : count_le i (ztake (k - 1) l) = count_le i l).
      { apply IH; [exact Hs|lia|].
        destruct (a <=? i) eqn:Ha; [lia|].
        apply Z.leb_gt in Ha.
        assert (count_le i l = 0).
        { apply count_le_none. revert Hall. apply Forall_impl. intros y Hy; lia. }
        lia. }
      unfold ztake in Hrest. rewrite Hrest. reflexivity.
Qed.

Lemma find_var_pos_app : forall v l1 l2,
  find_var_pos v (l1 ++ l2) =
  match find_var_pos v l1 with
  | Some k => Some k
  | None => option_map (Nat.add (List.length l1)) (find_var_pos v l2)
  end.
Proof.
  induction l1 as [|x l1 IH]; intros l2; simpl.
  - destruct (find_var_pos v l2) as [k|]; simpl; [f_equal; lia|reflexivity].
  - destruct (lit_var_c x =? v); [reflexivity|].
    rewrite IH.
    destruct (find_var_pos v l1) as [k|]; simpl; [reflexivity|].
    destruct (find_var_pos v l2) as [k|]; simpl; [f_equal; lia|reflexivity].
Qed.

Lemma find_var_pos_in : forall v l,
  In v (map lit_var_c l) -> exists k, find_var_pos v l = Some k.
Proof.
  intros v l Hin. destruct (find_var_pos v l) as [k|] eqn:Hf; [eauto|].
  exfalso. apply (proj1 (find_var_pos_none_iff v l) Hf). exact Hin.
Qed.

Lemma find_var_pos_min : forall v l k j,
  find_var_pos v l = Some k -> (j < k)%nat -> lit_var_c (nth j l 0) <> v.
Proof.
  induction l as [|x l IH]; intros k j H Hj; simpl in *; [discriminate|].
  destruct (lit_var_c x =? v) eqn:Hx.
  - inversion H; lia.
  - destruct (find_var_pos v l) as [i|] eqn:Hf; simpl in H; [|discriminate].
    inversion H; subst k.
    destruct j as [|j]; simpl.
    + apply Z.eqb_neq in Hx. exact Hx.
    + eapply IH; [reflexivity|lia].
Qed.

Lemma find_var_pos_prefix : forall v l1 l2 k,
  find_var_pos v (l1 ++ l2) = Some k -> (k < List.length l1)%nat ->
  find_var_pos v l1 = Some k.
Proof.
  intros v l1 l2 k H Hk. rewrite find_var_pos_app in H.
  destruct (find_var_pos v l1) as [j|]; [exact H|].
  destruct (find_var_pos v l2) as [j|]; simpl in H; [|discriminate].
  inversion H; lia.
Qed.

Lemma find_var_pos_ztake_lt : forall v l k b,
  find_var_pos v l = Some k -> (k < Z.to_nat b)%nat ->
  find_var_pos v (ztake b l) = Some k.
Proof.
  intros v l k b H Hk.
  pose proof (find_var_pos_bound v l k H) as Hlen.
  rewrite <- (ztake_zdrop b l) in H.
  apply find_var_pos_prefix in H; [exact H|].
  unfold ztake. rewrite length_firstn. lia.
Qed.

Lemma find_var_pos_ztake_none : forall v l k b,
  NoDup (map lit_var_c l) -> find_var_pos v l = Some k -> (Z.to_nat b <= k)%nat ->
  find_var_pos v (ztake b l) = None.
Proof.
  intros v l k b Hnd H Hk.
  apply find_var_pos_none_iff. intro Hin.
  apply in_map_iff in Hin. destruct Hin as [x [Hx Hxin]].
  assert (Hin' : In x (ztake b l)) by exact Hxin.
  destruct (In_Znth_index _ _ Hin') as [j [Hj Hjval]].
  assert (Hjb : j < b).
  { unfold ztake in Hj. rewrite Zlength_correct, length_firstn in Hj. lia. }
  assert (Hnth : lit_var_c (nth (Z.to_nat j) l 0) = v).
  { rewrite Znth_ztake in Hjval by lia. unfold Znth in Hjval.
    rewrite Hjval. exact Hx. }
  pose proof (Zlength_nonneg (ztake b l)).
  eapply find_var_pos_min; [exact H| |exact Hnth]. lia.
Qed.

Lemma find_var_pos_ztake_inv : forall v l b k,
  find_var_pos v (ztake b l) = Some k -> exists k', find_var_pos v l = Some k'.
Proof.
  intros v l b k H.
  apply find_var_pos_in.
  assert (Hin : In v (map lit_var_c (ztake b l))).
  { destruct (find_var_pos_none_iff v (ztake b l)) as [_ Hb].
    destruct (List.in_dec Z.eq_dec v (map lit_var_c (ztake b l))) as [Hi|Hi];
      [exact Hi|]. rewrite (Hb Hi) in H; discriminate. }
  apply in_map_iff in Hin. destruct Hin as [x [<- Hx]].
  apply in_map. eapply In_ztake; eauto.
Qed.

Definition lit_pol (l : Z) : bool := negb (Z.odd l).

Lemma lbool_val_lit_sig : forall l, lbool_val (lit_sig l) = Some (lit_pol l).
Proof. intro l. unfold lit_sig, lit_pol. destruct (Z.odd l); reflexivity. Qed.

Lemma lit_denote_satisfying : forall l,
  lit_denote l = satisfying_literal (lit_var_c l) (lit_pol l).
Proof.
  intro l. unfold lit_denote, satisfying_literal, lit_pol, lit_var_c.
  destruct (Z.odd l); reflexivity.
Qed.

Lemma lit_var_c_nonneg : forall n l, lit_wf_c n l -> 0 <= lit_var_c l.
Proof. intros n l H. apply (lit_var_c_in_range n l H). Qed.

(** *** The [assume] transient.
    After pushing [qtail] to [trail_lim] and before enqueue, the last limit
    equals the trail length. [mtrail_wf_pushed] relaxes [mtw_lim_range] from
    [<] to [<=] for this interval; the transition lemmas consume that carrier. *)
Record mtrail_wf_pushed (n : Z) (t : mtrail) : Prop := {
  mtwp_n_nonneg    : 0 <= n;
  mtwp_assigns_len : Zlength (mt_assigns t) = n;
  mtwp_levels_len  : Zlength (mt_levels t) = n;
  mtwp_cells       : Forall lbool_cell (mt_assigns t);
  mtwp_qhead_range : 0 <= mt_qhead t <= Zlength (mt_trail t);
  mtwp_trail_bound : Zlength (mt_trail t) <= n;
  mtwp_trail_lits  : Forall (lit_wf_c n) (mt_trail t);
  mtwp_trail_nodup : NoDup (map lit_var_c (mt_trail t));
  mtwp_trail_true  :
    Forall (fun l => Znth (lit_var_c l) (mt_assigns t) 0 = lit_sig l) (mt_trail t);
  mtwp_lim_sorted  : strict_sorted (mt_lim t);
  mtwp_lim_range   : Forall (fun b => 0 <= b <= Zlength (mt_trail t)) (mt_lim t);
  mtwp_levels_agree :
    forall i, 0 <= i < Zlength (mt_trail t) ->
      Znth (trail_var t i) (mt_levels t) 0 = level_of_index t i;
  mtwp_assigned_iff :
    forall v, 0 <= v < n ->
      (Znth v (mt_assigns t) 0 <> 0 <-> In v (map lit_var_c (mt_trail t)))
}.

Arguments mtwp_n_nonneg {n t} _.

Arguments mtwp_assigns_len {n t} _.

Arguments mtwp_levels_len {n t} _.

Arguments mtwp_cells {n t} _.

Arguments mtwp_qhead_range {n t} _.

Arguments mtwp_trail_bound {n t} _.

Arguments mtwp_trail_lits {n t} _.

Arguments mtwp_trail_nodup {n t} _.

Arguments mtwp_trail_true {n t} _.

Arguments mtwp_lim_sorted {n t} _.

Arguments mtwp_lim_range {n t} _.

Arguments mtwp_levels_agree {n t} _.

Arguments mtwp_assigned_iff {n t} _.

Lemma mtrail_wf_pushed_of_wf : forall n t, mtrail_wf n t -> mtrail_wf_pushed n t.
Proof.
  intros n t Hwf. constructor.
  - exact (mtw_n_nonneg Hwf).
  - exact (mtw_assigns_len Hwf).
  - exact (mtw_levels_len Hwf).
  - exact (mtw_cells Hwf).
  - exact (mtw_qhead_range Hwf).
  - exact (mtw_trail_bound Hwf).
  - exact (mtw_trail_lits Hwf).
  - exact (mtw_trail_nodup Hwf).
  - exact (mtw_trail_true Hwf).
  - exact (mtw_lim_sorted Hwf).
  - pose proof (mtw_lim_range Hwf) as HF. revert HF.
    apply Forall_impl. intros b Hb. lia.
  - exact (mtw_levels_agree Hwf).
  - exact (mtw_assigned_iff Hwf).
Qed.

(** [s->qhead++] and the [qhead = qtail] resets. *)
Definition mt_set_qhead (t : mtrail) (q : Z) : mtrail :=
  {| mt_assigns := mt_assigns t;
     mt_levels  := mt_levels t;
     mt_trail   := mt_trail t;
     mt_lim     := mt_lim t;
     mt_qhead   := q |}.

Lemma mtrail_wf_set_qhead : forall n t q,
  mtrail_wf n t ->
  0 <= q <= Zlength (mt_trail t) ->
  mtrail_wf n (mt_set_qhead t q).
Proof.
  intros n t q Hwf Hq. destruct Hwf. constructor; simpl; assumption.
Qed.

Lemma prop_level_unpropagated_current : forall t i,
  prop_level t -> mt_qhead t <= i -> level_of_index t i = Zlength (mt_lim t).
Proof.
  intros t i Hp Hi. unfold level_of_index. apply count_le_all.
  revert Hp. apply Forall_impl. intros b Hb. lia.
Qed.

Lemma prop_level_processed_level_le : forall t i,
  level_of_index t i <= Zlength (mt_lim t).
Proof. intros t i. apply count_le_length. Qed.

Lemma trail_lit_nonneg : forall n t i,
  mtrail_wf n t -> 0 <= i < Zlength (mt_trail t) -> 0 <= Znth i (mt_trail t) 0.
Proof.
  intros n t i Hwf Hi.
  pose proof (Forall_Znth_elim _ _ _ 0 i (mtw_trail_lits Hwf) Hi) as [H _]. lia.
Qed.

Lemma view_of_rank : forall n t r db,
  assignment_rank (view_of n t r db) = trail_pos t.
Proof. reflexivity. Qed.

Lemma trail_pos_of_index : forall t i,
  NoDup (map lit_var_c (mt_trail t)) -> 0 <= i < Zlength (mt_trail t) ->
  trail_pos t (trail_var t i) = Some (Z.to_nat i).
Proof.
  intros t i Hnd Hi.
  assert (Hin : In (trail_var t i) (map lit_var_c (mt_trail t))).
  { unfold trail_var. apply in_map. apply Znth_In. exact Hi. }
  destruct (find_var_pos_in _ _ Hin) as [k Hk].
  assert (Hkv : trail_var t (Z.of_nat k) = trail_var t i)
    by (apply trail_pos_var; exact Hk).
  pose proof (trail_pos_bound t _ _ Hk) as Hkb.
  unfold trail_pos. rewrite Hk. f_equal.
  assert (Hnodup_index : forall a b,
            0 <= a < Zlength (mt_trail t) -> 0 <= b < Zlength (mt_trail t) ->
            trail_var t a = trail_var t b -> a = b).
  { intros a b Ha Hb Heq.
    destruct (Z.eq_dec a b) as [->|Hne]; [reflexivity|exfalso].
    revert Hnd Ha Hb Heq Hne. unfold trail_var.
    generalize (mt_trail t). clear.
    intros l Hnd Ha Hb Heq Hne.
    assert (Hmap : NoDup (map lit_var_c l)) by exact Hnd.
    rewrite NoDup_nth_error in Hmap.
    specialize (Hmap (Z.to_nat a) (Z.to_nat b)).
    rewrite length_map in Hmap.
    assert (Hla : (Z.to_nat a < List.length l)%nat)
      by (rewrite Zlength_correct in Ha; lia).
    assert (Hlb : (Z.to_nat b < List.length l)%nat)
      by (rewrite Zlength_correct in Hb; lia).
    assert (Hnth : nth_error (map lit_var_c l) (Z.to_nat a) =
                   nth_error (map lit_var_c l) (Z.to_nat b)).
    { rewrite !nth_error_map.
      rewrite (nth_error_nth' l 0 Hla), (nth_error_nth' l 0 Hlb).
      simpl. unfold Znth in Heq. rewrite Heq. reflexivity. }
    specialize (Hmap Hla Hnth). lia. }
  apply Nat2Z.inj.
  rewrite Z2Nat.id by lia.
  apply Hnodup_index; [lia|lia|exact Hkv].
Qed.

Lemma mtrail_wf_trail_var_injective : forall n t i j,
  mtrail_wf n t ->
  0 <= i < Zlength (mt_trail t) ->
  0 <= j < Zlength (mt_trail t) ->
  trail_var t i = trail_var t j ->
  i = j.
Proof.
  intros n t i j Hwf Hi Hj Heq.
  pose proof (trail_pos_of_index t i (mtw_trail_nodup Hwf) Hi) as Hpi.
  pose proof (trail_pos_of_index t j (mtw_trail_nodup Hwf) Hj) as Hpj.
  rewrite Heq, Hpj in Hpi. inversion Hpi. lia.
Qed.

Definition mt_push_lim (t : mtrail) : mtrail :=
  {| mt_assigns := mt_assigns t;
     mt_levels  := mt_levels t;
     mt_trail   := mt_trail t;
     mt_lim     := mt_lim t ++ [Zlength (mt_trail t)];
     mt_qhead   := mt_qhead t |}.

Lemma mt_decide_push_lim : forall t l, mt_decide t l = mt_enqueue (mt_push_lim t) l.
Proof. reflexivity. Qed.

Lemma Zlength_clear_vars : forall ls a, Zlength (clear_vars ls a) = Zlength a.
Proof.
  induction ls as [|x ls IH]; intros a; simpl; [reflexivity|].
  rewrite IH, Zlength_replace_Znth. reflexivity.
Qed.

Lemma Forall_replace_nth : forall (P : Z -> Prop) (a : list Z) (m : nat) (v : Z),
  Forall P a -> P v -> Forall P (replace_nth m a v).
Proof.
  induction a as [|x a IH]; intros m v Ha Hv.
  - destruct m; simpl; constructor.
  - inversion Ha as [|? ? Hx Ha']; subst.
    destruct m as [|m]; simpl; constructor; try assumption.
    apply IH; assumption.
Qed.

Lemma Forall_replace_Znth : forall (P : Z -> Prop) i v a,
  Forall P a -> P v -> Forall P (replace_Znth i v a).
Proof. intros. unfold replace_Znth. apply Forall_replace_nth; assumption. Qed.

Lemma clear_vars_cells : forall ls a,
  Forall lbool_cell a -> Forall lbool_cell (clear_vars ls a).
Proof.
  induction ls as [|x ls IH]; intros a Ha; simpl; [exact Ha|].
  apply IH. apply Forall_replace_Znth; [exact Ha|right; left; reflexivity].
Qed.

(** ----- [mtrail_wf] preservation ----- *)

Lemma mtrail_wf_push : forall n t l lim',
  mtrail_wf_pushed n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  strict_sorted lim' ->
  Forall (fun b => 0 <= b < Zlength (mt_trail t) + 1) lim' ->
  (forall i, 0 <= i < Zlength (mt_trail t) ->
     count_le i lim' = count_le i (mt_lim t)) ->
  count_le (Zlength (mt_trail t)) lim' = Zlength lim' ->
  mtrail_wf n (mt_push t l lim').
Proof.
  intros n t l lim' Hwf Hlwf Hz Hsorted Hrange Hcount Hcountnew.
  pose proof (lit_var_c_in_range n l Hlwf) as Hv.
  pose proof (mtwp_assigns_len Hwf) as HAlen.
  pose proof (mtwp_levels_len Hwf) as HLlen.
  pose proof (mtwp_trail_lits Hwf) as HTlits.
  pose proof (mtwp_trail_nodup Hwf) as HTnd.
  pose proof (mtwp_trail_true Hwf) as HTtrue.
  pose proof (mtwp_trail_bound Hwf) as HTb.
  pose proof (mtwp_qhead_range Hwf) as HQ.
  pose proof (Zlength_nonneg (mt_trail t)) as HT0.
  assert (Hnin : ~ In (lit_var_c l) (map lit_var_c (mt_trail t))).
  { intro Hin. destruct (mtwp_assigned_iff Hwf (lit_var_c l) Hv) as [_ Hbwd].
    apply Hbwd in Hin. contradiction. }
  assert (HlenT : Zlength (mt_trail t ++ [l]) = Zlength (mt_trail t) + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hmapapp : map lit_var_c (mt_trail t ++ [l])
                    = map lit_var_c (mt_trail t) ++ [lit_var_c l])
    by (rewrite map_app; reflexivity).
  assert (Hnd' : NoDup (map lit_var_c (mt_trail t ++ [l]))).
  { rewrite Hmapapp. apply NoDup_snoc; assumption. }
  assert (Hlits' : Forall (lit_wf_c n) (mt_trail t ++ [l])).
  { apply Forall_app. split; [exact HTlits|constructor; [exact Hlwf|constructor]]. }
  assert (Hnbound : Zlength (mt_trail t) + 1 <= n).
  { assert (Hall : forall x, In x (map lit_var_c (mt_trail t ++ [l])) ->
                             0 <= x < n).
    { intros x Hx. apply in_map_iff in Hx. destruct Hx as [y [<- Hy]].
      apply (lit_var_c_in_range n). rewrite Forall_forall in Hlits'. auto. }
    pose proof (NoDup_Z_bounded_length _ n (mtwp_n_nonneg Hwf) Hnd' Hall) as Hle.
    assert (Heq : Zlength (mt_trail t ++ [l])
                  = Zlength (map lit_var_c (mt_trail t ++ [l])))
      by (rewrite Zlength_map_Z; reflexivity).
    rewrite <- HlenT, Heq, Zlength_correct. exact Hle. }
  assert (HvA : 0 <= lit_var_c l < Zlength (mt_assigns t)) by (rewrite HAlen; exact Hv).
  assert (HvL : 0 <= lit_var_c l < Zlength (mt_levels t)) by (rewrite HLlen; exact Hv).
  assert (HkA : forall k, In k (mt_trail t) ->
                  0 <= lit_var_c k < Zlength (mt_assigns t)).
  { intros k Hk. rewrite HAlen. apply (lit_var_c_in_range n).
    rewrite Forall_forall in HTlits. auto. }
  assert (HkL : forall k, In k (mt_trail t) ->
                  0 <= lit_var_c k < Zlength (mt_levels t)).
  { intros k Hk. rewrite HLlen. apply (lit_var_c_in_range n).
    rewrite Forall_forall in HTlits. auto. }
  assert (Hkne : forall k, In k (mt_trail t) -> lit_var_c l <> lit_var_c k).
  { intros k Hk Heq. apply Hnin. rewrite Heq. apply in_map. exact Hk. }
  unfold mt_push.
  constructor; cbn [mt_assigns mt_levels mt_trail mt_lim mt_qhead].
  - exact (mtwp_n_nonneg Hwf).
  - rewrite Zlength_replace_Znth. exact HAlen.
  - rewrite Zlength_replace_Znth. exact HLlen.
  - apply Forall_replace_Znth; [exact (mtwp_cells Hwf)|].
    destruct (lit_sig_values l) as [H|H]; rewrite H;
      [right; right; reflexivity|left; reflexivity].
  - rewrite HlenT. lia.
  - rewrite HlenT. exact Hnbound.
  - exact Hlits'.
  - exact Hnd'.
  - apply Forall_app. split.
    + rewrite Forall_forall. intros k Hk.
      rewrite (Znth_replace_Znth_Diff 0 (mt_assigns t) (lit_var_c l) (lit_var_c k)
                 (lit_sig l) HvA (HkA k Hk) (Hkne k Hk)).
      rewrite Forall_forall in HTtrue. auto.
    + constructor; [|constructor].
      apply Znth_replace_Znth_Same. exact HvA.
  - exact Hsorted.
  - rewrite HlenT. exact Hrange.
  - intros i Hi. rewrite HlenT in Hi.
    unfold trail_var, level_of_index. cbn [mt_trail mt_lim].
    destruct (Z.eq_dec i (Zlength (mt_trail t))) as [->|Hne].
    + rewrite app_Znth2 by lia.
      replace (Zlength (mt_trail t) - Zlength (mt_trail t)) with 0 by lia.
      rewrite Znth0_cons.
      rewrite Znth_replace_Znth_Same by exact HvL.
      symmetry. exact Hcountnew.
    + rewrite app_Znth1 by lia.
      assert (Hk : In (Znth i (mt_trail t) 0) (mt_trail t))
        by (apply Znth_In; lia).
      rewrite (Znth_replace_Znth_Diff 0 (mt_levels t) (lit_var_c l)
                 (lit_var_c (Znth i (mt_trail t) 0)) (Zlength lim')
                 HvL (HkL _ Hk) (Hkne _ Hk)).
      rewrite Hcount by lia.
      assert (Hi' : 0 <= i < Zlength (mt_trail t)) by lia.
      exact (mtwp_levels_agree Hwf i Hi').
  - intros w Hw. rewrite Hmapapp.
    destruct (Z.eq_dec w (lit_var_c l)) as [->|Hne].
    + rewrite Znth_replace_Znth_Same by exact HvA.
      split.
      * intros _. apply in_or_app. right. left. reflexivity.
      * intros _. apply lit_sig_nonzero.
    + assert (HwA : 0 <= w < Zlength (mt_assigns t)) by (rewrite HAlen; exact Hw).
      rewrite (Znth_replace_Znth_Diff 0 (mt_assigns t) (lit_var_c l) w
                 (lit_sig l) HvA HwA (fun H => Hne (eq_sym H))).
      rewrite (mtwp_assigned_iff Hwf w Hw).
      split.
      * intro Hin. apply in_or_app. left. exact Hin.
      * intro Hin. apply in_app_or in Hin.
        destruct Hin as [Hin|[Hin|[]]]; [exact Hin|].
        exfalso. apply Hne. symmetry. exact Hin.
Qed.

Lemma mtrail_wf_enqueue : forall n t l,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  mtrail_wf n (mt_enqueue t l).
Proof.
  intros n t l Hwf Hlwf Hz. unfold mt_enqueue.
  apply (mtrail_wf_pushed_of_wf n t) in Hwf.
  apply mtrail_wf_push; try assumption.
  - exact (mtwp_lim_sorted Hwf).
  - revert Hwf. clear. intro Hwf.
    pose proof (mtwp_lim_range Hwf) as HF. revert HF. apply Forall_impl.
    intros b Hb. lia.
  - intros i Hi. reflexivity.
  - apply count_le_all.
    pose proof (mtwp_lim_range Hwf) as HF. revert HF. apply Forall_impl.
    intros b Hb. lia.
Qed.

Lemma mtrail_wf_pushed_lim : forall n t,
  mtrail_wf n t -> mtrail_wf_pushed n (mt_push_lim t).
Proof.
  intros n t Hwf.
  pose proof (mtw_lim_range Hwf) as HF.
  pose proof (Zlength_nonneg (mt_trail t)) as HT0.
  unfold mt_push_lim.
  constructor; cbn [mt_assigns mt_levels mt_trail mt_lim mt_qhead].
  - exact (mtw_n_nonneg Hwf).
  - exact (mtw_assigns_len Hwf).
  - exact (mtw_levels_len Hwf).
  - exact (mtw_cells Hwf).
  - exact (mtw_qhead_range Hwf).
  - exact (mtw_trail_bound Hwf).
  - exact (mtw_trail_lits Hwf).
  - exact (mtw_trail_nodup Hwf).
  - exact (mtw_trail_true Hwf).
  - apply strict_sorted_snoc; [exact (mtw_lim_sorted Hwf)|].
    revert HF. apply Forall_impl. intros b Hb. lia.
  - apply Forall_app. split.
    + revert HF. apply Forall_impl. intros b Hb. lia.
    + constructor; [lia|constructor].
  - intros i Hi. unfold trail_var, level_of_index. cbn [mt_trail mt_lim].
    rewrite count_le_app. simpl.
    assert (Hb : (Zlength (mt_trail t) <=? i) = false) by (apply Z.leb_gt; lia).
    rewrite Hb.
    pose proof (mtw_levels_agree Hwf i Hi) as He.
    unfold trail_var, level_of_index in He. lia.
  - exact (mtw_assigned_iff Hwf).
Qed.

Lemma mtrail_wf_pushed_lim_enqueue : forall n t l,
  mtrail_wf_pushed n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  mtrail_wf n (mt_enqueue t l).
Proof.
  intros n t l Hwf Hlwf Hz. unfold mt_enqueue.
  apply mtrail_wf_push; try assumption.
  - exact (mtwp_lim_sorted Hwf).
  - pose proof (mtwp_lim_range Hwf) as HF. revert HF. apply Forall_impl.
    intros b Hb. lia.
  - intros i Hi. reflexivity.
  - apply count_le_all.
    pose proof (mtwp_lim_range Hwf) as HF. revert HF. apply Forall_impl.
    intros b Hb. lia.
Qed.

Lemma mtrail_wf_decide_via_transient : forall n t l,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  mtrail_wf n (mt_enqueue (mt_push_lim t) l).
Proof.
  intros n t l Hwf Hlwf Hz.
  apply mtrail_wf_pushed_lim_enqueue; [apply mtrail_wf_pushed_lim; exact Hwf | exact Hlwf |].
  cbn [mt_assigns mt_push_lim]. exact Hz.
Qed.

Lemma mtrail_wf_decide : forall n t l,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  mtrail_wf n (mt_decide t l).
Proof.
  intros n t l Hwf Hlwf Hz. rewrite mt_decide_push_lim.
  apply mtrail_wf_decide_via_transient; assumption.
Qed.

Lemma mtrail_wf_cancel : forall n t level,
  mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
  mtrail_wf n (mt_cancel t level).
Proof.
  intros n t level Hwf Hlevel.
  pose proof (lim_lt_trail n t level Hwf Hlevel) as Hb.
  unfold mt_cancel.
  set (bound := Znth level (mt_lim t) 0) in *.
  pose proof (mtw_assigns_len Hwf) as HAlen.
  pose proof (mtw_trail_lits Hwf) as HTlits.
  pose proof (mtw_trail_nodup Hwf) as HTnd.
  pose proof (mtw_trail_true Hwf) as HTtrue.
  assert (HmapS : map lit_var_c (mt_trail t)
                  = map lit_var_c (ztake bound (mt_trail t))
                    ++ map lit_var_c (zdrop bound (mt_trail t)))
    by apply map_ztake_zdrop.
  assert (HndS : NoDup (map lit_var_c (ztake bound (mt_trail t))
                        ++ map lit_var_c (zdrop bound (mt_trail t))))
    by (rewrite <- HmapS; exact HTnd).
  assert (Hlen : Zlength (ztake bound (mt_trail t)) = bound)
    by (apply Zlength_ztake; lia).
  assert (Hdroprange : forall x, In x (zdrop bound (mt_trail t)) ->
                         0 <= lit_var_c x < Zlength (mt_assigns t)).
  { intros x Hx. rewrite HAlen. apply (lit_var_c_in_range n).
    rewrite Forall_forall in HTlits. apply HTlits. eapply In_zdrop; eauto. }
  assert (Hkeep : forall k, In k (ztake bound (mt_trail t)) ->
                    Znth (lit_var_c k)
                      (clear_vars (zdrop bound (mt_trail t)) (mt_assigns t)) 0
                    = Znth (lit_var_c k) (mt_assigns t) 0).
  { intros k Hk. apply clear_vars_notin.
    - rewrite HAlen. apply (lit_var_c_in_range n).
      rewrite Forall_forall in HTlits. apply HTlits. eapply In_ztake; eauto.
    - exact Hdroprange.
    - eapply NoDup_app_disjoint; [exact HndS|apply in_map; exact Hk]. }
  constructor; cbn [mt_assigns mt_levels mt_trail mt_lim mt_qhead].
  - exact (mtw_n_nonneg Hwf).
  - rewrite Zlength_clear_vars. exact HAlen.
  - exact (mtw_levels_len Hwf).
  - apply clear_vars_cells. exact (mtw_cells Hwf).
  - rewrite Hlen. lia.
  - rewrite Hlen. pose proof (mtw_trail_bound Hwf). lia.
  - apply Forall_ztake. exact HTlits.
  - eapply NoDup_app_remove_r. exact HndS.
  - rewrite Forall_forall. intros k Hk.
    rewrite (Hkeep k Hk).
    rewrite Forall_forall in HTtrue. apply HTtrue. eapply In_ztake; eauto.
  - apply strict_sorted_ztake. exact (mtw_lim_sorted Hwf).
  - rewrite Hlen, Forall_forall. intros b Hb'.
    destruct (In_Znth_index _ _ Hb') as [j [Hj Hjval]].
    assert (Hjlen : Zlength (ztake level (mt_lim t)) = level)
      by (apply Zlength_ztake; lia).
    rewrite Hjlen in Hj.
    rewrite Znth_ztake in Hjval by lia.
    assert (Hjr : 0 <= j < Zlength (mt_lim t)) by lia.
    pose proof (Forall_Znth_elim _ _ _ 0 j (mtw_lim_range Hwf) Hjr) as Hjrange.
    cbv beta in Hjrange.
    split.
    + rewrite <- Hjval. lia.
    + rewrite <- Hjval. unfold bound.
      apply strict_sorted_Znth; [exact (mtw_lim_sorted Hwf)|lia|lia|lia].
  - intros i Hi. rewrite Hlen in Hi.
    unfold trail_var, level_of_index; cbn [mt_trail mt_lim].
    rewrite Znth_ztake by lia.
    assert (Hile : count_le i (mt_lim t) <= level).
    { destruct (Z_le_gt_dec (count_le i (mt_lim t)) level) as [H|H]; [exact H|].
      exfalso.
      assert (Hp : 0 <= level < count_le i (mt_lim t)) by lia.
      pose proof (strict_sorted_count_prefix (mt_lim t) i level
                    (mtw_lim_sorted Hwf) Hp) as Hcp.
      unfold bound in Hi. lia. }
    rewrite count_le_ztake;
      [ | exact (mtw_lim_sorted Hwf) | lia | exact Hile ].
    assert (Hi' : 0 <= i < Zlength (mt_trail t)) by lia.
    exact (mtw_levels_agree Hwf i Hi').
  - intros w Hw.
    assert (HwA : 0 <= w < Zlength (mt_assigns t)) by (rewrite HAlen; exact Hw).
    split.
    + intro Hne.
      assert (Hnotdrop : ~ In w (map lit_var_c (zdrop bound (mt_trail t)))).
      { intro Hin. apply Hne. apply clear_vars_in; assumption. }
      rewrite clear_vars_notin in Hne by assumption.
      destruct (mtw_assigned_iff Hwf w Hw) as [Hfwd _].
      specialize (Hfwd Hne). rewrite HmapS in Hfwd.
      apply in_app_or in Hfwd. destruct Hfwd as [H|H]; [exact H|contradiction].
    + intro Hin.
      assert (Hnotdrop : ~ In w (map lit_var_c (zdrop bound (mt_trail t))))
        by (eapply NoDup_app_disjoint; [exact HndS|exact Hin]).
      rewrite clear_vars_notin by assumption.
      destruct (mtw_assigned_iff Hwf w Hw) as [_ Hbwd].
      apply Hbwd. rewrite HmapS. apply in_or_app. left. exact Hin.
Qed.

(** ----- [prop_level] (INV-PROP-LEVEL) preservation ----- *)

Lemma prop_level_enqueue : forall t l, prop_level t -> prop_level (mt_enqueue t l).
Proof. intros t l H. exact H. Qed.

Lemma prop_level_qhead_advance : forall t q,
  prop_level t -> mt_qhead t <= q -> prop_level (mt_set_qhead t q).
Proof.
  intros t q H Hq. unfold prop_level, mt_set_qhead in *.
  cbn [mt_lim mt_qhead]. revert H. apply Forall_impl. intros b Hb. lia.
Qed.

Lemma prop_level_push_lim : forall t,
  prop_level t -> mt_qhead t = Zlength (mt_trail t) ->
  prop_level (mt_push_lim t).
Proof.
  intros t H Hq. unfold prop_level, mt_push_lim in *.
  cbn [mt_lim mt_qhead]. apply Forall_app. split; [exact H|].
  constructor; [lia|constructor].
Qed.

Lemma prop_level_decide : forall t l,
  prop_level t -> mt_qhead t = Zlength (mt_trail t) ->
  prop_level (mt_decide t l).
Proof.
  intros t l H Hq. rewrite mt_decide_push_lim.
  apply prop_level_enqueue. apply prop_level_push_lim; assumption.
Qed.

(** [solver_canceluntil] sets [qhead = qtail = trail_lim[level]] and
    truncates [trail_lim] to its first [level] entries, all of which are
    strictly below that bound -- so cancel *establishes* INV-PROP-LEVEL
    outright, no hypothesis on the pre-state needed. *)
Lemma prop_level_cancel : forall n t level,
  mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
  prop_level (mt_cancel t level).
Proof.
  intros n t level Hwf Hlev.
  unfold prop_level, mt_cancel. cbn [mt_lim mt_qhead].
  rewrite Forall_forall. intros b Hb.
  apply In_Znth_index in Hb. destruct Hb as [k [Hk Hval]].
  assert (Hklen : Zlength (ztake level (mt_lim t)) = level)
    by (apply Zlength_ztake; lia).
  rewrite Hklen in Hk.
  rewrite Znth_ztake in Hval by lia.
  rewrite <- Hval.
  pose proof (strict_sorted_Znth (mt_lim t) k level (mtw_lim_sorted Hwf)
                (proj1 Hk) (proj2 Hk) (proj2 Hlev)). lia.
Qed.

(** ===== E. the memory-to-view bridges for enqueue / assume ===== *)

Lemma trail_pos_push_new : forall n t l lim',
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  trail_pos (mt_push t l lim') (lit_var_c l) = Some (List.length (mt_trail t)).
Proof.
  intros n t l lim' Hwf Hlwf Hz.
  unfold trail_pos, mt_push; cbn [mt_trail].
  rewrite find_var_pos_app.
  assert (Hnone : find_var_pos (lit_var_c l) (mt_trail t) = None).
  { apply find_var_pos_none_iff. intro Hin.
    destruct (mtw_assigned_iff Hwf (lit_var_c l) (lit_var_c_in_range n l Hlwf))
      as [_ Hbwd].
    apply Hbwd in Hin. contradiction. }
  rewrite Hnone. simpl.
  rewrite Z.eqb_refl. simpl. f_equal. lia.
Qed.

Lemma trail_pos_push_other : forall t l lim' y,
  y <> lit_var_c l -> trail_pos (mt_push t l lim') y = trail_pos t y.
Proof.
  intros t l lim' y Hy. unfold trail_pos, mt_push; cbn [mt_trail].
  rewrite find_var_pos_app.
  destruct (find_var_pos y (mt_trail t)) as [k|]; [reflexivity|].
  simpl.
  assert (Hb : (lit_var_c l =? y) = false)
    by (apply Z.eqb_neq; intro H; apply Hy; symmetry; exact H).
  rewrite Hb. reflexivity.
Qed.

Lemma view_of_push_assignment : forall n t r db l lim',
  mtrail_wf n t -> lit_wf_c n l ->
  assignment (view_of n (mt_push t l lim') r db)
  = sat_function_update (assignment (view_of n t r db))
      (lit_var_c l) (Some (lit_pol l)).
Proof.
  intros n t r db l lim' Hwf Hlwf.
  pose proof (lit_var_c_in_range n l Hlwf) as Hv.
  pose proof (mtw_assigns_len Hwf) as HAlen.
  apply functional_extensionality. intro y.
  cbn [view_of assignment].
  destruct (Z_lt_le_dec y 0) as [Hyneg|Hy0].
  { rewrite sat_function_update_neq by lia.
    rewrite !mt_pv_neg by lia. reflexivity. }
  destruct (Z.eq_dec y (lit_var_c l)) as [->|Hne].
  - rewrite sat_function_update_eq.
    rewrite mt_pv_nonneg by lia.
    unfold mt_push; cbn [mt_assigns].
    rewrite Znth_replace_Znth_Same by (rewrite HAlen; exact Hv).
    apply lbool_val_lit_sig.
  - rewrite sat_function_update_neq by (intro H; apply Hne; symmetry; exact H).
    rewrite !mt_pv_nonneg by lia.
    unfold mt_push; cbn [mt_assigns].
    destruct (Z_lt_le_dec y (Zlength (mt_assigns t))) as [Hyl|Hyl].
    + rewrite (Znth_replace_Znth_Diff 0 (mt_assigns t) (lit_var_c l) y
                 (lit_sig l) (ltac:(rewrite HAlen; exact Hv)) (conj Hy0 Hyl)
                 (fun H => Hne (eq_sym H))).
      reflexivity.
    + assert (E1 : Znth y (replace_Znth (lit_var_c l) (lit_sig l) (mt_assigns t)) 0 = 0)
        by (apply znth_out_of_bounds; [lia|rewrite Zlength_replace_Znth; lia]).
      assert (E2 : Znth y (mt_assigns t) 0 = 0)
        by (apply znth_out_of_bounds; lia).
      rewrite E1, E2. reflexivity.
Qed.

Lemma view_of_push_level : forall n t r db l lim',
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  (forall i, 0 <= i < Zlength (mt_trail t) -> count_le i lim' = count_le i (mt_lim t)) ->
  count_le (Zlength (mt_trail t)) lim' = Zlength lim' ->
  level_of (view_of n (mt_push t l lim') r db)
  = sat_function_update (level_of (view_of n t r db)) (lit_var_c l)
      (Some (Zlength lim')).
Proof.
  intros n t r db l lim' Hwf Hlwf Hz Hcount Hcountnew.
  apply functional_extensionality. intro y.
  cbn [view_of level_of].
  destruct (Z.eq_dec y (lit_var_c l)) as [->|Hne].
  - rewrite sat_function_update_eq.
    rewrite (trail_pos_push_new n t l lim' Hwf Hlwf Hz).
    cbn [option_map]. unfold level_of_index, mt_push; cbn [mt_lim].
    rewrite <- Zlength_correct, Hcountnew. reflexivity.
  - rewrite sat_function_update_neq by (intro H; apply Hne; symmetry; exact H).
    rewrite (trail_pos_push_other t l lim' y Hne).
    destruct (trail_pos t y) as [k|] eqn:Hk; [|reflexivity].
    cbn [option_map]. unfold level_of_index, mt_push; cbn [mt_lim].
    f_equal. apply Hcount.
    pose proof (trail_pos_bound t y k Hk). lia.
Qed.

Lemma view_of_push_reason : forall n t r r' db l lim' rc,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  (forall y, y <> lit_var_c l -> r' y = r y) ->
  r' (lit_var_c l) = rc ->
  reason_of (view_of n (mt_push t l lim') r' db)
  = sat_function_update (reason_of (view_of n t r db)) (lit_var_c l) rc.
Proof.
  intros n t r r' db l lim' rc Hwf Hlwf Hz Hagree Hnew.
  apply functional_extensionality. intro y.
  cbn [view_of reason_of].
  destruct (Z.eq_dec y (lit_var_c l)) as [->|Hne].
  - rewrite sat_function_update_eq.
    rewrite (trail_pos_push_new n t l lim' Hwf Hlwf Hz). exact Hnew.
  - rewrite sat_function_update_neq by (intro H; apply Hne; symmetry; exact H).
    rewrite (trail_pos_push_other t l lim' y Hne).
    destruct (trail_pos t y) as [k|]; [apply Hagree; exact Hne|reflexivity].
Qed.

Lemma count_le_enqueue_new : forall n t,
  mtrail_wf n t -> count_le (Zlength (mt_trail t)) (mt_lim t) = Zlength (mt_lim t).
Proof.
  intros n t Hwf. apply count_le_all.
  pose proof (mtw_lim_range Hwf) as HF. revert HF. apply Forall_impl.
  intros b Hb. lia.
Qed.

Lemma count_le_decide_old : forall n t i,
  mtrail_wf n t -> 0 <= i < Zlength (mt_trail t) ->
  count_le i (mt_lim t ++ [Zlength (mt_trail t)]) = count_le i (mt_lim t).
Proof.
  intros n t i Hwf Hi. rewrite count_le_app. simpl.
  assert (Hb : (Zlength (mt_trail t) <=? i) = false) by (apply Z.leb_gt; lia).
  rewrite Hb. lia.
Qed.

Lemma count_le_decide_new : forall n t,
  mtrail_wf n t ->
  count_le (Zlength (mt_trail t)) (mt_lim t ++ [Zlength (mt_trail t)])
  = Zlength (mt_lim t ++ [Zlength (mt_trail t)]).
Proof.
  intros n t Hwf. rewrite count_le_app. simpl.
  assert (Hb : (Zlength (mt_trail t) <=? Zlength (mt_trail t)) = true)
    by (apply Z.leb_le; lia).
  rewrite Hb, Zlength_app, Zlength_cons, Zlength_nil.
  rewrite (count_le_enqueue_new n t Hwf). lia.
Qed.

Lemma view_of_assign : forall n t r r' db l rc,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  (forall y, y <> lit_var_c l -> r' y = r y) ->
  r' (lit_var_c l) = rc ->
  (forall c k, rc = Some c -> In k c -> literal_wf n k) ->
  assigns_one (view_of n t r db) (view_of n (mt_enqueue t l) r' db)
              (lit_var_c l) (lit_pol l) (Zlength (mt_lim t)) rc.
Proof.
  intros n t r r' db l rc Hwf Hlwf Hz Hagree Hnew Hrcwf.
  pose proof (lit_var_c_in_range n l Hlwf) as Hv.
  assert (HA : assignment (view_of n (mt_enqueue t l) r' db)
               = sat_function_update (assignment (view_of n t r db))
                   (lit_var_c l) (Some (lit_pol l)))
    by exact (view_of_push_assignment n t r db l (mt_lim t) Hwf Hlwf).
  assert (HL : level_of (view_of n (mt_enqueue t l) r' db)
               = sat_function_update (level_of (view_of n t r db))
                   (lit_var_c l) (Some (Zlength (mt_lim t))))
    by exact (view_of_push_level n t r db l (mt_lim t) Hwf Hlwf Hz
                (fun i _ => eq_refl) (count_le_enqueue_new n t Hwf)).
  assert (HR : reason_of (view_of n (mt_enqueue t l) r' db)
               = sat_function_update (reason_of (view_of n t r db))
                   (lit_var_c l) rc)
    by exact (view_of_push_reason n t r r' db l (mt_lim t) rc Hwf Hlwf Hz
                Hagree Hnew).
  unfold assigns_one.
  split. { cbn [view_of assignment]. apply mt_pv_zero_cell; [lia|exact Hz]. }
  split. { rewrite HA. apply sat_function_update_eq. }
  split. { rewrite HL. apply sat_function_update_eq. }
  split. { rewrite HR. apply sat_function_update_eq. }
  split.
  { exists (List.length (mt_trail t)).
    split.
    { cbn [view_of assignment_rank].
      apply (trail_pos_push_new n t l (mt_lim t) Hwf Hlwf Hz). }
    intros y [cc [ly [Hreason [Hin [Hvar [Hyx Heval]]]]]].
    rewrite HR, sat_function_update_eq in Hreason.
    assert (Hlywf : literal_wf n ly) by (apply (Hrcwf cc ly Hreason Hin)).
    destruct (eval_partial_literal_assigned _ _ _ Heval) as [b Hb].
    rewrite Hvar in Hb.
    rewrite HA, sat_function_update_neq in Hb
      by (intro H; apply Hyx; symmetry; exact H).
    cbn [view_of assignment] in Hb.
    destruct (trail_pos t y) as [k|] eqn:Hk.
    - exists k. split.
      + cbn [view_of assignment_rank]. unfold mt_enqueue.
        rewrite (trail_pos_push_other t l (mt_lim t) y Hyx). exact Hk.
      + apply (find_var_pos_bound y (mt_trail t) k Hk).
    - exfalso.
      assert (Hpv : mt_pv t y = None)
        by (apply (proj2 (view_unassigned_iff n t y Hwf)); exact Hk).
      rewrite Hpv in Hb. discriminate. }
  split.
  { intros y Hyx. repeat split.
    - rewrite HA. apply sat_function_update_neq.
      intro H; apply Hyx; symmetry; exact H.
    - rewrite HL. apply sat_function_update_neq.
      intro H; apply Hyx; symmetry; exact H.
    - rewrite HR. apply sat_function_update_neq.
      intro H; apply Hyx; symmetry; exact H.
    - cbn [view_of assignment_rank]. unfold mt_enqueue.
      apply trail_pos_push_other. exact Hyx. }
  reflexivity.
Qed.

Lemma view_of_decide_assign : forall n t r r' db l,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  (forall y, y <> lit_var_c l -> r' y = r y) ->
  r' (lit_var_c l) = None ->
  assigns_one (view_of n t r db) (view_of n (mt_decide t l) r' db)
              (lit_var_c l) (lit_pol l) (Zlength (mt_lim t) + 1) None.
Proof.
  intros n t r r' db l Hwf Hlwf Hz Hagree Hnew.
  pose proof (lit_var_c_in_range n l Hlwf) as Hv.
  set (lim' := mt_lim t ++ [Zlength (mt_trail t)]) in *.
  assert (Hlim' : Zlength lim' = Zlength (mt_lim t) + 1)
    by (unfold lim'; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (HA : assignment (view_of n (mt_decide t l) r' db)
               = sat_function_update (assignment (view_of n t r db))
                   (lit_var_c l) (Some (lit_pol l)))
    by exact (view_of_push_assignment n t r db l lim' Hwf Hlwf).
  assert (HL : level_of (view_of n (mt_decide t l) r' db)
               = sat_function_update (level_of (view_of n t r db))
                   (lit_var_c l) (Some (Zlength (mt_lim t) + 1))).
  { rewrite <- Hlim'.
    exact (view_of_push_level n t r db l lim' Hwf Hlwf Hz
             (fun i Hi => count_le_decide_old n t i Hwf Hi)
             (count_le_decide_new n t Hwf)). }
  assert (HR : reason_of (view_of n (mt_decide t l) r' db)
               = sat_function_update (reason_of (view_of n t r db))
                   (lit_var_c l) None)
    by exact (view_of_push_reason n t r r' db l lim' None Hwf Hlwf Hz
                Hagree Hnew).
  unfold assigns_one.
  split. { cbn [view_of assignment]. apply mt_pv_zero_cell; [lia|exact Hz]. }
  split. { rewrite HA. apply sat_function_update_eq. }
  split. { rewrite HL. apply sat_function_update_eq. }
  split. { rewrite HR. apply sat_function_update_eq. }
  split.
  { exists (List.length (mt_trail t)).
    split.
    { cbn [view_of assignment_rank].
      apply (trail_pos_push_new n t l lim' Hwf Hlwf Hz). }
    intros y [cc [ly [Hreason [Hin [Hvar [Hyx Heval]]]]]].
    rewrite HR, sat_function_update_eq in Hreason. discriminate. }
  split.
  { intros y Hyx. repeat split.
    - rewrite HA. apply sat_function_update_neq.
      intro H; apply Hyx; symmetry; exact H.
    - rewrite HL. apply sat_function_update_neq.
      intro H; apply Hyx; symmetry; exact H.
    - rewrite HR. apply sat_function_update_neq.
      intro H; apply Hyx; symmetry; exact H.
    - cbn [view_of assignment_rank]. unfold mt_decide.
      apply trail_pos_push_other. exact Hyx. }
  reflexivity.
Qed.

Lemma mt_cancel_lim : forall t level,
  mt_lim (mt_cancel t level) = ztake level (mt_lim t).
Proof. reflexivity. Qed.

Lemma mt_cancel_qhead : forall t level,
  mt_qhead (mt_cancel t level) = Znth level (mt_lim t) 0.
Proof. reflexivity. Qed.

Lemma trail_pos_cancel : forall n t level v,
  mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
  trail_pos (mt_cancel t level) v
  = match trail_pos t v with
    | Some k => if Z.of_nat k <? Znth level (mt_lim t) 0 then Some k else None
    | None => None
    end.
Proof.
  intros n t level v Hwf Hlevel.
  pose proof (lim_lt_trail n t level Hwf Hlevel) as Hb.
  unfold trail_pos. rewrite mt_cancel_trail.
  destruct (find_var_pos v (mt_trail t)) as [k|] eqn:Hk.
  - destruct (Z.of_nat k <? Znth level (mt_lim t) 0) eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      apply find_var_pos_ztake_lt; [exact Hk|lia].
    + apply Z.ltb_ge in Hlt.
      apply (find_var_pos_ztake_none v (mt_trail t) k);
        [exact (mtw_trail_nodup Hwf)|exact Hk|lia].
  - destruct (find_var_pos v (ztake (Znth level (mt_lim t) 0) (mt_trail t)))
      as [j|] eqn:Hj; [|reflexivity].
    exfalso.
    destruct (find_var_pos_ztake_inv v (mt_trail t) _ _ Hj) as [k' Hk'].
    rewrite Hk' in Hk. discriminate.
Qed.

Lemma mt_pv_cancel_drop : forall n t level v,
  mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
  trail_pos (mt_cancel t level) v = None ->
  mt_pv (mt_cancel t level) v = None.
Proof.
  intros n t level v Hwf Hlevel H.
  apply (proj2 (view_unassigned_iff n (mt_cancel t level) v
                  (mtrail_wf_cancel n t level Hwf Hlevel))).
  exact H.
Qed.

(** [solver_canceluntil] realises [restrict_above_level]: the levels at or
    below [level] survive untouched, everything above is unassigned.  Note the
    [levels] array is NOT cleaned -- the view reads levels only through
    [trail_pos], so the stale cells are invisible. *)
Lemma view_of_cancel : forall n t r db level,
  mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
  restrict_above_level (view_of n t r db) (view_of n (mt_cancel t level) r db) level.
Proof.
  intros n t r db level Hwf Hlevel.
  pose proof (lim_lt_trail n t level Hwf Hlevel) as Hb.
  pose proof (mtw_lim_sorted Hwf) as Hsorted.
  unfold restrict_above_level.
  split.
  { cbn [view_of current_level]. rewrite mt_cancel_lim.
    apply Zlength_ztake. lia. }
  split; [reflexivity|].
  intro x.
  pose proof (trail_pos_cancel n t level x Hwf Hlevel) as Hnewpos.
  destruct (trail_pos t x) as [k|] eqn:Hk.
  - assert (Hlo : level_of (view_of n t r db) x
                  = Some (level_of_index t (Z.of_nat k)))
      by (cbn [view_of level_of]; rewrite Hk; reflexivity).
    rewrite Hlo. cbv beta iota.
    destruct (level_of_index t (Z.of_nat k) <=? level) eqn:Hle.
    + apply Z.leb_le in Hle.
      assert (Hkb : Z.of_nat k < Znth level (mt_lim t) 0).
      { apply (strict_sorted_count_suffix (mt_lim t) (Z.of_nat k) level Hsorted);
          [exact Hle|lia]. }
      assert (Hb' : (Z.of_nat k <? Znth level (mt_lim t) 0) = true)
        by (apply Z.ltb_lt; exact Hkb).
      rewrite Hb' in Hnewpos.
      repeat split.
      * cbn [view_of assignment].
        apply (mt_pv_cancel_keep n t level x Hwf Hlevel).
        eapply find_var_pos_some_in. exact Hnewpos.
      * cbn [view_of level_of]. rewrite Hnewpos. cbn [option_map]. f_equal.
        unfold level_of_index. rewrite mt_cancel_lim.
        apply count_le_ztake; [exact Hsorted|lia|exact Hle].
      * cbn [view_of reason_of]. rewrite Hnewpos, Hk. reflexivity.
      * cbn [view_of assignment_rank]. rewrite Hnewpos, Hk. reflexivity.
    + apply Z.leb_gt in Hle.
      assert (Hkb : Znth level (mt_lim t) 0 <= Z.of_nat k).
      { destruct (Z_le_gt_dec (Znth level (mt_lim t) 0) (Z.of_nat k)) as [H|H];
          [exact H|exfalso].
        assert (Hcp : count_le (Z.of_nat k) (mt_lim t) <= level).
        { destruct (Z_le_gt_dec (count_le (Z.of_nat k) (mt_lim t)) level)
            as [H2|H2]; [exact H2|exfalso].
          assert (Hp : 0 <= level < count_le (Z.of_nat k) (mt_lim t)) by lia.
          pose proof (strict_sorted_count_prefix (mt_lim t) (Z.of_nat k) level
                        Hsorted Hp) as Hpp. lia. }
        unfold level_of_index in Hle. lia. }
      assert (Hb' : (Z.of_nat k <? Znth level (mt_lim t) 0) = false)
        by (apply Z.ltb_ge; exact Hkb).
      rewrite Hb' in Hnewpos.
      repeat split.
      * cbn [view_of assignment].
        apply (mt_pv_cancel_drop n t level x Hwf Hlevel Hnewpos).
      * cbn [view_of level_of]. rewrite Hnewpos. reflexivity.
      * cbn [view_of reason_of]. rewrite Hnewpos. reflexivity.
      * cbn [view_of assignment_rank]. exact Hnewpos.
  - assert (Hlo : level_of (view_of n t r db) x = None)
      by (cbn [view_of level_of]; rewrite Hk; reflexivity).
    rewrite Hlo. cbv beta iota.
    repeat split.
    + cbn [view_of assignment].
      apply (mt_pv_cancel_drop n t level x Hwf Hlevel Hnewpos).
    + cbn [view_of level_of]. rewrite Hnewpos. reflexivity.
    + cbn [view_of reason_of]. rewrite Hnewpos. reflexivity.
    + cbn [view_of assignment_rank]. exact Hnewpos.
Qed.

(** ===== G. TRAIL-IMPLIED ===== *)

Lemma ztake_app_le : forall d l1 l2,
  0 <= d <= Zlength l1 -> ztake d (l1 ++ l2) = ztake d l1.
Proof.
  intros d l1 l2 H. unfold ztake. rewrite firstn_app.
  rewrite Zlength_correct in H.
  replace (Z.to_nat d - List.length l1)%nat with 0%nat by lia.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma ztake_all : forall d l, Zlength l <= d -> ztake d l = l.
Proof.
  intros d l H. unfold ztake. apply firstn_all2.
  rewrite Zlength_correct in H. lia.
Qed.

Definition decisions_are (t : mtrail) (A : list literal) : Prop :=
  decisions_upto t (Zlength (mt_lim t)) = A.

Lemma decisions_upto_incl : forall t d1 d2,
  0 <= d1 <= d2 -> incl (decisions_upto t d1) (decisions_upto t d2).
Proof.
  intros t d1 d2 H x Hx. unfold decisions_upto in *.
  rewrite <- (ztake_ztake d1 d2 (mt_lim t) H) in Hx.
  apply in_map_iff in Hx. destruct Hx as [b [<- Hb]].
  apply (in_map (fun b0 => lit_denote (Znth b0 (mt_trail t) 0))).
  eapply In_ztake; eauto.
Qed.

Lemma level_of_index_nonneg : forall t i, 0 <= level_of_index t i.
Proof. intros. apply count_le_nonneg. Qed.

Lemma trail_implied_upgrade : forall F t i l d,
  trail_implied F t -> 0 <= i < Zlength (mt_trail t) ->
  Znth i (mt_trail t) 0 = l ->
  level_of_index t i <= d ->
  entails_clause (cnf_with_units F (decisions_upto t d)) [lit_denote l].
Proof.
  intros F t i l d Hti Hi Hl Hd.
  eapply entails_units_mono; [apply decisions_upto_incl|apply (Hti i l Hi Hl)].
  pose proof (level_of_index_nonneg t i). lia.
Qed.

(** ----- maintenance across the three transitions ----- *)

Lemma decisions_upto_enqueue : forall n t l d,
  mtrail_wf n t -> decisions_upto (mt_enqueue t l) d = decisions_upto t d.
Proof.
  intros n t l d Hwf.
  unfold decisions_upto, mt_enqueue, mt_push; cbn [mt_trail mt_lim].
  apply map_ext_in. intros b Hb.
  assert (Hr : 0 <= b < Zlength (mt_trail t)).
  { pose proof (mtw_lim_range Hwf) as HF. rewrite Forall_forall in HF.
    apply HF. eapply In_ztake; eauto. }
  rewrite app_Znth1 by exact Hr. reflexivity.
Qed.

Lemma level_of_index_enqueue : forall t l i,
  level_of_index (mt_enqueue t l) i = level_of_index t i.
Proof. reflexivity. Qed.

Lemma trail_implied_enqueue : forall n F t l,
  mtrail_wf n t ->
  entails_clause (cnf_with_units F (decisions_upto t (Zlength (mt_lim t))))
                 [lit_denote l] ->
  trail_implied F t ->
  trail_implied F (mt_enqueue t l).
Proof.
  intros n F t l Hwf Hent Hti.
  pose proof (Zlength_nonneg (mt_trail t)) as HT0.
  intros i ll Hi Hll.
  unfold mt_enqueue, mt_push in Hi, Hll; cbn [mt_trail] in Hi, Hll.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  rewrite (decisions_upto_enqueue n t l _ Hwf), level_of_index_enqueue.
  destruct (Z.eq_dec i (Zlength (mt_trail t))) as [->|Hne].
  - rewrite app_Znth2 in Hll by lia.
    replace (Zlength (mt_trail t) - Zlength (mt_trail t)) with 0 in Hll by lia.
    rewrite Znth0_cons in Hll. subst ll.
    unfold level_of_index. rewrite (count_le_enqueue_new n t Hwf). exact Hent.
  - rewrite app_Znth1 in Hll by lia.
    apply (Hti i ll); [lia|exact Hll].
Qed.

Lemma trail_implied_unit : forall n F t l rc,
  mtrail_wf n t -> trail_implied F t ->
  entails_clause F rc ->
  In (lit_denote l) rc ->
  (forall k, In k rc -> k <> lit_denote l ->
     exists j, 0 <= j < Zlength (mt_trail t) /\
               lit_denote (Znth j (mt_trail t) 0) = literal_neg k) ->
  trail_implied F (mt_enqueue t l).
Proof.
  intros n F t l rc Hwf Hti Hent Hin Hothers.
  apply (trail_implied_enqueue n F t l Hwf); [|exact Hti].
  eapply entails_unit_step with (c := rc).
  - apply entails_clause_units_weaken. exact Hent.
  - exact Hin.
  - intros k Hk Hne.
    destruct (Hothers k Hk Hne) as [j [Hj Hjval]].
    rewrite <- Hjval.
    eapply trail_implied_upgrade;
      [exact Hti|exact Hj|reflexivity|apply prop_level_processed_level_le].
Qed.

Lemma decisions_upto_decide_low : forall n t l d,
  mtrail_wf n t -> 0 <= d <= Zlength (mt_lim t) ->
  decisions_upto (mt_decide t l) d = decisions_upto t d.
Proof.
  intros n t l d Hwf Hd.
  unfold decisions_upto, mt_decide, mt_push; cbn [mt_trail mt_lim].
  rewrite ztake_app_le by lia.
  apply map_ext_in. intros b Hb.
  assert (Hr : 0 <= b < Zlength (mt_trail t)).
  { pose proof (mtw_lim_range Hwf) as HF. rewrite Forall_forall in HF.
    apply HF. eapply In_ztake; eauto. }
  rewrite app_Znth1 by exact Hr. reflexivity.
Qed.

Lemma decisions_upto_decide_top : forall n t l,
  mtrail_wf n t ->
  decisions_upto (mt_decide t l) (Zlength (mt_lim t) + 1)
  = decisions_upto t (Zlength (mt_lim t)) ++ [lit_denote l].
Proof.
  intros n t l Hwf.
  pose proof (Zlength_nonneg (mt_trail t)) as HT0.
  unfold decisions_upto, mt_decide, mt_push; cbn [mt_trail mt_lim].
  rewrite ztake_all by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite map_app. f_equal.
  - rewrite ztake_all by lia.
    apply map_ext_in. intros b Hb.
    assert (Hr : 0 <= b < Zlength (mt_trail t)).
    { pose proof (mtw_lim_range Hwf) as HF. rewrite Forall_forall in HF. auto. }
    rewrite app_Znth1 by exact Hr. reflexivity.
  - simpl. f_equal. f_equal.
    rewrite app_Znth2 by lia.
    replace (Zlength (mt_trail t) - Zlength (mt_trail t)) with 0 by lia.
    apply Znth0_cons.
Qed.

Lemma trail_implied_decision : forall n F t l,
  mtrail_wf n t -> trail_implied F t -> trail_implied F (mt_decide t l).
Proof.
  intros n F t l Hwf Hti.
  pose proof (Zlength_nonneg (mt_trail t)) as HT0.
  pose proof (Zlength_nonneg (mt_lim t)) as HL0.
  intros i ll Hi Hll.
  unfold mt_decide, mt_push in Hi, Hll; cbn [mt_trail] in Hi, Hll.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  destruct (Z.eq_dec i (Zlength (mt_trail t))) as [->|Hne].
  - rewrite app_Znth2 in Hll by lia.
    replace (Zlength (mt_trail t) - Zlength (mt_trail t)) with 0 in Hll by lia.
    rewrite Znth0_cons in Hll. subst ll.
    assert (Hlev : level_of_index (mt_decide t l) (Zlength (mt_trail t))
                   = Zlength (mt_lim t) + 1).
    { unfold level_of_index, mt_decide, mt_push; cbn [mt_lim].
      rewrite (count_le_decide_new n t Hwf), Zlength_app, Zlength_cons,
              Zlength_nil. lia. }
    rewrite Hlev, (decisions_upto_decide_top n t l Hwf).
    apply entails_clause_units_unit.
    apply in_or_app. right. left. reflexivity.
  - rewrite app_Znth1 in Hll by lia.
    assert (Hlev : level_of_index (mt_decide t l) i = level_of_index t i).
    { unfold level_of_index, mt_decide, mt_push; cbn [mt_lim].
      apply (count_le_decide_old n t i Hwf). lia. }
    rewrite Hlev, (decisions_upto_decide_low n t l (level_of_index t i) Hwf).
    + apply (Hti i ll); [lia|exact Hll].
    + pose proof (level_of_index_nonneg t i). pose proof (prop_level_processed_level_le t i).
      lia.
Qed.

(** Truncation preserves it: the surviving literals' hypotheses only mention
    surviving decisions, precisely because they are level-indexed. *)
Lemma trail_implied_cancel : forall n F t level,
  mtrail_wf n t -> 0 <= level < Zlength (mt_lim t) ->
  trail_implied F t -> trail_implied F (mt_cancel t level).
Proof.
  intros n F t level Hwf Hlevel Hti i l Hi Hl.
  pose proof (lim_lt_trail n t level Hwf Hlevel) as Hb.
  pose proof (mtw_lim_sorted Hwf) as Hsorted.
  rewrite mt_cancel_trail in Hi, Hl.
  assert (Hlen : Zlength (ztake (Znth level (mt_lim t) 0) (mt_trail t))
                 = Znth level (mt_lim t) 0) by (apply Zlength_ztake; lia).
  rewrite Hlen in Hi.
  rewrite Znth_ztake in Hl by lia.
  assert (Hile : count_le i (mt_lim t) <= level).
  { destruct (Z_le_gt_dec (count_le i (mt_lim t)) level) as [H|H]; [exact H|].
    exfalso.
    assert (Hp : 0 <= level < count_le i (mt_lim t)) by lia.
    pose proof (strict_sorted_count_prefix (mt_lim t) i level Hsorted Hp). lia. }
  assert (Hlev : level_of_index (mt_cancel t level) i = level_of_index t i).
  { unfold level_of_index. rewrite mt_cancel_lim.
    apply count_le_ztake; [exact Hsorted|lia|exact Hile]. }
  rewrite Hlev.
  assert (Hdec : decisions_upto (mt_cancel t level) (level_of_index t i)
                 = decisions_upto t (level_of_index t i)).
  { unfold decisions_upto. rewrite mt_cancel_lim, mt_cancel_trail.
    rewrite ztake_ztake by (pose proof (level_of_index_nonneg t i);
                            unfold level_of_index in *; lia).
    apply map_ext_in. intros b Hb'.
    assert (Hdlen : Zlength (ztake (level_of_index t i) (mt_lim t))
                    = level_of_index t i).
    { apply Zlength_ztake. pose proof (level_of_index_nonneg t i).
      unfold level_of_index in *. lia. }
    destruct (In_Znth_index _ _ Hb') as [j [Hj Hjval]].
    rewrite Hdlen in Hj.
    rewrite Znth_ztake in Hjval by lia.
    assert (Hjb : b < Znth level (mt_lim t) 0).
    { rewrite <- Hjval. apply strict_sorted_Znth; [exact Hsorted|lia| |lia].
      unfold level_of_index in Hj. lia. }
    assert (Hb0 : 0 <= b).
    { pose proof (mtw_lim_range Hwf) as HF. rewrite Forall_forall in HF.
      assert (Hinb : In b (mt_lim t)) by (eapply In_ztake; eauto).
      pose proof (HF b Hinb). lia. }
    rewrite Znth_ztake by lia. reflexivity. }
  rewrite Hdec.
  apply (Hti i l); [lia|exact Hl].
Qed.

(** ===== H. root conflicts, database and watcher lemmas ===== *)

Lemma trail_implied_at_root : forall F t A,
  trail_implied F t -> decisions_are t A ->
  forall i, 0 <= i < Zlength (mt_trail t) ->
    entails_clause (cnf_with_units F A) [lit_denote (Znth i (mt_trail t) 0)].
Proof.
  intros F t A Hti HA i Hi. unfold decisions_are in HA. subst A.
  eapply trail_implied_upgrade;
    [exact Hti|exact Hi|reflexivity|apply prop_level_processed_level_le].
Qed.

Lemma root_conflict_unsat : forall n F A t Cd,
  cnf_wf n F -> Forall (literal_wf n) A ->
  mtrail_wf n t -> trail_implied F t -> decisions_are t A ->
  entails_clause F Cd ->
  clause_false (assigns_pv (mt_assigns t)) Cd ->
  Forall (literal_wf n) Cd ->
  cnf_unsat n (cnf_with_units F A).
Proof.
  intros n F A t Cd HFwf HAwf Hwf Hti Hdec Hent Hfalse HCdwf.
  split; [apply cnf_with_units_wf; assumption|].
  intros rho Hbound Hmodels.
  destruct (proj1 (models_cnf_with_units rho F A) Hmodels) as [HmF _].
  destruct (Hent rho HmF) as [k [Hink Hktrue]].
  pose proof (Hfalse k Hink) as Hkfalse.
  rewrite Forall_forall in HCdwf.
  pose proof (HCdwf k Hink) as Hkwf.
  unfold literal_wf, var_in_range in Hkwf.
  assert (Hassigned : Znth (literal_var k) (mt_assigns t) 0 <> 0).
  { intro Hz.
    assert (Hnone : assigns_pv (mt_assigns t) (literal_var k) = None).
    { unfold assigns_pv, assigns_val. rewrite Hz.
      apply lbool_val_none. split; discriminate. }
    pose proof (eval_partial_literal_unassigned
                  (assigns_pv (mt_assigns t)) k Hnone) as Hn.
    rewrite Hn in Hkfalse. discriminate. }
  pose proof (proj1 (mtw_assigned_iff Hwf (literal_var k) Hkwf) Hassigned) as Hin.
  destruct (In_Znth_index _ _ Hin) as [j [Hj Hjval]].
  rewrite Zlength_map_Z in Hj.
  assert (Hvar : lit_var_c (Znth j (mt_trail t) 0) = literal_var k).
  { rewrite <- Hjval. symmetry.
    apply (Znth_map Z Z lit_var_c (mt_trail t) j 0 0). exact Hj. }
  pose proof (trail_implied_at_root F t A Hti Hdec j Hj) as Hentl.
  destruct (Hentl rho Hmodels) as [k' [Hink' Hk'true]].
  destruct Hink' as [Heq|[]]. subst k'.
  rewrite lit_denote_satisfying, Hvar in Hk'true.
  pose proof (eval_satisfying_literal_true_inv rho (literal_var k)
                (lit_pol (Znth j (mt_trail t) 0)) Hk'true) as Hrhov.
  assert (Hcell : assigns_pv (mt_assigns t) (literal_var k)
                  = Some (lit_pol (Znth j (mt_trail t) 0))).
  { unfold assigns_pv, assigns_val.
    assert (Hsig : Znth (literal_var k) (mt_assigns t) 0
                   = lit_sig (Znth j (mt_trail t) 0)).
    { rewrite <- Hvar.
      pose proof (mtw_trail_true Hwf) as HF. rewrite Forall_forall in HF.
      apply HF. apply Znth_In. exact Hj. }
    rewrite Hsig. apply lbool_val_lit_sig. }
  pose proof (eval_partial_literal_total_agree
                (assigns_pv (mt_assigns t)) rho k false
                (lit_pol (Znth j (mt_trail t) 0)) Hcell Hrhov Hkfalse) as Hkeval.
  rewrite Hkeval in Hktrue. discriminate.
Qed.

Lemma perm_swap_app :
  forall (X A Y : list Z), Permutation (X ++ A ++ Y) (A ++ X ++ Y).
Proof.
  intros X A Y.
  rewrite (app_assoc X A Y), (app_assoc A X Y).
  apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

Lemma perm_shuffle :
  forall (X A Y B : list Z),
    Permutation ((X ++ A ++ Y) ++ B) (A ++ (X ++ B ++ Y)).
Proof.
  intros X A Y B.
  eapply Permutation_trans; [apply Permutation_app_tail, perm_swap_app|].
  rewrite <- !app_assoc.
  apply Permutation_app_head, Permutation_app_head, Permutation_app_comm.
Qed.

Lemma Zlength_two_inv :
  forall (L : list Z), Zlength L = 2 -> L = [Znth 0 L 0; Znth 1 L 0].
Proof.
  intros L HL. destruct L as [|a [|b [|c L]]].
  - rewrite Zlength_nil in HL. lia.
  - rewrite Zlength_cons, Zlength_nil in HL. lia.
  - rewrite Znth0_cons. rewrite Znth_cons by lia.
    replace (1 - 1) with 0 by lia. rewrite Znth0_cons. reflexivity.
  - rewrite !Zlength_cons in HL. pose proof (Zlength_nonneg L). lia.
Qed.

Definition db_nil : dbmap := nil.

Definition z_nil : list Z := nil.

Definition msat_false : bool := false.

Lemma db_wf_obj : forall n db p co,
  db_wf n db -> In (p, co) db -> obj_wf n co.
Proof.
  intros n db p co [_ [_ Hall]] Hin.
  rewrite Forall_forall in Hall. exact (Hall _ Hin).
Qed.

Lemma db_wf_even : forall n db p co,
  db_wf n db -> In (p, co) db -> Z.even p = true.
Proof.
  intros n db p co [_ [Hall _]] Hin.
  rewrite Forall_forall in Hall. exact (proj2 (Hall _ Hin)).
Qed.

Lemma db_wf_ptr_pos : forall n db p co,
  db_wf n db -> In (p, co) db -> 0 < p.
Proof.
  intros n db p co [_ [Hall _]] Hin.
  rewrite Forall_forall in Hall. exact (proj1 (Hall _ Hin)).
Qed.

Lemma db_wf_lookup_unique : forall n db p co co',
  db_wf n db -> In (p, co) db -> In (p, co') db -> co = co'.
Proof.
  intros n db p co co' [Hnd _] H1 H2.
  revert p co co' Hnd H1 H2.
  induction db as [|e db IH]; intros p co co' Hnd H1 H2.
  - contradiction.
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
    destruct H1 as [He1|H1]; destruct H2 as [He2|H2].
    + congruence.
    + exfalso. apply Hni. rewrite He1.
      change (fst (p, co)) with (fst (p, co')). apply in_map. exact H2.
    + exfalso. apply Hni. rewrite He2.
      change (fst (p, co')) with (fst (p, co)). apply in_map. exact H1.
    + exact (IH p co co' Hnd' H1 H2).
Qed.

Lemma obj_wf_watch0 : forall n co, obj_wf n co -> lit_wf_c n (co_watch0 co).
Proof.
  intros n co [Hlen [Hall _]]. unfold co_watch0.
  apply Forall_Znth_elim; [exact Hall | lia].
Qed.

Lemma obj_wf_watch1 : forall n co, obj_wf n co -> lit_wf_c n (co_watch1 co).
Proof.
  intros n co [Hlen [Hall _]]. unfold co_watch1.
  apply Forall_Znth_elim; [exact Hall | lia].
Qed.

Lemma obj_wf_watch0_in : forall n co, obj_wf n co -> In (co_watch0 co) (co_lits co).
Proof.
  intros n co [Hlen _]. unfold co_watch0. apply Znth_In. lia.
Qed.

Lemma obj_wf_watch1_in : forall n co, obj_wf n co -> In (co_watch1 co) (co_lits co).
Proof.
  intros n co [Hlen _]. unfold co_watch1. apply Znth_In. lia.
Qed.

Lemma minisat_occurrence_of_entry_wf : forall n p co,
  obj_wf n co ->
  watch_occurrence_wf n (minisat_occurrence_of_entry (p, co)).
Proof.
  intros n p co Hobj.
  pose proof Hobj as [Hlen [Hlits _]].
  split.
  - unfold denote_obj. apply lits_denote_wf. exact Hlits.
  - split; unfold denote_obj.
    + apply lits_denote_in. eapply obj_wf_watch0_in; eassumption.
    + apply lits_denote_in. eapply obj_wf_watch1_in; eassumption.
Qed.

Lemma minisat_watch_occurrences_wf : forall n db,
  db_wf n db ->
  Forall (watch_occurrence_wf n) (minisat_watch_occurrences db).
Proof.
  intros n db [_ [_ Hobjects]].
  unfold minisat_watch_occurrences.
  apply Forall_map.
  revert Hobjects. apply Forall_impl.
  intros [p co] Hobj.
  apply minisat_occurrence_of_entry_wf. exact Hobj.
Qed.

Lemma minisat_focus_words_expected : forall db p,
  minisat_focus_words (minisat_focus_contributions db p) =
  expected_watchers db p.
Proof.
  intros db p. induction db as [|e db IH]; [reflexivity|].
  change
    (minisat_focus_words
       (minisat_entry_focus_contributions p e ++
        minisat_focus_contributions db p) =
     entry_watchers e p ++ expected_watchers db p).
  rewrite <- IH.
  unfold minisat_focus_words. rewrite map_app.
  unfold minisat_entry_focus_contributions.
  rewrite map_map. simpl. rewrite map_id. reflexivity.
Qed.

Lemma minisat_focus_words_reorder : forall cs ws,
  Permutation (minisat_focus_words cs) ws ->
  exists cs',
    Permutation cs' cs /\
    minisat_focus_words cs' = ws.
Proof.
  intros cs ws Hperm.
  unfold minisat_focus_words in Hperm |- *.
  pose proof (Permutation_sym Hperm) as Hsym.
  destruct (@Permutation_map_inv minisat_focus_contribution Z snd
              ws cs Hsym) as [cs' [Hwords Hcs]].
  exists cs'. split.
  - apply Permutation_sym. exact Hcs.
  - symmetry. exact Hwords.
Qed.

Lemma minisat_focus_scan_init : forall n db wm p P,
  wmap_exact n db wm ->
  0 <= p < 2 * n ->
  minisat_focus_scan_carrier db p P [] (Znth p wm nil).
Proof.
  intros n db wm p P [_ Hexact] Hp.
  specialize (Hexact p Hp).
  rewrite <- minisat_focus_words_expected in Hexact.
  destruct (minisat_focus_words_reorder
              (minisat_focus_contributions db p)
              (Znth p wm nil) (Permutation_sym Hexact))
    as [pending [Hpending Hwords]].
  unfold minisat_focus_scan_carrier.
  exists [], pending. split.
  - simpl. exact Hpending.
  - split; [reflexivity|]. split; [exact Hwords|constructor].
Qed.

Lemma minisat_focused_occurrence_contributes : forall n db p o,
  db_wf n db ->
  lit_wf_c n p ->
  In o (minisat_watch_occurrences db) ->
  (lit_denote p = literal_neg (watch_left o) \/
   lit_denote p = literal_neg (watch_right o)) ->
  exists w, In (o, w) (minisat_focus_contributions db p).
Proof.
  intros n db p o Hdb Hp Ho Hfocus.
  unfold minisat_watch_occurrences in Ho.
  apply in_map_iff in Ho.
  destruct Ho as [[q co] [Ho Hin]]. subst o.
  assert (Hobj : obj_wf n co) by (eapply db_wf_obj; eassumption).
  assert (H0wf : lit_wf_c n (co_watch0 co))
    by (eapply obj_wf_watch0; eassumption).
  assert (H1wf : lit_wf_c n (co_watch1 co))
    by (eapply obj_wf_watch1; eassumption).
  change
    (lit_denote p = literal_neg (lit_denote (co_watch0 co)) \/
     lit_denote p = literal_neg (lit_denote (co_watch1 co)))
    in Hfocus.
  destruct Hfocus as [Hfocus | Hfocus].
  - assert (Hnegwf : lit_wf_c n (lit_neg_c (co_watch0 co)))
      by (apply lit_neg_c_wf; exact H0wf).
    assert (Hden :
      lit_denote p = lit_denote (lit_neg_c (co_watch0 co))).
    { rewrite lit_denote_neg by (destruct H0wf; lia). exact Hfocus. }
    assert (Hindex : lit_neg_c (co_watch0 co) = p).
    { pose proof (f_equal lit_encode Hden) as Hencoded.
      rewrite (lit_encode_denote n p Hp) in Hencoded.
      rewrite (lit_encode_denote
                 n (lit_neg_c (co_watch0 co)) Hnegwf) in Hencoded.
      symmetry. exact Hencoded. }
    set (w := if 3 <=? Zlength (co_lits co)
              then q else tag_of_lit (co_watch1 co)).
    assert (Hwatch : In w (entry_watchers (q, co) p)).
    { unfold entry_watchers. rewrite Hindex, Z.eqb_refl.
      apply in_or_app. left. unfold w. simpl. auto. }
    exists w. unfold minisat_focus_contributions.
    apply in_flat_map. exists (q, co). split; [exact Hin|].
    unfold minisat_entry_focus_contributions. apply in_map. exact Hwatch.
  - assert (Hnegwf : lit_wf_c n (lit_neg_c (co_watch1 co)))
      by (apply lit_neg_c_wf; exact H1wf).
    assert (Hden :
      lit_denote p = lit_denote (lit_neg_c (co_watch1 co))).
    { rewrite lit_denote_neg by (destruct H1wf; lia). exact Hfocus. }
    assert (Hindex : lit_neg_c (co_watch1 co) = p).
    { pose proof (f_equal lit_encode Hden) as Hencoded.
      rewrite (lit_encode_denote n p Hp) in Hencoded.
      rewrite (lit_encode_denote
                 n (lit_neg_c (co_watch1 co)) Hnegwf) in Hencoded.
      symmetry. exact Hencoded. }
    set (w := if 3 <=? Zlength (co_lits co)
              then q else tag_of_lit (co_watch0 co)).
    assert (Hwatch : In w (entry_watchers (q, co) p)).
    { unfold entry_watchers. apply in_or_app. right.
      rewrite Hindex, Z.eqb_refl. unfold w. simpl. auto. }
    exists w. unfold minisat_focus_contributions.
    apply in_flat_map. exists (q, co). split; [exact Hin|].
    unfold minisat_entry_focus_contributions. apply in_map. exact Hwatch.
Qed.

Lemma expected_watchers_app : forall db1 db2 l,
  expected_watchers (db1 ++ db2) l
  = expected_watchers db1 l ++ expected_watchers db2 l.
Proof. intros. unfold expected_watchers. apply flat_map_app. Qed.

Lemma expected_watchers_cons : forall e db l,
  expected_watchers (e :: db) l = entry_watchers e l ++ expected_watchers db l.
Proof. reflexivity. Qed.

Lemma wmap_in_of_entry : forall n db wm e l w,
  wmap_exact n db wm -> In e db -> 0 <= l < 2 * n ->
  In w (entry_watchers e l) -> In w (Znth l wm nil).
Proof.
  intros n db wm e l w [_ Hp] Hin Hl Hw.
  apply (Permutation_in (l := expected_watchers db l)).
  - apply Permutation_sym. exact (Hp l Hl).
  - unfold expected_watchers. apply in_flat_map. exists e. split; assumption.
Qed.

Lemma wmap_present_real0 : forall n db wm p co,
  db_wf n db -> wmap_exact n db wm -> In (p, co) db ->
  3 <= Zlength (co_lits co) ->
  In p (Znth (lit_neg_c (co_watch0 co)) wm nil).
Proof.
  intros n db wm p co Hdb Hex Hin Hbig.
  assert (Hobj : obj_wf n co) by (eapply db_wf_obj; eassumption).
  assert (Hwf : lit_wf_c n (lit_neg_c (co_watch0 co)))
    by (apply lit_neg_c_wf; eapply obj_wf_watch0; eassumption).
  eapply wmap_in_of_entry; [exact Hex | exact Hin | exact Hwf |].
  simpl. rewrite Z.eqb_refl.
  assert (H3 : (3 <=? Zlength (co_lits co)) = true) by (apply Z.leb_le; lia).
  rewrite H3. simpl. left. reflexivity.
Qed.

Lemma wmap_present_real1 : forall n db wm p co,
  db_wf n db -> wmap_exact n db wm -> In (p, co) db ->
  3 <= Zlength (co_lits co) ->
  In p (Znth (lit_neg_c (co_watch1 co)) wm nil).
Proof.
  intros n db wm p co Hdb Hex Hin Hbig.
  assert (Hobj : obj_wf n co) by (eapply db_wf_obj; eassumption).
  assert (Hwf : lit_wf_c n (lit_neg_c (co_watch1 co)))
    by (apply lit_neg_c_wf; eapply obj_wf_watch1; eassumption).
  eapply wmap_in_of_entry; [exact Hex | exact Hin | exact Hwf |].
  simpl. rewrite Z.eqb_refl.
  assert (H3 : (3 <=? Zlength (co_lits co)) = true) by (apply Z.leb_le; lia).
  rewrite H3.
  destruct (lit_neg_c (co_watch0 co) =? lit_neg_c (co_watch1 co));
    simpl; [right | ]; left; reflexivity.
Qed.

Lemma wmap_present_bin0 : forall n db wm p co,
  db_wf n db -> wmap_exact n db wm -> In (p, co) db ->
  Zlength (co_lits co) = 2 ->
  In (tag_of_lit (co_watch1 co)) (Znth (lit_neg_c (co_watch0 co)) wm nil).
Proof.
  intros n db wm p co Hdb Hex Hin H2.
  assert (Hobj : obj_wf n co) by (eapply db_wf_obj; eassumption).
  assert (Hwf : lit_wf_c n (lit_neg_c (co_watch0 co)))
    by (apply lit_neg_c_wf; eapply obj_wf_watch0; eassumption).
  eapply wmap_in_of_entry; [exact Hex | exact Hin | exact Hwf |].
  simpl. rewrite Z.eqb_refl.
  assert (H3 : (3 <=? Zlength (co_lits co)) = false) by (apply Z.leb_gt; lia).
  rewrite H3. simpl. left. reflexivity.
Qed.

Lemma wmap_present_bin1 : forall n db wm p co,
  db_wf n db -> wmap_exact n db wm -> In (p, co) db ->
  Zlength (co_lits co) = 2 ->
  In (tag_of_lit (co_watch0 co)) (Znth (lit_neg_c (co_watch1 co)) wm nil).
Proof.
  intros n db wm p co Hdb Hex Hin H2.
  assert (Hobj : obj_wf n co) by (eapply db_wf_obj; eassumption).
  assert (Hwf : lit_wf_c n (lit_neg_c (co_watch1 co)))
    by (apply lit_neg_c_wf; eapply obj_wf_watch1; eassumption).
  eapply wmap_in_of_entry; [exact Hex | exact Hin | exact Hwf |].
  simpl. rewrite Z.eqb_refl.
  assert (H3 : (3 <=? Zlength (co_lits co)) = false) by (apply Z.leb_gt; lia).
  rewrite H3.
  destruct (lit_neg_c (co_watch0 co) =? lit_neg_c (co_watch1 co));
    simpl; [right | ]; left; reflexivity.
Qed.

Lemma wmap_tag_witness : forall n db wm l w,
  db_wf n db -> wmap_exact n db wm -> 0 <= l < 2 * n ->
  In w (Znth l wm nil) -> is_tag w = true ->
  exists p co, In (p, co) db /\ Zlength (co_lits co) = 2 /\
               Permutation (co_lits co) [lit_neg_c l; tag_lit w].
Proof.
  intros n db wm l w Hdb [_ Hp] Hl Hin Htag.
  assert (Hexp : In w (expected_watchers db l))
    by (apply (Permutation_in (l := Znth l wm nil)); [exact (Hp l Hl) | exact Hin]).
  unfold expected_watchers in Hexp. apply in_flat_map in Hexp.
  destruct Hexp as [[q co] [Hq Hw]].
  assert (Hobj : obj_wf n co) by (eapply db_wf_obj; eassumption).
  assert (Hqe : Z.even q = true) by (eapply db_wf_even; eassumption).
  assert (Hqt : is_tag q = false) by (apply even_not_tag; exact Hqe).
  assert (H0wf : lit_wf_c n (co_watch0 co)) by (eapply obj_wf_watch0; eassumption).
  assert (H1wf : lit_wf_c n (co_watch1 co)) by (eapply obj_wf_watch1; eassumption).
  exists q, co.
  simpl in Hw. apply in_app_or in Hw.
  destruct (3 <=? Zlength (co_lits co)) eqn:Hbig.
  { exfalso.
    destruct Hw as [Hw|Hw];
      destruct (lit_neg_c (co_watch0 co) =? l);
      destruct (lit_neg_c (co_watch1 co) =? l);
      simpl in Hw; try contradiction;
      destruct Hw as [Hw|Hw]; try contradiction; subst; congruence. }
  assert (Hlen2 : Zlength (co_lits co) = 2).
  { apply Z.leb_gt in Hbig. destruct Hobj as [Hge _]. lia. }
  assert (Hshape : co_lits co = [co_watch0 co; co_watch1 co]).
  { unfold co_watch0, co_watch1. apply Zlength_two_inv. exact Hlen2. }
  destruct Hw as [Hw|Hw].
  - destruct (lit_neg_c (co_watch0 co) =? l) eqn:E0; simpl in Hw; [|contradiction].
    destruct Hw as [Hw|Hw]; [|contradiction].
    apply Z.eqb_eq in E0. subst l w.
    rewrite lit_neg_c_involutive.
    rewrite tag_lit_of.
    split; [exact Hq | split; [exact Hlen2 |]].
    rewrite Hshape. apply Permutation_refl.
  - destruct (lit_neg_c (co_watch1 co) =? l) eqn:E1; simpl in Hw; [|contradiction].
    destruct Hw as [Hw|Hw]; [|contradiction].
    apply Z.eqb_eq in E1. subst l w.
    rewrite lit_neg_c_involutive.
    rewrite tag_lit_of.
    split; [exact Hq | split; [exact Hlen2 |]].
    rewrite Hshape. apply perm_swap.
Qed.

Lemma wmap_real_witness : forall n db wm l w,
  db_wf n db -> wmap_exact n db wm -> 0 <= l < 2 * n ->
  In w (Znth l wm nil) -> is_tag w = false ->
  exists co, In (w, co) db /\ 3 <= Zlength (co_lits co) /\
             (lit_neg_c (co_watch0 co) = l \/ lit_neg_c (co_watch1 co) = l).
Proof.
  intros n db wm l w Hdb [_ Hp] Hl Hin Hreal.
  assert (Hexp : In w (expected_watchers db l))
    by (apply (Permutation_in (l := Znth l wm nil)); [exact (Hp l Hl) | exact Hin]).
  unfold expected_watchers in Hexp. apply in_flat_map in Hexp.
  destruct Hexp as [[q co] [Hq Hw]].
  simpl in Hw. apply in_app_or in Hw.
  destruct (3 <=? Zlength (co_lits co)) eqn:Hbig.
  - apply Z.leb_le in Hbig.
    destruct Hw as [Hw|Hw].
    + destruct (lit_neg_c (co_watch0 co) =? l) eqn:E0; simpl in Hw; [|contradiction].
      destruct Hw as [Hw|Hw]; [|contradiction]. subst q.
      apply Z.eqb_eq in E0.
      exists co. split; [exact Hq | split; [exact Hbig | left; exact E0]].
    + destruct (lit_neg_c (co_watch1 co) =? l) eqn:E1; simpl in Hw; [|contradiction].
      destruct Hw as [Hw|Hw]; [|contradiction]. subst q.
      apply Z.eqb_eq in E1.
      exists co. split; [exact Hq | split; [exact Hbig | right; exact E1]].
  - exfalso.
    destruct Hw as [Hw|Hw];
      [ destruct (lit_neg_c (co_watch0 co) =? l); simpl in Hw; [|contradiction]
      | destruct (lit_neg_c (co_watch1 co) =? l); simpl in Hw; [|contradiction] ];
      destruct Hw as [Hw|Hw]; try contradiction; subst w;
      rewrite is_tag_of in Hreal; discriminate.
Qed.


(** A watch move replaces the selected clause's watcher contributions.
    The difference equation also covers swapping the first two literals,
    which leaves the contribution multiset unchanged. *)
Lemma wmap_move : forall n db1 e e' db2 wm wm',
  wmap_exact n (db1 ++ e :: db2) wm ->
  Zlength wm' = 2 * n ->
  (forall l, 0 <= l < 2 * n ->
     Permutation (Znth l wm' nil ++ entry_watchers e l)
                 (Znth l wm nil ++ entry_watchers e' l)) ->
  wmap_exact n (db1 ++ e' :: db2) wm'.
Proof.
  intros n db1 e e' db2 wm wm' [_ Hp] Hlen Hdiff.
  split; [exact Hlen|]. intros l Hl.
  rewrite expected_watchers_app, expected_watchers_cons.
  specialize (Hp l Hl). specialize (Hdiff l Hl).
  rewrite expected_watchers_app, expected_watchers_cons in Hp.
  apply (Permutation_app_inv_l (entry_watchers e l)).
  eapply Permutation_trans; [apply Permutation_app_comm|].
  eapply Permutation_trans; [exact Hdiff|].
  eapply Permutation_trans;
    [apply Permutation_app_tail; exact Hp|].
  apply perm_shuffle.
Qed.

Lemma wmap_remove_clause : forall n db1 e db2 wm wm',
  wmap_exact n (db1 ++ e :: db2) wm ->
  Zlength wm' = 2 * n ->
  (forall l, 0 <= l < 2 * n ->
     Permutation (Znth l wm nil) (entry_watchers e l ++ Znth l wm' nil)) ->
  wmap_exact n (db1 ++ db2) wm'.
Proof.
  intros n db1 e db2 wm wm' [_ Hp] Hlen Hdiff.
  split; [exact Hlen|]. intros l Hl.
  specialize (Hp l Hl). specialize (Hdiff l Hl).
  rewrite expected_watchers_app, expected_watchers_cons in Hp.
  rewrite expected_watchers_app.
  apply (Permutation_app_inv_l (entry_watchers e l)).
  eapply Permutation_trans;
    [apply Permutation_sym; exact Hdiff|].
  eapply Permutation_trans; [exact Hp|].
  apply perm_swap_app.
Qed.

Lemma lit_sig_neg : forall l, lit_sig (lit_neg_c l) = - lit_sig l.
Proof.
  intros l. unfold lit_sig. rewrite lit_neg_c_odd_parity.
  destruct (Z.odd l); simpl; lia.
Qed.

Lemma lit_true_false_contra : forall assigns l,
  lit_true assigns l -> lit_false assigns l -> False.
Proof.
  intros assigns l Ht Hf. unfold lit_true, lit_false in *.
  destruct (lit_sig_values l) as [H|H]; rewrite H in *; lia.
Qed.

Lemma lit_true_assigned : forall assigns l,
  lit_true assigns l -> Znth (lit_var_c l) assigns 0 <> 0.
Proof.
  intros assigns l Ht. unfold lit_true in Ht.
  destruct (lit_sig_values l) as [H|H]; rewrite H in Ht; lia.
Qed.

Lemma lit_false_neg_true : forall assigns l,
  lit_false assigns l -> lit_true assigns (lit_neg_c l).
Proof.
  intros assigns l Hf. unfold lit_true, lit_false in *.
  rewrite lit_var_c_neg, lit_sig_neg. exact Hf.
Qed.

Definition assigns_total (n : Z) (assigns : list Z) : Prop :=
  forall v, 0 <= v < n -> Znth v assigns 0 = 1 \/ Znth v assigns 0 = -1.

Lemma lit_true_or_false : forall n assigns l,
  assigns_total n assigns -> lit_wf_c n l ->
  lit_true assigns l \/ lit_false assigns l.
Proof.
  intros n assigns l Htot Hwf.
  destruct (Htot (lit_var_c l) (lit_var_c_in_range n l Hwf)) as [H|H];
    unfold lit_true, lit_false; rewrite H; unfold lit_sig;
    destruct (Z.odd l); lia.
Qed.

Definition rho_of_model (assigns : list Z) : valuation :=
  fun x => Znth x assigns 0 =? 1.

Lemma eval_true_of_lit_true : forall assigns l,
  lit_true assigns l -> eval_literal (rho_of_model assigns) (lit_denote l) = true.
Proof.
  intros assigns l Ht. unfold lit_true, lit_sig, lit_var_c in Ht.
  unfold lit_denote, eval_literal, rho_of_model.
  destruct (Z.odd l); rewrite Ht; reflexivity.
Qed.

Lemma processed_fresh_target_different : forall assigns trail qhead p q,
  processed assigns trail qhead p ->
  Znth (lit_var_c q) assigns 0 = 0 ->
  lit_var_c q <> lit_var_c p.
Proof.
  intros assigns trail qhead p q [Hp _] Hfresh Heq.
  apply lit_true_assigned in Hp. apply Hp.
  rewrite <- Heq. exact Hfresh.
Qed.

Lemma minisat_processed_denote : forall n assigns trail qhead packed,
  lit_wf_c n packed ->
  (minisat_processed n assigns trail qhead (lit_denote packed) <->
   processed assigns trail qhead packed).
Proof.
  intros n assigns trail qhead packed Hpacked. split.
  - intros [packed' [Hpacked' [Hden Hprocessed]]].
    pose proof (lit_encode_denote n packed Hpacked) as Hencode.
    pose proof (lit_encode_denote n packed' Hpacked') as Hencode'.
    rewrite Hden, Hencode in Hencode'. subst packed'. exact Hprocessed.
  - intros Hprocessed. exists packed. split; [exact Hpacked|].
    split; [reflexivity|exact Hprocessed].
Qed.

Lemma minisat_watch_frontier_close_scan :
  forall n db assigns trail qhead p kept,
    db_wf n db ->
    lit_wf_c n p ->
    minisat_watch_frontier_except
      n db assigns trail qhead (lit_denote p) ->
    minisat_focus_scan_carrier
      db p (minisat_processed n assigns trail qhead) kept [] ->
    minisat_watch_frontier n db assigns trail qhead.
Proof.
  intros n db assigns trail qhead p kept Hdb Hp Hexcept Hscan.
  unfold minisat_focus_scan_carrier in Hscan.
  destruct Hscan as
    [scanned [pending [Hperm [Hkept [Hrest Hsafe]]]]].
  assert (Hpending : pending = []).
  { destruct pending as [|c pending]; [reflexivity|].
    unfold minisat_focus_words in Hrest. simpl in Hrest. discriminate. }
  subst pending. rewrite app_nil_r in Hperm.
  unfold minisat_watch_frontier.
  unfold minisat_watch_frontier_except in Hexcept.
  eapply watch_frontier_close; [exact Hexcept|].
  intros o Ho Hfocused.
  destruct (minisat_focused_occurrence_contributes
              n db p o Hdb Hp Ho Hfocused) as [w Hw].
  assert (Hscanned : In (o, w) scanned).
  { eapply Permutation_in.
    - apply Permutation_sym. exact Hperm.
    - exact Hw. }
  rewrite Forall_forall in Hsafe.
  pose proof (Hsafe (o, w) Hscanned) as Htoken.
  unfold minisat_occurrence_safe in Htoken. simpl in Htoken. exact Htoken.
Qed.

(** A strict backjump removes an old current-level focus. Processed
    literals in the retained trail prefix were already processed before
    cancellation; these facts close the focused watcher frontier. *)
Lemma minisat_watch_frontier_cancel_current_level :
  forall n db t reasons clauses level focus,
    mtrail_wf n t ->
    prop_level t ->
    lit_wf_c n focus ->
    0 <= level < Zlength (mt_lim t) ->
    level_of (view_of n t reasons clauses) (lit_var_c focus) =
      Some (Zlength (mt_lim t)) ->
    minisat_watch_frontier_except
      n db (mt_assigns t) (mt_trail t) (mt_qhead t) (lit_denote focus) ->
    minisat_watch_frontier
      n db (mt_assigns (mt_cancel t level))
      (mt_trail (mt_cancel t level)) (mt_qhead (mt_cancel t level)).
Proof.
  intros n db t reasons clauses level focus
    Hwf Hprop _ Hlevel Hfocus Hfrontier.
  assert (Hbound : Znth level (mt_lim t) 0 <= mt_qhead t).
  { eapply Forall_Znth_elim; [exact Hprop|exact Hlevel]. }
  pose proof (lim_lt_trail n t level Hwf Hlevel) as Hbound_range.
  assert (Htake_len :
    Zlength (ztake (Znth level (mt_lim t) 0) (mt_trail t)) =
      Znth level (mt_lim t) 0).
  { apply Zlength_ztake. lia. }
  unfold minisat_watch_frontier, minisat_watch_frontier_except in *.
  eapply watch_frontier_rollback with
      (Pnew := minisat_processed
        n (mt_assigns t) (mt_trail t) (mt_qhead t))
      (focus := lit_denote focus).
  - exact Hfrontier.
  - intros l [packed [Hpacked [Hden [Htrue [i [Hi Htrail]]]]]].
    exists packed. split; [exact Hpacked|]. split; [exact Hden|].
    split.
    + unfold lit_true in Htrue |- *.
      rewrite mt_cancel_assigns in Htrue.
      rewrite <- Htrue. symmetry. apply clear_vars_notin.
      * rewrite (mtw_assigns_len Hwf). apply lit_var_c_in_range. exact Hpacked.
      * intros x Hx. rewrite (mtw_assigns_len Hwf).
        apply lit_var_c_in_range.
        pose proof (mtw_trail_lits Hwf) as Htrail_lits.
        rewrite Forall_forall in Htrail_lits.
        apply Htrail_lits. eapply In_zdrop; eauto.
      * eapply NoDup_app_disjoint.
        -- rewrite <- map_ztake_zdrop. exact (mtw_trail_nodup Hwf).
        -- rewrite mt_cancel_qhead in Hi. rewrite mt_cancel_trail in Htrail.
           apply in_map. rewrite <- Htrail. apply Znth_In.
           rewrite Htake_len. exact Hi.
    + exists i. rewrite mt_cancel_qhead in Hi.
      rewrite mt_cancel_trail in Htrail.
      split; [lia|]. rewrite Znth_ztake in Htrail by lia. exact Htrail.
  - intros [packed [Hpacked [Hden [_ [i [Hi Htrail]]]]]].
    assert (Hvar : lit_var_c packed = lit_var_c focus).
    { rewrite <- (lit_var_c_denote packed), <- (lit_var_c_denote focus).
      rewrite Hden. reflexivity. }
    pose proof (view_of_cancel n t reasons clauses level Hwf Hlevel)
      as Hcancel.
    destruct Hcancel as [_ [_ Hcancel]].
    specialize (Hcancel (lit_var_c focus)). rewrite Hfocus in Hcancel.
    assert (Habove : (Zlength (mt_lim t) <=? level) = false)
      by (apply Z.leb_gt; lia).
    rewrite Habove in Hcancel.
    destruct Hcancel as [_ [_ [_ Hrank]]].
    cbn [view_of assignment_rank] in Hrank.
    assert (Hin : In (lit_var_c focus)
      (map lit_var_c (mt_trail (mt_cancel t level)))).
    { rewrite <- Hvar. apply in_map. rewrite <- Htrail. apply Znth_In.
      pose proof (mtw_qhead_range
        (mtrail_wf_cancel n t level Hwf Hlevel)). lia. }
    destruct (find_var_pos_in _ _ Hin) as [k Hk].
    unfold trail_pos in Hrank. rewrite Hk in Hrank. discriminate.
Qed.

Lemma minisat_watch_frontier_before_first_dequeue :
  forall db assigns trail qhead,
    qhead <= 0 -> forall n, minisat_watch_frontier n db assigns trail qhead.
Proof.
  intros db assigns trail qhead Hq n.
  unfold minisat_watch_frontier, watch_frontier.
  rewrite Forall_forall. intros o Ho [Hleft _].
  unfold minisat_processed in Hleft.
  destruct Hleft as [packed [_ [_ [_ [i [Hi _]]]]]]. lia.
Qed.

(** *** FIXPOINT.

    Every literal that is true is on the trail; if the queue is drained
    ([qhead = |trail|]) every true literal is therefore processed. *)
Definition trail_covers (n : Z) (assigns trail : list Z) : Prop :=
  forall l, lit_wf_c n l -> lit_true assigns l ->
    exists i, 0 <= i < Zlength trail /\ Znth i trail 0 = l.

Lemma minisat_processed_false_complete :
  forall n assigns trail qhead,
    assigns_total n assigns ->
    qhead = Zlength trail ->
    trail_covers n assigns trail ->
    processed_false_complete n (rho_of_model assigns)
      (minisat_processed n assigns trail qhead).
Proof.
  intros n assigns trail qhead Htotal Hqhead Hcovers l Hwf Hfalse.
  set (packed := lit_encode l).
  assert (Hpacked_wf : lit_wf_c n packed).
  { unfold packed. apply lit_encode_wf. exact Hwf. }
  destruct (lit_true_or_false n assigns packed Htotal Hpacked_wf)
    as [Htrue|Hpacked_false].
  - pose proof (eval_true_of_lit_true assigns packed Htrue) as Heval.
    unfold packed in Heval.
    rewrite (lit_denote_encode n l Hwf) in Heval.
    congruence.
  - assert (Hneg_true : lit_true assigns (lit_neg_c packed)).
    { apply lit_false_neg_true. exact Hpacked_false. }
    assert (Hneg_wf : lit_wf_c n (lit_neg_c packed)).
    { apply lit_neg_c_wf. exact Hpacked_wf. }
    destruct (Hcovers _ Hneg_wf Hneg_true) as [i [Hi Htrail]].
    exists (lit_neg_c packed). split; [exact Hneg_wf|]. split.
    + rewrite lit_denote_neg.
      * unfold packed. rewrite (lit_denote_encode n l Hwf). reflexivity.
      * destruct Hpacked_wf. lia.
    + split; [exact Hneg_true|].
      exists i. split; [rewrite Hqhead; exact Hi|exact Htrail].
Qed.

Lemma minisat_watch_fixpoint_sat : forall n db assigns trail qhead,
  db_wf n db ->
  minisat_watch_frontier n db assigns trail qhead ->
  qhead = Zlength trail ->
  trail_covers n assigns trail ->
  assigns_total n assigns ->
  forall p co, In (p, co) db ->
    clause_satisfied (rho_of_model assigns) (denote_obj co).
Proof.
  intros n db assigns trail qhead Hdb Hfrontier Hqhead Hcovers Htotal.
  pose proof (minisat_watch_occurrences_wf n db Hdb) as Hwf.
  pose proof
    (minisat_processed_false_complete
      n assigns trail qhead Htotal Hqhead Hcovers) as Hcomplete.
  pose proof
    (watch_frontier_total_satisfies
      Z n (minisat_watch_occurrences db) (rho_of_model assigns)
      (minisat_processed n assigns trail qhead) Hwf Hfrontier Hcomplete)
    as Hsatisfied.
  rewrite Forall_forall in Hsatisfied.
  intros p co Hin.
  specialize (Hsatisfied (minisat_occurrence_of_entry (p, co))).
  apply Hsatisfied.
  unfold minisat_watch_occurrences. apply in_map. exact Hin.
Qed.

(** Keep step: the entry is copied to [*j] (each of upstream's
    [*j++ = *i] write-back steps). *)
Lemma wlist_scan_keep : forall ws0 kept moved w rest,
  wlist_scan_inv ws0 kept moved (w :: rest) ->
  wlist_scan_inv ws0 (kept ++ [w]) moved rest.
Proof.
  intros ws0 kept moved w rest H. unfold wlist_scan_inv in *.
  eapply Permutation_trans; [| exact H].
  rewrite <- app_assoc. simpl.
  apply Permutation_app_head.
  apply Permutation_middle.
Qed.

(** Move step: the entry is dropped from this list and pushed onto
    [wlists[~lits[1]_new]] (upstream's
    [vecp_push(solver_read_wlist(s, lit_neg(lits[1])), *i); goto next;]
    pair); it is not copied to [*j]. *)
Lemma wlist_scan_move : forall ws0 kept moved w rest,
  wlist_scan_inv ws0 kept moved (w :: rest) ->
  wlist_scan_inv ws0 kept (moved ++ [w]) rest.
Proof.
  intros ws0 kept moved w rest H. unfold wlist_scan_inv in *.
  rewrite <- app_assoc. simpl. exact H.
Qed.

(** Conflict copy-back (upstream's two [while (i < end) *j++ = *i++;]
    loops, one after each failing [enqueue]): the whole remaining
    suffix is retained verbatim. *)
Lemma wlist_scan_abort : forall ws0 kept moved rest,
  wlist_scan_inv ws0 kept moved rest ->
  wlist_scan_inv ws0 (kept ++ rest) moved nil.
Proof.
  intros ws0 kept moved rest H. unfold wlist_scan_inv in *.
  eapply Permutation_trans; [| exact H].
  rewrite app_nil_r, <- app_assoc.
  apply Permutation_app_head. apply Permutation_app_comm.
Qed.

(** The frontier is occurrence-indexed rather than membership-only.  A scan
    moves exactly one focused occurrence at a time; cancellation rolls back
    only work in the current outer propagation iteration. *)

