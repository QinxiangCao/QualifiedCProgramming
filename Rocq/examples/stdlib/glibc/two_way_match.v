Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
From MonadLib Require Export MonadLib.
Export StateRelMonadErr.
Export MonadNotation.

From SimpleC.EE.stdlib.glibc Require Import two_way_rel_lib.
From SimpleC.EE.stdlib.glibc Require Import two_way_list_lemmas.
From SimpleC.EE.stdlib.glibc Require Import two_way_critical_factorization_theorem.

Import ListNotations.
Import SetsNotation.

Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope monad.

(* Match-phase lemmas for the two_way high-level specification proof. *)

Section MatchAlgoProof.

Context (text patn : list Z).
Context (patn_nonempty : patn <> nil).

Record match_inv (pos : Z) : Prop := {
  match_inv_pos : 0 <= pos;
  match_inv_no_occur : no_occur text patn pos
}.

Lemma critical_factorization_bounds (l p : Z) :
  critical_factorization_prop patn l p ->
  0 <= l <= Zlength patn /\ 0 < p.
Proof.
  intros Hcf.
  destruct Hcf as [[mp [Hmp [Hl [[Hp_pos _] _]]]]].
  pose proof (minimal_period_le_Zlength 0 patn mp patn_nonempty Hmp) as Hmp_le.
  split; lia.
Qed.

Lemma match_inv_init :
  match_inv 0.
Proof.
  constructor.
  - lia.
  - unfold no_occur. intros; lia.
Qed.

Record match_right_inv (l pos j : Z) : Prop := {
  match_right_inv_range : l <= j <= Zlength patn;
  match_right_inv_partial :
    sublist l j patn = sublist (pos + l) (pos + j) text
}.

Record match_right_post (l pos j : Z) : Prop := {
  match_right_post_range : l <= j <= Zlength patn;
  match_right_post_partial :
    sublist l j patn = sublist (pos + l) (pos + j) text;
  match_right_post_stop :
    j >= Zlength patn \/ Znth j patn 0 <> Znth (pos + j) text 0
}.

Lemma match_right_prop (l p pos : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  Hoare
    (fun _ => True)
    (match_right text patn pos l)
    (fun j _ => match_right_post l pos j).
Proof.
  intros Hcf Hinv Htext.
  destruct (critical_factorization_bounds l p Hcf) as [Hl _].
  destruct Hinv as [Hpos Hnoc].
  unfold match_right.
  eapply Hoare_conseq with (P2 := fun _ => match_right_inv l pos l).
  - intros st _.
    constructor; [lia|].
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
  - intros j st Hpost; exact Hpost.
  -
    eapply (@Hoare_repeat_break'
              unit Z Z
              (match_right_f text patn pos)
              (fun j _ => match_right_inv l pos j)
              (fun j _ => match_right_post l pos j)).
    + intros j.
    unfold match_right_f.
    hoare_auto.
    destruct H as [Hrange Hcond].
    destruct H0 as [Hjrange Hpm].
    constructor; [lia|].
    unfold match_cond in Hcond.
    replace (pos + (j + 1)) with (pos + j + 1) by lia.
    eapply (Zsublist_hi_plus_1 0 patn text l j (pos + l) (pos + j));
      try lia; auto.
    + intros j.
    unfold match_right_f.
    hoare_auto.
    destruct H0 as [Hjrange Hpm].
    constructor; try lia.
      * exact Hpm.
      * destruct H as [Hstop | Hneq].
        -- left; lia.
        -- right. unfold match_cond in Hneq. exact Hneq.
Qed.

Record match_left_inv (l pos j : Z) : Prop := {
  match_left_inv_range : -1 <= j < l;
  match_left_inv_partial :
    sublist (j + 1) l patn = sublist (pos + j + 1) (pos + l) text
}.

Record match_left_post (l pos j : Z) : Prop := {
  match_left_post_range : -1 <= j < l;
  match_left_post_partial :
    sublist (j + 1) l patn = sublist (pos + j + 1) (pos + l) text;
  match_left_post_stop :
    j < 0 \/ Znth j patn 0 <> Znth (pos + j) text 0
}.

Lemma match_left_prop (l p pos : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos (Zlength patn) ->
  Hoare
    (fun _ => True)
    (match_left text patn pos 0 (l - 1))
    (fun j _ => match_left_post l pos j).
Proof.
  intros Hcf Hinv Htext Hright.
  destruct (critical_factorization_bounds l p Hcf) as [Hl _].
  destruct Hinv as [Hpos Hnoc].
  unfold match_left.
  eapply Hoare_conseq with (P2 := fun _ => match_left_inv l pos (l - 1)).
  - intros st _.
    constructor; [lia|].
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
  - intros j st Hpost; exact Hpost.
  -
    eapply (@Hoare_repeat_break'
              unit Z Z
              (match_left_f text patn pos 0)
              (fun j _ => match_left_inv l pos j)
              (fun j _ => match_left_post l pos j)).
    + intros j.
    unfold match_left_f.
    hoare_auto.
    destruct H as [Hrange Hcond].
    destruct H0 as [Hjrange Hpm].
    unfold match_cond in Hcond.
    constructor; [lia|].
    replace (j - 1 + 1) with j by lia.
    replace (pos + (j - 1) + 1) with (pos + j) by lia.
    rewrite (sublist_split j l (j + 1) patn); try lia.
    rewrite (sublist_split (pos + j) (pos + l) (pos + j + 1) text); try lia.
    rewrite (sublist_single 0); try lia.
    rewrite (sublist_single 0); try lia.
    rewrite Hcond. rewrite Hpm.
    reflexivity.
    + intros j.
    unfold match_left_f.
    hoare_auto.
    destruct H0 as [Hjrange Hpm].
    constructor; try lia.
    * exact Hpm.
    *
    destruct H as [Hlt | Hneq].
    -- left; lia.
    -- right. unfold match_cond in Hneq. exact Hneq.
Qed.

Lemma match_left_prop_pre (l p pos : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  Hoare
    (fun _ => match_right_post l pos (Zlength patn))
    (match_left text patn pos 0 (l - 1))
    (fun j _ => match_left_post l pos j).
Proof.
  intros Hcf Hinv Htext.
  unfold Hoare; split.
  - intros j st1 st2 Hright Hnrm.
    pose proof (match_left_prop l p pos Hcf Hinv Htext Hright) as Hleft.
    unfold Hoare in Hleft.
    destruct Hleft as [Hleft_nrm _].
    eapply Hleft_nrm; eauto.
  - intros st Hright Herr.
    pose proof (match_left_prop l p pos Hcf Hinv Htext Hright) as Hleft.
    unfold Hoare in Hleft.
    destruct Hleft as [_ Hleft_err].
    eapply Hleft_err; eauto.
Qed.

Lemma match_left_prop_pre_keep (l p pos : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  Hoare
    (fun _ => match_right_post l pos (Zlength patn))
    (match_left text patn pos 0 (l - 1))
    (fun j _ =>
       match_right_post l pos (Zlength patn) /\
       match_left_post l pos j).
Proof.
  intros Hcf Hinv Htext.
  unfold Hoare; split.
  - intros j st1 st2 Hright Hnrm.
    split; [exact Hright|].
    pose proof (match_left_prop l p pos Hcf Hinv Htext Hright) as Hleft.
    unfold Hoare in Hleft.
    destruct Hleft as [Hleft_nrm _].
    eapply Hleft_nrm; eauto.
  - intros st Hright Herr.
    pose proof (match_left_prop l p pos Hcf Hinv Htext Hright) as Hleft.
    unfold Hoare in Hleft.
    destruct Hleft as [_ Hleft_err].
    eapply Hleft_err; eauto.
Qed.

Lemma match_right_prop_from (l p pos start : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  l <= start <= Zlength patn ->
  sublist l start patn = sublist (pos + l) (pos + start) text ->
  Hoare
    (fun _ => True)
    (match_right text patn pos start)
    (fun j _ => match_right_post l pos j).
Proof.
  intros Hcf Hinv Htext Hstart Hpartial.
  destruct (critical_factorization_bounds l p Hcf) as [Hl _].
  destruct Hinv as [Hpos Hnoc].
  unfold match_right.
  eapply Hoare_conseq with (P2 := fun _ => match_right_inv l pos start).
  - intros st _.
    constructor; auto.
  - intros j st Hpost; exact Hpost.
  -
    eapply (@Hoare_repeat_break'
              unit Z Z
              (match_right_f text patn pos)
              (fun j _ => match_right_inv l pos j)
              (fun j _ => match_right_post l pos j)).
    + intros j.
      unfold match_right_f.
      hoare_auto.
      destruct H as [Hrange Hcond].
      destruct H0 as [Hjrange Hpm].
      constructor; [lia|].
      unfold match_cond in Hcond.
      replace (pos + (j + 1)) with (pos + j + 1) by lia.
      eapply (Zsublist_hi_plus_1 0 patn text l j (pos + l) (pos + j));
        try lia; auto.
    + intros j.
      unfold match_right_f.
      hoare_auto.
      destruct H0 as [Hjrange Hpm].
      constructor; try lia.
      * exact Hpm.
      * destruct H as [Hstop | Hneq].
        -- left; lia.
        -- right. unfold match_cond in Hneq. exact Hneq.
Qed.

Record match_left_post_from (s l pos j : Z) : Prop := {
  match_left_post_from_range : -1 <= j < l;
  match_left_post_from_partial :
    sublist (j + 1) l patn = sublist (pos + j + 1) (pos + l) text;
  match_left_post_from_stop :
    j < s \/ Znth j patn 0 <> Znth (pos + j) text 0
}.

Record match_left_inv_from (s l pos j : Z) : Prop := {
  match_left_inv_from_range : -1 <= j < l;
  match_left_inv_from_partial :
    sublist (j + 1) l patn = sublist (pos + j + 1) (pos + l) text
}.

Lemma match_left_prop_from (l p pos s start : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  0 <= s ->
  start = l - 1 ->
  Hoare
    (fun _ => True)
    (match_left text patn pos s start)
    (fun j _ => match_left_post_from s l pos j).
Proof.
  intros Hcf Hinv Htext Hs Hstart.
  destruct (critical_factorization_bounds l p Hcf) as [Hl _].
  destruct Hinv as [Hpos Hnoc].
  subst start.
  unfold match_left.
  eapply Hoare_conseq with (P2 := fun _ => match_left_inv_from s l pos (l - 1)).
  - intros st _.
    constructor; [lia|].
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
  - intros j st Hpost; exact Hpost.
  -
    eapply (@Hoare_repeat_break'
              unit Z Z
              (match_left_f text patn pos s)
              (fun j _ => match_left_inv_from s l pos j)
              (fun j _ => match_left_post_from s l pos j)).
    + intros j.
      unfold match_left_f.
      hoare_auto.
      destruct H as [Hrange Hcond].
      destruct H0 as [Hjrange Hpm].
      unfold match_cond in Hcond.
      constructor; [lia|].
      replace (j - 1 + 1) with j by lia.
      replace (pos + (j - 1) + 1) with (pos + j) by lia.
      rewrite (sublist_split j l (j + 1) patn); try lia.
      rewrite (sublist_split (pos + j) (pos + l) (pos + j + 1) text); try lia.
      rewrite (sublist_single 0); try lia.
      rewrite (sublist_single 0); try lia.
      rewrite Hcond. rewrite Hpm.
      reflexivity.
    + intros j.
      unfold match_left_f.
      hoare_auto.
      destruct H0 as [Hjrange Hpm].
      constructor; try lia.
      * exact Hpm.
      * destruct H as [Hlt | Hneq].
        -- left; lia.
        -- right. unfold match_cond in Hneq. exact Hneq.
Qed.

Lemma match_left_prop_from_pre_keep (l p pos memory : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  0 <= memory ->
  Hoare
    (fun _ => match_right_post l pos (Zlength patn))
    (match_left text patn pos memory (l - 1))
    (fun j _ =>
       match_right_post l pos (Zlength patn) /\
       match_left_post_from memory l pos j).
Proof.
  intros Hcf Hbase Htext Hmem.
  unfold Hoare; split.
  - intros j st1 st2 Hright Hnrm.
    split; [exact Hright|].
    pose proof (match_left_prop_from l p pos memory (l - 1)
                 Hcf Hbase Htext Hmem eq_refl) as Hleft.
    unfold Hoare in Hleft.
    destruct Hleft as [Hleft_nrm _].
    eapply Hleft_nrm; eauto.
  - intros st Hright Herr.
    pose proof (match_left_prop_from l p pos memory (l - 1)
                 Hcf Hbase Htext Hmem eq_refl) as Hleft.
    unfold Hoare in Hleft.
    destruct Hleft as [_ Hleft_err].
    eapply Hleft_err; eauto.
Qed.

Lemma prefix_match_sublist (pos memory lo hi : Z) :
  0 <= pos ->
  0 <= lo /\ lo <= hi /\ hi <= memory ->
  sublist 0 memory patn = sublist pos (pos + memory) text ->
  sublist lo hi patn = sublist (pos + lo) (pos + hi) text.
Proof.
  intros Hpos Hrange Hprefix.
  apply (f_equal (fun xs => sublist lo hi xs)) in Hprefix.
  rewrite Zsublist_Zsublist in Hprefix; try lia.
  rewrite Zsublist_Zsublist in Hprefix; try lia.
  replace (lo + 0) with lo in Hprefix by lia.
  replace (hi + 0) with hi in Hprefix by lia.
  replace (lo + pos) with (pos + lo) in Hprefix by lia.
  replace (hi + pos) with (pos + hi) in Hprefix by lia.
  exact Hprefix.
Qed.

Record periodic_match_inv (l p pos memory : Z) : Prop := {
  periodic_match_base : match_inv pos;
  periodic_match_memory_range : 0 <= memory <= Zlength patn;
  periodic_match_memory_prefix :
    sublist 0 memory patn = sublist pos (pos + memory) text
}.

Lemma periodic_match_inv_init (l p : Z) :
  periodic_match_inv l p 0 0.
Proof.
  constructor.
  - apply match_inv_init.
  - pose proof Zlength_nonneg patn. lia.
  - repeat rewrite Zsublist_nil; try lia.
    reflexivity.
Qed.

Lemma periodic_right_start_partial (l p pos memory : Z) :
  critical_factorization_prop patn l p ->
  periodic_match_inv l p pos memory ->
  l <= Z.max l memory <= Zlength patn /\
  sublist l (Z.max l memory) patn =
  sublist (pos + l) (pos + Z.max l memory) text.
Proof.
  intros Hcf Hpinv.
  destruct (critical_factorization_bounds l p Hcf) as [Hl _].
  destruct Hpinv as [Hbase Hmem Hprefix].
  split.
  - lia.
  - destruct (Z_le_dec memory l) as [Hle | Hgt].
    + replace (Z.max l memory) with l by lia.
      repeat rewrite Zsublist_nil; try lia.
      reflexivity.
    + replace (Z.max l memory) with memory by lia.
      destruct Hbase as [Hpos _].
      apply (prefix_match_sublist pos memory); auto.
      lia.
Qed.

Lemma periodic_match_right_prop (l p pos memory : Z) :
  critical_factorization_prop patn l p ->
  periodic_match_inv l p pos memory ->
  pos + Zlength patn <= Zlength text ->
  Hoare
    (fun _ => True)
    (match_right text patn pos (Z.max l memory))
    (fun j _ => match_right_post l pos j).
Proof.
  intros Hcf Hpinv Htext.
  destruct (periodic_right_start_partial l p pos memory Hcf Hpinv)
    as [Hstart Hpartial].
  destruct Hpinv as [Hbase _ _].
  eapply match_right_prop_from; eauto.
Qed.

Lemma repetitive_split_local_period (l p : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  local_period patn l p.
Proof.
  intros Hcf Hrep.
  destruct Hcf as [[mp [Hmp [Hl [[Hp_pos Hp_le] Hminlocal]]]]].
  pose proof (minimal_period_le_Zlength 0 patn mp patn_nonempty Hmp) as Hmp_len.
  unfold repetitive_split in Hrep.
  unfold local_period.
  split; [lia|split; [lia|]].
  intros i Hi Hleft Hright.
  set (k := l + i - p).
  assert (Hk : 0 <= k < l) by (subst k; lia).
  apply (f_equal (fun xs => Znth k xs 0)) in Hrep.
  rewrite Znth_sublist in Hrep; try lia.
  rewrite Znth_sublist in Hrep; try lia.
  subst k.
  replace (l + i - p + 0) with (l + i - p) in Hrep by lia.
  replace (l + i - p + p) with (l + i) in Hrep by lia.
  exact Hrep.
Qed.

Lemma repetitive_split_period (l p : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  is_period 0 patn p.
Proof.
  intros Hcf Hrep.
  pose proof Hcf as Hcf0.
  destruct Hcf as [[mp [Hmp [Hl [[Hp_pos Hp_le] Hminlocal]]]]].
  assert (Hlocal : local_period patn l p).
  { apply repetitive_split_local_period; auto. }
  destruct Hminlocal as [_ Hmin].
  specialize (Hmin p Hlocal).
  assert (p = mp) by lia.
  subst p.
  destruct Hmp as [Hperiod _].
  exact Hperiod.
Qed.

Lemma repetitive_split_l_lt_p (l p : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  l < p.
Proof.
  intros Hcf Hrep.
  pose proof Hcf as [[mp [Hmp [Hl [[Hp_pos Hp_le] Hminlocal]]]]].
  assert (Hlocal : local_period patn l p).
  { apply repetitive_split_local_period; auto. }
  destruct Hminlocal as [_ Hmin].
  specialize (Hmin p Hlocal).
  lia.
Qed.

Lemma period_prefix_suffix (p : Z) :
  is_period 0 patn p ->
  0 < p <= Zlength patn ->
  sublist 0 (Zlength patn - p) patn =
  sublist p (Zlength patn) patn.
Proof.
  intros Hperiod Hp.
  eapply (periodic_segment' 0 patn p 1
            0 (Zlength patn - p) p (Zlength patn));
    try exact Hperiod; lia.
Qed.

Record div_mod_prop (n p q r : Z) : Prop := {
  div_mod_nonneg_pos : n >= 0 /\ p > 0;
  div_mod_eq : n = p * q + r;
  div_mod_r_bound : 0 <= r < p;
  div_mod_q_nonneg : p * q >= 0
}.

Lemma Z_pos_div_mod_prop (n p q r : Z) :
  n >= 0 -> p > 0 -> q = n / p -> r = n mod p -> div_mod_prop n p q r.
Proof.
  intros Hn Hp Hq Hr.
  constructor; subst q r.
  - lia.
  - apply Z.div_mod. lia.
  - apply Z.mod_pos_bound. lia.
  - pose proof Z.div_mod n p ltac:(lia).
    replace (p * (n / p)) with (n - n mod p) by lia.
    pose proof Z.mod_bound_pos_le n p ltac:(lia) ltac:(lia).
    lia.
Qed.

Lemma local_period_multiple_of_global_period (l w p mp : Z) :
  is_minimal_period 0 patn mp ->
  min_local_period patn l mp ->
  local_period patn l w ->
  l + w <= Zlength patn ->
  exists k, w = k * mp.
Proof.
  intros Hmp Hminlocal Hlocal Hbound.
  destruct Hminlocal as [Hmp_local Hlocal_min].
  destruct Hmp as [Hmp_period _].
  destruct Hlocal as [Hlrange [Hw_pos Hlocal_body]].
  set (q := w / mp).
  set (r := w mod mp).
  assert (Hdiv : div_mod_prop w mp q r).
  { apply Z_pos_div_mod_prop; try reflexivity.
    - lia.
    - destruct Hmp_period as [Hmp_pos _]. lia. }
  destruct Hdiv as [[Hw_nonneg Hmp_pos] Hdiv_eq Hr_bound Hq_nonneg].
  destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
  - exists q. lia.
  - assert (Hr_pos : 0 < r < mp) by lia.
    assert (Hseg :
      sublist l (l + r) patn = sublist (l + w - r) (l + w) patn).
    { rewrite Hdiv_eq.
      replace (l + (mp * q + r) - r) with (l + q * mp) by lia.
      replace (l + (mp * q + r)) with (l + r + q * mp) by lia.
      eapply (periodic_segment' 0 patn mp q
                l (l + r) (l + q * mp) (l + r + q * mp));
        try exact Hmp_period; nia. }
    assert (Hr_local : local_period patn l r).
    { unfold local_period in *.
      split; [exact Hlrange|split; [lia|]].
      intros i Hi Hleft Hright.
      assert (Znth (l + (i + w - r) - w) patn 0 =
              Znth (l + (i + w - r)) patn 0) as Hfrom_w.
      { apply Hlocal_body; try lia. }
      replace (l + (i + w - r) - w) with (l + i - r) in Hfrom_w by lia.
      apply (f_equal (fun xs => Znth i xs 0)) in Hseg.
      rewrite Znth_sublist in Hseg; try lia.
      rewrite Znth_sublist in Hseg; try lia.
      replace (i + l) with (l + i) in Hseg by lia.
      replace (i + (l + w - r)) with (l + (i + w - r)) in Hseg by lia.
      rewrite Hseg.
      exact Hfrom_w. }
    specialize (Hlocal_min r Hr_local).
    lia.
Qed.

Definition match_inv_continue (a : CntOrBrk Z (option Z)) : Prop :=
  match a with
  | by_continue pos => match_inv pos
  | by_break _ => True
  end.

Lemma match_inv_continue_right (l p pos j : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos j ->
  j < Zlength patn ->
  match_inv_continue (by_continue (pos + j - l + 1)).
Proof.
  intros Hcf Hinv Htext Hright Hjlt.
  destruct Hcf as [[mp [Hmp [Hl [[Hp_pos Hp_le] Hminlocal]]]]].
  destruct Hinv as [Hpos Hnoc].
  destruct Hright as [Hjrange Hpm Hstop].
  unfold match_inv_continue.
  constructor; [lia|].
  unfold no_occur.
  intros t Ht.
  assert (t < pos \/ pos <= t < pos + j - l + 1) as [Htprev | Htjump] by lia.
  - apply Hnoc; lia.
  - apply (f_equal (fun xs => sublist 0 (t - pos) xs)) in Hpm.
    rewrite Zsublist_Zsublist in Hpm; try lia.
    rewrite Zsublist_Zsublist in Hpm; try lia.
    replace (0 + l) with l in Hpm by lia.
    replace (0 + (pos + l)) with (pos + l) in Hpm by lia.
    replace (t - pos + (pos + l)) with (l + t) in Hpm by lia.
    intros Hmatch.
    set (q := (t - pos) / mp).
    set (r := (t - pos) mod mp).
    assert (Hdiv : div_mod_prop (t - pos) mp q r).
    { apply Z_pos_div_mod_prop; try reflexivity.
      - lia.
      - destruct Hmp as [[Hmp_pos _] _]. lia. }
    destruct Hdiv as [[Hdisp_nonneg Hmp_pos] Hdiv_eq Hr_bound Hq_nonneg].
    destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
    + assert (Hdisp : t - pos = mp * q) by lia.
      destruct Hstop as [Hstop_len | Hstop_neq]; [lia|].
      assert (Htext_char : Znth (j - (t - pos)) patn 0 = Znth (pos + j) text 0).
      { apply (f_equal (fun xs => Znth (j - (t - pos)) xs 0)) in Hmatch.
        rewrite Znth_sublist in Hmatch; try lia.
        replace (j - (t - pos) + t) with (pos + j) in Hmatch by lia.
        rewrite Hmatch. reflexivity. }
      assert (Hpatn_char : Znth (j - (t - pos)) patn 0 = Znth j patn 0).
      { destruct Hmp as [Hmp_period _].
        eapply (is_period_ext 0 mp q); try exact Hmp_period; try lia. }
      rewrite Hpatn_char in Htext_char.
      contradiction.
    + assert (Hr_pos : 0 < r < mp) by lia.
      apply (f_equal (fun xs => sublist (l - (t - pos)) l xs)) in Hmatch.
      assert (Hlocal : local_period patn l (t - pos)).
      { destruct (Z_lt_ge_dec (l - (t - pos)) 0) as [Hneg | Hnonneg].
        - rewrite Zsublist_neg_iff_Zsublist_zero in Hmatch; try lia.
          rewrite Zsublist_Zsublist in Hmatch; try lia.
          replace (0 + t) with t in Hmatch by lia.
          rewrite (Zsublist_neg_iff_Zsublist_zero (l - (t - pos))) in Hmatch; try lia.
          unfold local_period.
          split; [lia|split; [lia|]].
          intros i Hi Hleft Hright.
          apply (f_equal (fun xs => Znth i xs 0)) in Hpm.
          rewrite Znth_sublist in Hpm; try lia.
          rewrite Znth_sublist in Hpm; try lia.
          replace (i + l) with (l + i) in Hpm by lia.
          replace (i + (pos + l)) with (pos + l + i) in Hpm by lia.
          rewrite Hpm.
          apply (f_equal (fun xs => Znth (l + i - (t - pos)) xs 0)) in Hmatch.
          rewrite Znth_sublist in Hmatch; try lia.
          rewrite Znth_sublist in Hmatch; try lia.
          replace (l + i - (t - pos) + t) with (pos + l + i) in Hmatch by lia.
          replace (l + i - (t - pos) + 0) with (l + i - (t - pos)) in Hmatch by lia.
          rewrite <- Hmatch. reflexivity.
        - rewrite Zsublist_Zsublist in Hmatch; try lia.
          unfold local_period.
          split; [lia|split; [lia|]].
          intros i Hi Hleft Hright.
          apply (f_equal (fun xs => Znth i xs 0)) in Hpm.
          rewrite Znth_sublist in Hpm; try lia.
          rewrite Znth_sublist in Hpm; try lia.
          replace (i + l) with (l + i) in Hpm by lia.
          replace (i + (pos + l)) with (pos + l + i) in Hpm by lia.
          rewrite Hpm.
          apply (f_equal (fun xs => Znth i xs 0)) in Hmatch.
          rewrite Znth_sublist in Hmatch; try lia.
          rewrite Znth_sublist in Hmatch; try lia.
          replace (i + (l - (t - pos) + t)) with (pos + l + i) in Hmatch by lia.
          replace (i + (l - (t - pos))) with (l + i - (t - pos)) in Hmatch by lia.
          rewrite <- Hmatch. reflexivity. }
      assert (exists k : Z, t - pos = k * mp).
      { eapply local_period_multiple_of_global_period; eauto; lia. }
      destruct H as [q' Hq'].
      destruct (Z.lt_trichotomy q q') as [Hlt | [Heq | Hgt]]; nia.
Qed.

Lemma periodic_inv_continue_right (l p pos memory j : Z) :
  critical_factorization_prop patn l p ->
  periodic_match_inv l p pos memory ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos j ->
  j < Zlength patn ->
  periodic_match_inv l p (pos + j - l + 1) 0.
Proof.
  intros Hcf Hpinv Htext Hright Hj.
  destruct Hpinv as [Hbase Hmem Hprefix].
  constructor.
  - apply (match_inv_continue_right l p pos j); auto.
  - pose proof Zlength_nonneg patn. lia.
  - repeat rewrite Zsublist_nil; try lia.
    reflexivity.
Qed.

Lemma match_left_post_from_sublist (s l pos j lo hi : Z) :
  match_inv pos ->
  match_left_post_from s l pos j ->
  0 <= j + 1 ->
  j + 1 <= lo /\ lo <= hi /\ hi <= l ->
  sublist lo hi patn = sublist (pos + lo) (pos + hi) text.
Proof.
  intros Hbase Hleft Hjnonneg Hrange.
  destruct Hbase as [Hpos _].
  destruct Hleft as [Hjrange Hpartial Hstop].
  apply (f_equal (fun xs => sublist (lo - (j + 1)) (hi - (j + 1)) xs)) in Hpartial.
  rewrite Zsublist_Zsublist in Hpartial; try lia.
  rewrite Zsublist_Zsublist in Hpartial; try lia.
  replace (lo - (j + 1) + (j + 1)) with lo in Hpartial by lia.
  replace (hi - (j + 1) + (j + 1)) with hi in Hpartial by lia.
  replace (lo - (j + 1) + (pos + j + 1)) with (pos + lo) in Hpartial by lia.
  replace (hi - (j + 1) + (pos + j + 1)) with (pos + hi) in Hpartial by lia.
  exact Hpartial.
Qed.

Lemma match_right_post_sublist (l pos j lo hi : Z) :
  match_inv pos ->
  match_right_post l pos j ->
  0 <= l ->
  l <= lo /\ lo <= hi /\ hi <= j ->
  sublist lo hi patn = sublist (pos + lo) (pos + hi) text.
Proof.
  intros Hbase Hright Hlnonneg Hrange.
  destruct Hbase as [Hpos _].
  destruct Hright as [Hjrange Hpartial Hstop].
  apply (f_equal (fun xs => sublist (lo - l) (hi - l) xs)) in Hpartial.
  rewrite Zsublist_Zsublist in Hpartial; try lia.
  rewrite Zsublist_Zsublist in Hpartial; try lia.
  replace (lo - l + l) with lo in Hpartial by lia.
  replace (hi - l + l) with hi in Hpartial by lia.
  replace (lo - l + (pos + l)) with (pos + lo) in Hpartial by lia.
  replace (hi - l + (pos + l)) with (pos + hi) in Hpartial by lia.
  exact Hpartial.
Qed.

Lemma periodic_first_occur_break (l p pos memory j : Z) :
  critical_factorization_prop patn l p ->
  periodic_match_inv l p pos memory ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos (Zlength patn) ->
  match_left_post_from memory l pos j ->
  j < memory ->
  first_occur text patn pos.
Proof.
  intros Hcf Hpinv Htext Hright Hleft Hjmem.
  destruct (critical_factorization_bounds l p Hcf) as [Hl _].
  destruct Hpinv as [Hbase Hmem Hprefix].
  pose proof Hbase as Hbase0.
  destruct Hbase as [Hpos Hnoc].
  unfold first_occur.
  split; [exact Hnoc|].
  destruct (Z_le_dec memory l) as [Hmemle | Hmemgt].
  - assert (Hleftseg :
      sublist memory l patn =
      sublist (pos + memory) (pos + l) text).
    { eapply (match_left_post_from_sublist memory l pos j memory l); eauto; try lia.
      destruct Hleft as [Hrange _ _]. lia. }
    assert (Hrightseg :
      sublist l (Zlength patn) patn =
      sublist (pos + l) (pos + Zlength patn) text).
    { destruct Hright as [_ Hpartial _]. exact Hpartial. }
    rewrite (sublist_split pos (pos + Zlength patn) (pos + memory) text); try lia.
    rewrite (sublist_split (pos + memory) (pos + Zlength patn) (pos + l) text); try lia.
    rewrite <- Hprefix.
    rewrite <- Hleftseg.
    rewrite <- Hrightseg.
    rewrite <- (sublist_split memory (Zlength patn) l patn); try lia.
    rewrite <- (sublist_split 0 (Zlength patn) memory patn); try lia.
    apply Zsublist_all.
  - assert (Hrightseg :
      sublist memory (Zlength patn) patn =
      sublist (pos + memory) (pos + Zlength patn) text).
    { eapply (match_right_post_sublist l pos (Zlength patn) memory (Zlength patn)); eauto; lia. }
    rewrite (sublist_split pos (pos + Zlength patn) (pos + memory) text); try lia.
    rewrite <- Hprefix.
    rewrite <- Hrightseg.
    rewrite <- (sublist_split 0 (Zlength patn) memory patn); try lia.
    apply Zsublist_all.
Qed.

Lemma match_left_post_from_to_zero (l pos memory j : Z) :
  0 <= memory ->
  j >= memory ->
  match_left_post_from memory l pos j ->
  match_left_post l pos j.
Proof.
  intros Hmem Hjmem Hleft.
  destruct Hleft as [Hrange Hpartial Hstop].
  constructor.
  - lia.
  - exact Hpartial.
  - destruct Hstop as [Hlt | Hneq]; [lia|right; exact Hneq].
Qed.

Lemma match_inv_continue_left (l p pos j : Z) :
  j >= 0 ->
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos (Zlength patn) ->
  match_left_post l pos j ->
  match_inv (pos + p).
Proof.
  intros Hj Hcf Hinv Htext Hright Hleftpost.
  destruct Hcf as [[mp [Hmp [Hl [[Hp_pos Hp_le] Hminlocal]]]]].
  destruct Hinv as [Hpos Hnoc].
  destruct Hright as [_ Hpm_mrp Hnpm_mrp].
  destruct Hleftpost as [Hjrange Hpm_mlp Hnpm_mlp].
  clear Hnpm_mrp.
  constructor; [lia|].
  unfold no_occur.
  intros t Ht.
  destruct (Z.lt_trichotomy t pos) as [Hlt | [Heq | Hgt]].
  - apply Hnoc. lia.
  - subst t. intros Hmatch.
    pose proof (minimal_period_le_Zlength 0 patn mp patn_nonempty Hmp) as Hmp_len.
    apply (f_equal (fun xs => Znth j xs 0)) in Hmatch.
    rewrite Znth_sublist in Hmatch; try lia.
    replace (j + pos) with (pos + j) in Hmatch by lia.
    symmetry in Hmatch.
    destruct Hnpm_mlp as [Hjneg | Hneq]; [lia|contradiction].
  - intros Hmatch.
    pose proof (minimal_period_le_Zlength 0 patn mp patn_nonempty Hmp) as Hmp_len.
    assert (Hlocal : local_period patn l (t - pos)).
    { unfold local_period.
      split; [lia|split; [lia|]].
      intros i Hi Hleft Hright_i.
      assert (Hright_len : l + (t - pos) <= Zlength patn \/
                           l + (t - pos) > Zlength patn) by lia.
      assert (Hleft_len : 0 <= l - (t - pos) \/
                          l - (t - pos) < 0) by lia.
      destruct Hright_len as [Hr_ok | Hr_short];
      destruct Hleft_len as [Hl_ok | Hl_short].
      - assert (HsegR :
          sublist l (l + (t - pos)) patn = sublist (pos + l) (t + l) text).
        { apply (f_equal (fun xs => sublist 0 (t - pos) xs)) in Hpm_mrp.
          rewrite Zsublist_Zsublist in Hpm_mrp; try lia.
          rewrite Zsublist_Zsublist in Hpm_mrp; try lia.
          simpl in Hpm_mrp.
          replace (t - pos + l) with (l + (t - pos)) in Hpm_mrp by lia.
          replace (t - pos + (pos + l)) with (t + l) in Hpm_mrp by lia.
          exact Hpm_mrp. }
        assert (HsegL :
          sublist (l - (t - pos)) l patn = sublist (pos + l) (t + l) text).
        { apply (f_equal (fun xs => sublist (l - (t - pos)) l xs)) in Hmatch.
          rewrite Zsublist_Zsublist in Hmatch; try lia.
          replace (l - (t - pos) + t) with (pos + l) in Hmatch by lia.
          replace (l + t) with (t + l) in Hmatch by lia.
          symmetry. exact Hmatch. }
        rewrite <- HsegR in HsegL.
        apply (f_equal (fun xs => Znth i xs 0)) in HsegL.
        rewrite Znth_sublist in HsegL; try lia.
        rewrite Znth_sublist in HsegL; try lia.
        replace (i + (l - (t - pos))) with (l + i - (t - pos)) in HsegL by lia.
        replace (i + l) with (l + i) in HsegL by lia.
        exact HsegL.
      - assert (HsegR :
          sublist (t - pos) (l + (t - pos)) patn = sublist t (t + l) text).
        { apply (f_equal (fun xs => sublist (t - pos - l) (t - pos) xs)) in Hpm_mrp.
          rewrite Zsublist_Zsublist in Hpm_mrp; try lia.
          rewrite Zsublist_Zsublist in Hpm_mrp; try lia.
          replace (t - pos - l + l) with (t - pos) in Hpm_mrp by lia.
          replace (t - pos + l) with (l + (t - pos)) in Hpm_mrp by lia.
          replace (t - pos - l + (pos + l)) with t in Hpm_mrp by lia.
          replace (t - pos + (pos + l)) with (t + l) in Hpm_mrp by lia.
          exact Hpm_mrp. }
        assert (HsegL : sublist 0 l patn = sublist t (t + l) text).
        { apply (f_equal (fun xs => sublist 0 l xs)) in Hmatch.
          rewrite Zsublist_Zsublist in Hmatch; try lia.
          simpl in Hmatch.
          replace (l + t) with (t + l) in Hmatch by lia.
          symmetry. exact Hmatch. }
        rewrite <- HsegR in HsegL.
        apply (f_equal (fun xs => Znth (l + i - (t - pos)) xs 0)) in HsegL.
        rewrite Znth_sublist in HsegL; try lia.
        rewrite Znth_sublist in HsegL; try lia.
        replace (l + i - (t - pos) + 0) with (l + i - (t - pos)) in HsegL by lia.
        replace (l + i - (t - pos) + (t - pos)) with (l + i) in HsegL by lia.
        exact HsegL.
      - assert (HsegR :
          sublist l (Zlength patn) patn =
          sublist (pos + l) (pos + Zlength patn) text).
        { apply (f_equal (fun xs => sublist 0 (Zlength patn - l) xs)) in Hpm_mrp.
          rewrite Zsublist_Zsublist in Hpm_mrp; try lia.
          rewrite Zsublist_Zsublist in Hpm_mrp; try lia.
          simpl in Hpm_mrp.
          replace (Zlength patn - l + l) with (Zlength patn) in Hpm_mrp by lia.
          replace (Zlength patn - l + (pos + l)) with (pos + Zlength patn) in Hpm_mrp by lia.
          exact Hpm_mrp. }
        assert (HsegL :
          sublist (l - (t - pos)) (Zlength patn - (t - pos)) patn =
          sublist (pos + l) (pos + Zlength patn) text).
        { apply (f_equal (fun xs =>
                            sublist (l - (t - pos)) (Zlength patn - (t - pos)) xs)) in Hmatch.
          rewrite Zsublist_Zsublist in Hmatch; try lia.
          replace (l - (t - pos) + t) with (pos + l) in Hmatch by lia.
          replace (Zlength patn - (t - pos) + t) with (pos + Zlength patn) in Hmatch by lia.
          symmetry. exact Hmatch. }
        rewrite <- HsegR in HsegL.
        apply (f_equal (fun xs => Znth i xs 0)) in HsegL.
        rewrite Znth_sublist in HsegL; try lia.
        rewrite Znth_sublist in HsegL; try lia.
        replace (l + i - (t - pos)) with (i + (l - (t - pos))) by lia.
        replace (l + i) with (i + l) by lia.
        exact HsegL.
      - assert (HsegR :
          sublist (t - pos) (Zlength patn) patn =
          sublist t (pos + Zlength patn) text).
        { apply (f_equal (fun xs =>
                            sublist (t - pos - l) (Zlength patn - l) xs)) in Hpm_mrp.
          rewrite Zsublist_Zsublist in Hpm_mrp; try lia.
          rewrite Zsublist_Zsublist in Hpm_mrp; try lia.
          replace (t - pos - l + l) with (t - pos) in Hpm_mrp by lia.
          replace (Zlength patn - l + l) with (Zlength patn) in Hpm_mrp by lia.
          replace (t - pos - l + (pos + l)) with t in Hpm_mrp by lia.
          replace (Zlength patn - l + (pos + l)) with (pos + Zlength patn) in Hpm_mrp by lia.
          exact Hpm_mrp. }
        assert (HsegL :
          sublist 0 (Zlength patn - (t - pos)) patn =
          sublist t (pos + Zlength patn) text).
        { apply (f_equal (fun xs => sublist 0 (Zlength patn - (t - pos)) xs)) in Hmatch.
          rewrite Zsublist_Zsublist in Hmatch; try lia.
          replace (l - (t - pos) + t) with (pos + l) in Hmatch by lia.
          replace (Zlength patn - (t - pos) + t) with (pos + Zlength patn) in Hmatch by lia.
          symmetry. exact Hmatch. }
        rewrite <- HsegR in HsegL.
        apply (f_equal (fun xs => Znth (l + i - (t - pos)) xs 0)) in HsegL.
        rewrite Znth_sublist in HsegL; try lia.
        rewrite Znth_sublist in HsegL; try lia.
        replace (l + i - (t - pos) + 0) with (l + i - (t - pos)) in HsegL by lia.
        replace (l + i - (t - pos) + (t - pos)) with (l + i) in HsegL by lia.
        exact HsegL. }
    destruct Hminlocal as [_ Hmin].
    specialize (Hmin (t - pos) Hlocal).
    lia.
Qed.

Lemma periodic_inv_continue_left (l p pos memory j : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  periodic_match_inv l p pos memory ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos (Zlength patn) ->
  match_left_post_from memory l pos j ->
  j >= memory ->
  periodic_match_inv l p (pos + p) (Zlength patn - p).
Proof.
  intros Hcf Hrep Hpinv Htext Hright Hleft Hjmem.
  destruct (critical_factorization_bounds l p Hcf) as [Hl Hp_pos].
  pose proof (repetitive_split_l_lt_p l p Hcf Hrep) as Hl_p.
  assert (Hp_le_len : p <= Zlength patn).
  { destruct Hcf as [[mp [Hmp [_ [[_ Hp_le] _]]]]].
    pose proof (minimal_period_le_Zlength 0 patn mp patn_nonempty Hmp).
    lia. }
  destruct Hpinv as [Hbase Hmem Hprefix].
  assert (Hleft0 : match_left_post l pos j).
  { eapply match_left_post_from_to_zero; eauto; lia. }
  constructor.
  - apply (match_inv_continue_left l p pos j); auto; lia.
  - lia.
  - assert (Hper : is_period 0 patn p).
    { apply (repetitive_split_period l p); auto. }
    assert (Hpatn_shift :
      sublist 0 (Zlength patn - p) patn =
      sublist p (Zlength patn) patn).
    { apply period_prefix_suffix; lia || exact Hper. }
    assert (Htext_shift :
      sublist p (Zlength patn) patn =
      sublist (pos + p) (pos + Zlength patn) text).
    { eapply (match_right_post_sublist l pos (Zlength patn) p (Zlength patn));
        eauto; lia. }
    rewrite Hpatn_shift.
    replace (pos + p + (Zlength patn - p)) with (pos + Zlength patn) by lia.
    exact Htext_shift.
Qed.

Definition periodic_match_post_continue
    (l p : Z) (a : CntOrBrk match_periodic_state (option Z)) : Prop :=
  match a with
  | by_continue (pos, memory) => periodic_match_inv l p pos memory
  | by_break _ => True
  end.

Definition periodic_match_post_break
    (a : CntOrBrk match_periodic_state (option Z)) : Prop :=
  match a with
  | by_continue _ => True
  | by_break x => match_post text patn x
  end.

Lemma periodic_match_proof_continue (l p pos memory : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  periodic_match_inv l p pos memory ->
  Hoare
    (fun _ => True)
    (match_periodic_loop_body text patn l p (pos, memory))
    (fun res _ => periodic_match_post_continue l p res).
Proof.
  intros Hcf Hrep Hpinv.
  unfold match_periodic_loop_body.
  hoare_auto.
  - eapply Hoare_bind.
    + apply (periodic_match_right_prop l p pos memory); auto.
    + intros j.
      unfold match_periodic_from_right, match_periodic_after_right.
      hoare_auto.
      * subst j.
        unfold match_periodic_from_left, match_periodic_after_left.
        eapply Hoare_bind.
        -- destruct Hpinv as [Hbase Hmem Hprefix].
           apply (match_left_prop_from_pre_keep l p pos memory); auto; lia.
        -- intros j'.
           hoare_auto; simpl.
           ++ exact I.
           ++ destruct H1 as [Hright Hleft].
              apply (periodic_inv_continue_left l p pos memory j'); auto.
      * simpl. apply (periodic_inv_continue_right l p pos memory j); auto; try lia.
Qed.

Definition match_post_break (a : CntOrBrk Z (option Z)) : Prop :=
  match a with
  | by_continue _ => True
  | by_break x => match_post text patn x
  end.

Lemma match_proof_continue (l p pos : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  Hoare
    (fun _ => True)
    (match_loop_body text patn l p pos)
    (fun res _ =>
       match res with
       | by_continue pos' => match_inv pos'
       | by_break _ => True
       end).
Proof.
  intros Hcf Hinv.
  unfold match_loop_body.
  hoare_auto.
  - eapply Hoare_bind.
    + apply (match_right_prop l p pos); auto.
    + intros j.
      hoare_auto.
      * subst j.
        eapply Hoare_bind.
        -- apply (match_left_prop_pre_keep l p pos); auto.
        -- intros j'.
           hoare_auto; simpl;
             try (destruct H1 as [Hright Hleft];
                  apply (match_inv_continue_left l p pos j'); auto);
             try exact I.
      * apply (match_inv_continue_right l p pos); auto; try lia.
Qed.

Lemma Zlength_overflow_NotFound (l p pos : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn > Zlength text ->
  no_occur text patn (Zlength text).
Proof.
  intros Hcf Hinv Hoverflow.
  destruct Hinv as [Hpos Hnoc].
  unfold no_occur in *.
  intros j Hj Hmatch.
  assert (0 <= j < pos \/ pos <= j) as [Hjpos | Hjpos] by lia.
  - exact (Hnoc j Hjpos Hmatch).
  - assert (j + Zlength patn > Zlength text) by lia.
    rewrite Zsublist_overflow_iff_Zsublist_Zlength in Hmatch; try lia.
    apply (f_equal (@Zlength Z)) in Hmatch.
    rewrite Zlength_sublist in Hmatch; try lia.
Qed.

Lemma periodic_match_proof_break (l p pos memory : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  periodic_match_inv l p pos memory ->
  Hoare
    (fun _ => True)
    (match_periodic_loop_body text patn l p (pos, memory))
    (fun res _ => periodic_match_post_break res).
Proof.
  intros Hcf Hrep Hpinv.
  unfold match_periodic_loop_body.
  hoare_auto.
  - unfold match_periodic_from_right, match_periodic_after_right.
    eapply Hoare_bind.
    + apply (periodic_match_right_prop l p pos memory); auto.
    + intros j.
      hoare_auto.
      * subst j.
        unfold match_periodic_from_left, match_periodic_after_left.
        eapply Hoare_bind.
        -- destruct Hpinv as [Hbase Hmem Hprefix].
           apply (match_left_prop_from_pre_keep l p pos memory); auto; lia.
        -- intros j'.
           hoare_auto; simpl.
           ++ destruct H1 as [Hright Hleft].
              apply (periodic_first_occur_break l p pos memory j'); auto.
           ++ exact I.
      * exact I.
  - simpl.
    destruct Hpinv as [Hbase _ _].
    apply (Zlength_overflow_NotFound l p pos); auto.
Qed.

Lemma periodic_match_proof_continue_pre (l p pos memory : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  Hoare
    (fun _ => periodic_match_inv l p pos memory)
    (match_periodic_loop_body text patn l p (pos, memory))
    (fun res _ => periodic_match_post_continue l p res).
Proof.
  intros Hcf Hrep.
  unfold Hoare; split.
  - intros res st1 st2 Hpinv Hnrm.
    pose proof (periodic_match_proof_continue l p pos memory Hcf Hrep Hpinv) as Hbody.
    unfold Hoare in Hbody.
    destruct Hbody as [Hbody_nrm _].
    eapply Hbody_nrm; eauto.
  - intros st Hpinv Herr.
    pose proof (periodic_match_proof_continue l p pos memory Hcf Hrep Hpinv) as Hbody.
    unfold Hoare in Hbody.
    destruct Hbody as [_ Hbody_err].
    eapply Hbody_err; eauto.
Qed.

Lemma periodic_match_proof_break_pre (l p pos memory : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  Hoare
    (fun _ => periodic_match_inv l p pos memory)
    (match_periodic_loop_body text patn l p (pos, memory))
    (fun res _ => periodic_match_post_break res).
Proof.
  intros Hcf Hrep.
  unfold Hoare; split.
  - intros res st1 st2 Hpinv Hnrm.
    pose proof (periodic_match_proof_break l p pos memory Hcf Hrep Hpinv) as Hbody.
    unfold Hoare in Hbody.
    destruct Hbody as [Hbody_nrm _].
    eapply Hbody_nrm; eauto.
  - intros st Hpinv Herr.
    pose proof (periodic_match_proof_break l p pos memory Hcf Hrep Hpinv) as Hbody.
    unfold Hoare in Hbody.
    destruct Hbody as [_ Hbody_err].
    eapply Hbody_err; eauto.
Qed.

Lemma match_algo_periodic_from_correct_state (l p pos memory : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  periodic_match_inv l p pos memory ->
  Hoare
    (fun _ => True)
    (match_algo_periodic_from text patn l p pos memory)
    (fun res _ => match_post text patn res).
Proof.
  intros Hcf Hrep Hpinv.
  unfold match_algo_periodic_from.
  eapply Hoare_conseq with
    (P2 := fun _ => periodic_match_inv l p pos memory)
    (Q2 := fun res _ => match_post text patn res).
  - intros st _. exact Hpinv.
  - intros res st Hpost. exact Hpost.
  - set (s0 := (pos, memory)).
    change (Hoare
              (fun _ : unit =>
                 let '(pos0, memory0) := s0 in
                 periodic_match_inv l p pos0 memory0)
              (repeat_break (match_periodic_loop_body text patn l p) s0)
              (fun res _ => match_post text patn res)).
    eapply (@Hoare_repeat_break'
              unit match_periodic_state (option Z)
              (match_periodic_loop_body text patn l p)
              (fun s _ =>
                 let '(pos, memory) := s in periodic_match_inv l p pos memory)
              (fun res _ => match_post text patn res)).
    + intros [pos' memory'].
      eapply Hoare_bind.
      * apply (periodic_match_proof_continue_pre l p pos' memory'); auto.
      * intros [[pos'' memory''] | res].
        -- unfold continue_case. simpl. unfold Hoare; split.
           ++ intros a st1 st2 Hcont Hnrm.
              destruct Hnrm as [Heq Ha]. subst. exact Hcont.
           ++ intros st Hcont Herr. exact Herr.
        -- unfold continue_case. simpl. unfold Hoare; split; intros; contradiction.
    + intros [pos' memory'].
      eapply Hoare_bind.
      * apply (periodic_match_proof_break_pre l p pos' memory'); auto.
      * intros [[pos'' memory''] | res].
        -- unfold break_case. simpl. unfold Hoare; split; intros; contradiction.
        -- unfold break_case. simpl. unfold Hoare; split.
           ++ intros a st1 st2 Hbrk Hnrm.
              destruct Hnrm as [Heq Ha]. subst. exact Hbrk.
           ++ intros st Hbrk Herr. exact Herr.
Qed.

Theorem match_algo_periodic_correct (l p : Z) :
  critical_factorization_prop patn l p ->
  repetitive_split patn l p ->
  Hoare
    (fun _ => True)
    (match_algo_periodic_from text patn l p 0 0)
    (fun res _ => match_post text patn res).
Proof.
  intros Hcf Hrep.
  apply (match_algo_periodic_from_correct_state l p 0 0); auto.
  apply periodic_match_inv_init.
Qed.

Definition nonrepetitive_shift_prop (l p : Z) : Prop :=
  let p' := Z.max l (Zlength patn - l) + 1 in
  critical_factorization_prop patn l p'.

Lemma first_occur_break (l p pos j : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  pos + Zlength patn <= Zlength text ->
  match_right_post l pos (Zlength patn) ->
  match_left_post l pos j ->
  j < 0 ->
  first_occur text patn pos.
Proof.
  intros Hcf Hinv Htext Hright Hleft Hjlt.
  destruct Hinv as [Hpos Hnoc].
  destruct Hright as [Hrrange Hpm_r Hstop_r].
  destruct Hleft as [Hlrange Hpm_l Hstop_l].
  destruct (critical_factorization_bounds l p Hcf) as [Hlbounds _].
  unfold first_occur.
  split; [exact Hnoc|].
  assert (j = -1) by lia.
  subst j.
  replace (-1 + 1) with 0 in Hpm_l by lia.
  replace (pos + -1 + 1) with pos in Hpm_l by lia.
  rewrite (sublist_split pos (pos + Zlength patn) (pos + l) text); try lia.
  rewrite <- Hpm_l.
  rewrite <- Hpm_r.
  rewrite <- (sublist_split 0 (Zlength patn) l patn); try lia.
  apply Zsublist_all.
Qed.

Lemma match_proof_break (l p pos : Z) :
  critical_factorization_prop patn l p ->
  match_inv pos ->
  Hoare
    (fun _ => True)
    (match_loop_body text patn l p pos)
    (fun res _ => match_post_break res).
Proof.
  intros Hcf Hinv.
  unfold match_loop_body.
  hoare_auto.
  - eapply Hoare_bind.
    + apply (match_right_prop l p pos); auto.
    + intros j.
      hoare_auto.
      * subst j.
        eapply Hoare_bind.
        -- apply (match_left_prop_pre_keep l p pos); auto.
        -- intros j'.
           hoare_auto; simpl;
             try (destruct H1 as [Hright Hleft];
                  apply (first_occur_break l p pos j'); auto);
             try exact I.
      * simpl. exact I.
  - simpl.
    apply (Zlength_overflow_NotFound l p pos); auto.
Qed.

Lemma match_proof_continue_pre (l p pos : Z) :
  critical_factorization_prop patn l p ->
  Hoare
    (fun _ => match_inv pos)
    (match_loop_body text patn l p pos)
    (fun res _ =>
       match res with
       | by_continue pos' => match_inv pos'
       | by_break _ => True
       end).
Proof.
  intros Hcf.
  unfold Hoare; split.
  - intros res st1 st2 Hinv Hnrm.
    pose proof (match_proof_continue l p pos Hcf Hinv) as Hbody.
    unfold Hoare in Hbody.
    destruct Hbody as [Hbody_nrm _].
    eapply Hbody_nrm; eauto.
  - intros st Hinv Herr.
    pose proof (match_proof_continue l p pos Hcf Hinv) as Hbody.
    unfold Hoare in Hbody.
    destruct Hbody as [_ Hbody_err].
    eapply Hbody_err; eauto.
Qed.

Lemma match_proof_break_pre (l p pos : Z) :
  critical_factorization_prop patn l p ->
  Hoare
    (fun _ => match_inv pos)
    (match_loop_body text patn l p pos)
    (fun res _ => match_post_break res).
Proof.
  intros Hcf.
  unfold Hoare; split.
  - intros res st1 st2 Hinv Hnrm.
    pose proof (match_proof_break l p pos Hcf Hinv) as Hbody.
    unfold Hoare in Hbody.
    destruct Hbody as [Hbody_nrm _].
    eapply Hbody_nrm; eauto.
  - intros st Hinv Herr.
    pose proof (match_proof_break l p pos Hcf Hinv) as Hbody.
    unfold Hoare in Hbody.
    destruct Hbody as [_ Hbody_err].
    eapply Hbody_err; eauto.
Qed.

Theorem match_algo_correct (l p : Z) :
  critical_factorization_prop patn l p ->
  Hoare
    (fun _ => True)
    (match_algo text patn l p)
    (fun res _ => match_post text patn res).
Proof.
  intros Hcf.
  unfold match_algo, match_algo_from.
  eapply Hoare_conseq with
    (P2 := fun _ => match_inv 0)
    (Q2 := fun res _ => match_post text patn res).
  - intros st _. apply match_inv_init.
  - intros res st Hpost. exact Hpost.
  - eapply (@Hoare_repeat_break'
              unit Z (option Z)
              (match_loop_body text patn l p)
              (fun pos _ => match_inv pos)
              (fun res _ => match_post text patn res)).
    + intros pos.
      eapply Hoare_bind.
      * apply (match_proof_continue_pre l p pos); auto.
      * intros [pos' | res].
        -- unfold continue_case. simpl. unfold Hoare; split.
           ++ intros a st1 st2 Hpos' Hnrm.
              destruct Hnrm as [Heq Ha]. subst. exact Hpos'.
           ++ intros st Hpos' Herr. exact Herr.
        -- unfold continue_case. simpl. unfold Hoare; split; intros; contradiction.
    + intros pos.
      eapply Hoare_bind.
      * apply (match_proof_break_pre l p pos); auto.
      * intros [pos' | res].
        -- unfold break_case. simpl. unfold Hoare; split; intros; contradiction.
        -- unfold break_case. simpl. unfold Hoare; split.
           ++ intros a st1 st2 Hres Hnrm.
              destruct Hnrm as [Heq Ha]. subst. exact Hres.
           ++ intros st Hres Herr. exact Herr.
Qed.

Theorem match_phase_correct_with_nonrep_shift (l p : Z) :
  critical_factorization_prop patn l p ->
  (~ repetitive_split patn l p -> nonrepetitive_shift_prop l p) ->
  Hoare
    (fun _ => True)
    (match_phase text patn l p)
    (fun res _ => match_post text patn res).
Proof.
  intros Hcf Hnonrep.
  unfold match_phase.
  hoare_auto.
  - apply match_algo_periodic_correct; auto.
  - apply match_algo_correct.
    apply Hnonrep; auto.
Qed.

End MatchAlgoProof.

Theorem two_way_algo_complete_sound:
  forall (text patn : list Z),
    Hoare (fun _ => patn <> nil)
          (two_way_algo_complete text patn)
          (fun res _ => match_post text patn res).
Proof.
  intros text patn.
  unfold two_way_algo_complete.
  eapply Hoare_bind
    with (Q := fun res _ =>
                 patn <> nil /\
                 critical_factorization_match_prop patn (fst res) (snd res)).
  - unfold Hoare. split.
    + intros res st1 st2 Hne Hnrm.
      split; [exact Hne|].
      pose proof (critical_factorization_prog_match_sound patn Hne) as Hcf.
      unfold Hoare in Hcf.
      destruct Hcf as [Hcf_nrm _].
      eapply Hcf_nrm; eauto.
    + intros st Hne Herr.
      pose proof (critical_factorization_prog_match_sound patn Hne) as Hcf.
      unfold Hoare in Hcf.
      destruct Hcf as [_ Hcf_err].
      eapply Hcf_err; eauto.
  - intros [l p].
    unfold Hoare. split.
    + intros res st1 st2 [Hne [Hcf Hnonrep]] Hnrm.
      pose proof (match_phase_correct_with_nonrep_shift text patn Hne l p Hcf Hnonrep)
        as Hmatch.
      unfold Hoare in Hmatch.
      destruct Hmatch as [Hmatch_nrm _].
      eapply Hmatch_nrm; eauto.
    + intros st [Hne [Hcf Hnonrep]] Herr.
      pose proof (match_phase_correct_with_nonrep_shift text patn Hne l p Hcf Hnonrep)
        as Hmatch.
      unfold Hoare in Hmatch.
      destruct Hmatch as [_ Hmatch_err].
      eapply Hmatch_err; eauto.
Qed.
