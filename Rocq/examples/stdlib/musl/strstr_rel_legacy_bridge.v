From SimpleC.EE.stdlib.musl Require Import strstr_rel_lib.
From SimpleC.EE.stdlib.musl Require Import two_way_critical_factorization_theorem.
From SimpleC.EE.stdlib.musl Require Import two_way_list_lemmas.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.Lists.List.
Require Import ListLib.Base.Positional ListLib.General.Length.
Import ListNotations.
Local Open Scope Z_scope.

Lemma current_optimal_to_legacy :
  forall needle start direction cmp_fn,
    0 <= start <= Zlength needle ->
    ((direction = 1 /\ cmp_fn = Z.compare) \/
     (direction = 0 /\ cmp_fn = Z_compare_rev)) ->
    strstr_rel_lib.maxsuf_optimal needle start direction ->
    maxsuf_optimality needle cmp_fn (start - 1) 0 0 0.
Proof.
  intros needle start direction cmp_fn Hstart Hcmp Hopt earlier Hearlier.
  unfold maxsuf_index in Hearlier.
  replace (start - 1 + 1) with start in Hearlier by lia.
  specialize (Hopt earlier Hearlier).
  destruct Hopt as [d [Hd [Hend [Hearlier_end [Heq [Hgt Hrev]]]]]].
  unfold maxsuf_index.
  replace (start - 1 + 1) with start by lia.
  unfold list_lex_gt. left.
  apply (proj2 (list_lex_gt_ex_ex' Z 0 cmp_fn
    (skipn' start needle) (skipn' earlier needle))).
  exists d. split; [exact Hd |].
  split; [unfold skipn'; rewrite Zlength_sublist by lia; lia |].
  split; [unfold skipn'; rewrite Zlength_sublist by lia; lia |].
  unfold list_lex_gt_ex'. split.
    + apply (Zsublist_eq_ext 0).
      * repeat rewrite Zlength_sublist by (unfold skipn'; rewrite Zlength_sublist; lia).
        reflexivity.
      * intros t Ht.
        assert (Ht0 : 0 <= t < d).
        { unfold skipn' in Ht.
          rewrite Zlength_sublist in Ht by (rewrite Zlength_sublist; lia).
          lia. }
        unfold skipn'.
        repeat rewrite Znth_sublist by lia.
        replace (t + 0 + start) with (start + t) by lia.
        replace (t + 0 + earlier) with (earlier + t) by lia.
        apply Heq; lia.
    + unfold skipn'. repeat rewrite Znth_sublist by lia.
      destruct Hcmp as [[Hdir Hcmp] | [Hdir Hcmp]]; subst.
      * apply Z.compare_gt_iff. specialize (Hgt eq_refl).
        replace (d + start) with (start + d) by lia.
        replace (d + earlier) with (earlier + d) by lia. lia.
      * unfold Z_compare_rev. apply Z.compare_gt_iff.
        specialize (Hrev eq_refl).
        replace (d + start) with (start + d) by lia.
        replace (d + earlier) with (earlier + d) by lia. lia.
Qed.

Lemma current_intermediate_to_legacy :
  forall needle start period direction cmp_fn,
    0 <= start -> 0 < period -> start + period <= Zlength needle ->
    ((direction = 1 /\ cmp_fn = Z.compare) \/
     (direction = 0 /\ cmp_fn = Z_compare_rev)) ->
    strstr_rel_lib.maxsuf_intermediate_optimal
      needle start period direction ->
    maxsuf_optimality2 needle cmp_fn (start - 1) 0 0 period.
Proof.
  intros needle start period direction cmp_fn Hstart Hp Hbound Hcmp Hmid t Ht.
  unfold maxsuf_index in Ht.
  replace (start - 1 + 1) with start in Ht by lia.
  specialize (Hmid t Ht).
  destruct Hmid as [d [Hd [Hend [Hneedle [Heq [Hgt Hrev]]]]]].
  unfold maxsuf_index.
  replace (start - 1 + 1) with start by lia.
  apply (proj2 (list_lex_gt_ex_ex' Z 0 cmp_fn
    (sublist start (start + period) needle)
    (sublist t (start + period) needle))).
  exists d. split; [exact Hd |].
  split; [rewrite Zlength_sublist by lia; lia |].
  split; [rewrite Zlength_sublist by lia; lia |].
  unfold list_lex_gt_ex'. split.
  - apply (Zsublist_eq_ext 0).
    + repeat rewrite Zlength_sublist by (rewrite Zlength_sublist; lia).
      reflexivity.
    + intros u Hu.
      assert (Hu0 : 0 <= u < d).
      { rewrite Zlength_sublist in Hu by (rewrite Zlength_sublist; lia).
        lia. }
      repeat rewrite Znth_sublist by lia.
      replace (u + 0 + start) with (start + u) by lia.
      replace (u + 0 + t) with (t + u) by lia.
      apply Heq; lia.
  - repeat rewrite Znth_sublist by lia.
    destruct Hcmp as [[Hdir Hcmp] | [Hdir Hcmp]]; subst.
    + apply Z.compare_gt_iff. specialize (Hgt eq_refl).
      replace (d + start) with (start + d) by lia.
      replace (d + t) with (t + d) by lia. lia.
    + unfold Z_compare_rev. apply Z.compare_gt_iff.
      specialize (Hrev eq_refl).
      replace (d + start) with (start + d) by lia.
      replace (d + t) with (t + d) by lia. lia.
Qed.

Lemma current_suffix_period_to_legacy :
  forall needle start period direction,
    0 <= start -> 0 < period ->
    start + period <= Zlength needle ->
    (direction = 0 \/ direction = 1) ->
    strstr_rel_lib.maxsuf_intermediate_optimal
      needle start period direction ->
    strstr_rel_lib.maxsuf_suffix_period needle start period ->
    is_minimal_period 0 (skipn' start needle) period.
Proof.
  intros needle start period direction Hstart Hp Hbound Hdir Hmid Hsuffix.
  unfold is_minimal_period. split.
  - unfold is_period. split; [exact Hp |].
    intros i Hi Hibound.
    unfold skipn' in Hibound |- *.
    rewrite Zlength_sublist in Hibound by lia.
    repeat rewrite Znth_sublist by lia.
    replace (i + period + start) with (i + start + period) by lia.
    apply Hsuffix; lia.
  - intros q [Hq Hqperiod].
    destruct (Z_le_gt_dec period q) as [Hle | Hgt]; [lia |].
    specialize (Hmid (start + q) ltac:(lia)).
    destruct Hmid as [d [Hd [_ [Hend [_ [Hfwd Hrev]]]]]].
    specialize (Hqperiod d ltac:(lia)).
    unfold skipn' in Hqperiod.
    rewrite Zlength_sublist in Hqperiod by lia.
    assert (Hdq : d + q < Zlength needle - start) by lia.
    specialize (Hqperiod Hdq).
    repeat rewrite Znth_sublist in Hqperiod by lia.
    replace (d + start) with (start + d) in Hqperiod by lia.
    replace (d + q + start) with (start + q + d) in Hqperiod by lia.
    destruct Hdir as [Hdir | Hdir]; subst direction.
    + specialize (Hrev eq_refl). lia.
    + specialize (Hfwd eq_refl). lia.
Qed.

Lemma current_scan_to_legacy_break :
  forall needle start period direction cmp_fn,
    0 <= start < Zlength needle ->
    0 < period <= Zlength needle - start ->
    ((direction = 1 /\ cmp_fn = Z.compare) \/
     (direction = 0 /\ cmp_fn = Z_compare_rev)) ->
    strstr_rel_lib.maxsuf_optimal needle start direction ->
    strstr_rel_lib.maxsuf_intermediate_optimal
      needle start period direction ->
    strstr_rel_lib.maxsuf_suffix_period needle start period ->
    exists j k,
      j + k = Zlength needle /\
      maxsuf_inv needle cmp_fn (start - 1) j k period.
Proof.
  intros needle start period direction cmp_fn Hstart Hp Hcmp Hopt Hmid Hsuffix.
  set (n := Zlength needle - start).
  set (z := n / period).
  set (r := n mod period).
  set (j := start + z * period - 1).
  set (k := r + 1).
  assert (Hdiv : n = z * period + r).
  { unfold z, r. pose proof (Z.div_mod n period ltac:(lia)). nia. }
  assert (Hr : 0 <= r < period).
  { unfold r. apply Z.mod_pos_bound; lia. }
  assert (Hz : 1 <= z) by (unfold n in *; nia).
  exists j, k.
  split; [unfold j, k, n in *; lia |].
  constructor.
  - constructor.
    + unfold j. lia.
    + unfold k. lia.
    + exists z. unfold maxsuf_probe, maxsuf_index, j. lia.
  - unfold maxsuf_partial_match, maxsuf_index, maxsuf_probe.
    replace (start - 1 + 1) with start by lia.
    eapply (maxsuf_periodic_extension needle
      (start - 1) j k period z); try lia.
    + unfold maxsuf_index. lia.
    + unfold maxsuf_index, maxsuf_probe, j. nia.
    + unfold maxsuf_periodicity, maxsuf_index.
      intros t Ht Htend. apply Hsuffix; lia.
    + unfold maxsuf_index, j, k, n in *. split; lia.
    + unfold maxsuf_index, j, k, n in *. split; lia.
  - eapply current_optimal_to_legacy; eauto; lia.
  - unfold maxsuf_periodicity, maxsuf_index.
    intros t Ht Htend. apply Hsuffix; lia.
  - eapply current_intermediate_to_legacy; eauto; lia.
Qed.

Lemma current_maxsuf_is_maximal :
  forall needle start period direction cmp_fn,
    Cmp Z cmp_fn ->
    0 <= start < Zlength needle ->
    0 < period <= Zlength needle - start ->
    ((direction = 1 /\ cmp_fn = Z.compare) \/
     (direction = 0 /\ cmp_fn = Z_compare_rev)) ->
    strstr_rel_lib.maxsuf_optimal needle start direction ->
    strstr_rel_lib.maxsuf_intermediate_optimal
      needle start period direction ->
    strstr_rel_lib.maxsuf_suffix_period needle start period ->
    is_maximal_suffix cmp_fn needle start.
Proof.
  intros needle start period direction cmp_fn Hcmpclass Hstart Hp Hcmp Hopt Hmid Hsuffix.
  destruct (current_scan_to_legacy_break needle start period direction cmp_fn
    Hstart Hp Hcmp Hopt Hmid Hsuffix) as [j [k [Hexit Hinv]]].
  pose proof (maxsuf_break_is_maximal_suffix needle cmp_fn Hcmpclass
    (start - 1, j, k, period) Hinv) as [Hsound _].
  replace start with ((start - 1) + 1) by lia.
  apply (Hsound (start - 1, period) tt tt I).
  unfold two_way_rel_lib.maxsuf_cal_body.
  simpl.
  unfold MonadErr.nrm_nrm.
  exists (by_break (start - 1, period)), tt.
  split.
  - left. unfold MonadErr.nrm_nrm.
    exists tt, tt. split.
    + split; [reflexivity | exact Hexit].
    + split; reflexivity.
  - split; reflexivity.
Qed.

Lemma current_scan_start_bounded :
  forall needle start direction,
    0 < Zlength needle ->
    0 <= start ->
    strstr_rel_lib.maxsuf_optimal needle start direction ->
    start < Zlength needle.
Proof.
  intros needle start direction Hlen Hstart Hopt.
  destruct (Z_lt_ge_dec start (Zlength needle)) as [Hlt | Hge]; [exact Hlt |].
  assert (Hpos : 0 < start) by lia.
  specialize (Hopt 0 ltac:(lia)).
  destruct Hopt as [d [Hd [Hend _]]]. lia.
Qed.

Lemma current_scan_period_bounded :
  forall needle start period direction,
    0 <= start < Zlength needle ->
    0 < period ->
    strstr_rel_lib.maxsuf_intermediate_optimal
      needle start period direction ->
    start + period <= Zlength needle.
Proof.
  intros needle start period direction Hstart Hp Hmid.
  destruct (Z.eq_dec period 1) as [Hone | Hmore]; [lia |].
  specialize (Hmid (start + period - 1) ltac:(lia)).
  destruct Hmid as [d [Hd [_ [Hend _]]]]. lia.
Qed.

Lemma current_scan_to_maxsuf_prop :
  forall needle start period direction cmp_fn,
    Cmp Z cmp_fn ->
    0 < Zlength needle -> 0 <= start -> 0 < period ->
    ((direction = 1 /\ cmp_fn = Z.compare) \/
     (direction = 0 /\ cmp_fn = Z_compare_rev)) ->
    strstr_rel_lib.maxsuf_optimal needle start direction ->
    strstr_rel_lib.maxsuf_intermediate_optimal
      needle start period direction ->
    strstr_rel_lib.maxsuf_suffix_period needle start period ->
    maxsuf_prop needle cmp_fn start period.
Proof.
  intros needle start period direction cmp_fn Hclass Hlen Hstart Hp
    Hcmp Hopt Hmid Hsuffix.
  assert (Hstartbound : 0 <= start < Zlength needle).
  { split; [exact Hstart |].
    eapply current_scan_start_bounded; eauto. }
  assert (Hperiodbound : start + period <= Zlength needle).
  { eapply current_scan_period_bounded; eauto. }
  assert (Hdir : direction = 0 \/ direction = 1).
  { destruct Hcmp as [[Hdir _] | [Hdir _]];
      [right | left]; exact Hdir. }
  constructor.
  - eapply current_maxsuf_is_maximal; eauto; lia.
  - eapply current_suffix_period_to_legacy; eauto; lia.
Qed.

Lemma current_pair_nonrep_critical_split :
  forall needle first first_period second second_period split scan_period,
    0 < Zlength needle ->
    0 <= first -> 0 <= second -> 0 <= split ->
    0 < first_period -> 0 < second_period -> 0 < scan_period ->
    selected_maxsuf_cuts split first second ->
    strstr_rel_lib.maxsuf_optimal needle first 1 ->
    strstr_rel_lib.maxsuf_intermediate_optimal needle first first_period 1 ->
    strstr_rel_lib.maxsuf_suffix_period needle first first_period ->
    strstr_rel_lib.maxsuf_optimal needle second 0 ->
    strstr_rel_lib.maxsuf_intermediate_optimal needle second second_period 0 ->
    strstr_rel_lib.maxsuf_suffix_period needle second second_period ->
    selected_maxsuf needle split scan_period ->
    strstr_rel_lib.maxsuf_suffix_period needle split scan_period ->
    sublist 0 split needle <> sublist scan_period (split + scan_period) needle ->
    critical_split needle split
      (Z.max split (Zlength needle - split) + 1).
Proof.
  intros needle first first_period second second_period split scan_period
    Hlen Hfirst Hsecond Hsplit Hfp Hsp Hscan Hcuts
    Hfopt Hfmid Hfsuffix Hsopt Hsmid Hssuffix
    Hselected Hselected_suffix Hnonrep.
  assert (Hne : needle <> []).
  { intro Heq. subst needle. cbn in Hlen. lia. }
  pose proof (current_scan_to_maxsuf_prop needle first first_period 1
    Z.compare Cmp_Zcompare Hlen Hfirst Hfp
    (or_introl (conj eq_refl eq_refl)) Hfopt Hfmid Hfsuffix) as Hfprop.
  pose proof (current_scan_to_maxsuf_prop needle second second_period 0
    Z_compare_rev Cmp_Zcompare_rev Hlen Hsecond Hsp
    (or_intror (conj eq_refl eq_refl)) Hsopt Hsmid Hssuffix) as Hsprop.
  destruct (least_string_period_exists needle Hlen) as [mp [Hglobal Hleast]].
  assert (Hlegacy_global : is_minimal_period 0 needle mp).
  { split; [exact Hglobal |].
    intros q Hq. specialize (Hleast q Hq). lia. }
  pose proof (critical_factorization_theorem needle Hne
    first second mp (maxsuf_is_maximal _ _ _ _ Hfprop)
    (maxsuf_is_maximal _ _ _ _ Hsprop) Hlegacy_global) as Hlocal.
  unfold selected_maxsuf_cuts in Hcuts.
  rewrite <- Hcuts in Hlocal.
  assert (Hsplitbound : 0 <= split <= Zlength needle).
  { destruct (maxsuf_is_maximal _ _ _ _ Hfprop) as [Hfcut _].
    destruct (maxsuf_is_maximal _ _ _ _ Hsprop) as [Hscut _].
    lia. }
  assert (Hselected_prop :
    (maxsuf_prop needle Z.compare split scan_period) \/
    (maxsuf_prop needle Z_compare_rev split scan_period)).
  { destruct Hselected as [[Hopt Hmid] | [Hopt Hmid]].
    - right. eapply (current_scan_to_maxsuf_prop needle split
        scan_period 0 Z_compare_rev Cmp_Zcompare_rev Hlen Hsplit Hscan);
        [right; split; reflexivity | exact Hopt | exact Hmid |
         exact Hselected_suffix].
    - left. eapply (current_scan_to_maxsuf_prop needle split
        scan_period 1 Z.compare Cmp_Zcompare Hlen Hsplit Hscan);
        [left; split; reflexivity | exact Hopt | exact Hmid |
         exact Hselected_suffix].
  }
  assert (Hshift : Z.max split (Zlength needle - split) + 1 <= mp).
  { destruct Hselected_prop as [Hprop | Hprop].
    - eapply (maxsuf_nonrep_shift_le_global needle Hne
        Z.compare split scan_period mp);
        [exact Cmp_Zcompare | exact Hlegacy_global | exact Hprop |
         exact Hlocal | unfold two_way_rel_lib.repetitive_split;
         exact Hnonrep].
    - eapply (maxsuf_nonrep_shift_le_global needle Hne
        Z_compare_rev split scan_period mp);
        [exact Cmp_Zcompare_rev | exact Hlegacy_global | exact Hprop |
         exact Hlocal | unfold two_way_rel_lib.repetitive_split;
         exact Hnonrep]. }
  pose proof (selected_maxsuf_critical_split needle split scan_period
    Hlen Hsplitbound Hscan Hselected) as Hcritical.
  destruct Hcritical as [mp' [[Hglobal' Hleast'] [Hcut [Hscanbound Hloc']]]].
  assert (Hmp : mp = mp').
  { specialize (Hleast mp' Hglobal').
    specialize (Hleast' mp Hglobal). lia. }
  subst mp'.
  exists mp. split; [split; assumption |].
  split; [exact Hcut |].
  split; [lia |].
  unfold local_period. destruct Hglobal as [Hmp_pos Hrepeat].
  repeat split; try lia.
  intros j Hj Hleft Hright.
  specialize (Hrepeat (split + j - mp) ltac:(lia) ltac:(lia)).
  replace (split + j - mp + mp) with (split + j) in Hrepeat by lia.
  exact Hrepeat.
Qed.

Lemma selected_maxsuf_period_bound :
  forall needle split period,
    0 <= split < Zlength needle -> 0 < period ->
    selected_maxsuf needle split period ->
    split + period <= Zlength needle.
Proof.
  intros needle split period Hsplit Hp [[_ Hmid] | [_ Hmid]];
    eapply current_scan_period_bounded; eauto.
Qed.

Lemma memcmp_nonzero_needle_nonrep :
  forall needle split period ret,
    0 <= split -> 0 <= period -> split + period <= Zlength needle ->
    memcmp_zero (needle ++ [0]) 0 period split ret -> ret <> 0 ->
    sublist 0 split needle <> sublist period (split + period) needle.
Proof.
  intros needle split period ret Hsplit Hp Hbound [_ Hcmp] Hret Heq.
  apply Hret. apply (proj2 Hcmp).
  repeat rewrite sublist_split_app_l by lia.
  replace (0 + split) with split by lia.
  replace (period + split) with (split + period) by lia.
  exact Heq.
Qed.

Lemma critical_split_weaken_shift :
  forall needle split big small,
    critical_split needle split big ->
    0 < small <= big ->
    critical_split needle split small.
Proof.
  intros needle split big small [period [Hleast [Hcut [Hshift Hlocal]]]] Hsmall.
  exists period. split; [exact Hleast |].
  split; [exact Hcut |].
  split; [lia | exact Hlocal].
Qed.


Lemma current_pair_min_local :
  forall needle first first_period second second_period split,
    0 < Zlength needle ->
    0 <= first -> 0 <= second ->
    0 < first_period -> 0 < second_period ->
    selected_maxsuf_cuts split first second ->
    strstr_rel_lib.maxsuf_optimal needle first 1 ->
    strstr_rel_lib.maxsuf_intermediate_optimal needle first first_period 1 ->
    strstr_rel_lib.maxsuf_suffix_period needle first first_period ->
    strstr_rel_lib.maxsuf_optimal needle second 0 ->
    strstr_rel_lib.maxsuf_intermediate_optimal needle second second_period 0 ->
    strstr_rel_lib.maxsuf_suffix_period needle second second_period ->
    critical_min_local needle split.
Proof.
  intros needle first first_period second second_period split
    Hlen Hfirst Hsecond Hfp Hsp Hcuts
    Hfopt Hfmid Hfsuffix Hsopt Hsmid Hssuffix.
  assert (Hne : needle <> []) by (intro Heq; subst needle; cbn in Hlen; lia).
  pose proof (current_scan_to_maxsuf_prop needle first first_period 1
    Z.compare Cmp_Zcompare Hlen Hfirst Hfp
    (or_introl (conj eq_refl eq_refl)) Hfopt Hfmid Hfsuffix) as Hfprop.
  pose proof (current_scan_to_maxsuf_prop needle second second_period 0
    Z_compare_rev Cmp_Zcompare_rev Hlen Hsecond Hsp
    (or_intror (conj eq_refl eq_refl)) Hsopt Hsmid Hssuffix) as Hsprop.
  destruct (least_string_period_exists needle Hlen) as [mp [Hglobal Hleast]].
  assert (Hlegacy_global : is_minimal_period 0 needle mp).
  { split; [exact Hglobal |].
    intros q Hq. specialize (Hleast q Hq). lia. }
  pose proof (critical_factorization_theorem needle Hne
    first second mp (maxsuf_is_maximal _ _ _ _ Hfprop)
    (maxsuf_is_maximal _ _ _ _ Hsprop) Hlegacy_global) as Hlocal.
  unfold selected_maxsuf_cuts in Hcuts.
  rewrite <- Hcuts in Hlocal.
  unfold critical_min_local.
  exists mp. split; [split; assumption |].
  unfold min_local_period in Hlocal.
  destruct Hlocal as [Hloc Hmin].
  split.
  - unfold strstr_rel_lib.local_period, two_way_critical_factorization_theorem.local_period in *.
    exact Hloc.
  - intros q Hq. specialize (Hmin q).
    unfold strstr_rel_lib.local_period, two_way_critical_factorization_theorem.local_period in *.
    specialize (Hmin Hq). lia.
Qed.
