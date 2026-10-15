Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition DecimalValue (digits : list Z) : Z :=
  fold_left (fun value digit => 10 * value + digit) digits 0.

Definition BadUglyDigits (n : Z) (digits : list Z) : Prop :=
  Zlength digits = n /\
  Forall (fun d => 1 <= d <= 9) digits /\
  DecimalValue digits > 0 /\
  Forall (fun d => ~ (d | DecimalValue digits)) digits.

Definition Pre (n : Z) : Prop :=
  1 <= n <= 100000.

Definition Spec (n : Z) (out : option (list Z)) : Prop :=
  (exists digits, out = Some digits /\ BadUglyDigits n digits) \/
  (out = None /\ forall digits, ~ BadUglyDigits n digits).

Require Import Coq.micromega.Psatz.
Lemma decimal_value_acc_last_digit_mod_2__spec_results :
  forall digits acc,
    digits <> nil ->
    fold_left (fun value digit => 10 * value + digit) digits acc mod 2 =
    last digits 0 mod 2.
Proof.
  induction digits as [|d digits IH]; intros acc Hne.
  - contradiction.
  - destruct digits as [|e digits].
    + simpl.
      change ((10 * acc + d) mod 2 = d mod 2).
      assert (Hten : (10 * acc) mod 2 = 0).
      { replace (10 * acc) with ((5 * acc) * 2) by ring.
        apply Z.mod_mul. lia. }
      rewrite Z.add_mod by lia.
      rewrite Hten. simpl.
      rewrite Z.mod_mod by lia.
      reflexivity.
    + simpl.
      apply IH.
      discriminate.
Qed.
Lemma decimal_value_last_digit_mod_2__spec_results :
  forall digits,
    digits <> nil ->
    DecimalValue digits mod 2 = last digits 0 mod 2.
Proof.
  intros digits Hne.
  unfold DecimalValue.
  apply decimal_value_acc_last_digit_mod_2__spec_results.
  exact Hne.
Qed.
Lemma decimal_value_acc_digit_sum_mod_3__spec_results :
  forall digits acc,
    fold_left (fun value digit => 10 * value + digit) digits acc mod 3 =
    (acc + fold_right Z.add 0 digits) mod 3.
Proof.
  induction digits as [|d digits IH]; intros acc.
  - simpl. f_equal. lia.
  - simpl.
    rewrite IH.
    change ((10 * acc + d + fold_right Z.add 0 digits) mod 3 =
            (acc + (d + fold_right Z.add 0 digits)) mod 3).
    replace (10 * acc + d + fold_right Z.add 0 digits)
      with ((acc + d + fold_right Z.add 0 digits) + (3 * acc) * 3) by ring.
    rewrite Z.add_mod by lia.
    assert (Hnine : ((3 * acc) * 3) mod 3 = 0).
    { apply Z.mod_mul. lia. }
    rewrite Hnine. simpl.
    replace (acc + d + fold_right Z.add 0 digits)
      with (acc + (d + fold_right Z.add 0 digits)) by ring.
    rewrite Z.add_0_r.
    rewrite Z.mod_mod by lia.
    reflexivity.
Qed.
Lemma decimal_value_digit_sum_mod_3__spec_results :
  forall digits,
    DecimalValue digits mod 3 = fold_right Z.add 0 digits mod 3.
Proof.
  intros digits.
  unfold DecimalValue.
  rewrite decimal_value_acc_digit_sum_mod_3__spec_results.
  f_equal.
Qed.
Lemma all_Znth_eq_Forall__spec_results :
  forall (l : list Z) d v,
    (forall k, 0 <= k < Zlength l -> Znth k l d = v) ->
    Forall (fun x => x = v) l.
Proof.
  induction l as [|x l IH]; intros d v Hall.
  - constructor.
  - pose proof (Zlength_nonneg l).
    constructor.
    + specialize (Hall 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hall.
      exact Hall.
    + apply IH with (d := d).
      intros k Hk.
      specialize (Hall (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hall by lia.
      replace (k + 1 - 1) with k in Hall by lia.
      exact Hall.
Qed.
Lemma fold_right_add_of_Forall_eq__spec_results :
  forall (l : list Z) v,
    Forall (fun x => x = v) l ->
    fold_right Z.add 0 l = v * Zlength l.
Proof.
  intros l v Hall.
  induction Hall.
  - simpl. rewrite Zlength_nil. ring.
  - simpl. rewrite Zlength_cons. subst x. rewrite IHHall. ring.
Qed.
Lemma decimal_fold_positive__spec_results :
  forall digits acc,
    0 < acc ->
    Forall (fun d => 0 <= d) digits ->
    0 < fold_left (fun value digit => 10 * value + digit) digits acc.
Proof.
  induction digits as [|d digits IH]; intros acc Hacc Hall.
  - exact Hacc.
  - inversion Hall; subst.
    simpl.
    apply IH; auto.
    change (0 < 10 * acc + d).
    nia.
Qed.
Lemma last_of_Forall_eq__spec_results :
  forall (l : list Z) v d,
    l <> nil ->
    Forall (fun x => x = v) l ->
    last l d = v.
Proof.
  induction l as [|x l IH]; intros v d Hne Hall.
  - contradiction.
  - inversion Hall; subst.
    destruct l as [|y l].
    + reflexivity.
    + simpl. apply IH; auto. discriminate.
Qed.
Lemma last_cons_nonempty__spec_results :
  forall (a : Z) l d,
    l <> nil -> last (cons a l) d = last l d.
Proof.
  intros a l d Hne.
  destruct l; [contradiction | reflexivity].
Qed.
Lemma two_then_threes_bad_ugly__spec_results :
  forall n digits,
    2 <= n ->
    Zlength digits = n ->
    Znth 0 digits 0 = 2 ->
    (forall k, 1 <= k < n -> Znth k digits 0 = 3) ->
    BadUglyDigits n digits.
Proof.
  intros n digits Hn Hlen Hfirst Hlater.
  destruct digits as [|d tail].
  - rewrite Zlength_nil in Hlen. lia.
  - rewrite Znth0_cons in Hfirst. subst d.
    assert (Htail_len : Zlength tail = n - 1).
    { rewrite Zlength_cons in Hlen. lia. }
    assert (Htail_values : Forall (fun x => x = 3) tail).
    { apply all_Znth_eq_Forall__spec_results with (d := 0).
      intros k Hk.
      specialize (Hlater (k + 1) ltac:(lia)).
      rewrite Znth_cons in Hlater by lia.
      replace (k + 1 - 1) with k in Hlater by lia.
      exact Hlater. }
    assert (Htail_nonempty : tail <> nil).
    { intro Heq. subst tail. rewrite Zlength_nil in Htail_len. lia. }
    unfold BadUglyDigits.
    split; [exact Hlen |].
    split.
    { constructor; [lia |].
      apply Forall_forall. intros x Hin.
      rewrite Forall_forall in Htail_values.
      specialize (Htail_values x Hin). subst x. lia. }
    split.
    { unfold DecimalValue.
      apply Z.lt_gt.
      change (0 < fold_left (fun value digit => 10 * value + digit) tail 2).
      apply decimal_fold_positive__spec_results; [lia |].
      apply Forall_forall. intros x Hin.
      rewrite Forall_forall in Htail_values.
      specialize (Htail_values x Hin). subst x. lia. }
    constructor.
    { intro Hdiv.
      apply (proj2 (Z.mod_divide (DecimalValue (cons 2 tail)) 2 ltac:(lia))) in Hdiv.
      pose proof (decimal_value_last_digit_mod_2__spec_results (cons 2 tail)
                    ltac:(discriminate)) as Hmod.
      rewrite (last_cons_nonempty__spec_results 2 tail 0 Htail_nonempty) in Hmod.
      rewrite (last_of_Forall_eq__spec_results tail 3 0 Htail_nonempty Htail_values) in Hmod.
      change (DecimalValue (cons 2 tail) mod 2 = 1) in Hmod.
      lia. }
    { apply Forall_forall. intros x Hin.
      pose proof Htail_values as Htail_values_at_x.
      rewrite Forall_forall in Htail_values_at_x.
      specialize (Htail_values_at_x x Hin). subst x.
      intro Hdiv.
      apply (proj2 (Z.mod_divide (DecimalValue (cons 2 tail)) 3 ltac:(lia))) in Hdiv.
      pose proof (decimal_value_digit_sum_mod_3__spec_results (cons 2 tail)) as Hmod.
      change (DecimalValue (cons 2 tail) mod 3 =
              (2 + fold_right Z.add 0 tail) mod 3) in Hmod.
      rewrite (fold_right_add_of_Forall_eq__spec_results tail 3 Htail_values) in Hmod.
      assert (Hrhs : (2 + 3 * Zlength tail) mod 3 = 2).
      { replace (2 + 3 * Zlength tail) with (2 + Zlength tail * 3) by ring.
        rewrite Z.mod_add by lia. reflexivity. }
      rewrite Hrhs in Hmod.
      lia. }
Qed.
Lemma no_bad_ugly_length_one__spec_results :
  forall digits, ~ BadUglyDigits 1 digits.
Proof.
  intros digits Hbad.
  unfold BadUglyDigits in Hbad.
  destruct Hbad as [Hlen [_ [_ Hnodiv]]].
  destruct digits as [|d tail].
  - rewrite Zlength_nil in Hlen. lia.
  - destruct tail as [|e tail].
    + inversion Hnodiv as [|? ? Hnotd ?]; subst.
      apply Hnotd.
      unfold DecimalValue. simpl.
      exists 1. ring.
    + rewrite Zlength_cons in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof (Zlength_nonneg tail).
      lia.
Qed.
Lemma Znth_map_inbounds_Z__spec_results :
  forall (f : Z -> Z) l i da db,
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros f l.
  induction l as [|x l IH]; intros i da db Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite !Znth0_cons. reflexivity.
    + change (Znth i (cons (f x) (map f l)) db = f (Znth i (cons x l) da)).
      rewrite !Znth_cons by lia.
      apply IH. lia.
Qed.
Lemma Zlength_map_Z__spec_results :
  forall (f : Z -> Z) l, Zlength (map f l) = Zlength l.
Proof.
  intros f l. induction l as [|x l IH].
  - rewrite !Zlength_nil. reflexivity.
  - change (Zlength (cons (f x) (map f l)) = Zlength (cons x l)).
    rewrite !Zlength_cons. lia.
Qed.
