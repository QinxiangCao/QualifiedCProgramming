Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P047 solver Require, so dropped here:
       2 <= Zlength a <= 100000 /\
       Forall (fun x => - 10000 <= x <= 10000 /\ x <> 0) a  *)
  True.

Definition Spec (a out : list Z) : Prop :=
  Zlength out = Zlength a /\ Forall (fun x => x <> 0) out /\
  (fold_right Z.add 0) (map (fun q => fst q * snd q) (combine a out)) = 0 /\
  (fold_right Z.add 0) (map Z.abs out) <= 1000000000.

Definition GcdValue (a b : Z) : Z := Z.gcd a b.

Definition OutputPrefix (a out : list Z) (budget : Z) : Prop :=
  Zlength out = Zlength a /\
  Forall (fun x => x <> 0) out /\
  (fold_right Z.add 0)
    (map (fun q => fst q * snd q) (combine a out)) = 0 /\
  (fold_right Z.add 0) (map Z.abs out) <=
    10000 * Zlength out + budget.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Lemma gcd_abs_positive__pair_fill : forall a b : Z,
  a <> 0 -> b <> 0 -> 0 < Z.gcd (Z.abs a) (Z.abs b).
Proof.
  intros a b Ha Hb.
  pose proof (Z.gcd_nonneg (Z.abs a) (Z.abs b)) as Hnonneg.
  assert (Z.gcd (Z.abs a) (Z.abs b) <> 0) as Hneq.
  {
    intro Hg.
    apply Z.gcd_eq_0_l in Hg.
    apply (proj2 (Z.abs_pos a)) in Ha.
    lia.
  }
  lia.
Qed.
Lemma pair_output_prefix__pair_fill : forall a b : Z,
  -10000 <= a <= 10000 -> a <> 0 ->
  -10000 <= b <= 10000 -> b <> 0 ->
  OutputPrefix [a; b]
    [b ÷ Z.gcd (Z.abs a) (Z.abs b);
     (-a) ÷ Z.gcd (Z.abs a) (Z.abs b)] 0.
Proof.
  intros a b Ha_bounds Ha_nz Hb_bounds Hb_nz.
  set (g := Z.gcd (Z.abs a) (Z.abs b)).
  assert (Hgpos : 0 < g).
  { subst g. apply gcd_abs_positive__pair_fill; assumption. }
  assert (Hga : (g | a)).
  {
    subst g.
    rewrite <- Z.divide_abs_r.
    apply Z.gcd_divide_l.
  }
  assert (Hgb : (g | b)).
  {
    subst g.
    rewrite <- Z.divide_abs_r.
    apply Z.gcd_divide_r.
  }
  destruct Hga as [ka Hka].
  destruct Hgb as [kb Hkb].
  assert (Ha_div : a ÷ g = ka).
  { rewrite Hka, Z.quot_mul by lia. reflexivity. }
  assert (Hb_div : b ÷ g = kb).
  { rewrite Hkb, Z.quot_mul by lia. reflexivity. }
  assert (Hna_div : (-a) ÷ g = -ka).
  {
    rewrite Hka.
    replace (- (ka * g)) with ((-ka) * g) by ring.
    rewrite Z.quot_mul by lia.
    reflexivity.
  }
  assert (Hka_nz : ka <> 0) by (intro; subst ka; lia).
  assert (Hkb_nz : kb <> 0) by (intro; subst kb; lia).
  assert (Habs_a : Z.abs a = g * Z.abs ka).
  { rewrite Hka, Z.abs_mul, (Z.abs_eq g ltac:(lia)). ring. }
  assert (Habs_b : Z.abs b = g * Z.abs kb).
  { rewrite Hkb, Z.abs_mul, (Z.abs_eq g ltac:(lia)). ring. }
  assert (Habs_a_bound : Z.abs a <= 10000).
  { apply (proj2 (Z.abs_le a 10000)); lia. }
  assert (Habs_b_bound : Z.abs b <= 10000).
  { apply (proj2 (Z.abs_le b 10000)); lia. }
  assert (Hka_bound : Z.abs ka <= Z.abs a).
  { pose proof (Z.abs_nonneg ka). nia. }
  assert (Hkb_bound : Z.abs kb <= Z.abs b).
  { pose proof (Z.abs_nonneg kb). nia. }
  unfold OutputPrefix.
  rewrite Hb_div, Hna_div.
  simpl.
  repeat split.
  - repeat constructor; lia.
  - rewrite Hka, Hkb. ring.
  - lia.
Qed.
Lemma output_prefix_three_case1__solver_initialization :
  forall x y z,
    -10000 <= x <= 10000 -> x <> 0 ->
    -10000 <= y <= 10000 -> y <> 0 ->
    -10000 <= z <= 10000 -> z <> 0 ->
    x + y <> 0 ->
    OutputPrefix [x; y; z] [z; z; -(x + y)] 10000.
Proof.
  intros x y z Hxb Hxn Hyb Hyn Hzb Hzn Hxy.
  unfold OutputPrefix.
  cbn.
  repeat split; try lia; try ring.
  repeat constructor; lia.
Qed.
Lemma output_prefix_three_case2__solver_initialization :
  forall x y z,
    -10000 <= x <= 10000 -> x <> 0 ->
    -10000 <= y <= 10000 -> y <> 0 ->
    -10000 <= z <= 10000 -> z <> 0 ->
    x + y = 0 -> x + z <> 0 ->
    OutputPrefix [x; y; z] [y; -(x + z); y] 10000.
Proof.
  intros x y z Hxb Hxn Hyb Hyn Hzb Hzn Hxy Hxz.
  unfold OutputPrefix.
  cbn.
  repeat split; try lia; try ring.
  repeat constructor; lia.
Qed.
Lemma output_prefix_three_case3__solver_initialization :
  forall x y z,
    -10000 <= x <= 10000 -> x <> 0 ->
    -10000 <= y <= 10000 -> y <> 0 ->
    -10000 <= z <= 10000 -> z <> 0 ->
    x + y = 0 -> x + z = 0 ->
    OutputPrefix [x; y; z] [-(y + z); x; x] 10000.
Proof.
  intros x y z Hxb Hxn Hyb Hyn Hzb Hzn Hxy Hxz.
  unfold OutputPrefix.
  cbn.
  repeat split; try lia; try ring.
  repeat constructor; lia.
Qed.
Lemma combine_app__loop_extension :
  forall {A B : Type} (l1 l2 : list A) (r1 r2 : list B),
    length l1 = length r1 ->
    combine (l1 ++ l2) (r1 ++ r2) = combine l1 r1 ++ combine l2 r2.
Proof.
  intros A B l1. induction l1 as [| x xs IH]; intros l2 r1 r2 Hlen.
  - destruct r1; simpl in *; [reflexivity | discriminate].
  - destruct r1 as [| y ys]; simpl in Hlen; [discriminate |].
    simpl. f_equal. apply IH. lia.
Qed.
Lemma output_prefix_append_pair__loop_extension :
  forall values written pair_out budget i,
    0 <= i ->
    i + 1 < Zlength values ->
    OutputPrefix (sublist 0 i values) written budget ->
    OutputPrefix [Znth i values 0; Znth (i + 1) values 0] pair_out 0 ->
    OutputPrefix (sublist 0 (i + 2) values) (written ++ pair_out) budget.
Proof.
  intros values written pair_out budget i Hi Hbound Hprefix Hpair.
  assert (Hpiece :
    sublist 0 (i + 2) values =
      sublist 0 i values ++ [Znth i values 0; Znth (i + 1) values 0]).
  {
    rewrite (sublist_split 0 (i + 2) i values) by lia.
    rewrite (sublist_split i (i + 2) (i + 1) values) by lia.
    rewrite (sublist_single 0 i values) by lia.
    replace (i + 2) with ((i + 1) + 1) by lia.
    rewrite (sublist_single 0 (i + 1) values) by lia.
    reflexivity.
  }
  unfold OutputPrefix in *.
  destruct Hprefix as [Hlen_written [Hnonnull_written [Hdot_written Hbudget_written]]].
  destruct Hpair as [Hlen_pair [Hnonnull_pair [Hdot_pair Hbudget_pair]]].
  rewrite Hpiece.
  split.
  - rewrite !Zlength_app. lia.
  - split.
    + apply Forall_app. split; assumption.
    + split.
      * rewrite combine_app__loop_extension.
        -- rewrite map_app, fold_right_app, Hdot_pair, Hdot_written.
           reflexivity.
        -- rewrite !Zlength_correct in Hlen_written.
           apply Nat2Z.inj. symmetry. exact Hlen_written.
      * rewrite map_app, fold_right_app, Zlength_app.
        assert (Hfold : forall l z,
          fold_right Z.add z l = fold_right Z.add 0 l + z).
        {
          intros l. induction l as [| x xs IH]; intros z; simpl.
          - lia.
          - rewrite IH. lia.
        }
        rewrite Hfold.
        lia.
Qed.
Lemma output_prefix_to_spec_by_parity__final_result :
  forall n values written i start,
    i + 1 >= n ->
    2 <= n ->
    n <= 100000 ->
    n = Zlength values ->
    (start = 0 \/ start = 3) ->
    start <= i ->
    i <= n ->
    Z.rem n 2 = Z.rem start 2 ->
    Z.rem (i - start) 2 = 0 ->
    OutputPrefix (sublist 0 i values) written
      (Z.quot (10000 * start) 3) ->
    i = n /\ Spec values written.
Proof.
  intros n values written i start Hexit Hnlo Hnhi Hvalues Hstart
    Hstart_i Hi_n Hnmod Himod Hprefix.
  assert (Hi : i = n).
  {
    rewrite Z.rem_mod_nonneg in Himod by lia.
    rewrite !Z.rem_mod_nonneg in Hnmod by lia.
    apply (proj1 (Z.mod_divide (i - start) 2 ltac:(lia))) in Himod.
    destruct Himod as [k Hk].
    assert (Hnstartmod : (n - start) mod 2 = 0).
    {
      rewrite Zminus_mod by lia.
      rewrite Hnmod, Z.sub_diag.
      apply Z.mod_0_l; lia.
    }
    apply (proj1 (Z.mod_divide (n - start) 2 ltac:(lia))) in Hnstartmod.
    destruct Hnstartmod as [q Hq].
    nia.
  }
  subst i.
  rewrite (sublist_self values n) in Hprefix by lia.
  split; [reflexivity |].
  unfold OutputPrefix in Hprefix.
  unfold Spec.
  destruct Hprefix as [Hwritten [Hnonzero [Hdot Hbudget]]].
  split; [exact Hwritten |].
  split; [exact Hnonzero |].
  split; [exact Hdot |].
  destruct Hstart as [Hstart | Hstart]; subst start.
  - replace (Z.quot (10000 * 0) 3) with 0 in Hbudget by reflexivity.
    rewrite Hwritten in Hbudget.
    rewrite <- Hvalues in Hbudget.
    eapply Z.le_trans; [exact Hbudget |].
    nia.
  - replace (Z.quot (10000 * 3) 3) with 10000 in Hbudget by reflexivity.
    change (Z.rem n 2 = 1) in Hnmod.
    rewrite Hwritten in Hbudget.
    rewrite <- Hvalues in Hbudget.
    assert (Hneq : n <> 100000).
    {
      intro Heq.
      rewrite Heq in Hnmod.
      vm_compute in Hnmod.
      discriminate Hnmod.
    }
    eapply Z.le_trans; [exact Hbudget |].
    nia.
Qed.
