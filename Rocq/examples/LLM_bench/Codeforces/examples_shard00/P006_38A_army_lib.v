Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Pre (n : Z) (years : list Z) (a b : Z) : Prop :=
  2 <= n <= 100 /\
  Zlength years = n - 1 /\
  Forall (fun d => 1 <= d <= 100) years /\
  1 <= a < b /\ b <= n.

Definition Spec (n : Z) (years : list Z) (a b out : Z) : Prop :=
  out = fold_right Z.add 0 (sublist (a - 1) (b - 1) years).

Require Import Coq.micromega.Lia.
Lemma Spec_succ__loop_step :
  forall n years a i ans,
    1 <= a ->
    a <= i ->
    i <= Zlength years ->
    Spec n years a i ans ->
    Spec n years a (i + 1) (ans + Znth i (0 :: years) 0).
Proof.
  intros n years a i ans Ha Hai Hi HSpec.
  unfold Spec in *.
  change (ans = ListLib.sum (sublist (a - 1) (i - 1) years)) in HSpec.
  change (ans + Znth i (0 :: years) 0 =
    ListLib.sum (sublist (a - 1) (i + 1 - 1) years)).
  replace (i + 1 - 1) with i by lia.
  rewrite (sublist_split (a - 1) i (i - 1) years) by lia.
  rewrite ListLib.sum_app.
  pose proof (sublist_single 0 (i - 1) years ltac:(lia)) as Hsingle.
  replace (i - 1 + 1) with i in Hsingle by lia.
  rewrite Hsingle.
  simpl.
  rewrite Znth_cons by lia.
  lia.
Qed.
