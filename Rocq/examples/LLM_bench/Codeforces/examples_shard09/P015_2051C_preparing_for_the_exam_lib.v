Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Per-case signature: solve_case(n,missing,known)->list Z. Position i is 1
   exactly when every question except missing[i] belongs to known. *)
Definition Pre (n : Z) (missing : list Z) (known : Z -> Prop) : Prop :=
  (* Stated explicitly in the solver Require, so dropped here:
       2 <= n <= 300000 /\
       1 <= Zlength missing <= n /\
       Forall (fun x => 1 <= x <= n) missing /\
       (forall q, known q -> 1 <= q <= n) /\ *)
  NoDup missing /\
  mono_inc missing /\
  exists q, known q.

Definition CanPass (n missing_question : Z) (known : Z -> Prop) : Prop :=
  forall q, 1 <= q <= n -> q = missing_question \/ known q.

Definition QuestionResult
    (n : Z) (known : Z -> Prop) (missing_question result : Z) : Prop :=
  (result = 1 /\ CanPass n missing_question known) \/
  (result = 0 /\ ~ CanPass n missing_question known).

Definition Spec
    (n : Z) (missing : list Z) (known : Z -> Prop) (out : list Z) : Prop :=
  Forall2 (QuestionResult n known) missing out.

Definition KnownFlagsBridge
    (n : Z) (known : Z -> Prop) (flags : list Z) : Prop :=
  Zlength flags = n + 1 /\
  forall q, 1 <= q <= n ->
    ((known q /\ Znth q flags 0 <> 0) \/
     (~ known q /\ Znth q flags 0 = 0)).

Definition ResultDigitByte (result byte : Z) : Prop :=
  (result = 0 /\ byte = 48) \/ (result = 1 /\ byte = 49).

Definition ResultStringBridge (out bytes : list Z) : Prop :=
  Zlength bytes = Zlength out + 1 /\
  Forall2 ResultDigitByte out (sublist 0 (Zlength out) bytes) /\
  Znth (Zlength out) bytes 0 = 0.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* [next] is the first question not yet inspected.  The three cases record
   whether the inspected interval [1,next) has no unknown question, exactly
   one unknown question, or at least two. *)
Definition UnknownPrefixSummary
    (n : Z) (known : Z -> Prop)
    (next unknown only : Z) : Prop :=
  1 <= next <= n + 1 /\
  ((unknown = 0 /\
    forall q, 1 <= q < next -> known q) \/
   (unknown = 1 /\
    1 <= only < next /\
    ~ known only /\
    forall q, 1 <= q < next -> q = only \/ known q) \/
   (2 <= unknown /\
    exists q1 q2,
      1 <= q1 < next /\
      1 <= q2 < next /\
      q1 <> q2 /\
      ~ known q1 /\
      ~ known q2)).

(* The first [upto] answers and their bytes already agree with the problem
   specification; the terminating zero is deliberately outside this prefix. *)
Definition ResultPrefix
    (n : Z) (missing : list Z) (known : Z -> Prop) (upto : Z)
    (out bytes : list Z) : Prop :=
  Zlength out = upto /\
  Zlength bytes = upto /\
  Spec n (sublist 0 upto missing) known out /\
  Forall2 ResultDigitByte out bytes.

Require Import Coq.micromega.Lia.
Lemma unknown_prefix_summary_unknown_step__prefix_scan :
  forall (n : Z) (known : Z -> Prop) (q unknown only : Z),
    1 <= q <= n ->
    UnknownPrefixSummary n known q unknown only ->
    ~ known q ->
    UnknownPrefixSummary n known (q + 1) (unknown + 1) q.
Proof.
  intros n known q unknown only Hq Hsummary Hunknown.
  unfold UnknownPrefixSummary in *.
  destruct Hsummary as [Hnext Hcases].
  split; [lia |].
  destruct Hcases as [Hcase_zero | Hcases].
  - destruct Hcase_zero as [Hzero Hall].
    right; left.
    split; [lia |].
    split; [lia |].
    split; [exact Hunknown |].
    intros x Hx.
    destruct (Z.eq_dec x q) as [-> | Hxq]; [left; reflexivity |].
    right. apply Hall. lia.
  - destruct Hcases as [Hcase_one | Hcase_many].
    + destruct Hcase_one as [Hone [Honly [Honly_unknown Hall]]].
      right; right.
      split; [lia |].
      exists only, q.
      repeat split; try lia; assumption.
    + destruct Hcase_many as
          [Hmany [q1 [q2 [Hq1 [Hq2 [Hneq [Hq1_unknown Hq2_unknown]]]]]]].
      right; right.
      split; [lia |].
      exists q1, q2.
      repeat split; try lia; assumption.
Qed.
Lemma unknown_prefix_summary_known_step__prefix_scan :
  forall (n : Z) (known : Z -> Prop) (q unknown only : Z),
    1 <= q <= n ->
    UnknownPrefixSummary n known q unknown only ->
    known q ->
    UnknownPrefixSummary n known (q + 1) unknown only.
Proof.
  intros n known q unknown only Hq Hsummary Hknown.
  unfold UnknownPrefixSummary in *.
  destruct Hsummary as [Hnext Hcases].
  split; [lia |].
  destruct Hcases as [Hcase_zero | Hcases].
  - destruct Hcase_zero as [Hzero Hall].
    left.
    split; [exact Hzero |].
    intros x Hx.
    destruct (Z.eq_dec x q) as [-> | Hxq]; [exact Hknown |].
    apply Hall. lia.
  - destruct Hcases as [Hcase_one | Hcase_many].
    + destruct Hcase_one as [Hone [Honly [Honly_unknown Hall]]].
      right; left.
      split; [exact Hone |].
      split; [lia |].
      split; [exact Honly_unknown |].
      intros x Hx.
      destruct (Z.eq_dec x q) as [-> | Hxq]; [right; exact Hknown |].
      apply Hall. lia.
    + destruct Hcase_many as
          [Hmany [q1 [q2 [Hq1 [Hq2 [Hneq [Hq1_unknown Hq2_unknown]]]]]]].
      right; right.
      split; [exact Hmany |].
      exists q1, q2.
      repeat split; try lia; assumption.
Qed.
Lemma result_prefix_extend__result_steps :
  forall n missing known i out bytes result byte,
    0 <= i < Zlength missing ->
    ResultPrefix n missing known i out bytes ->
    QuestionResult n known (Znth i missing 0) result ->
    ResultDigitByte result byte ->
    ResultPrefix n missing known (i + 1)
      (app out (cons result nil)) (app bytes (cons byte nil)).
Proof.
  intros n missing known i out bytes result byte Hi Hprefix Hresult Hbyte.
  unfold ResultPrefix in *.
  destruct Hprefix as (Hout & Hbytes & Hspec & Hbridge).
  repeat split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - unfold Spec in *.
    rewrite (sublist_split 0 (i + 1) i missing) by lia.
    rewrite (sublist_single 0 i missing) by lia.
    apply Forall2_app.
    + exact Hspec.
    + constructor; auto.
  - apply Forall2_app.
    + exact Hbridge.
    + constructor; auto.
Qed.
Lemma result_prefix_accept_only__result_steps :
  forall n missing known i out bytes unknown only,
    0 <= i < Zlength missing ->
    unknown = 1 ->
    Znth i missing 0 = only ->
    UnknownPrefixSummary n known (n + 1) unknown only ->
    ResultPrefix n missing known i out bytes ->
    ResultPrefix n missing known (i + 1)
      (app out (cons 1 nil)) (app bytes (cons 49 nil)).
Proof.
  intros n missing known i out bytes unknown only Hi Hunknown Honly
    Hsummary Hprefix.
  eapply result_prefix_extend__result_steps; eauto.
  - unfold QuestionResult.
    left. split; [reflexivity|].
    unfold CanPass.
    subst unknown.
    destruct Hsummary as (_ & [Hzero | [Hone | Hmany]]).
    + lia.
    + destruct Hone as (_ & _ & _ & Hall).
      intros q Hq.
      specialize (Hall q ltac:(lia)).
      rewrite Honly.
      exact Hall.
    + lia.
  - unfold ResultDigitByte. auto.
Qed.
Lemma result_prefix_accept_all_known__result_steps :
  forall n missing known i out bytes unknown only,
    0 <= i < Zlength missing ->
    unknown = 0 ->
    UnknownPrefixSummary n known (n + 1) unknown only ->
    ResultPrefix n missing known i out bytes ->
    ResultPrefix n missing known (i + 1)
      (app out (cons 1 nil)) (app bytes (cons 49 nil)).
Proof.
  intros n missing known i out bytes unknown only Hi Hunknown Hsummary Hprefix.
  eapply result_prefix_extend__result_steps; eauto.
  - unfold QuestionResult.
    left. split; [reflexivity|].
    unfold CanPass.
    subst unknown.
    destruct Hsummary as (_ & [Hzero | [Hone | Hmany]]).
    + destruct Hzero as (_ & Hall).
      intros q Hq. right. apply Hall. lia.
    + lia.
    + lia.
  - unfold ResultDigitByte. auto.
Qed.
Lemma result_prefix_reject_many_unknown__result_steps :
  forall n missing known i out bytes unknown only,
    0 <= i < Zlength missing ->
    2 <= unknown ->
    UnknownPrefixSummary n known (n + 1) unknown only ->
    ResultPrefix n missing known i out bytes ->
    ResultPrefix n missing known (i + 1)
      (app out (cons 0 nil)) (app bytes (cons 48 nil)).
Proof.
  intros n missing known i out bytes unknown only Hi Hunknown Hsummary Hprefix.
  eapply result_prefix_extend__result_steps; eauto.
  - unfold QuestionResult.
    right. split; [reflexivity|].
    unfold CanPass.
    intros Hpass.
    destruct Hsummary as (_ & [Hzero | [Hone | Hmany]]).
    + lia.
    + lia.
    + destruct Hmany as (_ & q1 & q2 & Hq1 & Hq2 & Hneq & Hnq1 & Hnq2).
      pose proof (Hpass q1 ltac:(lia)) as Hpass1.
      pose proof (Hpass q2 ltac:(lia)) as Hpass2.
      destruct Hpass1 as [Heq1 | Hknown1]; [|contradiction].
      destruct Hpass2 as [Heq2 | Hknown2]; [|contradiction].
      congruence.
  - unfold ResultDigitByte. auto.
Qed.
Lemma result_prefix_reject_other__result_steps :
  forall n missing known i out bytes unknown only,
    0 <= i < Zlength missing ->
    unknown = 1 ->
    Znth i missing 0 <> only ->
    UnknownPrefixSummary n known (n + 1) unknown only ->
    ResultPrefix n missing known i out bytes ->
    ResultPrefix n missing known (i + 1)
      (app out (cons 0 nil)) (app bytes (cons 48 nil)).
Proof.
  intros n missing known i out bytes unknown only Hi Hunknown Hother
    Hsummary Hprefix.
  eapply result_prefix_extend__result_steps; eauto.
  - unfold QuestionResult.
    right. split; [reflexivity|].
    unfold CanPass.
    intros Hpass.
    subst unknown.
    destruct Hsummary as (_ & [Hzero | [Hone | Hmany]]).
    + lia.
    + destruct Hone as (_ & Honly_bounds & Hnot_known & _).
      specialize (Hpass only ltac:(lia)).
      destruct Hpass as [Heq | Hknown]; [|contradiction].
      apply Hother. symmetry. exact Heq.
    + lia.
  - unfold ResultDigitByte. auto.
Qed.
Lemma result_prefix_finish__final_result :
  forall n missing known upto out bytes,
    upto = Zlength missing ->
    ResultPrefix n missing known upto out bytes ->
    Spec n missing known out /\
    ResultStringBridge out (bytes ++ (0 :: nil)).
Proof.
  intros n missing known upto out bytes Hupto Hprefix.
  subst upto.
  unfold ResultPrefix in Hprefix.
  destruct Hprefix as [Hout [Hbytes [Hspec Hdigits]]].
  split.
  - rewrite sublist_self in Hspec by reflexivity.
    exact Hspec.
  - unfold ResultStringBridge.
    split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + split.
      * replace (sublist 0 (Zlength out) (bytes ++ 0 :: nil)) with bytes.
        -- exact Hdigits.
        -- rewrite Hout, <- Hbytes.
           symmetry.
           apply sublist_app_exact1.
      * rewrite Hout, <- Hbytes.
        rewrite app_Znth2 by lia.
        rewrite Z.sub_diag.
        reflexivity.
Qed.
