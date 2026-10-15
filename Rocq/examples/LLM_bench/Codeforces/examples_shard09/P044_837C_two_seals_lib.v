Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Oriented (s o:Z*Z) : Prop := o=s \/ o=(snd s,fst s).
Definition TwoFit (a b:Z) (x y:Z*Z) : Prop :=
  (fst x + fst y <= a /\ Z.max(snd x)(snd y) <= b) \/
  (Z.max(fst x)(fst y) <= a /\ snd x + snd y <= b).
Definition SealArea (paper:Z*Z) (seals:list(Z*Z)) (v:Z) : Prop :=
  (v = 0) \/ exists i j x y,0 <= i < j /\ j < Zlength seals /\
    Oriented(Znth i seals(0,0))x /\ Oriented(Znth j seals(0,0))y /\
    TwoFit(fst paper)(snd paper)x y /\ v = fst x * snd x + fst y * snd y.
Definition Pre (paper:Z*Z) (seals:list(Z*Z)) : Prop :=
  (* The solver Require states these constraints explicitly:
       1 <= fst paper <= 100 /\ 1 <= snd paper <= 100 /\
       1 <= Zlength seals <= 100 /\
       Forall (fun s =>
         1 <= fst s <= 100 /\ 1 <= snd s <= 100) seals. *)
  True.
Definition Spec (paper:Z*Z) (seals:list(Z*Z)) (out:Z) : Prop := max_value_of_subset Z.le (SealArea paper seals) (fun x => x) out.

(* Implementation-facing mathematical interfaces.  [rotate_seal] is the two
   possible orientations of one seal, and [BestBefore] is the optimum over the
   lexicographic prefix of pair/orientation choices preceding [i,j,ri,rj]. *)
Definition rotate_seal (s : Z * Z) (r : Z) : Z * Z :=
  if Z.eq_dec r 0 then s else (snd s, fst s).

Definition FitsDims
    (w1 h1 w2 h2 a b : Z) : Prop :=
  TwoFit a b (w1, h1) (w2, h2).

Definition SealChoice
    (paper : Z * Z) (seals : list (Z * Z))
    (i j ri rj area : Z) : Prop :=
  0 <= i < j /\ j < Zlength seals /\
  0 <= ri < 2 /\ 0 <= rj < 2 /\
  let s1 := rotate_seal (Znth i seals (0, 0)) ri in
  let s2 := rotate_seal (Znth j seals (0, 0)) rj in
  TwoFit (fst paper) (snd paper) s1 s2 /\
  area = fst s1 * snd s1 + fst s2 * snd s2.

Definition ChoiceBefore
    (i j ri rj pi pj pri prj : Z) : Prop :=
  pi < i \/
  (pi = i /\
   (pj < j \/
    (pj = j /\ (pri < ri \/ (pri = ri /\ prj < rj))))).

Definition SealAreaBefore
    (paper : Z * Z) (seals : list (Z * Z))
    (i j ri rj area : Z) : Prop :=
  area = 0 \/
  exists pi pj pri prj,
    ChoiceBefore i j ri rj pi pj pri prj /\
    SealChoice paper seals pi pj pri prj area.

Definition BestBefore
    (paper : Z * Z) (seals : list (Z * Z))
    (i j ri rj best : Z) : Prop :=
  max_value_of_subset Z.le
    (SealAreaBefore paper seals i j ri rj) (fun x => x) best.

Require Import Coq.micromega.Lia.
Lemma best_before_initial__invariant_init :
  forall paper seals, BestBefore paper seals 0 1 0 0 0.
Proof.
  intros paper seals.
  unfold BestBefore, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset.
  exists 0.
  split.
  - split.
    + unfold SealAreaBefore.
      left.
      reflexivity.
    + intros area Harea.
      unfold SealAreaBefore in Harea.
      destruct Harea as [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
      * lia.
      * unfold ChoiceBefore in Hbefore.
        unfold SealChoice in Hchoice.
        destruct Hchoice as [Hpi [_ [Hpri [Hrj _]]]].
        destruct Hbefore as
          [Hlt_i | [Heq_i [Hlt_j | [Heq_j [Hlt_ri | [Heq_ri Hlt_rj]]]]]];
          lia.
  - reflexivity.
Qed.
Lemma best_before_transport__loop_transitions :
  forall paper seals i1 j1 ri1 rj1 i2 j2 ri2 rj2 best,
    (forall area,
        SealAreaBefore paper seals i1 j1 ri1 rj1 area <->
        SealAreaBefore paper seals i2 j2 ri2 rj2 area) ->
    BestBefore paper seals i1 j1 ri1 rj1 best ->
    BestBefore paper seals i2 j2 ri2 rj2 best.
Proof.
  intros paper seals i1 j1 ri1 rj1 i2 j2 ri2 rj2 best Hequiv Hbest.
  unfold BestBefore, max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [area [[Hin Hmax] Heq]].
  exists area. split.
  - split.
    + apply (proj1 (Hequiv area)). exact Hin.
    + intros candidate Hcandidate.
      apply Hmax.
      apply (proj2 (Hequiv candidate)). exact Hcandidate.
  - exact Heq.
Qed.
Lemma best_before_finish_j__loop_transitions :
  forall paper seals i n best,
    n = Zlength seals ->
    BestBefore paper seals i n 0 0 best ->
    BestBefore paper seals (i + 1) ((i + 1) + 1) 0 0 best.
Proof.
  intros paper seals i n best Hlen Hbest.
  eapply best_before_transport__loop_transitions; [|exact Hbest].
  intro area. unfold SealAreaBefore. split.
  - intros [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
    + now left.
    + right. exists pi, pj, pri, prj. split; [|exact Hchoice].
      pose proof Hchoice as Hbounds.
      unfold SealChoice in Hbounds.
      unfold ChoiceBefore in *.
      intuition lia.
  - intros [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
    + now left.
    + right. exists pi, pj, pri, prj. split; [|exact Hchoice].
      pose proof Hchoice as Hbounds.
      unfold SealChoice in Hbounds.
      unfold ChoiceBefore in *.
      intuition lia.
Qed.
Lemma best_before_finish_ri__loop_transitions :
  forall paper seals i j best,
    BestBefore paper seals i j 2 0 best ->
    BestBefore paper seals i (j + 1) 0 0 best.
Proof.
  intros paper seals i j best Hbest.
  eapply best_before_transport__loop_transitions; [|exact Hbest].
  intro area. unfold SealAreaBefore. split.
  - intros [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
    + now left.
    + right. exists pi, pj, pri, prj. split; [|exact Hchoice].
      pose proof Hchoice as Hbounds.
      unfold SealChoice in Hbounds.
      unfold ChoiceBefore in *.
      intuition lia.
  - intros [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
    + now left.
    + right. exists pi, pj, pri, prj. split; [|exact Hchoice].
      pose proof Hchoice as Hbounds.
      unfold SealChoice in Hbounds.
      unfold ChoiceBefore in *.
      intuition lia.
Qed.
Lemma best_before_finish_rj__loop_transitions :
  forall paper seals i j ri best,
    BestBefore paper seals i j ri 2 best ->
    BestBefore paper seals i j (ri + 1) 0 best.
Proof.
  intros paper seals i j ri best Hbest.
  eapply best_before_transport__loop_transitions; [|exact Hbest].
  intro area. unfold SealAreaBefore. split.
  - intros [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
    + now left.
    + right. exists pi, pj, pri, prj. split; [|exact Hchoice].
      pose proof Hchoice as Hbounds.
      unfold SealChoice in Hbounds.
      unfold ChoiceBefore in *.
      intuition lia.
  - intros [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
    + now left.
    + right. exists pi, pj, pri, prj. split; [|exact Hchoice].
      pose proof Hchoice as Hbounds.
      unfold SealChoice in Hbounds.
      unfold ChoiceBefore in *.
      intuition lia.
Qed.
Lemma best_before_take_current__choice_improve :
  forall paper seals i j ri rj best area,
    BestBefore paper seals i j ri rj best ->
    SealChoice paper seals i j ri rj area ->
    best < area ->
    BestBefore paper seals i j ri (rj + 1) area.
Proof.
  intros paper seals i j ri rj best area Hbest Hcurrent Hlt.
  unfold BestBefore, max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [old [[Hold_in Hold_max] Hold_eq]].
  exists area.
  split.
  - split.
    + right.
      exists i, j, ri, rj.
      split; [unfold ChoiceBefore; lia | exact Hcurrent].
    + intros value Hvalue.
      unfold SealAreaBefore in Hvalue.
      destruct Hvalue as [Hzero | Hvalue].
      * subst value.
        assert (0 <= best).
        { rewrite <- Hold_eq.
          apply Hold_max.
          left; reflexivity. }
        lia.
      * destruct Hvalue as [pi [pj [pri [prj [Hbefore Hchoice]]]]].
        unfold ChoiceBefore in Hbefore.
        destruct Hbefore as
            [Hpi
            | [Hpi [Hpj
                    | [Hpj [Hpri
                            | [Hpri Hprj]]]]]].
        -- assert (SealAreaBefore paper seals i j ri rj value).
           { right; exists pi, pj, pri, prj; split.
             - unfold ChoiceBefore; left; exact Hpi.
             - exact Hchoice. }
           specialize (Hold_max value H).
           rewrite Hold_eq in Hold_max.
           lia.
        -- assert (SealAreaBefore paper seals i j ri rj value).
           { right; exists pi, pj, pri, prj; split.
             - unfold ChoiceBefore; right; split; [exact Hpi | left; exact Hpj].
             - exact Hchoice. }
           specialize (Hold_max value H).
           rewrite Hold_eq in Hold_max.
           lia.
        -- assert (SealAreaBefore paper seals i j ri rj value).
           { right; exists pi, pj, pri, prj; split.
             - unfold ChoiceBefore; right; split; [exact Hpi |].
               right; split; [exact Hpj | left; exact Hpri].
             - exact Hchoice. }
           specialize (Hold_max value H).
           rewrite Hold_eq in Hold_max.
           lia.
        -- destruct (Z.eq_dec prj rj) as [Hprj_eq | Hprj_neq].
           ++ subst pi pj pri prj.
              unfold SealChoice in Hcurrent, Hchoice.
              cbn in Hcurrent, Hchoice.
              destruct Hcurrent as [_ [_ [_ [_ [_ Harea_current]]]]].
              destruct Hchoice as [_ [_ [_ [_ [_ Harea_value]]]]].
              rewrite Harea_current, Harea_value.
              reflexivity.
           ++ assert (prj < rj) by lia.
              assert (SealAreaBefore paper seals i j ri rj value).
              { right; exists pi, pj, pri, prj; split.
                - unfold ChoiceBefore; right; split; [exact Hpi |].
                  right; split; [exact Hpj |].
                  right; split; [exact Hpri | exact H].
                - exact Hchoice. }
              specialize (Hold_max value H0).
              rewrite Hold_eq in Hold_max.
              lia.
  - reflexivity.
Qed.
Lemma best_before_skip_dominated__choice_retain_fit :
  forall paper seals i j ri rj best area,
    BestBefore paper seals i j ri rj best ->
    SealChoice paper seals i j ri rj area ->
    area <= best ->
    BestBefore paper seals i j ri (rj + 1) best.
Proof.
  intros paper seals i j ri rj best area Hbest Hcurrent Hdominated.
  unfold BestBefore, MaxMin.max_value_of_subset,
    MaxMin.max_object_of_subset in *.
  destruct Hbest as (old & (Hold_in & Hold_max) & Hold_eq).
  subst old.
  exists best.
  split; [split | reflexivity].
  - destruct Hold_in as [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
    + left. exact Hzero.
    + right. exists pi, pj, pri, prj. split; [| exact Hchoice].
      unfold ChoiceBefore in *.
      intuition lia.
  - intros value Hvalue.
    destruct Hvalue as [Hzero | (pi & pj & pri & prj & Hbefore & Hchoice)].
    + apply Hold_max. left. exact Hzero.
    + unfold ChoiceBefore in Hbefore.
      destruct Hbefore as
        [Hpi | [Hpi [Hpj | [Hpj [Hpri | [Hpri Hprj]]]]]].
      * apply Hold_max. right. exists pi, pj, pri, prj.
        split; [unfold ChoiceBefore; left; exact Hpi | exact Hchoice].
      * apply Hold_max. right. exists pi, pj, pri, prj.
        split; [unfold ChoiceBefore; right; split; [exact Hpi | left; exact Hpj] |
                exact Hchoice].
      * apply Hold_max. right. exists pi, pj, pri, prj.
        split; [unfold ChoiceBefore; right; split; [exact Hpi | right; split;
                  [exact Hpj | left; exact Hpri]] | exact Hchoice].
      * assert (prj < rj \/ prj = rj) as Hposition by lia.
        destruct Hposition as [Hprj_old | Hprj_current].
        -- apply Hold_max. right. exists pi, pj, pri, prj.
           split; [unfold ChoiceBefore; right; split; [exact Hpi | right; split;
                     [exact Hpj | right; split; [exact Hpri | exact Hprj_old]]] |
                   exact Hchoice].
        -- subst pi pj pri prj.
           unfold SealChoice in Hcurrent, Hchoice.
           destruct Hcurrent as (_ & _ & _ & _ & _ & Harea).
           destruct Hchoice as (_ & _ & _ & _ & _ & Hvalue_area).
           lia.
Qed.
Lemma best_before_skip_invalid__choice_retain_invalid :
  forall paper seals i j ri rj best,
    BestBefore paper seals i j ri rj best ->
    (forall area, ~ SealChoice paper seals i j ri rj area) ->
    BestBefore paper seals i j ri (rj + 1) best.
Proof.
  intros paper seals i j ri rj best Hbest Hinvalid.
  unfold BestBefore in *.
  eapply (max_eq_forward Z.le).
  - exact Hbest.
  - intros area Harea.
    exists area; split; [| lia].
    destruct Harea as [Hzero | [pi [pj [pri [prj [Hbefore Hchoice]]]]]].
    + left; exact Hzero.
    + right. exists pi, pj, pri, prj. split; [| exact Hchoice].
      unfold ChoiceBefore in *.
      destruct Hbefore as [Hpi | [Hpi [Hpj | [Hpj [Hpri | [Hpri Hprj]]]]]];
        subst; intuition lia.
  - intros area Harea.
    exists area; split; [| lia].
    destruct Harea as [Hzero | [pi [pj [pri [prj [Hbefore Hchoice]]]]]].
    + left; exact Hzero.
    + unfold ChoiceBefore in Hbefore.
      destruct Hbefore as [Hpi | [Hpi [Hpj | [Hpj [Hpri | [Hpri Hprj]]]]]].
      * right. exists pi, pj, pri, prj. split; [| exact Hchoice].
        unfold ChoiceBefore. left; exact Hpi.
      * right. exists pi, pj, pri, prj. split; [| exact Hchoice].
        unfold ChoiceBefore. right; split; [exact Hpi|]. left; exact Hpj.
      * right. exists pi, pj, pri, prj. split; [| exact Hchoice].
        unfold ChoiceBefore. right; split; [exact Hpi|].
        right; split; [exact Hpj|]. left; exact Hpri.
      * destruct (Z.eq_dec prj rj) as [Heq | Hneq].
        -- subst pi pj pri prj. exfalso. exact (Hinvalid area Hchoice).
        -- right. exists pi, pj, pri, prj. split; [| exact Hchoice].
           unfold ChoiceBefore. subst pi pj pri. right; split; [reflexivity|].
           right; split; [reflexivity|].
           right; split; [reflexivity|]. lia.
Qed.
Lemma best_before_complete__final_result :
  forall paper seals n best,
    n = Zlength seals ->
    BestBefore paper seals n (n + 1) 0 0 best ->
    Spec paper seals best.
Proof.
  intros paper seals n best Hn Hbest.
  unfold BestBefore in Hbest.
  unfold Spec.
  eapply (max_eq_forward Z.le) with
      (P1 := SealAreaBefore paper seals n (n + 1) 0 0)
      (f1 := fun x => x).
  - exact Hbest.
  - intros area Harea.
    exists area.
    split; [| lia].
    unfold SealAreaBefore in Harea.
    unfold SealArea.
    destruct Harea as
        [Hz | [pi [pj [pri [prj [Hbefore Hchoice]]]]]].
    + left; exact Hz.
    + right.
      exists pi, pj,
        (rotate_seal (Znth pi seals (0, 0)) pri),
        (rotate_seal (Znth pj seals (0, 0)) prj).
      unfold SealChoice in Hchoice.
      cbn in Hchoice.
      destruct Hchoice as
          [Hpi [Hpj [Hpri [Hprj [Hfit Harea]]]]].
      assert (Hori_i :
        Oriented (Znth pi seals (0, 0))
          (rotate_seal (Znth pi seals (0, 0)) pri)).
      { unfold Oriented, rotate_seal.
        destruct (Z.eq_dec pri 0); [left | right]; reflexivity. }
      assert (Hori_j :
        Oriented (Znth pj seals (0, 0))
          (rotate_seal (Znth pj seals (0, 0)) prj)).
      { unfold Oriented, rotate_seal.
        destruct (Z.eq_dec prj 0); [left | right]; reflexivity. }
      exact (conj Hpi
        (conj Hpj
          (conj Hori_i
            (conj Hori_j (conj Hfit Harea))))).
  - intros area Harea.
    exists area.
    split; [| lia].
    unfold SealArea in Harea.
    unfold SealAreaBefore.
    destruct Harea as
        [Hz | [pi [pj [x [y [Hpi [Hpj [Hori_i [Hori_j [Hfit Harea]]]]]]]]]].
    + left; exact Hz.
    + assert (Hrot_i : exists ri,
          0 <= ri < 2 /\
          rotate_seal (Znth pi seals (0, 0)) ri = x).
      { unfold Oriented in Hori_i.
        destruct Hori_i as [Hx | Hx].
        - exists 0; split; [lia |].
          subst x.
          unfold rotate_seal.
          destruct (Z.eq_dec 0 0); congruence.
        - exists 1; split; [lia |].
          subst x.
          unfold rotate_seal.
          destruct (Z.eq_dec 1 0); congruence. }
      assert (Hrot_j : exists rj,
          0 <= rj < 2 /\
          rotate_seal (Znth pj seals (0, 0)) rj = y).
      { unfold Oriented in Hori_j.
        destruct Hori_j as [Hy | Hy].
        - exists 0; split; [lia |].
          subst y.
          unfold rotate_seal.
          destruct (Z.eq_dec 0 0); congruence.
        - exists 1; split; [lia |].
          subst y.
          unfold rotate_seal.
          destruct (Z.eq_dec 1 0); congruence. }
      destruct Hrot_i as [ri [Hri Hrotate_i]].
      destruct Hrot_j as [rj [Hrj Hrotate_j]].
      right.
      exists pi, pj, ri, rj.
      split.
      * unfold ChoiceBefore.
        left.
        lia.
      * unfold SealChoice.
        cbn.
        rewrite Hrotate_i, Hrotate_j.
        exact (conj Hpi
          (conj Hpj
            (conj Hri (conj Hrj (conj Hfit Harea))))).
Qed.
