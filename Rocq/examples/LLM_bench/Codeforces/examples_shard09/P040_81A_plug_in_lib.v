Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition DeletePair (a b:list Z) : Prop :=
  exists i,0 <= i < Zlength a - 1 /\ Znth i a 0 = Znth(i + 1) a 0 /\
    b = sublist 0 i a ++ sublist (i + 2) (Zlength a) a.
Definition ReducedFrom (a b:list Z) : Prop :=
  exists st:list(list Z),st <> [] /\ Znth 0 st[] = a /\ Znth(Zlength st - 1) st[] = b /\
    (forall i,0 <= i < Zlength st - 1 -> DeletePair(Znth i st[])(Znth(i + 1) st[])) /\
    ~exists q,DeletePair b q.
Definition Pre (s:list Z) : Prop :=
  (* Every clause below is stated explicitly in the P040 solver Require, which
     therefore omits the Pre(text) call:
       1 <= Zlength s <= 200000 /\ Forall(fun c => 97 <= c <= 122) s. *)
  True.
Definition Spec (s out:list Z) : Prop := ReducedFrom s out.

Require Import Coq.micromega.Lia.
Lemma DeletePair_snoc__stack_transitions : forall a b c,
  DeletePair a b -> DeletePair (a ++ [c]) (b ++ [c]).
Proof.
  intros a b c [k [Hk [Heq ->]]].
  exists k.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - split.
    + rewrite !app_Znth1 by lia. exact Heq.
    + rewrite (sublist_split (k + 2) (Zlength (a ++ [c])) (Zlength a))
        by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
      rewrite sublist_split_app_l by lia.
      rewrite sublist_split_app_l by lia.
      rewrite (sublist_split_app_r (Zlength a) (Zlength (a ++ [c]))
        (Zlength a) a [c]) by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
      replace (Zlength a - Zlength a) with 0 by lia.
      replace (Zlength (a ++ [c]) - Zlength a) with 1
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      change (sublist 0 1 [c]) with [c].
      rewrite app_assoc. reflexivity.
Qed.
Lemma no_DeletePair_snoc__stack_transitions : forall st c,
  (~ exists q, DeletePair st q) ->
  (st = [] \/ Znth (Zlength st - 1) st 0 <> c) ->
  ~ exists q, DeletePair (st ++ [c]) q.
Proof.
  intros st c Hnormal Hboundary [q [k [Hk [Heq Hq]]]].
  destruct (Z_lt_ge_dec k (Zlength st - 1)) as [Hin|Hlast].
  - apply Hnormal. exists (sublist 0 k st ++ sublist (k + 2) (Zlength st) st).
    exists k. split; [lia|]. split.
    + rewrite !app_Znth1 in Heq by lia. exact Heq.
    + reflexivity.
  - assert (k = Zlength st - 1).
    { rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk. lia. }
    subst k.
    destruct st as [|x st].
    + simpl in Hk. lia.
    + destruct Hboundary as [Hnil|Hneq]; [discriminate|].
      apply Hneq.
      rewrite app_Znth1 in Heq by (rewrite Zlength_cons; pose proof (Zlength_nonneg st); lia).
      rewrite app_Znth2 in Heq by lia.
      replace (Zlength (x :: st) - 1 + 1 - Zlength (x :: st)) with 0 in Heq by lia.
      exact Heq.
Qed.
Lemma no_DeletePair_prefix__stack_transitions : forall st,
  (~ exists q, DeletePair st q) ->
  ~ exists q, DeletePair (sublist 0 (Zlength st - 1) st) q.
Proof.
  intros st Hnormal [q [k [Hk [Heq Hq]]]].
  destruct st as [|x st].
  - simpl in Hk. lia.
  - apply Hnormal.
    exists (sublist 0 k (x :: st) ++ sublist (k + 2) (Zlength (x :: st)) (x :: st)).
    exists k.
    rewrite Zlength_sublist0 in Hk by (rewrite Zlength_cons; pose proof (Zlength_nonneg st); lia).
    split; [lia|]. split.
    + rewrite !Znth_sublist0 in Heq by lia. exact Heq.
    + reflexivity.
Qed.
Lemma DeletePair_last_equal__stack_transitions : forall st c,
  st <> [] -> Znth (Zlength st - 1) st 0 = c ->
  DeletePair (st ++ [c]) (sublist 0 (Zlength st - 1) st).
Proof.
  intros st c Hne Hlast.
  exists (Zlength st - 1).
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    destruct st; [contradiction|]. rewrite Zlength_cons. pose proof (Zlength_nonneg st). lia.
  - split.
    + rewrite app_Znth1.
      * rewrite app_Znth2 by lia.
        replace (Zlength st - 1 + 1 - Zlength st) with 0 by lia.
        simpl. exact Hlast.
      * destruct st; [contradiction|]. rewrite Zlength_cons. pose proof (Zlength_nonneg st). lia.
    + rewrite sublist_split_app_l by (destruct st; [contradiction|]; rewrite Zlength_cons; pose proof (Zlength_nonneg st); lia).
      rewrite (Zsublist_nil (st ++ [c]) (Zlength st - 1 + 2) (Zlength (st ++ [c])))
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      rewrite app_nil_r. reflexivity.
Qed.
Lemma Zlength_map__stack_transitions : forall {A B} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__stack_transitions : forall {A B} (f : A -> B) l d db i,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l d).
Proof.
  intros A B f l. induction l as [|x xs IH]; intros d db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [->|Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Spec_extend_keep_distinct__stack_transitions : forall xs st c,
  Spec xs st ->
  (st = [] \/ Znth (Zlength st - 1) st 0 <> c) ->
  Spec (xs ++ [c]) (st ++ [c]).
Proof.
  intros xs st c [states [Hstates [Hfirst [Hlast [Hsteps Hnormal]]]]] Hboundary.
  unfold Spec, ReducedFrom.
  exists (map (fun l => l ++ [c]) states).
  split.
  - intro Hnil. apply Hstates.
    destruct states; [reflexivity|discriminate].
  - assert (Hlen : 0 < Zlength states).
    { destruct states; [contradiction|]. rewrite Zlength_cons. pose proof (Zlength_nonneg states). lia. }
    split.
    + rewrite (@Znth_map__stack_transitions (list Z) (list Z)
        (fun l => l ++ [c]) states [] [] 0) by lia. now rewrite Hfirst.
    + split.
      * rewrite Zlength_map__stack_transitions.
        rewrite (@Znth_map__stack_transitions (list Z) (list Z)
          (fun l => l ++ [c]) states [] [] (Zlength states - 1)) by lia.
        now rewrite Hlast.
      * split.
        -- intros k Hk.
           rewrite Zlength_map__stack_transitions in Hk.
           rewrite (@Znth_map__stack_transitions (list Z) (list Z)
             (fun l => l ++ [c]) states [] [] k) by lia.
           rewrite (@Znth_map__stack_transitions (list Z) (list Z)
             (fun l => l ++ [c]) states [] [] (k + 1)) by lia.
           apply DeletePair_snoc__stack_transitions. apply Hsteps. lia.
        -- apply no_DeletePair_snoc__stack_transitions; assumption.
Qed.
Lemma Spec_extend_drop_equal__stack_transitions : forall xs st c,
  Spec xs st -> st <> [] -> Znth (Zlength st - 1) st 0 = c ->
  Spec (xs ++ [c]) (sublist 0 (Zlength st - 1) st).
Proof.
  intros xs st c [states [Hstates [Hfirst [Hlast [Hsteps Hnormal]]]]] Hst Hboundary.
  unfold Spec, ReducedFrom.
  set (lifted := map (fun l => l ++ [c]) states).
  set (out := sublist 0 (Zlength st - 1) st).
  exists (lifted ++ [out]).
  assert (Hlen : 0 < Zlength states).
  { destruct states; [contradiction|]. rewrite Zlength_cons. pose proof (Zlength_nonneg states). lia. }
  assert (Hliftlen : Zlength lifted = Zlength states).
  { unfold lifted. apply Zlength_map__stack_transitions. }
  split.
  - intro Hnil. destruct lifted; discriminate.
  - split.
    + rewrite app_Znth1 by (rewrite Hliftlen; lia).
      unfold lifted. rewrite (@Znth_map__stack_transitions (list Z) (list Z)
        (fun l => l ++ [c]) states [] [] 0) by lia. now rewrite Hfirst.
    + split.
      * rewrite Zlength_app.
        rewrite app_Znth2 by (rewrite Zlength_cons, Zlength_nil; lia).
        replace (Zlength lifted + Zlength [out] - 1 - Zlength lifted) with 0
          by (rewrite Zlength_cons, Zlength_nil; lia).
        reflexivity.
      * split.
        -- intros k Hk.
           rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
           destruct (Z_lt_ge_dec k (Zlength lifted - 1)) as [Hold|Hfinal].
           ++ rewrite !app_Znth1 by lia.
              unfold lifted.
              rewrite (@Znth_map__stack_transitions (list Z) (list Z)
                (fun l => l ++ [c]) states [] [] k) by (rewrite <- Hliftlen; lia).
              rewrite (@Znth_map__stack_transitions (list Z) (list Z)
                (fun l => l ++ [c]) states [] [] (k + 1)) by (rewrite <- Hliftlen; lia).
              apply DeletePair_snoc__stack_transitions. apply Hsteps.
              rewrite <- Hliftlen. lia.
           ++ assert (k = Zlength lifted - 1) by lia. subst k.
              rewrite app_Znth1 by lia.
              rewrite app_Znth2 by lia.
              replace (Zlength lifted - 1 + 1 - Zlength lifted) with 0 by lia.
              unfold lifted. rewrite Zlength_map__stack_transitions.
              rewrite (@Znth_map__stack_transitions (list Z) (list Z)
                (fun l => l ++ [c]) states [] [] (Zlength states - 1)) by lia.
              rewrite Hlast. unfold out.
              apply DeletePair_last_equal__stack_transitions; assumption.
        -- unfold out. apply no_DeletePair_prefix__stack_transitions. exact Hnormal.
Qed.
