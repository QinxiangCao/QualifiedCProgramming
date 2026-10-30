Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.
Require Import GraphLib.reachable.vpath.
Require Import GraphLib.reachable.reachable_basic.

Import ListNotations.
Local Open Scope Z_scope.

Definition VertexCover (n : Z) (e : list (Z * Z)%type) (sel : Z -> Prop) : Prop :=
  (forall x, sel x -> 1 <= x <= n) /\
  forall q, In q e -> sel (fst q) \/ sel (snd q).
Definition MinCoverSize (n : Z) (e : list (Z * Z)%type) (v : Z) : Prop :=
  min_value_of_subset Z.le
    (fun z => exists s, VertexCover n e s /\ z = #(fun x : Z => 1 <= x < n + 1 /\ s x))
    (fun x => x) v.
Definition RootParityCount (n : Z) (e : list (Z * Z)%type) (v : Z) : Prop :=
  exists d : Z -> Z, (forall x, 1 <= x <= n ->
  min_value_of_subset Z.le
    (fun q => exists path,
      (1 <= 1 <= n /\ 1 <= x <= n /\
  valid_vpath ({| zv := fun y => 1 <= y <= n ; ze := fun y z => In (y, z) e \/ In (z, y) e|} : ZGraph) 1 path x /\ NoDup path) /\ q = Zlength path - 1)
    (fun q => q) (d x)) /\
    v = Z.min (#(fun x : Z => 1 <= x < n + 1 /\ Z.even (d x) = true))
            (#(fun x : Z => 1 <= x < n + 1 /\ Z.even (d x) = false)).
Definition WrongTree (n : Z) (e : list (Z * Z)%type) : Prop :=
  (Zlength e = n - 1 /\ (Forall (fun p => 1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
  forall p q, In p e -> In q e ->
    (p = q \/ p = (snd q, fst q)) -> p = q) /\
  (connected ({| zv := fun x => 1 <= x <= n ; ze := fun x y => In (x, y) e \/ In (y, x) e|} : ZGraph))) /\ exists a b, RootParityCount n e a /\ MinCoverSize n e b /\ a <> b.
Definition CorrectTree (n : Z) (e : list (Z * Z)%type) : Prop :=
  (Zlength e = n - 1 /\ (Forall (fun p => 1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
  forall p q, In p e -> In q e ->
    (p = q \/ p = (snd q, fst q)) -> p = q) /\
  (connected ({| zv := fun x => 1 <= x <= n ; ze := fun x y => In (x, y) e \/ In (y, x) e|} : ZGraph))) /\ exists a, RootParityCount n e a /\ MinCoverSize n e a.
Definition Pre (n : Z) : Prop :=
  (* Every clause below is stated explicitly in the P045 solver Require, which
     therefore omits the Pre(...) call:
       2<=n<=100000. *)
  True.
Definition Spec (n : Z) (out : option (list (Z * Z)%type) * option (list (Z * Z)%type)) : Prop :=
  ((fst out = None /\ ~exists e, WrongTree n e) \/ exists e, fst out = Some e /\ WrongTree n e) /\
  ((snd out = None /\ ~exists e, CorrectTree n e) \/ exists e, snd out = Some e /\ CorrectTree n e).

Require Import Coq.micromega.Lia.

(** For the constructed double-star, the two root-distance parity classes
    have sizes [3] and [n - 3].  This arithmetic endpoint records the correct
    minimum; in particular it is not [1]. *)
Lemma min_three_n_minus_three__final_semantics :
  forall n, 6 <= n -> Z.min 3 (n - 3) = 3.
Proof.
  intros n Hn.
  rewrite Z.min_l; lia.
Qed.

(** Once the constructed edge family has been shown to be a tree, its
    corrected parity value [3] and minimum-cover value [2] are already
    sufficient for the final [WrongTree] conclusion. *)
Lemma parity_three_cover_two_implies_wrong_tree__final_semantics :
  forall n e,
    (Zlength e = n - 1 /\
     (Forall
        (fun p =>
           1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
      forall p q, In p e -> In q e ->
        (p = q \/ p = (snd q, fst q)) -> p = q) /\
     connected
       ({| zv := fun x => 1 <= x <= n;
           ze := fun x y => In (x, y) e \/ In (y, x) e |} : ZGraph)) ->
    RootParityCount n e 3 ->
    MinCoverSize n e 2 ->
    WrongTree n e.
Proof.
  intros n e Htree Hparity Hcover.
  unfold WrongTree.
  split.
  - exact Htree.
  - exists 3, 2.
    repeat split; try assumption; lia.
Qed.

Lemma seed_lists_properties__invariant_construction :
  Zlength [1; 1; 1; 2; 2] = 5 /\
  Zlength [2; 3; 4; 5; 6] = 5 /\
  forall i,
    0 <= i < 5 ->
    ((((i = 3 \/ i = 4) -> Znth i [1; 1; 1; 2; 2] 0 = 2) /\
      ((i <> 3 /\ i <> 4) -> Znth i [1; 1; 1; 2; 2] 0 = 1)) /\
     Znth i [2; 3; 4; 5; 6] 0 = i + 2).
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) as Hcases by lia.
      destruct Hcases as [-> | [-> | [-> | [-> | ->]]]];
        cbn [Znth]; intuition lia.
Qed.
Lemma valid_vpath_simple_le__final_semantics :
  forall (g : ZGraph) u p v,
    valid_vpath g u p v ->
    exists q, valid_vpath g u q v /\ NoDup q /\ (length q <= length p)%nat.
Proof.
  intros g u p v Hp.
  remember (length p) as k eqn:Hk.
  revert u p v Hp Hk.
  induction k using lt_wf_ind; intros u p v Hp Hk.
  destruct (classic (NoDup p)) as [Hnd | Hnd].
  - exists p. repeat split; try assumption. lia.
  - apply ListLib.General.NoDup.Nodup_exists_repetition in Hnd.
    destruct Hnd as [x [l1 [l2 [l3 ->]]]].
    set (p' := l1 ++ x :: l3).
    assert (Hp' : valid_vpath g u p' v).
    { unfold p'. eapply valid_vpath_remove_cycle. exact Hp. }
    assert (Hlt : (length p' < length (l1 ++ x :: l2 ++ x :: l3))%nat).
    { unfold p'. rewrite !length_app; simpl.
      rewrite !length_app; simpl. lia. }
    destruct (H (length p') ltac:(lia) u p' v Hp' eq_refl)
      as [q [Hq [Hndq Hle]]].
    exists q. repeat split; try assumption. lia.
Qed.
Lemma root_distance_data__final_semantics :
  forall n e d x,
    1 <= x <= n ->
    min_value_of_subset Z.le
      (fun q => exists path,
        (1 <= 1 <= n /\ 1 <= x <= n /\
         valid_vpath
           ({| zv := fun y => 1 <= y <= n;
               ze := fun y z => In (y,z) e \/ In (z,y) e |} : ZGraph)
           1 path x /\ NoDup path) /\ q = Zlength path - 1)
      (fun q => q) (d x) ->
    (exists path,
       valid_vpath
         ({| zv := fun y => 1 <= y <= n;
             ze := fun y z => In (y,z) e \/ In (z,y) e |} : ZGraph)
         1 path x /\ NoDup path /\ d x = Zlength path - 1) /\
    (forall path,
       valid_vpath
         ({| zv := fun y => 1 <= y <= n;
             ze := fun y z => In (y,z) e \/ In (z,y) e |} : ZGraph)
         1 path x -> NoDup path -> d x <= Zlength path - 1).
Proof.
  intros n e d x Hx Hd.
  unfold min_value_of_subset, min_object_of_subset in Hd.
  destruct Hd as [q [[[path [[_ [_ [Hp Hnd]]] Hqlen]] Hleast] Hqd]].
  subst q. simpl in Hqd.
  split.
  - exists path. repeat split; try assumption. lia.
  - intros path' Hp' Hnd'.
    rewrite <- Hqd. apply Hleast.
    exists path'. repeat split; try assumption; lia.
Qed.
Lemma root_distance_edge_lipschitz__final_semantics :
  forall n e d x y,
    1 <= x <= n -> 1 <= y <= n ->
    (In (x,y) e \/ In (y,x) e) ->
    (forall z, 1 <= z <= n ->
      min_value_of_subset Z.le
        (fun q => exists path,
          (1 <= 1 <= n /\ 1 <= z <= n /\
           valid_vpath
             ({| zv := fun a => 1 <= a <= n;
                 ze := fun a b => In (a,b) e \/ In (b,a) e |} : ZGraph)
             1 path z /\ NoDup path) /\ q = Zlength path - 1)
        (fun q => q) (d z)) ->
    d x <= d y + 1 /\ d y <= d x + 1.
Proof.
  intros n e d x y Hx Hy Hedge Hd.
  assert (Hedge' : In (y,x) e \/ In (x,y) e) by tauto.
  assert (Hxy : step
    ({| zv := fun a => 1 <= a <= n;
        ze := fun a b => In (a,b) e \/ In (b,a) e |} : ZGraph) x y).
  { exists (x,y). unfold zstep_aux. simpl.
    repeat split; try reflexivity; try exact Hedge; lia. }
  assert (Hyx : step
    ({| zv := fun a => 1 <= a <= n;
        ze := fun a b => In (a,b) e \/ In (b,a) e |} : ZGraph) y x).
  { exists (y,x). unfold zstep_aux. simpl.
    repeat split; try reflexivity; try exact Hedge'; lia. }
  split.
  - destruct (root_distance_data__final_semantics n e d y Hy (Hd y Hy))
      as [[py [Hpy [Hndy Hdy]]] HleX].
    pose proof (valid_vpath_snoc _ _ _ _ _ Hpy Hyx) as Hpys.
    destruct (valid_vpath_simple_le__final_semantics _ _ _ _ Hpys)
      as [q [Hq [Hndq Hlenq]]].
    specialize (root_distance_data__final_semantics n e d x Hx (Hd x Hx))
      as [_ Hleast].
    specialize (Hleast q Hq Hndq).
    rewrite Zlength_correct in Hdy, Hleast.
    rewrite length_app in Hlenq. simpl in Hlenq. lia.
  - destruct (root_distance_data__final_semantics n e d x Hx (Hd x Hx))
      as [[px [Hpx [Hndx Hdx]]] HleY].
    pose proof (valid_vpath_snoc _ _ _ _ _ Hpx Hxy) as Hpxs.
    destruct (valid_vpath_simple_le__final_semantics _ _ _ _ Hpxs)
      as [q [Hq [Hndq Hlenq]]].
    specialize (root_distance_data__final_semantics n e d y Hy (Hd y Hy))
      as [_ Hleast].
    specialize (Hleast q Hq Hndq).
    rewrite Zlength_correct in Hdx, Hleast.
    rewrite length_app in Hlenq. simpl in Hlenq. lia.
Qed.
Lemma root_distance_predecessor__final_semantics :
  forall n e d x,
    2 <= n -> 1 <= x <= n -> x <> 1 ->
    (forall z, 1 <= z <= n ->
      min_value_of_subset Z.le
        (fun q => exists path,
          (1 <= 1 <= n /\ 1 <= z <= n /\
           valid_vpath
             ({| zv := fun a => 1 <= a <= n;
                 ze := fun a b => In (a,b) e \/ In (b,a) e |} : ZGraph)
             1 path z /\ NoDup path) /\ q = Zlength path - 1)
        (fun q => q) (d z)) ->
    exists y edge,
      1 <= y <= n /\ In edge e /\
      (edge = (y,x) \/ edge = (x,y)) /\ d x = d y + 1.
Proof.
  intros n e d x Hn Hx Hx1 Hd.
  destruct (root_distance_data__final_semantics n e d x Hx (Hd x Hx))
    as [[p [Hp [Hnd Hdx]]] Hleastx].
  destruct (valid_vpath_inv_n1 _ _ _ _ Hp) as [[Heq _] | [p' [y [Heqp [Hp' Hstep]]]]].
  - congruence.
  - subst p. destruct Hstep as [[a b] Hstep]. unfold zstep_aux in Hstep.
    simpl in Hstep. destruct Hstep as [Hya [Hxb [Hedge [Hy Hx']]]].
    subst y x.
    cbn in Hx1, Hx, Hp, Hnd, Hdx, Hp', Hy, Hx', Hedge.
    assert (Hnd' : NoDup p').
    { eapply NoDup_app_remove_r. exact Hnd. }
    assert (Hdy_le : d a <= Zlength p' - 1).
    { specialize (root_distance_data__final_semantics n e d a Hy (Hd a Hy))
        as [_ Hle]. exact (Hle p' Hp' Hnd'). }
    assert (Hlip := root_distance_edge_lipschitz__final_semantics
      n e d b a Hx Hy ltac:(tauto) Hd).
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hdx.
    assert (Hdist : d b = d a + 1) by lia.
    destruct Hedge as [Hab | Hba].
    + exists a, (a,b). repeat split; try assumption; try tauto.
    + exists a, (b,a). repeat split; try assumption; try tauto.
Qed.
Lemma predecessor_child_unique__final_semantics :
  forall (d : Z -> Z) (x y z w : Z) (q : Z * Z),
    (q = (y,x) \/ q = (x,y)) -> d x = d y + 1 ->
    (q = (w,z) \/ q = (z,w)) -> d z = d w + 1 -> x = z.
Proof.
  intros d x y z w q Hxy Hdxy Hzw Hdzw.
  destruct Hxy as [-> | ->]; destruct Hzw as [He | He];
    inversion He; subst; lia.
Qed.
Lemma every_edge_layered_below_six__final_semantics :
  forall n e d,
    2 <= n < 6 -> Zlength e = n - 1 ->
    (forall z, 1 <= z <= n ->
      min_value_of_subset Z.le
        (fun q => exists path,
          (1 <= 1 <= n /\ 1 <= z <= n /\
           valid_vpath
             ({| zv := fun a => 1 <= a <= n;
                 ze := fun a b => In (a,b) e \/ In (b,a) e |} : ZGraph)
             1 path z /\ NoDup path) /\ q = Zlength path - 1)
        (fun q => q) (d z)) ->
    forall q, In q e ->
      exists y x, (q = (y,x) \/ q = (x,y)) /\ d x = d y + 1.
Proof.
  intros n e d Hn Hlen Hd q Hq.
  assert (Hcases : n = 2 \/ n = 3 \/ n = 4 \/ n = 5) by lia.
  destruct Hcases as [-> | [-> | [-> | ->]]].
  - destruct (root_distance_predecessor__final_semantics 2 e d 2 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y2 [q2 [_ [Hq2 [Ho2 Hd2]]]]].
    assert (Hin : incl e [q2]).
    { eapply NoDup_length_incl.
      - repeat constructor; simpl; tauto.
      - apply Nat2Z.inj_le. simpl. rewrite <- Zlength_correct. lia.
      - intros z [-> | []]. exact Hq2. }
    specialize (Hin q Hq). simpl in Hin. destruct Hin as [-> | []].
    exists y2, 2. auto.
  - destruct (root_distance_predecessor__final_semantics 3 e d 2 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y2 [q2 [_ [Hq2 [Ho2 Hd2]]]]].
    destruct (root_distance_predecessor__final_semantics 3 e d 3 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y3 [q3 [_ [Hq3 [Ho3 Hd3]]]]].
    assert (Hq23 : q2 <> q3).
    { intro Heq. subst q3.
      pose proof (predecessor_child_unique__final_semantics
        d 2 y2 3 y3 q2 Ho2 Hd2 Ho3 Hd3). lia. }
    assert (Hin : incl e [q2;q3]).
    { eapply NoDup_length_incl.
      - repeat constructor; simpl; intuition (auto with *).
      - apply Nat2Z.inj_le. simpl. rewrite <- Zlength_correct. lia.
      - intros z [-> | [-> | []]]; assumption. }
    specialize (Hin q Hq). simpl in Hin. destruct Hin as [-> | [-> | []]].
    + exists y2, 2. auto.
    + exists y3, 3. auto.
  - destruct (root_distance_predecessor__final_semantics 4 e d 2 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y2 [q2 [_ [Hq2 [Ho2 Hd2]]]]].
    destruct (root_distance_predecessor__final_semantics 4 e d 3 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y3 [q3 [_ [Hq3 [Ho3 Hd3]]]]].
    destruct (root_distance_predecessor__final_semantics 4 e d 4 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y4 [q4 [_ [Hq4 [Ho4 Hd4]]]]].
    assert (Hq23 : q2 <> q3) by
      (intro Heq; subst q3; pose proof (predecessor_child_unique__final_semantics
        d 2 y2 3 y3 q2 Ho2 Hd2 Ho3 Hd3); lia).
    assert (Hq24 : q2 <> q4) by
      (intro Heq; subst q4; pose proof (predecessor_child_unique__final_semantics
        d 2 y2 4 y4 q2 Ho2 Hd2 Ho4 Hd4); lia).
    assert (Hq34 : q3 <> q4) by
      (intro Heq; subst q4; pose proof (predecessor_child_unique__final_semantics
        d 3 y3 4 y4 q3 Ho3 Hd3 Ho4 Hd4); lia).
    assert (Hin : incl e [q2;q3;q4]).
    { eapply NoDup_length_incl.
      - repeat constructor; simpl; intuition (auto with *).
      - apply Nat2Z.inj_le. simpl. rewrite <- Zlength_correct. lia.
      - intros z [-> | [-> | [-> | []]]]; assumption. }
    specialize (Hin q Hq). simpl in Hin.
    destruct Hin as [-> | [-> | [-> | []]]].
    + exists y2, 2. auto.
    + exists y3, 3. auto.
    + exists y4, 4. auto.
  - destruct (root_distance_predecessor__final_semantics 5 e d 2 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y2 [q2 [_ [Hq2 [Ho2 Hd2]]]]].
    destruct (root_distance_predecessor__final_semantics 5 e d 3 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y3 [q3 [_ [Hq3 [Ho3 Hd3]]]]].
    destruct (root_distance_predecessor__final_semantics 5 e d 4 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y4 [q4 [_ [Hq4 [Ho4 Hd4]]]]].
    destruct (root_distance_predecessor__final_semantics 5 e d 5 ltac:(lia)
      ltac:(lia) ltac:(lia) Hd) as [y5 [q5 [_ [Hq5 [Ho5 Hd5]]]]].
    assert (Hq23 : q2 <> q3) by
      (intro Heq; subst q3; pose proof (predecessor_child_unique__final_semantics
        d 2 y2 3 y3 q2 Ho2 Hd2 Ho3 Hd3); lia).
    assert (Hq24 : q2 <> q4) by
      (intro Heq; subst q4; pose proof (predecessor_child_unique__final_semantics
        d 2 y2 4 y4 q2 Ho2 Hd2 Ho4 Hd4); lia).
    assert (Hq25 : q2 <> q5) by
      (intro Heq; subst q5; pose proof (predecessor_child_unique__final_semantics
        d 2 y2 5 y5 q2 Ho2 Hd2 Ho5 Hd5); lia).
    assert (Hq34 : q3 <> q4) by
      (intro Heq; subst q4; pose proof (predecessor_child_unique__final_semantics
        d 3 y3 4 y4 q3 Ho3 Hd3 Ho4 Hd4); lia).
    assert (Hq35 : q3 <> q5) by
      (intro Heq; subst q5; pose proof (predecessor_child_unique__final_semantics
        d 3 y3 5 y5 q3 Ho3 Hd3 Ho5 Hd5); lia).
    assert (Hq45 : q4 <> q5) by
      (intro Heq; subst q5; pose proof (predecessor_child_unique__final_semantics
        d 4 y4 5 y5 q4 Ho4 Hd4 Ho5 Hd5); lia).
    assert (Hin : incl e [q2;q3;q4;q5]).
    { eapply NoDup_length_incl.
      - repeat constructor; simpl; intuition (auto with *).
      - apply Nat2Z.inj_le. simpl. rewrite <- Zlength_correct. lia.
      - intros z [-> | [-> | [-> | [-> | []]]]]; assumption. }
    specialize (Hin q Hq). simpl in Hin.
    destruct Hin as [-> | [-> | [-> | [-> | []]]]].
    + exists y2, 2. auto.
    + exists y3, 3. auto.
    + exists y4, 4. auto.
    + exists y5, 5. auto.
Qed.
Lemma combine_Znth_pair__final_semantics :
  forall {A B : Type} (xs : list A) (ys : list B) i dx dy,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    Znth i (combine xs ys) (dx, dy) = (Znth i xs dx, Znth i ys dy).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys i dx dy Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
      * rewrite !Znth0_cons. reflexivity.
      * rewrite !Znth_cons by lia. apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_combine_eq__final_semantics :
  forall {A B : Type} (xs : list A) (ys : list B),
    Zlength xs = Zlength ys ->
    Zlength (combine xs ys) = Zlength xs.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys Hlen.
  - reflexivity.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. rewrite !Zlength_cons. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma set_card_ext__final_semantics :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Heq.
  unfold set_card, SumLib.Sum.sum.
  assert (Permutation (@enum A P FP) (@enum A Q FQ)) as Hperm.
  { apply NoDup_Permutation.
    - apply enum_nodup.
    - apply enum_nodup.
    - intro x. rewrite <- !enum_ok. apply Heq. }
  assert (Hfold : forall l : list A,
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  { intro l. induction l as [|a l IH]; [reflexivity |].
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            Z.of_nat (S (length l))).
    rewrite IH, Nat2Z.inj_succ. lia. }
  rewrite !Hfold.
  apply Permutation_length in Hperm. simpl in Hperm. rewrite Hperm. reflexivity.
Qed.
Lemma set_card_Z_as_sum__final_semantics :
  forall (low high : Z) (P : Z -> Prop),
    #(fun x : Z => low <= x < high /\ P x) =
    SumLib.Sum.sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (P x) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun x => if prop_dec (P x) then true else false) xs) =
    fold_right (fun x acc : Z =>
      (if prop_dec (P x) then 1 else 0) + acc) 0 xs).
  { induction xs as [|x xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P x)); simpl.
    - exact (f_equal (fun z : Z => 1 + z) IH).
    - exact IH. }
  apply Hfilter.
Qed.
Lemma set_card_Z_range__final_semantics :
  forall low high, low <= high ->
    #(fun x : Z => low <= x < high) = high - low.
Proof.
  intros low high Hrange.
  transitivity (#(fun x : Z => low <= x < high /\ True)).
  - apply set_card_ext__final_semantics. intuition (auto with *).
  - rewrite set_card_Z_as_sum__final_semantics.
    destruct (prop_dec True) as [_ | Hfalse]; [|contradiction].
    rewrite SumLib.ZRange.sum_Z_range_const by lia. lia.
Qed.
Lemma set_card_member_positive__final_semantics :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x,
    P x -> 1 <= @set_card A P FP.
Proof.
  intros A P FP x Hx.
  unfold set_card, SumLib.Sum.sum.
  assert (In x (@enum A P FP)) as Hin by
    (apply (proj1 (@enum_ok A P FP x)); exact Hx).
  assert (Hfold : forall l : list A,
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  { intro l. induction l as [|y ys IH]; [reflexivity |].
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 ys =
            Z.of_nat (S (length ys))).
    rewrite IH, Nat2Z.inj_succ. lia. }
  rewrite Hfold.
  replace 1 with (Z.of_nat 1) by reflexivity.
  apply Nat2Z.inj_le. simpl.
  apply in_split in Hin as [l1 [l2 Heq]].
  rewrite Heq, length_app. simpl. lia.
Qed.
Lemma Zlength_Zrange__final_semantics :
  forall low high, low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hrange. unfold Zrange.
  rewrite Zlength_correct.
  assert (Hlen : forall k start, length (Zrange_aux start k) = k).
  { induction k as [|k IH]; intros start; simpl; [reflexivity |].
    rewrite IH. reflexivity. }
  rewrite Hlen. lia.
Qed.
Lemma valid_vpath_length_nonneg__final_semantics :
  forall g u p v, valid_vpath g u p v -> 0 <= Zlength p - 1.
Proof.
  intros g u p v Hp.
  apply valid_vpath_not_nil in Hp.
  destruct p as [|x xs]; [contradiction |].
  rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
Qed.
Lemma valid_vpath_length_pos__final_semantics :
  forall g u p v,
    u <> v -> valid_vpath g u p v -> 1 <= Zlength p - 1.
Proof.
  intros g u p v Hne Hp.
  destruct p as [|x [|y ys]].
  - exfalso. apply valid_vpath_not_nil in Hp. contradiction.
  - apply valid_vpath_empty_inv in Hp. destruct Hp. congruence.
  - rewrite !Zlength_cons. pose proof (Zlength_nonneg ys). lia.
Qed.
Lemma canonical_star_correct__final_semantics :
  forall n, 2 <= n ->
    CorrectTree n (map (fun x => (1, x)) (Zrange 2 (n + 1))).
Proof.
  intros n Hn.
  set (e := map (fun x => (1, x)) (Zrange 2 (n + 1))).
  assert (Hedge : forall x, 2 <= x <= n -> In (1, x) e).
  { intros x Hx. unfold e. apply in_map. apply In_Zrange. lia. }
  assert (Htree :
    Zlength e = n - 1 /\
    (Forall (fun p => 1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
     forall p q, In p e -> In q e ->
       (p = q \/ p = (snd q, fst q)) -> p = q) /\
    connected
      ({| zv := fun x => 1 <= x <= n;
          ze := fun x y => In (x, y) e \/ In (y, x) e |} : ZGraph)).
  { split.
    - unfold e. rewrite Zlength_correct, length_map, <- Zlength_correct.
      rewrite Zlength_Zrange__final_semantics by lia. lia.
    - split.
      + split.
        * apply Forall_forall. intros [a b] Hin. unfold e in Hin.
          apply in_map_iff in Hin as [x [Heq Hx]].
          inversion Heq; subst a b.
          apply In_Zrange in Hx. cbn.
          split.
          -- split; lia.
          -- split; [split; lia | lia].
        * intros [a b] [c d] Hp Hq Hor. unfold e in Hp, Hq.
          apply in_map_iff in Hp as [x [Hpx Hx]].
          apply in_map_iff in Hq as [y [Hqy Hy]].
          inversion Hpx; inversion Hqy; subst a b c d.
          destruct Hor as [Heq | Hrev]; [exact Heq |].
          inversion Hrev. apply In_Zrange in Hx, Hy. lia.
      + unfold connected. intros x y Hx Hy. simpl in Hx, Hy.
        eapply reachable_trans with (y := 1).
        * destruct (Z.eq_dec x 1) as [-> | Hx1]; [reflexivity |].
          apply step_rt. exists (x, 1). unfold zstep_aux. simpl.
          repeat split; try lia. right. apply Hedge. lia.
        * destruct (Z.eq_dec y 1) as [-> | Hy1]; [reflexivity |].
          apply step_rt. exists (1, y). unfold zstep_aux. simpl.
          repeat split; try lia. left. apply Hedge. lia. }
  unfold CorrectTree. split; [exact Htree |].
  exists 1. split.
  - unfold RootParityCount.
    exists (fun x => if Z.eq_dec x 1 then 0 else 1).
    split.
    + intros x Hx.
      unfold min_value_of_subset, min_object_of_subset.
      destruct (Z.eq_dec x 1) as [-> | Hx1].
      * exists 0. split.
        -- split.
           ++ exists [1]. repeat split; try lia.
              ** apply valid_vpath_empty.
              ** constructor; [intro Hin; inversion Hin | constructor].
           ++ intros q [path [[_ [_ [Hp _]]] ->]].
              apply valid_vpath_length_nonneg__final_semantics in Hp. lia.
        -- reflexivity.
      * exists 1. split.
        -- split.
           ++ exists [1; x]. repeat split; try lia.
              ** apply single_vpath_valid. exists (1, x).
                 unfold zstep_aux. simpl. repeat split; try lia.
                 left. apply Hedge. lia.
              ** repeat constructor; simpl; intuition (auto with *).
           ++ intros q [path [[_ [_ [Hp _]]] ->]].
              apply valid_vpath_length_pos__final_semantics with (u := 1) (v := x) in Hp;
                [lia | congruence].
        -- reflexivity.
    + assert (Heven :
        #(fun x : Z => 1 <= x < n + 1 /\
             Z.even (if Z.eq_dec x 1 then 0 else 1) = true) = 1).
      { transitivity (#(fun x : Z => 1 <= x < 2)).
        - apply set_card_ext__final_semantics. intro x.
          destruct (Z.eq_dec x 1); subst; simpl; intuition lia.
        - apply set_card_Z_range__final_semantics; lia. }
      assert (Hodd :
        #(fun x : Z => 1 <= x < n + 1 /\
             Z.even (if Z.eq_dec x 1 then 0 else 1) = false) = n - 1).
      { transitivity (#(fun x : Z => 2 <= x < n + 1)).
        - apply set_card_ext__final_semantics. intro x.
          destruct (Z.eq_dec x 1); subst; simpl; intuition lia.
        - rewrite set_card_Z_range__final_semantics by lia. lia. }
      rewrite Heven, Hodd, Z.min_l; lia.
  - unfold MinCoverSize, min_value_of_subset, min_object_of_subset.
    exists 1. split.
    + split.
      * exists (fun x => x = 1). split.
        -- unfold VertexCover. split.
           ++ intros x ->. lia.
           ++ intros [a b] Hin. unfold e in Hin.
              apply in_map_iff in Hin as [x [Heq Hx]].
              inversion Heq; subst a b. simpl. auto.
        -- transitivity (#(fun x : Z => 1 <= x < 2)).
           ++ symmetry. apply set_card_Z_range__final_semantics; lia.
           ++ apply set_card_ext__final_semantics. intro x. intuition lia.
      * intros z [s [[Hsrange Hscover] Hz]]. subst z.
        specialize (Hscover (1, 2) (Hedge 2 ltac:(lia))). simpl in Hscover.
        destruct Hscover as [Hs1 | Hs2].
        -- apply set_card_member_positive__final_semantics with (x := 1).
           split; [lia | exact Hs1].
        -- apply set_card_member_positive__final_semantics with (x := 2).
           split; [lia | exact Hs2].
    + reflexivity.
Qed.
Lemma In_exists_Znth__final_semantics :
  forall {A : Type} (l : list A) x d,
    In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l. induction l as [|y ys IH]; intros x d Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + exists 0. split.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg ys). lia.
      * rewrite Znth0_cons. reflexivity.
    + destruct (IH x d Hin) as [i [Hi Hz]].
      exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia. exact Hz.
Qed.
Lemma set_card_two_members__final_semantics :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x y,
    x <> y -> P x -> P y -> 2 <= @set_card A P FP.
Proof.
  intros A P FP x y Hxy Hx Hy.
  unfold set_card, SumLib.Sum.sum.
  assert (HinX : In x (@enum A P FP)) by
    (apply (proj1 (@enum_ok A P FP x)); exact Hx).
  assert (HinY : In y (@enum A P FP)) by
    (apply (proj1 (@enum_ok A P FP y)); exact Hy).
  assert (Hlen : (2 <= length (@enum A P FP))%nat).
  { pose proof (NoDup_incl_length (l := [x;y]) (l' := @enum A P FP)) as Hle.
    apply Hle.
    - repeat constructor; simpl; intuition (auto with *).
    - intros z [-> | [-> | []]]; assumption. }
  assert (Hfold : forall l : list A,
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  { intro l. induction l as [|z zs IH]; [reflexivity |].
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 zs =
            Z.of_nat (S (length zs))).
    rewrite IH, Nat2Z.inj_succ. lia. }
  rewrite Hfold. replace 2 with (Z.of_nat 2) by reflexivity.
  apply Nat2Z.inj_le. exact Hlen.
Qed.
Lemma set_card_three_exact__final_semantics :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x y z,
    x <> y -> x <> z -> y <> z ->
    P x -> P y -> P z ->
    (forall a, P a -> a = x \/ a = y \/ a = z) ->
    @set_card A P FP = 3.
Proof.
  intros A P FP x y z Hxy Hxz Hyz Hx Hy Hz Honly.
  unfold set_card, SumLib.Sum.sum.
  assert (Hlen : length (@enum A P FP) = 3%nat).
  { apply Nat.le_antisymm.
    - change (length (@enum A P FP) <= length [x;y;z])%nat.
      eapply NoDup_incl_length.
      + exact (@enum_nodup A P FP).
      + intros a Hin. apply (proj2 (@enum_ok A P FP a)) in Hin.
        specialize (Honly a Hin). destruct Honly as [-> | [-> | ->]]; simpl; auto.
    - change (length [x;y;z] <= length (@enum A P FP))%nat.
      eapply NoDup_incl_length.
      + repeat constructor; simpl; intuition (auto with *).
      + intros a [Ha | [Ha | [Ha | []]]].
        * subst a. apply (proj1 (@enum_ok A P FP x)). exact Hx.
        * subst a. apply (proj1 (@enum_ok A P FP y)). exact Hy.
        * subst a. apply (proj1 (@enum_ok A P FP z)). exact Hz. }
  assert (Hfold : forall l : list A,
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  { intro l. induction l as [|a l IH]; [reflexivity |].
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            Z.of_nat (S (length l))).
    rewrite IH, Nat2Z.inj_succ. lia. }
  rewrite Hfold, Hlen. reflexivity.
Qed.
Lemma valid_vpath_length_two_if_no_step__final_semantics :
  forall g u p v,
    u <> v -> ~ step g u v -> valid_vpath g u p v -> 2 <= Zlength p - 1.
Proof.
  intros g u p v Hne Hnostep Hp.
  destruct p as [|x [|y [|z zs]]].
  - apply valid_vpath_not_nil in Hp. contradiction.
  - apply valid_vpath_empty_inv in Hp as [Hu Hv]. congruence.
  - apply valid_vpath_single_inv in Hp as [Hux [Hvy Hstep]].
    subst x y.
    exfalso. exact (Hnostep Hstep).
  - rewrite !Zlength_cons. pose proof (Zlength_nonneg zs). lia.
Qed.
Lemma indexed_double_star_wrong__final_semantics :
  forall n us vs,
    6 <= n ->
    Zlength us = n - 1 ->
    Zlength vs = n - 1 ->
    (forall i, 0 <= i < n - 1 ->
      ((((i = 3 \/ i = 4) -> Znth i us 0 = 2) /\
        ((i <> 3 /\ i <> 4) -> Znth i us 0 = 1)) /\
       Znth i vs 0 = i + 2)) ->
    WrongTree n (combine us vs).
Proof.
  intros n us vs Hn Hus Hvs Hidx.
  set (e := combine us vs).
  assert (Hlene : Zlength e = n - 1).
  { unfold e. rewrite Zlength_combine_eq__final_semantics; lia. }
  assert (Hedge_at : forall i, 0 <= i < n - 1 ->
    In (Znth i us 0, i + 2) e).
  { intros i Hi. unfold e.
    destruct (Hidx i Hi) as [_ Hvi]. rewrite <- Hvi.
    rewrite <- (combine_Znth_pair__final_semantics us vs i 0 0) by lia.
    apply Znth_In_Zlength. rewrite Zlength_combine_eq__final_semantics; lia. }
  assert (Hedge_shape : forall p, In p e -> exists i,
    0 <= i < n - 1 /\
    p = (Znth i us 0, i + 2) /\
    (((i = 3 \/ i = 4) -> Znth i us 0 = 2) /\
     ((i <> 3 /\ i <> 4) -> Znth i us 0 = 1))).
  { intros p Hp.
    destruct (In_exists_Znth__final_semantics e p (0, 0) Hp) as [i [Hi Hpi]].
    rewrite Hlene in Hi.
    unfold e in Hpi.
    rewrite combine_Znth_pair__final_semantics in Hpi by lia.
    destruct (Hidx i Hi) as [Hui Hvi].
    exists i. split; [exact Hi |]. split.
    - rewrite <- Hpi, Hvi. reflexivity.
    - exact Hui. }
  assert (Hedge_12 : In (1, 2) e).
  { specialize (Hidx 0 ltac:(lia)) as [[_ Hu] _].
    replace (1,2) with (Znth 0 us 0, 0+2) by (rewrite (Hu ltac:(lia)); reflexivity).
    apply Hedge_at. lia. }
  assert (Hedge_13 : In (1, 3) e).
  { specialize (Hidx 1 ltac:(lia)) as [[_ Hu] _].
    replace (1,3) with (Znth 1 us 0, 1+2) by (rewrite (Hu ltac:(lia)); reflexivity).
    apply Hedge_at. lia. }
  assert (Hedge_25 : In (2, 5) e).
  { specialize (Hidx 3 ltac:(lia)) as [[Hu _] _].
    replace (2,5) with (Znth 3 us 0, 3+2) by (rewrite (Hu ltac:(auto)); reflexivity).
    apply Hedge_at. lia. }
  assert (Htree :
    Zlength e = n - 1 /\
    (Forall (fun p => 1 <= fst p <= n /\ 1 <= snd p <= n /\ fst p <> snd p) e /\
     forall p q, In p e -> In q e ->
       (p = q \/ p = (snd q, fst q)) -> p = q) /\
    connected
      ({| zv := fun x => 1 <= x <= n;
          ze := fun x y => In (x, y) e \/ In (y, x) e |} : ZGraph)).
  { split; [exact Hlene |]. split.
    - split.
      + apply Forall_forall. intros [a b] Hp.
        destruct (Hedge_shape (a,b) Hp) as [i [Hi [Heq [Hu3 Hu1]]]].
        inversion Heq; subst a b. simpl.
        destruct (Z.eq_dec i 3) as [-> | Hi3].
        * rewrite (Hu3 ltac:(auto)). repeat split; lia.
        * destruct (Z.eq_dec i 4) as [-> | Hi4].
          -- rewrite (Hu3 ltac:(auto)). repeat split; lia.
          -- rewrite (Hu1 ltac:(auto)). repeat split; lia.
      + intros p q Hp Hq Hor.
        destruct (Hedge_shape p Hp) as [i [Hi [Hpe [HiS HiN]]]].
        destruct (Hedge_shape q Hq) as [j [Hj [Hqe [HjS HjN]]]].
        destruct Hor as [-> | Hrev]; [reflexivity |].
        rewrite Hpe, Hqe in Hrev. inversion Hrev as [[Ha Hb]]. exfalso.
        destruct (Z.eq_dec i 3), (Z.eq_dec i 4),
                 (Z.eq_dec j 3), (Z.eq_dec j 4);
          try rewrite (HiS ltac:(auto)) in *;
          try rewrite (HiN ltac:(auto)) in *;
          try rewrite (HjS ltac:(auto)) in *;
          try rewrite (HjN ltac:(auto)) in *; lia.
    - unfold connected. intros x y Hx Hy. simpl in Hx, Hy.
      assert (Hreach1 : forall z, 1 <= z <= n -> reachable
        ({| zv := fun t => 1 <= t <= n;
            ze := fun a b => In (a,b) e \/ In (b,a) e |} : ZGraph) z 1).
      { intros z Hz. destruct (Z.eq_dec z 1) as [-> | Hz1]; [reflexivity |].
        destruct (Z.eq_dec z 5) as [-> | Hz5].
        - eapply reachable_trans with (y := 2).
          + apply step_rt. exists (5,2). unfold zstep_aux. simpl.
            repeat split; try lia. right. exact Hedge_25.
          + apply step_rt. exists (2,1). unfold zstep_aux. simpl.
            repeat split; try lia. right. exact Hedge_12.
        - destruct (Z.eq_dec z 6) as [-> | Hz6].
          + assert (Hedge_26 : In (2,6) e).
            { specialize (Hidx 4 ltac:(lia)) as [[Hu _] _].
              replace (2,6) with (Znth 4 us 0, 4+2) by
                (rewrite (Hu ltac:(auto)); reflexivity).
              apply Hedge_at. lia. }
            eapply reachable_trans with (y := 2).
            * apply step_rt. exists (6,2). unfold zstep_aux. simpl.
              repeat split; try lia. right. exact Hedge_26.
            * apply step_rt. exists (2,1). unfold zstep_aux. simpl.
              repeat split; try lia. right. exact Hedge_12.
          + assert (Hedge_1z : In (1,z) e).
            { set (i := z - 2). assert (Hi : 0 <= i < n - 1) by (unfold i; lia).
              specialize (Hidx i Hi) as [[_ Hu] Hv].
              assert (i <> 3 /\ i <> 4) by (unfold i; lia).
              specialize (Hu H).
              replace (1,z) with (Znth i us 0, i+2) by
                (rewrite Hu; f_equal; unfold i; lia).
              apply Hedge_at. exact Hi. }
            apply step_rt. exists (z,1). unfold zstep_aux. simpl.
            repeat split; try lia. right. exact Hedge_1z. }
      eapply reachable_trans with (y := 1); [apply Hreach1; exact Hx |].
      destruct (Z.eq_dec y 1) as [-> | Hy1]; [reflexivity |].
      (* Reverse the explicit root path, using symmetry of the edge predicate. *)
      destruct (Z.eq_dec y 5) as [-> | Hy5].
      + eapply reachable_trans with (y := 2).
        * apply step_rt. exists (1,2). unfold zstep_aux. simpl.
          repeat split; try lia. left. exact Hedge_12.
        * apply step_rt. exists (2,5). unfold zstep_aux. simpl.
          repeat split; try lia. left. exact Hedge_25.
      + destruct (Z.eq_dec y 6) as [-> | Hy6].
        * assert (Hedge_26 : In (2,6) e).
          { specialize (Hidx 4 ltac:(lia)) as [[Hu _] _].
            replace (2,6) with (Znth 4 us 0, 4+2) by
              (rewrite (Hu ltac:(auto)); reflexivity).
            apply Hedge_at. lia. }
          eapply reachable_trans with (y := 2).
          -- apply step_rt. exists (1,2). unfold zstep_aux. simpl.
             repeat split; try lia. left. exact Hedge_12.
          -- apply step_rt. exists (2,6). unfold zstep_aux. simpl.
             repeat split; try lia. left. exact Hedge_26.
        * assert (Hedge_1y : In (1,y) e).
          { set (i := y - 2). assert (Hi : 0 <= i < n - 1) by (unfold i; lia).
            specialize (Hidx i Hi) as [[_ Hu] Hv].
            assert (i <> 3 /\ i <> 4) by (unfold i; lia).
            specialize (Hu H).
            replace (1,y) with (Znth i us 0, i+2) by
              (rewrite Hu; f_equal; unfold i; lia).
            apply Hedge_at. exact Hi. }
          apply step_rt. exists (1,y). unfold zstep_aux. simpl.
          repeat split; try lia. left. exact Hedge_1y. }
  assert (Hparity : RootParityCount n e 3).
  { unfold RootParityCount.
    exists (fun x => if Z.eq_dec x 1 then 0
                     else if (Z.eq_dec x 5) then 2
                     else if (Z.eq_dec x 6) then 2 else 1).
    split.
    - intros x Hx. unfold min_value_of_subset, min_object_of_subset.
      destruct (Z.eq_dec x 1) as [-> | Hx1].
      + exists 0. split; [|reflexivity]. split.
        * exists [1]. repeat split; try lia.
          -- apply valid_vpath_empty.
          -- repeat constructor; simpl; intuition (auto with *).
        * intros q [path [[_ [_ [Hp _]]] ->]].
          apply valid_vpath_length_nonneg__final_semantics in Hp. lia.
      + destruct (Z.eq_dec x 5) as [-> | Hx5].
        * exists 2. split; [|reflexivity]. split.
          -- exists [1;2;5]. repeat split; try lia.
             ++ eapply valid_vpath_cons.
                ** exists (1,2). unfold zstep_aux. simpl. repeat split; try lia.
                   all: cbn; try lia; try tauto.
                ** apply single_vpath_valid. exists (2,5). unfold zstep_aux. simpl.
                   repeat split; try lia. all: cbn; try lia; try tauto.
             ++ repeat constructor; simpl; intuition (auto with *).
          -- intros q [path [[_ [_ [Hp _]]] ->]].
             apply valid_vpath_length_two_if_no_step__final_semantics with (u:=1) (v:=5) in Hp;
               try lia.
             intro Hstep. destruct Hstep as [[a b] Hs]. unfold zstep_aux in Hs.
             destruct Hs as [Ha [Hb [Hadj _]]]. simpl in Ha, Hb. subst a b.
             simpl in Hadj. destruct Hadj as [He | He].
             ++ destruct (Hedge_shape _ He) as [i [Hi [Heq [HiS HiN]]]].
                inversion Heq as [[Ha Hb]].
                assert (i = 3) by lia. specialize (HiS ltac:(auto)). lia.
             ++ destruct (Hedge_shape _ He) as [i [Hi [Heq _]]].
                inversion Heq. lia.
        * destruct (Z.eq_dec x 6) as [-> | Hx6].
        { assert (Hedge_26 : In (2,6) e).
          { specialize (Hidx 4 ltac:(lia)) as [[Hu _] _].
            replace (2,6) with (Znth 4 us 0, 4+2) by
              (rewrite (Hu ltac:(auto)); reflexivity).
            apply Hedge_at. lia. }
          exists 2. split; [|reflexivity]. split.
          -- exists [1;2;6]. repeat split; try lia.
             ++ eapply valid_vpath_cons.
                ** exists (1,2). unfold zstep_aux. simpl. repeat split; try lia.
                   all: cbn; try lia; try tauto.
                ** apply single_vpath_valid. exists (2,6). unfold zstep_aux. simpl.
                   repeat split; try lia. all: cbn; try lia; try tauto.
             ++ repeat constructor; simpl; intuition (auto with *).
          -- intros q [path [[_ [_ [Hp _]]] ->]].
             apply valid_vpath_length_two_if_no_step__final_semantics with (u:=1) (v:=6) in Hp;
               try lia.
             intro Hstep. destruct Hstep as [[a b] Hs]. unfold zstep_aux in Hs.
             destruct Hs as [Ha [Hb [Hadj _]]]. simpl in Ha, Hb. subst a b.
             simpl in Hadj. destruct Hadj as [He | He].
             ++ destruct (Hedge_shape _ He) as [i [Hi [Heq [HiS HiN]]]].
                inversion Heq as [[Ha Hb]].
                assert (i = 4) by lia. specialize (HiS ltac:(auto)). lia.
             ++ destruct (Hedge_shape _ He) as [i [Hi [Heq _]]].
                inversion Heq. lia. }
        { assert (Hedge_1x : In (1,x) e).
          { set (i := x-2). assert (Hi : 0 <= i < n-1) by (unfold i; lia).
            specialize (Hidx i Hi) as [[_ Hu] Hv].
            specialize (Hu ltac:(unfold i; lia)). unfold i in Hu, Hv.
            replace (1,x) with (Znth (x-2) us 0, (x-2)+2) by
              (rewrite Hu; f_equal; lia).
            apply Hedge_at. exact Hi. }
          exists 1. split; [|reflexivity]. split.
          -- exists [1;x]. repeat split; try lia.
             ++ apply single_vpath_valid. exists (1,x). unfold zstep_aux. simpl.
                repeat split; try lia. all: cbn; try lia; try tauto.
             ++ repeat constructor; simpl; intuition (auto with *).
          -- intros q [path [[_ [_ [Hp _]]] ->]].
             apply valid_vpath_length_pos__final_semantics with (u:=1) (v:=x) in Hp;
               [lia | congruence]. }
    - assert (Heven :
        #(fun x : Z => 1 <= x < n+1 /\
          Z.even (if Z.eq_dec x 1 then 0 else if Z.eq_dec x 5 then 2
                  else if Z.eq_dec x 6 then 2 else 1) = true) = 3).
      { transitivity (#(fun x : Z => 1 <= x < n+1 /\ (x=1 \/ x=5 \/ x=6))).
        - apply set_card_ext__final_semantics. intro x.
          repeat destruct (Z.eq_dec x _); subst; simpl; intuition congruence.
        - transitivity (#(fun x : Z => 1 <= x < 7 /\ (x=1 \/ x=5 \/ x=6))).
          + apply set_card_ext__final_semantics. intro x. intuition lia.
          + eapply set_card_three_exact__final_semantics
              with (x := 1) (y := 5) (z := 6);
              simpl; try lia; intuition (auto with *). }
      assert (Hodd :
        #(fun x : Z => 1 <= x < n+1 /\
          Z.even (if Z.eq_dec x 1 then 0 else if Z.eq_dec x 5 then 2
                  else if Z.eq_dec x 6 then 2 else 1) = false) = n-3).
      { transitivity (#(fun x : Z => 1 <= x < n+1 /\ x<>1 /\ x<>5 /\ x<>6)).
        - apply set_card_ext__final_semantics. intro x.
          repeat destruct (Z.eq_dec x _); subst; simpl; intuition congruence.
        - rewrite set_card_Z_as_sum__final_semantics.
          rewrite (SumLib.ZRange.sum_Z_range_split 1 7 (n+1)) by lia.
          assert (Hfirst : SumLib.Sum.sum (fun x : Z => 1 <= x < 7)
            (fun x => if prop_dec (x<>1 /\ x<>5 /\ x<>6) then 1 else 0) = 3).
          { rewrite <- set_card_Z_as_sum__final_semantics.
            eapply set_card_three_exact__final_semantics
              with (x := 2) (y := 3) (z := 4);
              simpl; try lia; intuition lia. }
          rewrite Hfirst.
          assert (Htail : SumLib.Sum.sum (fun x : Z => 7 <= x < n+1)
              (fun x => if prop_dec (x<>1 /\ x<>5 /\ x<>6) then 1 else 0) =
              SumLib.Sum.sum (fun x : Z => 7 <= x < n+1) (fun _ => 1)).
          { apply SumLib.Sum.sum_ext. intros x Hx.
            destruct (prop_dec (x<>1 /\ x<>5 /\ x<>6)); [reflexivity |].
            exfalso. apply n0. lia. }
          rewrite Htail, SumLib.ZRange.sum_Z_range_const by lia. lia. }
      rewrite Heven, Hodd. symmetry.
      apply min_three_n_minus_three__final_semantics. exact Hn. }
  assert (Hcover : MinCoverSize n e 2).
  { unfold MinCoverSize, min_value_of_subset, min_object_of_subset.
    exists 2. split; [|reflexivity]. split.
    - exists (fun x => x=1 \/ x=2). split.
      + unfold VertexCover. split.
        * intros x [-> | ->]; lia.
        * intros p Hp. destruct (Hedge_shape p Hp) as [i [Hi [-> [HiS HiN]]]].
          simpl. destruct (Z.eq_dec i 3), (Z.eq_dec i 4); subst;
            try rewrite (HiS ltac:(auto)); try rewrite (HiN ltac:(auto)); auto.
      + transitivity (#(fun x : Z => 1 <= x < 3)).
        * symmetry. apply set_card_Z_range__final_semantics; lia.
        * apply set_card_ext__final_semantics. intro x. intuition lia.
    - intros z [s [[Hsrange Hscover] ->]].
      pose proof (Hscover (1,3) Hedge_13) as Hcover13. simpl in Hcover13.
      pose proof (Hscover (2,5) Hedge_25) as Hcover25. simpl in Hcover25.
      destruct Hcover13 as [Hs1 | Hs3]; destruct Hcover25 as [Hs2 | Hs5].
      + eapply set_card_two_members__final_semantics with (x := 1) (y := 2);
          [lia | split; [lia | exact Hs1] | split; [lia | exact Hs2]].
      + eapply set_card_two_members__final_semantics with (x := 1) (y := 5);
          [lia | split; [lia | exact Hs1] | split; [lia | exact Hs5]].
      + eapply set_card_two_members__final_semantics with (x := 3) (y := 2);
          [lia | split; [lia | exact Hs3] | split; [lia | exact Hs2]].
      + eapply set_card_two_members__final_semantics with (x := 3) (y := 5);
          [lia | split; [lia | exact Hs3] | split; [lia | exact Hs5]].
  }
  apply parity_three_cover_two_implies_wrong_tree__final_semantics;
    assumption.
Qed.
Lemma parity_card_sum__final_semantics :
  forall n (d : Z -> Z), 1 <= n ->
    #(fun x : Z => 1 <= x < n+1 /\ Z.even (d x) = true) +
    #(fun x : Z => 1 <= x < n+1 /\ Z.even (d x) = false) = n.
Proof.
  intros n d Hn.
  rewrite !set_card_Z_as_sum__final_semantics.
  rewrite <- SumLib.Sum.sum_add.
  transitivity (SumLib.Sum.sum (fun x : Z => 1 <= x < n+1) (fun _ => 1)).
  - apply SumLib.Sum.sum_ext. intros x Hx.
    destruct (Z.even (d x)) eqn:Hev;
      repeat destruct prop_dec; simpl in *; try contradiction;
      try discriminate; try congruence; reflexivity.
  - rewrite SumLib.ZRange.sum_Z_range_const by lia. lia.
Qed.
Lemma set_card_one_unique__final_semantics :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x y,
    @set_card A P FP = 1 -> P x -> P y -> x = y.
Proof.
  intros A P FP x y Hcard Hx Hy.
  destruct (classic (x = y)); auto.
  pose proof (set_card_two_members__final_semantics P FP x y H Hx Hy).
  lia.
Qed.
Lemma set_card_singleton_exact__final_semantics :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x,
    P x -> (forall y, P y -> y = x) -> @set_card A P FP = 1.
Proof.
  intros A P FP x Hx Honly.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) [x]).
  { apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - repeat constructor; simpl; auto.
    - intro y. rewrite <- (@enum_ok A P FP y). simpl.
      split.
      + intro Hy. left. symmetry. apply Honly. exact Hy.
      + intros [-> | []]. exact Hx. }
  assert (Hfold : forall l : list A,
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  { intro l. induction l as [|a l IH]; [reflexivity |].
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            Z.of_nat (S (length l))).
    rewrite IH, Nat2Z.inj_succ. lia. }
  rewrite Hfold.
  pose proof (Permutation_length Hperm) as Hlen.
  simpl in Hlen. rewrite Hlen. reflexivity.
Qed.
Lemma root_distance_one_zero__final_semantics :
  forall n e d,
    2 <= n ->
    (forall z, 1 <= z <= n ->
      min_value_of_subset Z.le
        (fun q => exists path,
          (1 <= 1 <= n /\ 1 <= z <= n /\
           valid_vpath
             ({| zv := fun a => 1 <= a <= n;
                 ze := fun a b => In (a,b) e \/ In (b,a) e |} : ZGraph)
             1 path z /\ NoDup path) /\ q = Zlength path - 1)
        (fun q => q) (d z)) -> d 1 = 0.
Proof.
  intros n e d Hn Hd.
  destruct (root_distance_data__final_semantics n e d 1 ltac:(lia) (Hd 1 ltac:(lia)))
    as [[p [Hp [Hnd Hdp]]] Hleast].
  assert (Hupper : d 1 <= 0).
  { specialize (Hleast [1] ltac:(apply valid_vpath_empty)
      ltac:(constructor; [simpl; tauto | constructor])).
    simpl in Hleast. exact Hleast. }
  apply valid_vpath_length_nonneg__final_semantics in Hp. lia.
Qed.
Lemma no_wrong_tree_below_six__final_semantics :
  forall n, 2 <= n < 6 -> ~ exists e, WrongTree n e.
Proof.
  intros n Hn Hex.
  destruct Hex as [e Hwrong]. unfold WrongTree in Hwrong.
  destruct Hwrong as [Htree Habex].
  destruct Htree as [Hlen [Hrest Hconn]].
  destruct Hrest as [Hfor Huniq].
  destruct Habex as [a [b [Hpar [Hcover Hneq]]]].
  unfold RootParityCount in Hpar.
  destruct Hpar as [d [Hd Ha]].
  unfold MinCoverSize, min_value_of_subset, min_object_of_subset in Hcover.
  destruct Hcover as [z [[[s [Hvc Hzcard]] Hmincover] Hzb]].
  subst z. simpl in Hzb.
  destruct Hvc as [Hsrange Hscovers].
  assert (Hlayer : forall q, In q e ->
      exists y x, (q = (y,x) \/ q = (x,y)) /\ d x = d y + 1).
  { eapply every_edge_layered_below_six__final_semantics; eauto. }
  set (E := #(fun x : Z => 1 <= x < n+1 /\ Z.even (d x) = true)).
  set (O := #(fun x : Z => 1 <= x < n+1 /\ Z.even (d x) = false)).
  assert (Hnonempty : exists q, In q e).
  { destruct e as [|q es].
    - rewrite Zlength_nil in Hlen. lia.
    - exists q. simpl. auto. }
  destruct Hnonempty as [q0 Hq0].
  destruct q0 as [u0 v0].
  rewrite Forall_forall in Hfor.
  pose proof (Hfor (u0,v0) Hq0) as Hbounds0.
  simpl in Hbounds0.
  destruct (Hlayer (u0,v0) Hq0) as [y0 [x0 [Hor0 Hdist0]]].
  assert (HEpos : 1 <= E).
  { unfold E. destruct Hor0 as [Heq | Heq]; inversion Heq; subst.
    all: destruct (Z.even (d y0)) eqn:Hev.
    - eapply set_card_member_positive__final_semantics with (x := y0).
      split; [lia | exact Hev].
    - eapply set_card_member_positive__final_semantics with (x := x0).
      split; [lia |]. replace (d x0) with (Z.succ (d y0)) by lia.
      rewrite Z.even_succ, <- Z.negb_even, Hev; reflexivity.
    - eapply set_card_member_positive__final_semantics with (x := y0).
      split; [lia | exact Hev].
    - eapply set_card_member_positive__final_semantics with (x := x0).
      split; [lia |]. replace (d x0) with (Z.succ (d y0)) by lia.
      rewrite Z.even_succ, <- Z.negb_even, Hev; reflexivity. }
  assert (HOpos : 1 <= O).
  { unfold O. destruct Hor0 as [Heq | Heq]; inversion Heq; subst.
    all: destruct (Z.even (d y0)) eqn:Hev.
    - eapply set_card_member_positive__final_semantics with (x := x0).
      split; [lia |]. replace (d x0) with (Z.succ (d y0)) by lia.
      rewrite Z.even_succ, <- Z.negb_even, Hev; reflexivity.
    - eapply set_card_member_positive__final_semantics with (x := y0).
      split; [lia | exact Hev].
    - eapply set_card_member_positive__final_semantics with (x := x0).
      split; [lia |]. replace (d x0) with (Z.succ (d y0)) by lia.
      rewrite Z.even_succ, <- Z.negb_even, Hev; reflexivity.
    - eapply set_card_member_positive__final_semantics with (x := y0).
      split; [lia | exact Hev]. }
  assert (HVCE : VertexCover n e
      (fun x => 1 <= x <= n /\ Z.even (d x) = true)).
  { split; [intros x Hx; tauto |].
    intros [u v] Huv. simpl.
    pose proof (Hfor (u,v) Huv) as Hbnd. simpl in Hbnd.
    destruct (Hlayer (u,v) Huv) as [y [x [Hor Hdist]]].
    destruct Hor as [Heq | Heq]; inversion Heq; subst;
      destruct (Z.even (d y)) eqn:Hev.
    - left. split; [lia | reflexivity].
    - right. split; [lia |]. replace (d x) with (Z.succ (d y)) by lia.
      rewrite Z.even_succ, <- Z.negb_even, Hev. reflexivity.
    - right. split; [lia | reflexivity].
    - left. split; [lia |]. replace (d x) with (Z.succ (d y)) by lia.
      rewrite Z.even_succ, <- Z.negb_even, Hev. reflexivity. }
  assert (HVCO : VertexCover n e
      (fun x => 1 <= x <= n /\ Z.even (d x) = false)).
  { split; [intros x Hx; tauto |].
    intros [u v] Huv. simpl.
    pose proof (Hfor (u,v) Huv) as Hbnd. simpl in Hbnd.
    destruct (Hlayer (u,v) Huv) as [y [x [Hor Hdist]]].
    destruct Hor as [Heq | Heq]; inversion Heq; subst;
      destruct (Z.even (d y)) eqn:Hev.
    - right. split; [lia |]. replace (d x) with (Z.succ (d y)) by lia.
      rewrite Z.even_succ, <- Z.negb_even, Hev. reflexivity.
    - left. split; [lia | reflexivity].
    - left. split; [lia |]. replace (d x) with (Z.succ (d y)) by lia.
      rewrite Z.even_succ, <- Z.negb_even, Hev. reflexivity.
    - right. split; [lia | reflexivity]. }
  assert (HbE : b <= E).
  { rewrite <- Hzb. apply Hmincover.
    exists (fun x => 1 <= x <= n /\ Z.even (d x) = true). split.
    - exact HVCE.
    - unfold E. apply set_card_ext__final_semantics. intro x. intuition lia. }
  assert (HbO : b <= O).
  { rewrite <- Hzb. apply Hmincover.
    exists (fun x => 1 <= x <= n /\ Z.even (d x) = false). split.
    - exact HVCO.
    - unfold O. apply set_card_ext__final_semantics. intro x. intuition lia. }
  assert (Hbpos : 1 <= b).
  { rewrite <- Hzb.
    specialize (Hscovers (u0,v0) Hq0). simpl in Hscovers.
    destruct Hscovers as [Hsu | Hsv].
    - eapply set_card_member_positive__final_semantics with (x := u0).
      split; [lia | exact Hsu].
    - eapply set_card_member_positive__final_semantics with (x := v0).
      split; [lia | exact Hsv]. }
  assert (Hsum : E + O = n).
  { unfold E, O. apply parity_card_sum__final_semantics. lia. }
  assert (Hab : a = Z.min E O) by (unfold E, O; exact Ha).
  assert (Hba : b <= a).
  { rewrite Hab. apply Z.min_glb; assumption. }
  assert (Haub : a <= 2).
  { rewrite Hab. destruct (Z_le_gt_dec E 2).
    - eapply Z.le_trans; [apply Z.le_min_l | exact l].
    - assert (O <= 2) by lia.
      eapply Z.le_trans; [apply Z.le_min_r | assumption]. }
  assert (Hapos : 1 <= a) by (rewrite Hab; apply Z.min_glb; assumption).
  assert (Habvals : a = 2 /\ b = 1) by lia.
  destruct Habvals as [-> Hb1].
  assert (HcardS : #(fun x : Z => 1 <= x < n+1 /\ s x) = 1) by lia.
  pose proof (Hscovers (u0,v0) Hq0) as Hhit0. simpl in Hhit0.
  destruct Hhit0 as [Hc | Hc].
  - set (c := u0).
    assert (Hcrange : 1 <= c <= n) by (unfold c; lia).
    assert (Hcs : s c) by exact Hc.
    assert (Honly : forall x, s x -> x = c).
    { intros x Hsx. eapply set_card_one_unique__final_semantics
        with (P := fun z : Z => 1 <= z < n+1 /\ s z); eauto.
      - split; [apply Hsrange in Hsx; lia | exact Hsx].
      - split; [lia | exact Hcs]. }
    assert (Hincident : forall u v, In (u,v) e -> u = c \/ v = c).
    { intros u v Huv. pose proof (Hscovers (u,v) Huv) as Hhit. simpl in Hhit.
      destruct Hhit; [left | right]; apply Honly; assumption. }
    assert (Hd1 := root_distance_one_zero__final_semantics n e d ltac:(lia) Hd).
    destruct (Z.eq_dec c 1) as [Hc1 | Hc1].
    + assert (HEone : E = 1).
      { unfold E. eapply set_card_singleton_exact__final_semantics with (x := 1).
        - split; [lia | rewrite Hd1; reflexivity].
        - intros x [Hxrange Heven].
          destruct (Z.eq_dec x 1); auto.
          destruct (root_distance_predecessor__final_semantics n e d x
            ltac:(lia) ltac:(lia) n0 Hd) as [y [edge [Hy [Hedge [Horient Hdist]]]]].
          destruct edge as [u v]. specialize (Hincident u v Hedge).
          assert (Hyc : y = c).
          { destruct Horient as [Heq | Heq]; inversion Heq; subst u v;
              simpl in Hincident; intuition congruence. }
          rewrite Hyc, Hc1, Hd1 in Hdist.
          replace (d x) with 1 in Heven by lia; discriminate. }
      rewrite HEone, Z.min_l in Hab by lia. lia.
    + assert (Hdc : d c = 1).
      { destruct (root_distance_predecessor__final_semantics n e d c
          ltac:(lia) Hcrange Hc1 Hd) as [y [edge [Hy [Hedge [Horient Hdist]]]]].
        assert (Hyc : y <> c) by (intro Heq; subst y; lia).
        assert (Hy1 : y = 1).
        { destruct (Z.eq_dec y 1); auto.
          destruct (root_distance_predecessor__final_semantics n e d y
            ltac:(lia) Hy n0 Hd) as [w [edge' [Hw [Hedge' [Horient' Hdist']]]]].
          destruct edge' as [u v]. specialize (Hincident u v Hedge').
          assert (Hwc : w = c).
          { destruct Horient' as [Heq | Heq]; inversion Heq; subst u v;
              simpl in Hincident; intuition congruence. }
          rewrite Hwc in Hdist'. lia. }
        subst y. lia. }
      assert (HOone : O = 1).
      { unfold O. eapply set_card_singleton_exact__final_semantics with (x := c).
        - split; [lia | rewrite Hdc; reflexivity].
        - intros x [Hxrange Hodd].
          destruct (Z.eq_dec x c); auto.
          destruct (Z.eq_dec x 1).
          { subst x. rewrite Hd1 in Hodd. discriminate. }
          destruct (root_distance_predecessor__final_semantics n e d x
            ltac:(lia) ltac:(lia) n1 Hd) as [y [edge [Hy [Hedge [Horient Hdist]]]]].
          destruct edge as [u v]. specialize (Hincident u v Hedge).
          assert (Hyc' : y = c).
          { destruct Horient as [Heq | Heq]; inversion Heq; subst u v;
              simpl in Hincident; intuition congruence. }
          rewrite Hyc', Hdc in Hdist.
          replace (d x) with 2 in Hodd by lia; discriminate. }
      rewrite HOone, Z.min_r in Hab by lia. lia.
  - (* The symmetric endpoint choice gives the same center argument. *)
    set (c := v0).
    assert (Hcrange : 1 <= c <= n) by (unfold c; lia).
    assert (Hcs : s c) by exact Hc.
    assert (Honly : forall x, s x -> x = c).
    { intros x Hsx. eapply set_card_one_unique__final_semantics
        with (P := fun z : Z => 1 <= z < n+1 /\ s z); eauto.
      - split; [apply Hsrange in Hsx; lia | exact Hsx].
      - split; [lia | exact Hcs]. }
    assert (Hincident : forall u v, In (u,v) e -> u = c \/ v = c).
    { intros u v Huv. pose proof (Hscovers (u,v) Huv) as Hhit. simpl in Hhit.
      destruct Hhit; [left | right]; apply Honly; assumption. }
    assert (Hd1 := root_distance_one_zero__final_semantics n e d ltac:(lia) Hd).
    destruct (Z.eq_dec c 1) as [Hc1 | Hc1].
    + assert (HEone : E = 1).
      { unfold E. eapply set_card_singleton_exact__final_semantics with (x := 1).
        - split; [lia | rewrite Hd1; reflexivity].
        - intros x [Hxrange Heven]. destruct (Z.eq_dec x 1); auto.
          destruct (root_distance_predecessor__final_semantics n e d x
            ltac:(lia) ltac:(lia) n0 Hd) as [y [edge [Hy [Hedge [Horient Hdist]]]]].
          destruct edge as [u v]. specialize (Hincident u v Hedge).
          assert (Hyc : y = c).
          { destruct Horient as [Heq | Heq]; inversion Heq; subst u v;
              simpl in Hincident; intuition congruence. }
          rewrite Hyc, Hc1, Hd1 in Hdist.
          replace (d x) with 1 in Heven by lia; discriminate. }
      rewrite HEone, Z.min_l in Hab by lia. lia.
    + assert (Hdc : d c = 1).
      { destruct (root_distance_predecessor__final_semantics n e d c
          ltac:(lia) Hcrange Hc1 Hd) as [y [edge [Hy [Hedge [Horient Hdist]]]]].
        assert (Hyc : y <> c) by (intro Heq; subst y; lia).
        assert (Hy1 : y = 1).
        { destruct (Z.eq_dec y 1); auto.
          destruct (root_distance_predecessor__final_semantics n e d y
            ltac:(lia) Hy n0 Hd) as [w [edge' [Hw [Hedge' [Horient' Hdist']]]]].
          destruct edge' as [u v]. specialize (Hincident u v Hedge').
          assert (Hwc : w = c).
          { destruct Horient' as [Heq | Heq]; inversion Heq; subst u v;
              simpl in Hincident; intuition congruence. }
          rewrite Hwc in Hdist'. lia. }
        subst y. lia. }
      assert (HOone : O = 1).
      { unfold O. eapply set_card_singleton_exact__final_semantics with (x := c).
        - split; [lia | rewrite Hdc; reflexivity].
        - intros x [Hxrange Hodd]. destruct (Z.eq_dec x c); auto.
          destruct (Z.eq_dec x 1).
          { subst x. rewrite Hd1 in Hodd. discriminate. }
          destruct (root_distance_predecessor__final_semantics n e d x
            ltac:(lia) ltac:(lia) n1 Hd) as [y [edge [Hy [Hedge [Horient Hdist]]]]].
          destruct edge as [u v]. specialize (Hincident u v Hedge).
          assert (Hyc' : y = c).
          { destruct Horient as [Heq | Heq]; inversion Heq; subst u v;
              simpl in Hincident; intuition congruence. }
          rewrite Hyc', Hdc in Hdist.
          replace (d x) with 2 in Hodd by lia; discriminate. }
      rewrite HOone, Z.min_r in Hab by lia. lia.
Qed.
