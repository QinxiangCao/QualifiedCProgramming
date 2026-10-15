Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.
Local Open Scope Z_scope.

Definition CanonicalEdge (p : Z * Z) : Z * Z :=
  if Z.leb (fst p) (snd p) then p else (snd p, fst p).

Definition Incident (x : Z) (p : Z * Z) : Prop :=
  fst p = x \/ snd p = x.

Definition EdgeDegree (x : Z) (e : list (Z * Z)) : Z :=
  Z.of_nat (length (filter
    (fun p => orb (Z.eqb (fst p) x) (Z.eqb (snd p) x)) e)).

Definition InputGraph (n : Z) (e : list (Z * Z)) : ZGraph :=
  {| zv := fun v => 0 <= v < n;
     ze := fun u v => exists j,
       0 <= j < Zlength e /\
       (Znth j e (0,0) = (u,v) \/ Znth j e (0,0) = (v,u)) |}.

Definition InputConnected (n : Z) (e : list (Z * Z)) : Prop :=
  forall u v, 0 <= u < n -> 0 <= v < n ->
    reachable (InputGraph n e) u v.

Definition CompanyGraph (n : Z) (c : list Z) (e : list (Z * Z))
    (labels : list Z) : ZGraph :=
  {| zv := fun v => 0 <= v < n;
     ze := fun u v => exists j,
       0 <= j < Zlength e /\
       (Znth j e (0,0) = (u,v) \/ Znth j e (0,0) = (v,u)) /\
       In (Znth j labels 0) c |}.

Definition CompanyConnected (n : Z) (c : list Z) (e : list (Z * Z))
    (labels : list Z) : Prop :=
  forall u v, 0 <= u < n -> 0 <= v < n ->
    reachable (CompanyGraph n c e labels) u v.

Definition ValidTrainPlan (n : Z) (e : list (Z * Z)) (k : Z)
    (labels : list Z) : Prop :=
  2 <= k <= 3 /\ Zlength labels = Zlength e /\
  Forall (fun x => 1 <= x <= k) labels /\
  (forall c, 1 <= c <= k -> ~ CompanyConnected n (c :: nil) e labels) /\
  forall c d, 1 <= c <= k -> 1 <= d <= k -> c <> d ->
    CompanyConnected n (c :: d :: nil) e labels.

Definition Pre (n : Z) (e : list (Z * Z)) : Prop :=
  3 <= n <= 50 /\ n - 1 <= Zlength e /\ Zlength e <= 1225 /\
  Forall (fun p => 0 <= fst p < n /\
    0 <= snd p < n /\ fst p <> snd p) e /\
  NoDup (map CanonicalEdge e) /\ InputConnected n e.

Definition Spec (n : Z) (e : list (Z * Z)) (out : Z * list Z) : Prop :=
  ValidTrainPlan n e (fst out) (snd out).

Definition DegreePrefix (n : Z) (e : list (Z * Z)) (i : Z)
    (degrees : list Z) : Prop :=
  Zlength degrees = n /\
  forall x, 0 <= x < n ->
    Znth x degrees 0 = EdgeDegree x (sublist 0 i e).

Definition PivotPrefix (n : Z) (degrees : list Z) (i : Z) : Prop :=
  forall x, 0 <= x < i -> Znth x degrees 0 >= n - 1.

Definition PivotChoice (n : Z) (degrees : list Z) (pivot : Z) : Prop :=
  (0 <= pivot < n /\ Znth pivot degrees 0 < n - 1 /\
    PivotPrefix n degrees pivot) \/
  (pivot = -1 /\ PivotPrefix n degrees n).

Definition PivotColorPrefix (e : list (Z * Z)) (pivot i : Z)
    (labels : list Z) : Prop :=
  Zlength labels = i /\
  forall j, 0 <= j < i ->
    Znth j labels 0 =
      if orb (Z.eqb (fst (Znth j e (0,0))) pivot)
             (Z.eqb (snd (Znth j e (0,0))) pivot)
      then 1 else 2.

Definition IsFirstIncident (e : list (Z * Z)) (h : Z) : Prop :=
  0 <= h < Zlength e /\ Incident 0 (Znth h e (0,0)) /\
  forall j, 0 <= j < h -> ~ Incident 0 (Znth j e (0,0)).

Definition CompleteColorPrefix (e : list (Z * Z)) (i first : Z)
    (labels : list Z) : Prop :=
  Zlength labels = i /\
  ((first = 1 /\
      forall j, 0 <= j < i ->
        ~ Incident 0 (Znth j e (0,0)) /\ Znth j labels 0 = 3) \/
   (first = 0 /\ exists h,
      IsFirstIncident (sublist 0 i e) h /\
      forall j, 0 <= j < i ->
        Znth j labels 0 =
          if Z.eqb j h then 1
          else if orb (Z.eqb (fst (Znth j e (0,0))) 0)
                      (Z.eqb (snd (Znth j e (0,0))) 0)
               then 2 else 3)).

Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Lemma Zlength_replace_Znth__degree_update_exit : forall {A : Type}
    (l : list A) n (v : A),
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. revert n.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma Znth_replace_Znth_Same__degree_update_exit : forall {A : Type}
    (d : A) (l : list A) (i : Z) (v : A),
  0 <= i < Zlength l -> Znth i (replace_Znth i v l) d = v.
Proof.
  intros A d l i v H.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  rewrite Zlength_correct in H.
  assert (0 <= m < length l)%nat by lia.
  clearbody m. clear H i.
  generalize dependent m.
  induction l; simpl in *; intros.
  - lia.
  - destruct m.
    + reflexivity.
    + simpl. rewrite IHl; auto. lia.
Qed.
Lemma Znth_replace_Znth_Diff__degree_update_exit : forall {A : Type}
    (d : A) (l : list A) (i j : Z) (v : A),
  0 <= i < Zlength l -> 0 <= j < Zlength l -> i <> j ->
  Znth j (replace_Znth i v l) d = Znth j l d.
Proof.
  intros A d l i j v H H0 H1.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  set (n := Z.to_nat j).
  rewrite Zlength_correct in H, H0.
  assert (0 <= m < length l)%nat by lia.
  assert (0 <= n < length l)%nat by lia.
  assert (m <> n) by lia.
  clearbody m. clearbody n.
  clear H H0 H1 i j.
  generalize dependent m. generalize dependent n.
  induction l; simpl in *; intros.
  - lia.
  - destruct m, n; simpl in *; try auto; try lia.
    rewrite IHl; try lia. auto.
Qed.
Lemma sublist_split_app_l__degree_update_exit : forall {A : Type}
    lo hi (l1 l2 : list A),
  0 <= lo <= hi -> hi <= Zlength l1 ->
  sublist lo hi (l1 ++ l2) = sublist lo hi l1.
Proof.
  intros A lo hi l1 l2 H H0.
  unfold sublist.
  rewrite firstn_app. simpl.
  rewrite Zlength_correct in H0.
  replace (Z.to_nat hi - length l1)%nat with O by lia.
  rewrite app_nil_r. auto.
Qed.
Lemma sublist_single__degree_update_exit : forall {A : Type} (d : A)
    n (l : list A),
  0 <= n < Zlength l -> sublist n (n + 1) l = Znth n l d :: nil.
Proof.
  intros A d n l H.
  rewrite Zlength_correct in *.
  rewrite (firstn_skipSn d (Z.to_nat n) l) at 1; try lia.
  unfold Znth, sublist.
  rewrite firstn_app.
  assert (length (firstn (Z.to_nat n) l) = Z.to_nat n)
    by (rewrite length_firstn; lia).
  rewrite firstn_all2; try lia.
  replace (Z.to_nat (n + 1) - length (firstn (Z.to_nat n) l))%nat
    with 1%nat by lia.
  rewrite skipn_app.
  replace (Z.to_nat n - length (firstn (Z.to_nat n) l))%nat
    with 0%nat by lia.
  rewrite skipn_all2; try lia.
  simpl. reflexivity.
Qed.
Lemma sublist_split__degree_update_exit : forall {A : Type}
    lo hi mid (l : list A),
  0 <= lo <= mid -> mid <= hi <= Zlength l ->
  sublist lo hi l = sublist lo mid l ++ sublist mid hi l.
Proof.
  intros A lo hi mid l H H0.
  rewrite <- (firstn_skipn (Z.to_nat hi) l).
  remember (firstn (Z.to_nat hi) l) as l1.
  remember (skipn (Z.to_nat hi) l) as l2.
  assert (Z.of_nat (length l1) = hi).
  { rewrite Heql1, length_firstn, Zlength_correct in *. lia. }
  assert (length l = length l1 + length l2)%nat.
  { rewrite Heql1, Heql2, length_firstn, length_skipn. lia. }
  rewrite Zlength_correct in H0.
  rewrite H2 in H0.
  clear Heql1 Heql2 H2 l.
  do 3 (rewrite sublist_split_app_l__degree_update_exit;
    rewrite ?Zlength_correct in *; try lia).
  unfold sublist.
  replace (Z.to_nat hi)%nat with (length l1) by lia.
  assert (mid <= Z.of_nat (length l1)) by lia.
  clear H0 H1 l2 hi.
  rewrite firstn_all2; try lia.
  rename l1 into l.
  rewrite <- (firstn_skipn (Z.to_nat lo) l).
  remember (firstn (Z.to_nat lo) l) as l1.
  remember (skipn (Z.to_nat lo) l) as l2.
  assert (Z.of_nat (length l1) = lo).
  { rewrite Heql1, length_firstn. lia. }
  rewrite firstn_app.
  do 3 rewrite skipn_app.
  rewrite firstn_all2; try lia.
  replace (Z.to_nat lo - length l1)%nat with O by lia.
  simpl.
  do 2 (rewrite skipn_all2; try lia).
  rewrite !app_nil_l, firstn_skipn.
  reflexivity.
Qed.
Lemma canonical_edge_swap__degree_update_exit : forall a b,
  CanonicalEdge (a, b) = CanonicalEdge (b, a).
Proof.
  intros a b. unfold CanonicalEdge. simpl.
  destruct (Z.leb_spec a b), (Z.leb_spec b a); simpl; try lia;
    try (f_equal; lia); reflexivity.
Qed.
Lemma other_endpoint_incident__degree_update_exit : forall x p,
  Incident x p -> fst p <> snd p ->
  (if Z.eqb (fst p) x then snd p else fst p) <> x /\
  CanonicalEdge p =
    CanonicalEdge (x, if Z.eqb (fst p) x then snd p else fst p).
Proof.
  intros x [a b] Hinc Hneq. unfold Incident in Hinc. simpl in *.
  destruct Hinc as [-> | ->].
  - rewrite Z.eqb_refl. split; [congruence | reflexivity].
  - destruct (Z.eqb_spec a x); [congruence |].
    split; [congruence |].
    symmetry. apply canonical_edge_swap__degree_update_exit.
Qed.
Lemma skip_vertex_range__degree_update_exit : forall n x y,
  0 <= x < n -> 0 <= y < n -> y <> x ->
  0 <= (if Z.ltb y x then y else y - 1) < n - 1.
Proof.
  intros n x y Hx Hy Hneq.
  destruct (Z.ltb_spec y x); lia.
Qed.
Lemma skip_vertex_injective__degree_update_exit : forall x y z,
  y <> x -> z <> x ->
  (if Z.ltb y x then y else y - 1) =
  (if Z.ltb z x then z else z - 1) ->
  y = z.
Proof.
  intros x y z Hy Hz Heq.
  destruct (Z.ltb_spec y x), (Z.ltb_spec z x); lia.
Qed.
Lemma nodup_map_on__degree_update_exit : forall {A B : Type} (f : A -> B) xs,
  NoDup xs ->
  (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
  NoDup (map f xs).
Proof.
  intros A B f xs Hnd. induction Hnd as [|x xs Hnot Hnd IH]; intros Hinj.
  - constructor.
  - simpl. constructor.
    + intro Hmap. apply in_map_iff in Hmap.
      destruct Hmap as [y [Heq Hy]].
      assert (x = y) by (eapply Hinj; simpl; eauto).
      subst y. contradiction.
    + apply IH. intros u v Hu Hv Heq.
      eapply Hinj; simpl; eauto.
Qed.
Lemma nodup_map_value_injective__degree_update_exit : forall {A B : Type}
    (f : A -> B) xs x y,
  NoDup (map f xs) -> In x xs -> In y xs -> f x = f y -> x = y.
Proof.
  intros A B f xs. induction xs as [|a xs IH]; intros x y Hnd Hx Hy Heq.
  - contradiction.
  - simpl in Hnd. inversion Hnd as [|? ? Hnot Htail]; subst.
    simpl in Hx, Hy. destruct Hx as [-> | Hx], Hy as [-> | Hy]; auto.
    + exfalso. apply Hnot. apply in_map_iff. exists y.
      split; [symmetry; exact Heq | exact Hy].
    + exfalso. apply Hnot. apply in_map_iff. exists x.
      split; [exact Heq | exact Hx].
Qed.
Lemma nodup_range_length__degree_update_exit : forall limit picks,
  0 <= limit -> NoDup picks ->
  Forall (fun y : Z => 0 <= y < limit) picks ->
  Z.of_nat (length picks) <= limit.
Proof.
  intros limit picks Hlimit Hnd Hrange.
  assert (Hnonneg : Forall (fun y : Z => 0 <= y) picks).
  { apply Forall_forall. intros y Hy.
    rewrite Forall_forall in Hrange. specialize (Hrange y Hy). lia. }
  assert (Hnatnd : NoDup (map Z.to_nat picks)).
  { apply nodup_map_on__degree_update_exit; [exact Hnd |].
    intros x y Hinx Hiny Heq.
    assert (Hx0 : 0 <= x).
    { rewrite Forall_forall in Hnonneg. eauto. }
    assert (Hy0 : 0 <= y).
    { rewrite Forall_forall in Hnonneg. eauto. }
    apply Z2Nat.inj in Heq; auto. }
  assert (Hincl : incl (map Z.to_nat picks) (seq 0 (Z.to_nat limit))).
  { intros k Hk. apply in_map_iff in Hk.
    destruct Hk as [y [Hky Hy]]. subst k. apply in_seq.
    apply Forall_forall with (x := y) in Hrange; auto. lia. }
  pose proof (NoDup_incl_length Hnatnd Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia. lia.
Qed.
Lemma edge_degree_simple_bound__degree_update_exit : forall n e x,
  Pre n e -> 0 <= x < n -> EdgeDegree x e <= n - 1.
Proof.
  intros n e x Hpre Hx.
  destruct Hpre as [_ [_ [_ [Hedges [Hcanon _]]]]].
  set (inc := filter
    (fun p : Z * Z => orb (Z.eqb (fst p) x) (Z.eqb (snd p) x)) e).
  set (other := fun p : Z * Z =>
    if Z.eqb (fst p) x then snd p else fst p).
  set (key := fun p : Z * Z =>
    if Z.ltb (other p) x then other p else other p - 1).
  set (keys := map key inc).
  assert (Hinc_info : forall p, In p inc ->
      In p e /\ Incident x p /\
      0 <= fst p < n /\ 0 <= snd p < n /\ fst p <> snd p).
  { intros p Hp. subst inc. apply filter_In in Hp. destruct Hp as [Hpe Hb].
    rewrite orb_true_iff in Hb.
    unfold Incident. rewrite !Z.eqb_eq in Hb.
    rewrite Forall_forall in Hedges. specialize (Hedges p Hpe).
    tauto. }
  assert (Hinc_nd : NoDup inc).
  { apply NoDup_filter. eapply NoDup_map_inv. exact Hcanon. }
  assert (Hkeys_nd : NoDup keys).
  { subst keys. apply nodup_map_on__degree_update_exit; [exact Hinc_nd |].
    intros p q Hp Hq Heq.
    pose proof (Hinc_info p Hp) as [Hpe [Hpinc [_ [_ Hpneq]]]].
    pose proof (Hinc_info q Hq) as [Hqe [Hqinc [_ [_ Hqneq]]]].
    pose proof (other_endpoint_incident__degree_update_exit x p Hpinc Hpneq)
      as [Hpop Hpcan].
    pose proof (other_endpoint_incident__degree_update_exit x q Hqinc Hqneq)
      as [Hqop Hqcan].
    unfold key, other in Heq, Hpop, Hpcan, Hqop, Hqcan.
    assert ((if Z.eqb (fst p) x then snd p else fst p) =
            (if Z.eqb (fst q) x then snd q else fst q)) as Hother.
    { eapply skip_vertex_injective__degree_update_exit; eauto. }
    eapply nodup_map_value_injective__degree_update_exit
      with (f := CanonicalEdge) (xs := e); eauto.
    rewrite Hpcan, Hqcan, Hother. reflexivity. }
  assert (Hkeys_range : Forall (fun y : Z => 0 <= y < n - 1) keys).
  { apply Forall_forall. intros y Hy. subst keys.
    apply in_map_iff in Hy. destruct Hy as [p [Hpy Hp]]. subst y.
    pose proof (Hinc_info p Hp) as [_ [Hpinc [Hpfst [Hpsnd Hpneq]]]].
    pose proof (other_endpoint_incident__degree_update_exit x p Hpinc Hpneq)
      as [Hop _].
    unfold key, other in *.
    apply skip_vertex_range__degree_update_exit; auto.
    destruct (Z.eqb_spec (fst p) x); [exact Hpsnd | exact Hpfst]. }
  pose proof (nodup_range_length__degree_update_exit (n - 1) keys)
    as Hbound.
  specialize (Hbound ltac:(lia) Hkeys_nd Hkeys_range).
  unfold EdgeDegree. subst keys key other inc. rewrite length_map in Hbound.
  exact Hbound.
Qed.
Lemma degree_prefix_step__degree_update_exit : forall n e i degrees,
  Pre n e ->
  0 <= i < Zlength e ->
  DegreePrefix n e i degrees ->
  DegreePrefix n e (i + 1)
    (replace_Znth (snd (Znth i e (0, 0)))
      (Znth (snd (Znth i e (0, 0)))
        (replace_Znth (fst (Znth i e (0, 0)))
          (Znth (fst (Znth i e (0, 0))) degrees 0 + 1) degrees) 0 + 1)
      (replace_Znth (fst (Znth i e (0, 0)))
        (Znth (fst (Znth i e (0, 0))) degrees 0 + 1) degrees)).
Proof.
  intros n e i degrees Hpre Hi [Hlen Hprefix].
  destruct Hpre as [Hn [_ [_ [Hedges _]]]].
  assert (Hin : In (Znth i e (0, 0)) e).
  { unfold Znth. apply nth_In.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite Zlength_correct in Hi.
    lia. }
  rewrite Forall_forall in Hedges.
  pose proof (Hedges _ Hin) as Hedge.
  destruct Hedge as [[Hu0 Hun] [[Hv0 Hvn] Huv]].
  set (p := Znth i e (0, 0)) in *.
  set (u := fst p) in *.
  set (v := snd p) in *.
  split.
  - rewrite !Zlength_replace_Znth__degree_update_exit. exact Hlen.
  - intros x Hx.
    rewrite (sublist_split__degree_update_exit 0 (i + 1) i e) by lia.
    rewrite (sublist_single__degree_update_exit (0, 0) i e) by lia.
    unfold EdgeDegree.
    rewrite filter_app, length_app.
    simpl.
    unfold EdgeDegree in Hprefix.
    rewrite Nat2Z.inj_add.
    rewrite <- (Hprefix x Hx).
    destruct (Z.eq_dec x u) as [-> | Hxu].
    + rewrite Znth_replace_Znth_Diff__degree_update_exit by
        (repeat rewrite Zlength_replace_Znth__degree_update_exit; lia).
      rewrite Znth_replace_Znth_Same__degree_update_exit by (rewrite Hlen; lia).
      subst u v p.
      rewrite Z.eqb_refl.
      simpl.
      lia.
    + destruct (Z.eq_dec x v) as [-> | Hxv].
      * rewrite Znth_replace_Znth_Same__degree_update_exit by
          (rewrite Zlength_replace_Znth__degree_update_exit, Hlen; lia).
        rewrite Znth_replace_Znth_Diff__degree_update_exit by
          (repeat rewrite Zlength_replace_Znth__degree_update_exit;
            try rewrite Hlen; lia).
        subst u v p.
        destruct (Z.eqb_spec (fst (Znth i e (0, 0)))
          (snd (Znth i e (0, 0)))); [contradiction | simpl].
        rewrite Z.eqb_refl.
        simpl.
        lia.
      * rewrite Znth_replace_Znth_Diff__degree_update_exit by
          (repeat rewrite Zlength_replace_Znth__degree_update_exit; lia).
        rewrite Znth_replace_Znth_Diff__degree_update_exit by lia.
        subst u v p.
        destruct (Z.eqb_spec (fst (Znth i e (0, 0))) x);
          [congruence | simpl].
        destruct (Z.eqb_spec (snd (Znth i e (0, 0))) x);
          [congruence | simpl].
        lia.
Qed.
Lemma Znth_app_left__pivot_color :
  forall (l1 l2 : list Z) (d j : Z),
    0 <= j < Zlength l1 ->
    Znth j (l1 ++ l2) d = Znth j l1 d.
Proof.
  intros l1 l2 d j Hj.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hj.
  lia.
Qed.
Lemma Znth_app_last__pivot_color :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ (x :: nil)) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma pivot_color_prefix_incident_step__pivot_color :
  forall (e : list (Z * Z)) pivot i labels,
    0 <= i ->
    PivotColorPrefix e pivot i labels ->
    (fst (Znth i e (0, 0)) = pivot \/
     snd (Znth i e (0, 0)) = pivot) ->
    PivotColorPrefix e pivot (i + 1) (labels ++ (1 :: nil)).
Proof.
  intros e pivot i labels Hi Hprefix Hincident.
  unfold PivotColorPrefix in *.
  destruct Hprefix as [Hlen Hlabels].
  split.
  - rewrite Zlength_app, Hlen, Zlength_cons, Zlength_nil.
    lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + rewrite Znth_app_left__pivot_color by (rewrite Hlen; lia).
      apply Hlabels.
      lia.
    + assert (j = i) by lia.
      subst j.
      rewrite <- Hlen in Hincident.
      replace i with (Zlength labels) by lia.
      rewrite Znth_app_last__pivot_color.
      destruct Hincident as [Hfst | Hsnd].
      * rewrite Hfst, Z.eqb_refl.
        reflexivity.
      * rewrite Hsnd, Z.eqb_refl.
        destruct (Z.eqb (fst (Znth (Zlength labels) e (0, 0))) pivot);
          reflexivity.
Qed.
Lemma pivot_color_prefix_nonincident_step__pivot_color :
  forall (e : list (Z * Z)) pivot i labels,
    0 <= i ->
    PivotColorPrefix e pivot i labels ->
    fst (Znth i e (0, 0)) <> pivot ->
    snd (Znth i e (0, 0)) <> pivot ->
    PivotColorPrefix e pivot (i + 1) (labels ++ (2 :: nil)).
Proof.
  intros e pivot i labels Hi Hprefix Hfst Hsnd.
  unfold PivotColorPrefix in *.
  destruct Hprefix as [Hlen Hlabels].
  split.
  - rewrite Zlength_app, Hlen, Zlength_cons, Zlength_nil.
    lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + rewrite Znth_app_left__pivot_color by (rewrite Hlen; lia).
      apply Hlabels.
      lia.
    + assert (j = i) by lia.
      subst j.
      rewrite <- Hlen in Hfst, Hsnd.
      replace i with (Zlength labels) by lia.
      rewrite Znth_app_last__pivot_color.
      destruct (Z.eqb (fst (Znth (Zlength labels) e (0, 0))) pivot)
        eqn:Efst.
      * apply Z.eqb_eq in Efst.
        contradiction.
      * destruct (Z.eqb (snd (Znth (Zlength labels) e (0, 0))) pivot)
          eqn:Esnd.
        -- apply Z.eqb_eq in Esnd.
           contradiction.
        -- reflexivity.
Qed.
Lemma complete_color_prefix_first_incident_step__complete_color_incident :
  forall (e : list (Z * Z)) (i : Z) (labels : list Z),
    0 <= i < Zlength e ->
    CompleteColorPrefix e i 1 labels ->
    Incident 0 (Znth i e (0, 0)) ->
    CompleteColorPrefix e (i + 1) 0 (labels ++ 1 :: nil).
Proof.
  intros e i labels Hi Hprefix Hincident.
  unfold CompleteColorPrefix in *.
  destruct Hprefix as [Hlength [[_ Hold] | [Hbad _]]]; try lia.
  split.
  - rewrite Zlength_app_cons. lia.
  - right. split; [reflexivity |].
    exists i. split.
    + unfold IsFirstIncident.
      rewrite Zlength_sublist0 by lia.
      split; [lia |]. split.
      * rewrite Znth_sublist0 by lia. exact Hincident.
      * intros j Hj.
        rewrite Znth_sublist0 by lia.
        specialize (Hold j ltac:(lia)) as [Hnot _].
        exact Hnot.
    + intros j Hj.
      destruct (Z_lt_ge_dec j i) as [Hji | Hji].
      * rewrite app_Znth1 by lia.
        assert (Hji_eqb : Z.eqb j i = false) by (apply Z.eqb_neq; lia).
        rewrite Hji_eqb.
        specialize (Hold j ltac:(lia)) as [Hnot Hlabel].
        rewrite Hlabel.
        destruct (Z.eqb (fst (Znth j e (0, 0))) 0) eqn:Hfst.
        -- apply Z.eqb_eq in Hfst. exfalso. apply Hnot. left. exact Hfst.
        -- destruct (Z.eqb (snd (Znth j e (0, 0))) 0) eqn:Hsnd.
           ++ apply Z.eqb_eq in Hsnd. exfalso. apply Hnot. right. exact Hsnd.
           ++ reflexivity.
      * assert (j = i) by lia. subst j.
        rewrite app_Znth2 by lia.
        replace (i - Zlength labels) with 0 by lia.
        simpl. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma complete_color_prefix_later_incident_step__complete_color_incident :
  forall (e : list (Z * Z)) (i : Z) (labels : list Z),
    0 <= i < Zlength e ->
    CompleteColorPrefix e i 0 labels ->
    Incident 0 (Znth i e (0, 0)) ->
    CompleteColorPrefix e (i + 1) 0 (labels ++ 2 :: nil).
Proof.
  intros e i labels Hi Hprefix Hincident.
  unfold CompleteColorPrefix in *.
  destruct Hprefix as [Hlength [[Hbad _] | [_ [h [Hfirst Hold]]]]]; try lia.
  split.
  - rewrite Zlength_app_cons. lia.
  - right. split; [reflexivity |].
    exists h. split.
    + unfold IsFirstIncident in *.
      destruct Hfirst as [Hh [Hhinc Hbefore]].
      rewrite Zlength_sublist0 in Hh by lia.
      rewrite Zlength_sublist0 by lia.
      split; [lia |]. split.
      * rewrite Znth_sublist0 in Hhinc by lia.
        rewrite Znth_sublist0 by lia.
        exact Hhinc.
      * intros j Hj.
        specialize (Hbefore j Hj).
        rewrite Znth_sublist0 in Hbefore by lia.
        rewrite Znth_sublist0 by lia.
        exact Hbefore.
    + intros j Hj.
      destruct (Z_lt_ge_dec j i) as [Hji | Hji].
      * rewrite app_Znth1 by lia.
        apply Hold. lia.
      * assert (j = i) by lia. subst j.
        rewrite app_Znth2 by lia.
        replace (i - Zlength labels) with 0 by lia.
        simpl.
        unfold IsFirstIncident in Hfirst.
        destruct Hfirst as [Hh _].
        rewrite Zlength_sublist0 in Hh by lia.
        assert (Hih_eqb : Z.eqb i h = false) by (apply Z.eqb_neq; lia).
        rewrite Hih_eqb.
        destruct Hincident as [Hincident | Hincident].
        -- rewrite Hincident, Z.eqb_refl. reflexivity.
        -- rewrite Hincident, Z.eqb_refl, Bool.orb_true_r. reflexivity.
Qed.
Lemma complete_color_prefix_nonincident_step__complete_color_nonincident :
  forall (e : list (Z * Z)) (i first : Z) (labels : list Z),
    0 <= i ->
    i < Zlength e ->
    ~ Incident 0 (Znth i e (0, 0)) ->
    CompleteColorPrefix e i first labels ->
    CompleteColorPrefix e (i + 1) first (labels ++ (3 :: nil)).
Proof.
  intros e i first labels Hi Hie Hnonincident Hprefix.
  unfold CompleteColorPrefix in Hprefix |- *.
  destruct Hprefix as [Hlabels Hprefix].
  split.
  - rewrite Zlength_app_cons.
    lia.
  - destruct Hprefix as [[Hfirst Hcolors] | [Hfirst [h [Hincident Hcolors]]]].
    + left.
      split; [exact Hfirst |].
      intros j Hj.
      destruct (Z_lt_ge_dec j i) as [Hji | Hij].
      * specialize (Hcolors j ltac:(lia)).
        rewrite app_Znth1 by lia.
        exact Hcolors.
      * assert (j = i) by lia.
        subst j.
        split; [exact Hnonincident |].
        rewrite app_Znth2 by lia.
        rewrite Hlabels.
        replace (i - i) with 0 by lia.
        reflexivity.
    + right.
      split; [exact Hfirst |].
      exists h.
      split.
      * unfold IsFirstIncident in Hincident |- *.
        destruct Hincident as [[Hh0 Hhi] [Hhincident Hbefore]].
        rewrite Zlength_sublist0 in Hhi by lia.
        split.
        -- rewrite Zlength_sublist0 by lia.
           lia.
        -- split.
           ++ rewrite Znth_sublist0 by lia.
              rewrite Znth_sublist0 in Hhincident by lia.
              exact Hhincident.
           ++ intros j Hj.
              specialize (Hbefore j Hj).
              rewrite Znth_sublist0 in Hbefore by lia.
              rewrite Znth_sublist0 by lia.
              exact Hbefore.
      * intros j Hj.
        destruct (Z_lt_ge_dec j i) as [Hji | Hij].
        -- rewrite app_Znth1 by lia.
           apply Hcolors.
           lia.
        -- assert (j = i) by lia.
           subst j.
           rewrite app_Znth2 by lia.
           rewrite Hlabels.
           replace (i - i) with 0 by lia.
           simpl.
           destruct (Z.eqb i h) eqn:Hih.
           ++ apply Z.eqb_eq in Hih.
              subst h.
              unfold IsFirstIncident in Hincident.
              destruct Hincident as [[_ Hhi] _].
              rewrite Zlength_sublist0 in Hhi by lia.
              lia.
           ++ unfold Incident in Hnonincident.
              destruct (Z.eqb (fst (Znth i e (0, 0))) 0) eqn:Hfst.
              ** apply Z.eqb_eq in Hfst.
                 exfalso.
                 apply Hnonincident.
                 left.
                 exact Hfst.
              ** destruct (Z.eqb (snd (Znth i e (0, 0))) 0) eqn:Hsnd.
                 --- apply Z.eqb_eq in Hsnd.
                     exfalso.
                     apply Hnonincident.
                     right.
                     exact Hsnd.
                 --- reflexivity.
Qed.
Lemma Zrange_length__final_pivot_two_color : forall lo hi,
  lo <= hi -> Z.of_nat (length (Zrange lo hi)) = hi - lo.
Proof.
  intros lo hi Hle.
  assert (Haux : forall k x, length (Zrange_aux x k) = k).
  { induction k as [|k IH]; intros x; simpl; auto. }
  unfold Zrange. rewrite Haux, Z2Nat.id; lia.
Qed.
Lemma underfull_degree_nonneighbor__final_pivot_two_color :
  forall n e pivot,
    0 <= pivot < n ->
    EdgeDegree pivot e < n - 1 ->
    exists q, 0 <= q < n /\ q <> pivot /\
      forall j, 0 <= j < Zlength e ->
        Znth j e (0, 0) <> (pivot, q) /\
        Znth j e (0, 0) <> (q, pivot).
Proof.
  intros n e pivot Hpiv Hdeg.
  set (incidentb := fun (x : Z) (p : Z * Z) =>
    orb (Z.eqb (fst p) x) (Z.eqb (snd p) x)).
  set (other_endpoint := fun (x : Z) (p : Z * Z) =>
    if Z.eqb (fst p) x then snd p else fst p).
  set (inc := filter (incidentb pivot) e).
  set (neigh := map (other_endpoint pivot) inc).
  destruct (classic (exists q, 0 <= q < n /\ q <> pivot /\
      forall j, 0 <= j < Zlength e ->
        Znth j e (0, 0) <> (pivot, q) /\
        Znth j e (0, 0) <> (q, pivot))) as [Hex | Hnone].
  { exact Hex. }
  exfalso.
  assert (Hall : forall q, 0 <= q < n -> q <> pivot -> In q neigh).
  {
    intros q Hq Hqp.
    assert (Hexedge : exists j, 0 <= j < Zlength e /\
        (Znth j e (0, 0) = (pivot, q) \/ Znth j e (0, 0) = (q, pivot))).
    {
      destruct (classic (exists j, 0 <= j < Zlength e /\
          (Znth j e (0, 0) = (pivot, q) \/ Znth j e (0, 0) = (q, pivot))))
        as [Hexedge | Hnoedge]; [exact Hexedge |].
      exfalso. apply Hnone. exists q. split; [exact Hq|]. split; [exact Hqp|].
      intros j Hj. split; intro Heq; apply Hnoedge; exists j; split; auto.
    }
    destruct Hexedge as [j [Hj [Heq | Heq]]].
    - unfold neigh, inc.
      apply in_map_iff. exists (Znth j e (0, 0)). split.
      + rewrite Heq. unfold other_endpoint. simpl.
        rewrite Z.eqb_refl. reflexivity.
      + apply filter_In. split.
        * apply Znth_In_Zlength. exact Hj.
        * unfold incidentb. rewrite Heq. simpl.
          rewrite Z.eqb_refl. reflexivity.
    - unfold neigh, inc.
      apply in_map_iff. exists (Znth j e (0, 0)). split.
      + rewrite Heq. unfold other_endpoint. simpl.
        destruct (Z.eqb q pivot) eqn:Eqp.
        * apply Z.eqb_eq in Eqp. contradiction.
        * reflexivity.
      + apply filter_In. split.
        * apply Znth_In_Zlength. exact Hj.
        * unfold incidentb. rewrite Heq. simpl.
          rewrite Z.eqb_refl, Bool.orb_true_r. reflexivity.
  }
  assert (Hincl : incl (Zrange 0 n) (pivot :: neigh)).
  {
    intros q Hqin.
    apply In_Zrange in Hqin.
    destruct (Z.eq_dec q pivot) as [-> | Hneq].
    - left. reflexivity.
    - right. apply Hall; lia.
  }
  pose proof (NoDup_incl_length (NoDup_Zrange 0 n) Hincl) as Hlen.
  assert (Hrange : Z.of_nat (length (Zrange 0 n)) = n) by
    (rewrite Zrange_length__final_pivot_two_color; lia).
  assert (Hneigh : Z.of_nat (length neigh) = EdgeDegree pivot e).
  {
    unfold neigh, inc, EdgeDegree, incidentb.
    rewrite length_map. reflexivity.
  }
  change (length (Zrange 0 n) <= S (length neigh))%nat in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Nat2Z.inj_succ, Hrange, Hneigh in Hlen.
  lia.
Qed.
Lemma reachable_mono__final_pivot_two_color :
  forall (g1 g2 : ZGraph) x y,
    (forall a b, step g1 a b -> step g2 a b) ->
    reachable g1 x y -> reachable g2 x y.
Proof.
  intros g1 g2 x y Hstep Hreach.
  unfold reachable, clos_refl_trans in *.
  destruct Hreach as [k Hreach]. exists k.
  revert x y Hreach.
  induction k as [|k IH]; intros x y Hreach; simpl in *.
  - exact Hreach.
  - destruct Hreach as [z [Hfirst Hrest]].
    exists z. split.
    + apply Hstep. exact Hfirst.
    + apply IH. exact Hrest.
Qed.
Lemma pivot_coloring_valid__final_pivot_two_color :
  forall n e degrees pivot labels,
    Pre n e ->
    DegreePrefix n e (Zlength e) degrees ->
    0 <= pivot < n ->
    PivotChoice n degrees pivot ->
    PivotColorPrefix e pivot (Zlength e) labels ->
    ValidTrainPlan n e 2 labels.
Proof.
  intros n e degrees pivot labels Hpre Hdegprefix Hpivot Hchoice Hcolor.
  destruct Hpre as [Hn [_ [_ [Hedges [_ Hconnected]]]]].
  destruct Hdegprefix as [Hdegrees Hdegree].
  destruct Hcolor as [Hlabels Hlabel].
  assert (Hunder : EdgeDegree pivot e < n - 1).
  {
    destruct Hchoice as [[_ [Hunder _]] | [Hpminus _]]; [|lia].
    specialize (Hdegree pivot Hpivot).
    rewrite (sublist_self e (Zlength e)) in Hdegree by reflexivity.
    lia.
  }
  destruct (underfull_degree_nonneighbor__final_pivot_two_color
      n e pivot Hpivot Hunder) as [q [Hq [Hqp Hnonedge]]].
  assert (Hlabel12 : forall j, 0 <= j < Zlength e ->
      Znth j labels 0 = 1 \/ Znth j labels 0 = 2).
  {
    intros j Hj. specialize (Hlabel j Hj).
    destruct (orb (Z.eqb (fst (Znth j e (0, 0))) pivot)
                  (Z.eqb (snd (Znth j e (0, 0))) pivot)); auto.
  }
  unfold ValidTrainPlan.
  split; [lia|].
  split; [exact Hlabels|].
  split.
  - apply Forall_forall. intros x Hxin.
    apply In_nth with (d := 0) in Hxin as [k [Hk Hnth]].
    specialize (Hlabel12 (Z.of_nat k)).
    assert (Hkz : 0 <= Z.of_nat k < Zlength labels) by
      (rewrite Zlength_correct; lia).
    rewrite Hlabels in Hkz.
    specialize (Hlabel12 Hkz).
    unfold Znth in Hlabel12. rewrite Nat2Z.id in Hlabel12.
    rewrite Hnth in Hlabel12. lia.
  - split.
    { intros c Hc.
    assert (Hcases : c = 1 \/ c = 2) by lia.
    destruct Hcases as [-> | ->].
    - unfold CompanyConnected. intro Hconn.
      specialize (Hconn q pivot Hq Hpivot).
      apply reachable_1n in Hconn as [[z [Hstep _]] | Heq]; [|exfalso; apply Hqp; exact Heq].
      unfold step in Hstep. destruct Hstep as [xy Hstep].
      unfold zstep_aux in Hstep. simpl in Hstep.
      destruct Hstep as [_ [_ [Hze _]]].
      destruct Hze as [j [Hj [[He | He] Hcolor1]]].
      + simpl in Hcolor1. destruct Hcolor1 as [Hlab | []].
        specialize (Hlabel j Hj). rewrite <- Hlab in Hlabel.
        destruct (orb (Z.eqb (fst (Znth j e (0, 0))) pivot)
                      (Z.eqb (snd (Znth j e (0, 0))) pivot)) eqn:Hinc; [|lia].
        apply Bool.orb_true_iff in Hinc as [Hinc' | Hinc'].
        all: apply Z.eqb_eq in Hinc'.
        all: rewrite He in Hinc'; simpl in Hinc'.
        all: assert (Hz : z = pivot) by lia; subst z;
          specialize (Hnonedge j Hj); tauto.
      + simpl in Hcolor1. destruct Hcolor1 as [Hlab | []].
        specialize (Hlabel j Hj). rewrite <- Hlab in Hlabel.
        destruct (orb (Z.eqb (fst (Znth j e (0, 0))) pivot)
                      (Z.eqb (snd (Znth j e (0, 0))) pivot)) eqn:Hinc; [|lia].
        apply Bool.orb_true_iff in Hinc as [Hinc' | Hinc'].
        all: apply Z.eqb_eq in Hinc'.
        all: rewrite He in Hinc'; simpl in Hinc'.
        all: assert (Hz : z = pivot) by lia; subst z;
          specialize (Hnonedge j Hj); tauto.
    - unfold CompanyConnected. intro Hconn.
      set (r := if Z.eqb pivot 0 then 1 else 0).
      assert (Hr : 0 <= r < n /\ r <> pivot).
      {
        unfold r. destruct (Z.eqb pivot 0) eqn:Hp0.
        - apply Z.eqb_eq in Hp0. subst pivot. lia.
        - apply Z.eqb_neq in Hp0. lia.
      }
      destruct Hr as [Hr Hrp].
      specialize (Hconn pivot r Hpivot Hr).
      apply reachable_1n in Hconn as [[z [Hstep _]] | Heq];
        [|exfalso; apply Hrp; symmetry; exact Heq].
      unfold step in Hstep. destruct Hstep as [xy Hstep].
      unfold zstep_aux in Hstep. simpl in Hstep.
      destruct Hstep as [_ [_ [Hze _]]].
      destruct Hze as [j [Hj [[He | He] Hcolor2]]].
      + simpl in Hcolor2. destruct Hcolor2 as [Hlab | []].
        specialize (Hlabel j Hj). rewrite <- Hlab in Hlabel.
        rewrite He in Hlabel. simpl in Hlabel. rewrite Z.eqb_refl in Hlabel.
        simpl in Hlabel.
        lia.
      + simpl in Hcolor2. destruct Hcolor2 as [Hlab | []].
        specialize (Hlabel j Hj). rewrite <- Hlab in Hlabel.
        rewrite He in Hlabel. simpl in Hlabel. rewrite Z.eqb_refl, Bool.orb_true_r in Hlabel.
        simpl in Hlabel.
        lia. }
    { intros c d Hc Hd Hcd.
    unfold CompanyConnected. intros u v Hu Hv.
    specialize (Hconnected u v Hu Hv).
    eapply reachable_mono__final_pivot_two_color; [|exact Hconnected].
    intros a b Hstep.
    unfold step in *. destruct Hstep as [xy Hstep].
    exists xy. unfold zstep_aux in *. simpl in *.
    destruct Hstep as [Ha [Hb [Hze [Hva Hvb]]]].
    split; [exact Ha|]. split; [exact Hb|]. split.
    - destruct Hze as [j [Hj He]].
      exists j. split; [exact Hj|]. split; [exact He|].
      specialize (Hlabel12 j Hj).
      assert (Hcd_cases : (c = 1 /\ d = 2) \/ (c = 2 /\ d = 1)) by lia.
      destruct Hcd_cases as [[-> ->] | [-> ->]]; simpl.
      + destruct Hlabel12 as [Hlab | Hlab].
        * left. symmetry. exact Hlab.
        * right. left. symmetry. exact Hlab.
      + destruct Hlabel12 as [Hlab | Hlab].
        * right. left. symmetry. exact Hlab.
        * left. symmetry. exact Hlab.
    - split; assumption. }
Qed.
Lemma incident_bool_iff__final_complete_three_color :
  forall x p,
    orb (Z.eqb (fst p) x) (Z.eqb (snd p) x) = true <-> Incident x p.
Proof.
  intros x [a b].
  unfold Incident; simpl.
  rewrite Bool.orb_true_iff, !Z.eqb_eq.
  tauto.
Qed.
Lemma canonical_swap__final_complete_three_color :
  forall a b, CanonicalEdge (a, b) = CanonicalEdge (b, a).
Proof.
  intros a b.
  unfold CanonicalEdge; simpl.
  destruct (Z.leb a b) eqn:Hab, (Z.leb b a) eqn:Hba.
  - apply Z.leb_le in Hab. apply Z.leb_le in Hba. f_equal; lia.
  - reflexivity.
  - reflexivity.
  - apply Z.leb_gt in Hab. apply Z.leb_gt in Hba. lia.
Qed.
Lemma canonical_incident_other__final_complete_three_color :
  forall x p q,
    Incident x p -> Incident x q ->
    fst p <> snd p -> fst q <> snd q ->
    (if Z.eq_dec (fst p) x then snd p else fst p) =
    (if Z.eq_dec (fst q) x then snd q else fst q) ->
    CanonicalEdge p = CanonicalEdge q.
Proof.
  intros x [a b] [c d].
  unfold Incident; simpl.
  intros [Ha | Hb] [Hc | Hd] Hneqp Hneqq Hother.
  - subst a c. destruct (Z.eq_dec x x); [|contradiction].
    simpl in Hother. subst d. reflexivity.
  - subst a d. destruct (Z.eq_dec x x); [|contradiction].
    destruct (Z.eq_dec c x); [congruence|].
    simpl in Hother. subst c.
    apply canonical_swap__final_complete_three_color.
  - subst b c. destruct (Z.eq_dec a x); [congruence|].
    destruct (Z.eq_dec x x); [|contradiction].
    simpl in Hother. subst d.
    symmetry. apply canonical_swap__final_complete_three_color.
  - subst b d. destruct (Z.eq_dec a x); [congruence|].
    destruct (Z.eq_dec c x); [congruence|].
    simpl in Hother. subst c. reflexivity.
Qed.
Lemma nodup_incident_neighbors__final_complete_three_color :
  forall x e,
    Forall (fun p => fst p <> snd p) e ->
    NoDup (map CanonicalEdge e) ->
    NoDup
      (map (fun p => if Z.eq_dec (fst p) x then snd p else fst p)
        (filter
          (fun p => orb (Z.eqb (fst p) x) (Z.eqb (snd p) x)) e)).
Proof.
  intros x e Hproper Hnodup.
  induction e as [|p es IH]; simpl.
  - constructor.
  - inversion Hproper as [|? ? Hp Hproper']; subst.
    inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    destruct (orb (Z.eqb (fst p) x) (Z.eqb (snd p) x)) eqn:Hpinc.
    + simpl. constructor.
      * intro Hin.
        apply in_map_iff in Hin.
        destruct Hin as [q [Hother Hq]].
        apply filter_In in Hq as [Hqes Hqinc].
        apply Hnotin.
        apply in_map_iff. exists q. split; [|exact Hqes].
        assert (Hqproper : fst q <> snd q).
        { apply Forall_forall with (x := q) in Hproper'; auto. }
        symmetry. eapply canonical_incident_other__final_complete_three_color; eauto.
        -- apply incident_bool_iff__final_complete_three_color; exact Hpinc.
        -- apply incident_bool_iff__final_complete_three_color; exact Hqinc.
      * apply IH; auto.
    + apply IH; auto.
Qed.
Lemma nodup_map_Z_to_nat__final_complete_three_color :
  forall xs,
    Forall (fun x => 0 <= x) xs ->
    NoDup xs ->
    NoDup (map Z.to_nat xs).
Proof.
  intros xs Hnonneg Hnodup.
  induction xs as [|x xs IH]; simpl.
  - constructor.
  - inversion Hnonneg as [|? ? Hx Hxs]; subst.
    inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Heq Hin]].
      assert (Hy : 0 <= y).
      { apply Forall_forall with (x := y) in Hxs; auto. }
      apply Hnotin.
      apply Z2Nat.inj in Heq; auto. congruence.
    + apply IH; auto.
Qed.
Lemma nodup_range_length__final_complete_three_color :
  forall limit xs,
    0 <= limit ->
    NoDup xs ->
    Forall (fun x => 0 <= x < limit) xs ->
    Zlength xs <= limit.
Proof.
  intros limit xs Hlimit Hnodup Hrange.
  assert (Hnonneg : Forall (fun x => 0 <= x) xs).
  {
    apply Forall_forall. intros x Hx.
    apply Forall_forall with (x := x) in Hrange; auto. lia.
  }
  pose proof
    (nodup_map_Z_to_nat__final_complete_three_color xs Hnonneg Hnodup)
    as Hmap.
  assert (Hincl : incl (map Z.to_nat xs) (seq 0 (Z.to_nat limit))).
  {
    intros k Hk.
    apply in_map_iff in Hk as [x [Hx Hinx]]. subst k.
    apply in_seq.
    apply Forall_forall with (x := x) in Hrange; auto.
    lia.
  }
  pose proof (NoDup_incl_length Hmap Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  rewrite Zlength_correct.
  exact Hlen.
Qed.
Lemma input_edge_of_member__final_complete_three_color :
  forall n e p u v,
    In p e ->
    (p = (u, v) \/ p = (v, u)) ->
    ze (InputGraph n e) u v.
Proof.
  intros n e p u v Hin Hshape.
  unfold InputGraph; simpl.
  apply In_nth with (d := (0, 0)) in Hin.
  destruct Hin as [k [Hk Hnth]].
  exists (Z.of_nat k).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. rewrite Hnth. exact Hshape.
Qed.
Lemma no_pivot_complete__final_complete_three_color :
  forall n e degrees,
    Pre n e ->
    DegreePrefix n e (Zlength e) degrees ->
    PivotChoice n degrees (-1) ->
    forall u v,
      0 <= u < n -> 0 <= v < n -> u <> v ->
      ze (InputGraph n e) u v.
Proof.
  intros n e degrees Hpre Hdegrees Hpivot u v Hu Hv Huv.
  destruct Hpre as
    [[Hn3 Hn50] [Hmlo [Hmhi [Hedges [Hcanon Hconnected]]]]].
  destruct Hdegrees as [Hdegrees_len Hdegree].
  destruct Hpivot as [[Hpivot_range _] | [Hpivot_eq Hprefix]]; [lia|].
  assert (Hdeglo : n - 1 <= EdgeDegree u e).
  {
    specialize (Hprefix u Hu).
    specialize (Hdegree u Hu).
    pose proof (sublist_app_exact1 e (@nil (Z * Z))) as Hsub.
    rewrite app_nil_r in Hsub.
    rewrite Hsub in Hdegree.
    lia.
  }
  set (inc :=
    filter (fun p => orb (Z.eqb (fst p) u) (Z.eqb (snd p) u)) e).
  set (neighbors :=
    map (fun p => if Z.eq_dec (fst p) u then snd p else fst p) inc).
  destruct (classic (ze (InputGraph n e) u v)) as [Hedge | Hnoedge]; auto.
  assert (Hproper : Forall (fun p => fst p <> snd p) e).
  {
    apply Forall_forall. intros p Hp.
    apply Forall_forall with (x := p) in Hedges; auto. tauto.
  }
  assert (Hneighbors_nodup : NoDup neighbors).
  {
    unfold neighbors, inc.
    apply nodup_incident_neighbors__final_complete_three_color; auto.
  }
  assert (Hneighbors_range :
    Forall (fun z => 0 <= z < n /\ z <> u /\ z <> v) neighbors).
  {
    apply Forall_forall.
    intros z Hz.
    unfold neighbors in Hz.
    apply in_map_iff in Hz.
    destruct Hz as [p [Hz Hpinc]]. subst z.
    unfold inc in Hpinc.
    apply filter_In in Hpinc as [Hpin Htest].
    apply incident_bool_iff__final_complete_three_color in Htest.
    assert (Hpvalid :
      0 <= fst p < n /\ 0 <= snd p < n /\ fst p <> snd p).
    { apply Forall_forall with (x := p) in Hedges; auto. }
    destruct Hpvalid as [Hpfst [Hpsnd Hpneq]].
    destruct Htest as [Hfst | Hsnd].
    - subst u. destruct (Z.eq_dec (fst p) (fst p)); [|contradiction].
      simpl. split; [exact Hpsnd|]. split; [congruence|].
      intro Hpv. apply Hnoedge.
      eapply input_edge_of_member__final_complete_three_color; [exact Hpin|].
      left. destruct p as [a b]; simpl in *; subst. reflexivity.
    - subst u. destruct (Z.eq_dec (fst p) (snd p)); [congruence|].
      simpl. split; [exact Hpfst|]. split; [congruence|].
      intro Hpv. apply Hnoedge.
      eapply input_edge_of_member__final_complete_three_color; [exact Hpin|].
      right. destruct p as [a b]; simpl in *; subst. reflexivity.
  }
  assert (Hbig_nodup : NoDup (u :: v :: neighbors)).
  {
    constructor.
    - simpl. intros [Heq | Hin]; [congruence|].
      apply Forall_forall with (x := u) in Hneighbors_range; auto. tauto.
    - constructor.
      + intro Hin.
        apply Forall_forall with (x := v) in Hneighbors_range; auto. tauto.
      + exact Hneighbors_nodup.
  }
  assert (Hbig_range : Forall (fun z => 0 <= z < n) (u :: v :: neighbors)).
  {
    constructor; [exact Hu|]. constructor; [exact Hv|].
    apply Forall_forall. intros z Hz.
    apply Forall_forall with (x := z) in Hneighbors_range; auto. tauto.
  }
  pose proof
    (nodup_range_length__final_complete_three_color n (u :: v :: neighbors)
      (ltac:(lia)) Hbig_nodup Hbig_range) as Hlen.
  rewrite Zlength_cons, Zlength_cons in Hlen.
  assert (Hneighbors_len : Zlength neighbors = EdgeDegree u e).
  {
    unfold neighbors, inc, EdgeDegree.
    rewrite Zlength_correct, length_map. reflexivity.
  }
  lia.
Qed.
Lemma input_edge_index_unique__final_complete_three_color :
  forall e j k,
    NoDup (map CanonicalEdge e) ->
    0 <= j < Zlength e ->
    0 <= k < Zlength e ->
    CanonicalEdge (Znth j e (0, 0)) =
      CanonicalEdge (Znth k e (0, 0)) ->
    j = k.
Proof.
  intros e j k Hnodup Hj Hk Heq.
  apply Z2Nat.inj; [lia|lia|].
  apply (proj1 (NoDup_nth (map CanonicalEdge e) (CanonicalEdge (0, 0)))
    Hnodup).
  - rewrite length_map, <- (Nat2Z.id (length e)).
    apply Z2Nat.inj_lt; rewrite Zlength_correct in Hj; lia.
  - rewrite length_map, <- (Nat2Z.id (length e)).
    apply Z2Nat.inj_lt; rewrite Zlength_correct in Hk; lia.
  - unfold Znth in Heq.
    rewrite !map_nth. exact Heq.
Qed.
Lemma company_step_at_index__final_complete_three_color :
  forall n e labels cs j u v,
    0 <= u < n -> 0 <= v < n ->
    0 <= j < Zlength e ->
    (Znth j e (0, 0) = (u, v) \/ Znth j e (0, 0) = (v, u)) ->
    In (Znth j labels 0) cs ->
    step (CompanyGraph n cs e labels) u v.
Proof.
  intros n e labels cs j u v Hu Hv Hj Hedge Hlabel.
  unfold step.
  exists (u, v).
  unfold zstep_aux; simpl.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - unfold CompanyGraph; simpl.
    exists j. tauto.
  - split; [exact Hu|exact Hv].
Qed.
Lemma company_connected_hub__final_complete_three_color :
  forall n e labels cs hub,
    0 <= hub < n ->
    (forall x,
      0 <= x < n -> x <> hub ->
      step (CompanyGraph n cs e labels) x hub) ->
    CompanyConnected n cs e labels.
Proof.
  intros n e labels cs hub Hhub Hstep u v Hu Hv.
  destruct (Z.eq_dec u v) as [-> | Huv].
  - unfold reachable. reflexivity.
  - assert (Huh : reachable (CompanyGraph n cs e labels) u hub).
    {
      destruct (Z.eq_dec u hub) as [-> | Hneq].
      - unfold reachable. reflexivity.
      - apply step_rt. apply Hstep; auto.
    }
    assert (Hhv : reachable (CompanyGraph n cs e labels) hub v).
    {
      destruct (Z.eq_dec v hub) as [-> | Hneq].
      - unfold reachable. reflexivity.
      - apply step_rt.
        pose proof (Hstep v Hv Hneq) as Hvh.
        destruct Hvh as [edge Haux].
        exists (hub, v).
        unfold zstep_aux in Haux |- *; simpl in Haux |- *.
        destruct Haux as [_ [_ [Hze [Hvx Hvh]]]].
        split; [reflexivity|]. split; [reflexivity|]. split.
        + unfold CompanyGraph in Hze |- *; simpl in Hze |- *.
          destruct Hze as [j [Hj [Hshape Hlabel]]].
          exists j. split; [exact Hj|]. split; [|exact Hlabel].
          destruct Hshape; [right|left]; auto.
        + split; [exact Hhub|exact Hv].
    }
    eapply reachable_trans; eauto.
Qed.
Lemma company_isolated_not_connected__final_complete_three_color :
  forall n e labels c x y,
    0 <= x < n -> 0 <= y < n -> x <> y ->
    (forall z, ~ ze (CompanyGraph n (c :: nil) e labels) x z) ->
    ~ CompanyConnected n (c :: nil) e labels.
Proof.
  intros n e labels c x y Hx Hy Hxy Hisolated Hconnected.
  specialize (Hconnected x y Hx Hy).
  apply reachable_1n in Hconnected.
  destruct Hconnected as [[z [Hstep _]] | Heq]; [|congruence].
  destruct Hstep as [edge Haux].
  unfold zstep_aux in Haux; simpl in Haux.
  destruct Haux as [_ [_ [Hze _]]].
  exact (Hisolated z Hze).
Qed.
Lemma complete_coloring_valid__final_complete_three_color :
  forall n e degrees first labels,
    Pre n e ->
    DegreePrefix n e (Zlength e) degrees ->
    PivotChoice n degrees (-1) ->
    CompleteColorPrefix e (Zlength e) first labels ->
    ValidTrainPlan n e 3 labels.
Proof.
  intros n e degrees first labels Hpre Hdegrees Hpivot Hcolors.
  pose proof
    (no_pivot_complete__final_complete_three_color
      n e degrees Hpre Hdegrees Hpivot) as Hcomplete.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as
    [[Hn3 Hn50] [Hmlo [Hmhi [Hedges [Hcanon Hconnected]]]]].
  unfold CompleteColorPrefix in Hcolors.
  destruct Hcolors as [Hlabels_len Hcolor_case].
  pose proof (sublist_app_exact1 e (@nil (Z * Z))) as Hsub.
  rewrite app_nil_r in Hsub.
  destruct Hcolor_case as [[Hfirst Hnone] | [Hfirst [h [Hfirst_edge Hformula]]]].
  - subst first.
    specialize (Hcomplete 0 1 (ltac:(lia)) (ltac:(lia)) (ltac:(lia))).
    unfold InputGraph in Hcomplete; simpl in Hcomplete.
    destruct Hcomplete as [j [Hj Hshape]].
    specialize (Hnone j Hj).
    destruct Hnone as [Hnotincident _].
    exfalso. apply Hnotincident.
    unfold Incident. destruct Hshape as [Hshape | Hshape]; rewrite Hshape; simpl; auto.
  - subst first.
    rewrite Hsub in Hfirst_edge.
    unfold IsFirstIncident in Hfirst_edge.
    destruct Hfirst_edge as [Hh [Hhincident Hbefore]].
    assert (Hedge_at : forall j,
      0 <= j < Zlength e ->
      0 <= fst (Znth j e (0, 0)) < n /\
      0 <= snd (Znth j e (0, 0)) < n /\
      fst (Znth j e (0, 0)) <> snd (Znth j e (0, 0))).
    {
      intros j Hj.
      apply Forall_forall with (x := Znth j e (0, 0)) in Hedges.
      - exact Hedges.
      - unfold Znth. apply nth_In.
        rewrite <- (Nat2Z.id (length e)).
        apply Z2Nat.inj_lt; rewrite Zlength_correct in Hj; lia.
    }
    remember (Znth h e (0, 0)) as eh eqn:Heh.
    pose proof (Hedge_at h Hh) as Hehvalid.
    rewrite <- Heh in Hehvalid.
    set (w := if Z.eq_dec (fst eh) 0 then snd eh else fst eh).
    assert (Hhwshape : eh = (0, w) \/ eh = (w, 0)).
    {
      destruct eh as [a b].
      unfold Incident in Hhincident; simpl in Hhincident.
      destruct Hehvalid as [_ [_ Hab]]. simpl in Hab.
      unfold w; simpl.
      destruct Hhincident as [Ha | Hb].
      - subst a. destruct (Z.eq_dec 0 0); [|contradiction].
        left. reflexivity.
      - subst b. destruct (Z.eq_dec a 0); [congruence|].
        right. reflexivity.
    }
    assert (Hw : 0 <= w < n).
    {
      destruct Hhwshape as [Hshape | Hshape];
        rewrite Hshape in Hehvalid; simpl in Hehvalid; tauto.
    }
    assert (Hw0 : w <> 0).
    {
      unfold w. destruct eh as [a b]. simpl in Hehvalid |- *.
      destruct Hehvalid as [Ha [Hb Hab]].
      destruct (Z.eq_dec a 0); congruence.
    }
    set (t := if Z.eq_dec w 1 then 2 else 1).
    assert (Ht : 0 <= t < n).
    { unfold t. destruct (Z.eq_dec w 1); lia. }
    assert (Ht0 : t <> 0).
    { unfold t. destruct (Z.eq_dec w 1); lia. }
    assert (Htw : t <> w).
    { unfold t. destruct (Z.eq_dec w 1); lia. }
    assert (Hlabel_cases : forall j,
      0 <= j < Zlength e ->
      (Incident 0 (Znth j e (0, 0)) ->
        (j = h -> Znth j labels 0 = 1) /\
        (j <> h -> Znth j labels 0 = 2)) /\
      (~ Incident 0 (Znth j e (0, 0)) -> Znth j labels 0 = 3)).
    {
      intros j Hj.
      specialize (Hformula j Hj).
      split.
      - intro Hincident. split.
        + intro Hjh. subst j. rewrite Z.eqb_refl in Hformula. exact Hformula.
        + intro Hjneq.
          apply Z.eqb_neq in Hjneq.
          rewrite Hjneq in Hformula.
          apply incident_bool_iff__final_complete_three_color in Hincident.
          rewrite Hincident in Hformula. exact Hformula.
      - intro Hnotincident.
        assert (Hjneq : j <> h).
        { intro Hjh. subst j. rewrite <- Heh in Hnotincident. contradiction. }
        apply Z.eqb_neq in Hjneq.
        rewrite Hjneq in Hformula.
        destruct (orb (Z.eqb (fst (Znth j e (0, 0))) 0)
          (Z.eqb (snd (Znth j e (0, 0))) 0)) eqn:Htest.
        + apply incident_bool_iff__final_complete_three_color in Htest. contradiction.
        + exact Hformula.
    }
    assert (Hlabels_range : Forall (fun z => 1 <= z <= 3) labels).
    {
      apply Forall_forall. intros z Hz.
      apply In_nth with (d := 0) in Hz.
      destruct Hz as [k [Hk Hkval]].
      set (j := Z.of_nat k).
      assert (Hj : 0 <= j < Zlength labels).
      { unfold j. rewrite Zlength_correct. lia. }
      assert (Hzj : Znth j labels 0 = z).
      { unfold j, Znth. rewrite Nat2Z.id. exact Hkval. }
      rewrite Hlabels_len in Hj.
      specialize (Hlabel_cases j Hj).
      destruct Hlabel_cases as [Hinc Hnon].
      destruct (classic (Incident 0 (Znth j e (0, 0)))) as [Hi | Hni].
      - specialize (Hinc Hi). destruct Hinc as [Heq Hneq].
        destruct (Z.eq_dec j h); [specialize (Heq e0)|specialize (Hneq n0)]; lia.
      - specialize (Hnon Hni). lia.
    }
    assert (HC12 : forall cs,
      In 1 cs -> In 2 cs -> CompanyConnected n cs e labels).
    {
      intros cs H1 H2.
      apply company_connected_hub__final_complete_three_color with (hub := 0);
        [lia|].
      intros x Hx Hx0.
      specialize (Hcomplete x 0 Hx (ltac:(lia)) Hx0).
      unfold InputGraph in Hcomplete; simpl in Hcomplete.
      destruct Hcomplete as [j [Hj Hshape]].
      eapply company_step_at_index__final_complete_three_color with (j := j);
        [exact Hx|lia|exact Hj|exact Hshape|].
      assert (Hi : Incident 0 (Znth j e (0, 0))).
      { unfold Incident. destruct Hshape; rewrite H; simpl; auto. }
      specialize (Hlabel_cases j Hj).
      destruct Hlabel_cases as [Hinc _]. specialize (Hinc Hi).
      destruct (Z.eq_dec j h) as [Heq | Hneq].
      - rewrite (proj1 Hinc Heq). exact H1.
      - rewrite (proj2 Hinc Hneq). exact H2.
    }
    assert (HC13 : forall cs,
      In 1 cs -> In 3 cs -> CompanyConnected n cs e labels).
    {
      intros cs H1 H3.
      apply company_connected_hub__final_complete_three_color with (hub := w);
        [exact Hw|].
      intros x Hx Hxw.
      destruct (Z.eq_dec x 0) as [-> | Hx0].
      - eapply company_step_at_index__final_complete_three_color with (j := h);
          [lia|exact Hw|exact Hh| |].
        + rewrite <- Heh. exact Hhwshape.
        + specialize (Hlabel_cases h Hh).
          destruct Hlabel_cases as [Hinc _].
          assert (Hhi : Incident 0 (Znth h e (0, 0))).
          { rewrite <- Heh. exact Hhincident. }
          specialize (Hinc Hhi).
          rewrite (proj1 Hinc eq_refl). exact H1.
      - specialize (Hcomplete x w Hx Hw Hxw).
        unfold InputGraph in Hcomplete; simpl in Hcomplete.
        destruct Hcomplete as [j [Hj Hshape]].
        eapply company_step_at_index__final_complete_three_color with (j := j);
          [exact Hx|exact Hw|exact Hj|exact Hshape|].
        specialize (Hlabel_cases j Hj).
        assert (Hni : ~ Incident 0 (Znth j e (0, 0))).
        { unfold Incident. destruct Hshape; rewrite H; simpl; tauto. }
        rewrite (proj2 Hlabel_cases Hni). exact H3.
    }
    assert (HC23 : forall cs,
      In 2 cs -> In 3 cs -> CompanyConnected n cs e labels).
    {
      intros cs H2 H3.
      apply company_connected_hub__final_complete_three_color with (hub := t);
        [exact Ht|].
      intros x Hx Hxt.
      destruct (Z.eq_dec x 0) as [-> | Hx0].
      - specialize (Hcomplete 0 t (ltac:(lia)) Ht (ltac:(lia))).
        unfold InputGraph in Hcomplete; simpl in Hcomplete.
        destruct Hcomplete as [j [Hj Hshape]].
        eapply company_step_at_index__final_complete_three_color with (j := j);
          [lia|exact Ht|exact Hj|exact Hshape|].
        assert (Hi : Incident 0 (Znth j e (0, 0))).
        { unfold Incident. destruct Hshape; rewrite H; simpl; auto. }
        specialize (Hlabel_cases j Hj).
        destruct Hlabel_cases as [Hinc _]. specialize (Hinc Hi).
        assert (Hjh : j <> h).
        {
          intro Heq. subst j.
          rewrite <- Heh in Hshape.
          destruct Hshape, Hhwshape; congruence.
        }
        rewrite (proj2 Hinc Hjh). exact H2.
      - specialize (Hcomplete x t Hx Ht Hxt).
        unfold InputGraph in Hcomplete; simpl in Hcomplete.
        destruct Hcomplete as [j [Hj Hshape]].
        eapply company_step_at_index__final_complete_three_color with (j := j);
          [exact Hx|exact Ht|exact Hj|exact Hshape|].
        specialize (Hlabel_cases j Hj).
        assert (Hni : ~ Incident 0 (Znth j e (0, 0))).
        { unfold Incident. destruct Hshape; rewrite H; simpl; tauto. }
        rewrite (proj2 Hlabel_cases Hni). exact H3.
    }
    assert (HNC1 : ~ CompanyConnected n (1 :: nil) e labels).
    {
      eapply company_isolated_not_connected__final_complete_three_color
        with (x := t) (y := 0); eauto; [lia|].
      intros z Hze.
      unfold CompanyGraph in Hze; simpl in Hze.
      destruct Hze as [j [Hj [Hshape Hlab]]].
      simpl in Hlab. destruct Hlab as [Hlab | []].
      specialize (Hlabel_cases j Hj).
      destruct (classic (Incident 0 (Znth j e (0, 0)))) as [Hi | Hni].
      - destruct (proj1 Hlabel_cases Hi) as [Heq Hneq].
        destruct (Z.eq_dec j h) as [Hjh | Hjh].
        + subst j. rewrite <- Heh in Hshape.
          destruct Hshape, Hhwshape; congruence.
        + specialize (Hneq Hjh). congruence.
      - specialize (proj2 Hlabel_cases Hni). congruence.
    }
    assert (HNC2 : ~ CompanyConnected n (2 :: nil) e labels).
    {
      eapply company_isolated_not_connected__final_complete_three_color
        with (x := w) (y := 0).
      - exact Hw.
      - lia.
      - exact Hw0.
      - intros z Hze.
      unfold CompanyGraph in Hze; simpl in Hze.
      destruct Hze as [j [Hj [Hshape Hlab]]].
      simpl in Hlab. destruct Hlab as [Hlab | []].
      specialize (Hlabel_cases j Hj).
      assert (Hi : Incident 0 (Znth j e (0, 0))).
      {
        destruct (classic (Incident 0 (Znth j e (0, 0)))) as [Hi | Hni]; auto.
        specialize (proj2 Hlabel_cases Hni). congruence.
      }
      destruct (proj1 Hlabel_cases Hi) as [Heq Hneq].
      assert (Hjhneq : j <> h).
      { intro Hjh. specialize (Heq Hjh). congruence. }
      specialize (Hneq Hjhneq).
      assert (Hjwshape :
        Znth j e (0, 0) = (0, w) \/ Znth j e (0, 0) = (w, 0)).
      {
        destruct (Znth j e (0, 0)) as [a b] eqn:Hab.
        unfold Incident in Hi; simpl in Hi.
        simpl in Hshape.
        destruct Hi as [Ha | Hb], Hshape as [Hs | Hs];
          inversion Hs; subst; try congruence; auto.
      }
      assert (Hcan :
        CanonicalEdge (Znth j e (0, 0)) = CanonicalEdge (Znth h e (0, 0))).
      {
        rewrite <- Heh.
        destruct Hjwshape as [Hjshape | Hjshape],
          Hhwshape as [Hhshape | Hhshape];
          rewrite Hjshape, Hhshape;
          try reflexivity;
          try apply canonical_swap__final_complete_three_color;
          try (symmetry; apply canonical_swap__final_complete_three_color).
      }
      pose proof
        (input_edge_index_unique__final_complete_three_color
          e j h Hcanon Hj Hh Hcan) as Hjh.
      contradiction.
    }
    assert (HNC3 : ~ CompanyConnected n (3 :: nil) e labels).
    {
      eapply company_isolated_not_connected__final_complete_three_color
        with (x := 0) (y := 1).
      - lia.
      - lia.
      - lia.
      - intros z Hze.
      unfold CompanyGraph in Hze; simpl in Hze.
      destruct Hze as [j [Hj [Hshape Hlab]]].
      simpl in Hlab. destruct Hlab as [Hlab | []].
      assert (Hi : Incident 0 (Znth j e (0, 0))).
      { unfold Incident. destruct Hshape; rewrite H; simpl; auto. }
      specialize (Hlabel_cases j Hj).
      destruct (proj1 Hlabel_cases Hi) as [Heq Hneq].
      destruct (Z.eq_dec j h) as [Hjh | Hjh];
        [specialize (Heq Hjh)|specialize (Hneq Hjh)]; congruence.
    }
    unfold ValidTrainPlan.
    repeat split; try lia; try assumption.
    + intros c Hc.
      assert (c = 1 \/ c = 2 \/ c = 3) by lia.
      destruct H as [-> | [-> | ->]]; assumption.
    + intros c d Hc Hd Hcd.
      assert (c = 1 \/ c = 2 \/ c = 3) by lia.
      assert (d = 1 \/ d = 2 \/ d = 3) by lia.
      destruct H as [-> | [-> | ->]], H0 as [-> | [-> | ->]];
        try contradiction.
      * apply HC12; simpl; auto.
      * apply HC13; simpl; auto.
      * apply HC12; simpl; auto.
      * apply HC23; simpl; auto.
      * apply HC13; simpl; auto.
      * apply HC23; simpl; auto.
Qed.
