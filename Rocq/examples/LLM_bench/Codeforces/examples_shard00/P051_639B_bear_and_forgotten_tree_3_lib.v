Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.vpath.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.
Local Open Scope Z_scope.

Definition TreeVertex (n v : Z) : Prop :=
  1 <= v <= n.

Definition RememberedGraph (n : Z) (e : list (Z * Z)) : ZGraph :=
  {| zv := TreeVertex n;
     ze := fun x y => In (x,y) e \/ In (y,x) e |}.

Definition PathInEdges (n : Z) (e : list (Z * Z)) (p : list Z) : Prop :=
  0 < Zlength p /\ NoDup p /\
  valid_vpath (RememberedGraph n e) (Znth 0 p 0) p
    (Znth (Zlength p - 1) p 0).

Definition RootPathInEdges (n : Z) (e : list (Z * Z))
    (p : list Z) : Prop :=
  PathInEdges n e p /\ Znth 0 p 0 = 1.

(** The edge at index [k] gives the sole parent of vertex [k+2].
    Parents have smaller positive numbers, so repeatedly following parents
    is well-founded and reaches the root; all edge endpoints lie in [1,n]. *)
Definition IncreasingParentTree (n : Z) (e : list (Z * Z)) : Prop :=
  Zlength e = n - 1 /\
  forall k, 0 <= k < n - 1 ->
    exists parent,
      Znth k e (0, 0) = (parent, k + 2) /\
      1 <= parent < k + 2.

(** This is the reusable metric consequence of the rooted-tree certificate:
    every simple endpoint path is controlled by the two root arms, each of
    which has length at most [h].  Keeping it explicit in the certificate
    exposes exactly the tree theorem needed by infeasibility proofs. *)
Definition PathsControlledByRootHeight
    (n : Z) (e : list (Z * Z)) (h : Z) : Prop :=
  forall p, PathInEdges n e p -> Zlength p - 1 <= 2 * h.

Definition ValidRememberedTree (n d h : Z) (e : list (Z * Z)) : Prop :=
  IncreasingParentTree n e /\
  (forall v, 1 <= v <= n ->
    exists p, PathInEdges n e p /\
      Znth 0 p 0 = 1 /\ Znth (Zlength p - 1) p 0 = v) /\
  max_value_of_subset Z.le (RootPathInEdges n e)
    (fun p => Zlength p - 1) h /\
  max_value_of_subset Z.le (PathInEdges n e)
    (fun p => Zlength p - 1) d /\
  PathsControlledByRootHeight n e h.

Lemma valid_remembered_tree_diameter_le_twice_height :
  forall n d h e, ValidRememberedTree n d h e -> d <= 2 * h.
Proof.
  intros n d h e Htree.
  destruct Htree as [_ [_ [_ [Hdiam Hcontrolled]]]].
  unfold max_value_of_subset, max_object_of_subset in Hdiam.
  destruct Hdiam as [p [[Hp _] Hlength]].
  specialize (Hcontrolled p Hp).
  rewrite Hlength in Hcontrolled.
  exact Hcontrolled.
Qed.

Definition Pre (n d h : Z) : Prop :=
  2 <= n <= 100000 /\ 1 <= h <= d /\ d <= n - 1.

Definition Feasible (n d h : Z) : Prop :=
  d <= 2 * h /\ (d <> 1 \/ n <= 2).

Definition CanonicalParent (d h k : Z) : Z :=
  if Z_lt_dec k h then k + 1
  else if Z.eq_dec d h then 2
  else if Z.eq_dec k h then 1
  else if Z_lt_dec k d then k + 1
  else 1.

Definition CanonicalEndpoints (d h k u v : Z) : Prop :=
  u = CanonicalParent d h k /\ v = k + 2.

Definition Spec (n d h : Z) (out : option (list (Z * Z))) : Prop :=
  (exists e, out = Some e /\ ValidRememberedTree n d h e) \/
  (out = None /\ forall e, ~ ValidRememberedTree n d h e).

Require Import Coq.micromega.Lia.
Lemma last_in__constructive_returns : forall {A : Type} (l : list A) d,
  l <> nil -> In (last l d) l.
Proof.
  intros A l. induction l as [|x tl IH]; intros d Hne; [contradiction|].
  destruct tl as [|y tl].
  - simpl. left. reflexivity.
  - simpl. right. apply IH. discriminate.
Qed.
Lemma nodup_of_nodup_map__constructive_returns : forall
    {A B : Type} (f : A -> B) l,
  NoDup (map f l) -> NoDup l.
Proof.
  intros A B f l. induction l as [|x tl IH]; intros Hnd.
  - constructor.
  - simpl in Hnd. inversion Hnd as [|? ? Hnot Htail]; subst.
    constructor.
    + intro Hin. apply Hnot. apply in_map. exact Hin.
    + apply IH. exact Htail.
Qed.
Lemma Zlength_Zrange_aux__constructive_returns : forall lo m,
  Zlength (Zrange_aux lo m) = Z.of_nat m.
Proof.
  intros lo m. revert lo. induction m as [|m IH]; intros lo; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__constructive_returns : forall lo hi,
  lo <= hi -> Zlength (Zrange lo hi) = hi - lo.
Proof.
  intros lo hi H. unfold Zrange.
  rewrite Zlength_Zrange_aux__constructive_returns. lia.
Qed.
Lemma nodup_bounded_Zlength__constructive_returns : forall l lo hi,
  lo <= hi -> NoDup l ->
  (forall x, In x l -> lo <= x < hi) ->
  Zlength l <= hi - lo.
Proof.
  intros l lo hi Hrange Hnd Hb.
  assert (Hincl : incl l (Zrange lo hi)).
  { intros x Hx. apply In_Zrange. apply Hb. exact Hx. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite <- !Zlength_correct in Hlen.
  rewrite Zlength_Zrange__constructive_returns in Hlen by exact Hrange.
  exact Hlen.
Qed.
Lemma unit_pairs_continue_up__constructive_returns : forall x y tl,
  y = x + 1 ->
  NoDup (x :: y :: tl) ->
  Forall (fun q : Z * Z => snd q = fst q + 1 \/ snd q = fst q - 1)
    (combine (x :: y :: tl) (y :: tl)) ->
  Forall (fun q : Z * Z => snd q = fst q + 1)
    (combine (x :: y :: tl) (y :: tl)).
Proof.
  intros x y tl Hxy Hnd Hw. revert x y Hxy Hnd Hw.
  induction tl as [|z tl IH]; intros x y Hxy Hnd Hw; simpl in *.
  - constructor. exact Hxy. constructor.
  - inversion Hnd as [|? ? Hnotx Hndyt]; subst.
    inversion Hndyt as [|? ? Hnoty Hndzt]; subst.
    inversion Hw as [|? ? Hstep Hwyt]; subst.
    inversion Hwyt as [|? ? Hstepyz Hwzt]; subst.
    constructor. reflexivity.
    destruct Hstepyz as [Hup | Hdown].
    + eapply IH; eauto.
    + exfalso. apply Hnotx. simpl. right. left. simpl in Hdown. lia.
Qed.
Lemma unit_pairs_continue_down__constructive_returns : forall x y tl,
  y = x - 1 ->
  NoDup (x :: y :: tl) ->
  Forall (fun q : Z * Z => snd q = fst q + 1 \/ snd q = fst q - 1)
    (combine (x :: y :: tl) (y :: tl)) ->
  Forall (fun q : Z * Z => snd q = fst q - 1)
    (combine (x :: y :: tl) (y :: tl)).
Proof.
  intros x y tl Hxy Hnd Hw. revert x y Hxy Hnd Hw.
  induction tl as [|z tl IH]; intros x y Hxy Hnd Hw; simpl in *.
  - constructor. exact Hxy. constructor.
  - inversion Hnd as [|? ? Hnotx Hndyt]; subst.
    inversion Hndyt as [|? ? Hnoty Hndzt]; subst.
    inversion Hw as [|? ? Hstep Hwyt]; subst.
    inversion Hwyt as [|? ? Hstepyz Hwzt]; subst.
    constructor. reflexivity.
    destruct Hstepyz as [Hup | Hdown].
    + exfalso. apply Hnotx. simpl. right. left. simpl in Hup. lia.
    + eapply IH; eauto.
Qed.
Lemma unit_pairs_monotone__constructive_returns : forall p,
  NoDup p ->
  Forall (fun q : Z * Z => snd q = fst q + 1 \/ snd q = fst q - 1)
    (combine p (tl p)) ->
  Forall (fun q : Z * Z => snd q = fst q + 1) (combine p (tl p)) \/
  Forall (fun q : Z * Z => snd q = fst q - 1) (combine p (tl p)).
Proof.
  intros p Hnd Hw. destruct p as [|x [|y tl]]; simpl in *.
  - left. constructor.
  - left. constructor.
  - inversion Hw as [|? ? Hstep Hrest]; subst.
    destruct Hstep as [Hup | Hdown].
    + left. eapply unit_pairs_continue_up__constructive_returns; eauto.
    + right. eapply unit_pairs_continue_down__constructive_returns; eauto.
Qed.
Lemma increasing_pairs_last_length__constructive_returns : forall x tl,
  Forall (fun q : Z * Z => snd q = fst q + 1)
    (combine (x :: tl) tl) ->
  last (x :: tl) 0 = x + Zlength (x :: tl) - 1.
Proof.
  intros x tl. revert x. induction tl as [|y tl IH]; intros x H; simpl in *.
  - change (x = x + 1 - 1). lia.
  - inversion H as [|? ? Hxy Htail]; subst.
    rewrite (IH y Htail). rewrite !Zlength_cons.
    simpl in Hxy. lia.
Qed.
Lemma decreasing_pairs_last_length__constructive_returns : forall x tl,
  Forall (fun q : Z * Z => snd q = fst q - 1)
    (combine (x :: tl) tl) ->
  last (x :: tl) 0 = x - (Zlength (x :: tl) - 1).
Proof.
  intros x tl. revert x. induction tl as [|y tl IH]; intros x H; simpl in *.
  - change (x = x - (1 - 1)). lia.
  - inversion H as [|? ? Hxy Htail]; subst.
    rewrite (IH y Htail). rewrite !Zlength_cons.
    simpl in Hxy. lia.
Qed.
Lemma unit_pairs_start_bound__constructive_returns : forall L c tl,
  1 <= c < L -> NoDup (c :: tl) ->
  Forall (fun q : Z * Z => snd q = fst q + 1 \/ snd q = fst q - 1)
    (combine (c :: tl) tl) ->
  (forall x, In x (c :: tl) -> 0 <= x <= L) ->
  Zlength (c :: tl) <= L.
Proof.
  intros L c tl Hc Hnd Hw Hb.
  destruct (unit_pairs_monotone__constructive_returns _ Hnd Hw) as [Hup | Hdown].
  - pose proof (increasing_pairs_last_length__constructive_returns _ _ Hup) as Hlast.
    assert (Hin : In (last (c :: tl) 0) (c :: tl)) by
      (apply last_in__constructive_returns; discriminate).
    specialize (Hb _ Hin). lia.
  - pose proof (decreasing_pairs_last_length__constructive_returns _ _ Hdown) as Hlast.
    assert (Hin : In (last (c :: tl) 0) (c :: tl)) by
      (apply last_in__constructive_returns; discriminate).
    specialize (Hb _ Hin). lia.
Qed.
Lemma unit_pairs_end_bound__constructive_returns : forall L c x tl,
  1 <= c < L -> NoDup (x :: tl) ->
  Forall (fun q : Z * Z => snd q = fst q + 1 \/ snd q = fst q - 1)
    (combine (x :: tl) tl) ->
  (forall z, In z (x :: tl) -> 0 <= z <= L) ->
  last (x :: tl) 0 = c ->
  Zlength (x :: tl) <= L.
Proof.
  intros L c x tl Hc Hnd Hw Hb Hend.
  destruct (unit_pairs_monotone__constructive_returns _ Hnd Hw) as [Hup | Hdown].
  - pose proof (increasing_pairs_last_length__constructive_returns _ _ Hup) as Hlast.
    specialize (Hb x ltac:(left; reflexivity)). lia.
  - pose proof (decreasing_pairs_last_length__constructive_returns _ _ Hdown) as Hlast.
    specialize (Hb x ltac:(left; reflexivity)). lia.
Qed.
Lemma pendant_pairs_from_spine_form__constructive_returns : forall c x tl,
  NoDup (inl x :: tl) ->
  Forall
    (fun q : (Z + Z) * (Z + Z) =>
      match fst q, snd q with
      | inl a, inl b => b = a + 1 \/ b = a - 1
      | inl a, inr _ => a = c
      | inr _, inl b => b = c
      | inr _, inr _ => False
      end)
    (combine (inl x :: tl) tl) ->
  (exists coords,
      inl x :: tl = map (@inl Z Z) coords /\
      Forall (fun q : Z * Z => snd q = fst q + 1 \/ snd q = fst q - 1)
        (combine coords (List.tl coords))) \/
  (exists coords leaf,
      inl x :: tl = map (@inl Z Z) coords ++ (inr leaf :: nil) /\
      Forall (fun q : Z * Z => snd q = fst q + 1 \/ snd q = fst q - 1)
        (combine coords (List.tl coords)) /\
      last coords 0 = c).
Proof.
  intros c x tl. revert x.
  induction tl as [|y tl IH]; intros x Hnd Hw; simpl in *.
  - left. exists (x :: nil). split; [reflexivity|constructor].
  - inversion Hnd as [|? ? Hnotx Hndtail]; subst.
    inversion Hw as [|? ? Hxy Hwtail]; subst.
    destruct y as [y | leaf].
    + specialize (IH y Hndtail Hwtail).
      destruct IH as [[coords [Heq Hunit]] |
        [coords [leaf2 [Heq [Hunit Hlast]]]]].
      * destruct coords as [|z coords]; [discriminate|].
        inversion Heq; subst z tl; clear Heq.
        left. exists (x :: y :: coords). split; [reflexivity|].
        simpl. constructor; [simpl in Hxy; exact Hxy|exact Hunit].
      * destruct coords as [|z coords]; [discriminate|].
        inversion Heq; subst z; clear Heq.
        right. exists (x :: y :: coords), leaf2.
        split; [reflexivity|]. split.
        -- simpl. constructor; [simpl in Hxy; exact Hxy|exact Hunit].
        -- destruct coords; simpl in *; exact Hlast.
    + simpl in Hxy. subst x.
      destruct tl as [|z tl].
      * right. exists (c :: nil), leaf. simpl.
        split; [reflexivity|]. split; [constructor|reflexivity].
      * inversion Hwtail as [|? ? Hyz Hwrest]; subst.
        destruct z as [z | leaf2]; simpl in Hyz; [subst z|contradiction].
        exfalso. apply Hnotx. simpl. right. left. reflexivity.
Qed.
Lemma pendant_pairs_length_bound__constructive_returns : forall L c p,
  1 <= c < L -> p <> nil -> NoDup p ->
  Forall
    (fun v : Z + Z =>
      match v with inl a => 0 <= a <= L | inr _ => True end) p ->
  Forall
    (fun q : (Z + Z) * (Z + Z) =>
      match fst q, snd q with
      | inl a, inl b => b = a + 1 \/ b = a - 1
      | inl a, inr _ => a = c
      | inr _, inl b => b = c
      | inr _, inr _ => False
      end)
    (combine p (tl p)) ->
  Zlength p - 1 <= L.
Proof.
  intros L c p Hc Hne Hnd Hvalid Hwalk.
  destruct p as [|head rest]; [contradiction|].
  destruct head as [x | leaf].
  - pose proof (pendant_pairs_from_spine_form__constructive_returns
      c x rest Hnd Hwalk) as Hform.
    destruct Hform as [[coords [Heq Hunit]] |
      [coords [leaf2 [Heq [Hunit Hlast]]]]].
    + assert (Hndmap : NoDup (map (@inl Z Z) coords)).
      { rewrite <- Heq. exact Hnd. }
      pose proof (nodup_of_nodup_map__constructive_returns
        (@inl Z Z) coords Hndmap) as Hndcoords.
      assert (Hb : forall z, In z coords -> 0 <= z < L + 1).
      { intros z Hz. assert (Hin : In (inl z) (inl x :: rest)).
        { rewrite Heq. apply in_map. exact Hz. }
        apply Forall_forall with (x := inl z) in Hvalid; auto. simpl in Hvalid. lia. }
      pose proof (nodup_bounded_Zlength__constructive_returns
        coords 0 (L + 1) ltac:(lia) Hndcoords Hb) as Hlen.
      rewrite Heq. rewrite Zlength_correct, length_map.
      rewrite <- Zlength_correct. lia.
    + assert (Hndmap : NoDup (map (@inl Z Z) coords)).
      { rewrite Heq in Hnd. eapply NoDup_app_remove_r. exact Hnd. }
      pose proof (nodup_of_nodup_map__constructive_returns
        (@inl Z Z) coords Hndmap) as Hndcoords.
      assert (Hb : forall z, In z coords -> 0 <= z <= L).
      { intros z Hz. assert (Hin : In (inl z) (inl x :: rest)).
        { rewrite Heq. apply in_or_app. left. apply in_map. exact Hz. }
        apply Forall_forall with (x := inl z) in Hvalid; auto. }
      destruct coords as [|z coords]; [discriminate|].
      pose proof (unit_pairs_end_bound__constructive_returns
        L c z coords Hc Hndcoords Hunit Hb Hlast) as Hlen.
      rewrite Heq, Zlength_app, Zlength_cons, Zlength_nil.
      rewrite Zlength_correct, length_map, <- Zlength_correct. lia.
  - destruct rest as [|y rest].
    + rewrite Zlength_cons, Zlength_nil. lia.
    + inversion Hnd as [|? ? Hnotleaf Hndtail]; subst.
      inversion Hvalid as [|? ? Hvalidleaf Hvalidtail]; subst.
      inversion Hwalk as [|? ? Hstep Hwalktail]; subst.
      destruct y as [y | leaf2]; simpl in Hstep; [subst y|contradiction].
      pose proof (pendant_pairs_from_spine_form__constructive_returns
        c c rest Hndtail Hwalktail) as Hform.
      destruct Hform as [[coords [Heq Hunit]] |
        [coords [leaf3 [Heq [Hunit Hlast]]]]].
      * assert (Hndmap : NoDup (map (@inl Z Z) coords)).
        { rewrite <- Heq. exact Hndtail. }
        pose proof (nodup_of_nodup_map__constructive_returns
          (@inl Z Z) coords Hndmap) as Hndcoords.
        assert (Hb : forall z, In z coords -> 0 <= z <= L).
        { intros z Hz. apply Forall_forall with (x := inl z) in Hvalidtail.
          - exact Hvalidtail.
          - rewrite Heq. apply in_map. exact Hz. }
        destruct coords as [|z coords]; [discriminate|].
        inversion Heq; subst z.
        pose proof (unit_pairs_start_bound__constructive_returns
          L c coords Hc Hndcoords Hunit Hb) as Hlen.
        rewrite !Zlength_cons, Zlength_correct, length_map.
        rewrite <- Zlength_correct.
        rewrite Zlength_cons in Hlen. lia.
      * assert (Hndmap : NoDup (map (@inl Z Z) coords)).
        { rewrite Heq in Hndtail. eapply NoDup_app_remove_r. exact Hndtail. }
        pose proof (nodup_of_nodup_map__constructive_returns
          (@inl Z Z) coords Hndmap) as Hndcoords.
        destruct coords as [|z coords]; [discriminate|].
        inversion Heq; subst z.
        destruct coords as [|w coords].
        -- change (2 <= L). lia.
        -- inversion Hndcoords as [|? ? Hnotc Hndrest]; subst.
           exfalso. apply Hnotc.
           assert (Hinlast : In (last (w :: coords) 0) (w :: coords)) by
             (apply last_in__constructive_returns; discriminate).
           assert (Heqlast : last (w :: coords) 0 = c).
           { simpl in Hlast. exact Hlast. }
           rewrite Heqlast in Hinlast. exact Hinlast.
Qed.
Lemma pendant_step_symmetric__constructive_returns : forall c (a b : Z + Z),
  (match a, b with
   | inl x, inl y => y = x + 1 \/ y = x - 1
   | inl x, inr _ => x = c
   | inr _, inl y => y = c
   | inr _, inr _ => False
   end) ->
  (match b, a with
   | inl x, inl y => y = x + 1 \/ y = x - 1
   | inl x, inr _ => x = c
   | inr _, inl y => y = c
   | inr _, inr _ => False
   end).
Proof.
  intros c [x | x] [y | y]; simpl; intros H.
  - destruct H as [H | H]; [right | left]; lia.
  - exact H.
  - exact H.
  - contradiction.
Qed.
Lemma unit_pairs_center_bound__constructive_returns : forall L c tl,
  0 <= c <= L -> L <= 2 * c -> NoDup (c :: tl) ->
  Forall (fun q : Z * Z => snd q = fst q + 1 \/ snd q = fst q - 1)
    (combine (c :: tl) tl) ->
  (forall x, In x (c :: tl) -> 0 <= x <= L) ->
  Zlength (c :: tl) - 1 <= c.
Proof.
  intros L c tl Hc HL Hnd Hw Hb.
  destruct (unit_pairs_monotone__constructive_returns _ Hnd Hw) as [Hup | Hdown].
  - pose proof (increasing_pairs_last_length__constructive_returns _ _ Hup) as Hlast.
    assert (Hin : In (last (c :: tl) 0) (c :: tl)) by
      (apply last_in__constructive_returns; discriminate).
    specialize (Hb _ Hin). lia.
  - pose proof (decreasing_pairs_last_length__constructive_returns _ _ Hdown) as Hlast.
    assert (Hin : In (last (c :: tl) 0) (c :: tl)) by
      (apply last_in__constructive_returns; discriminate).
    specialize (Hb _ Hin). lia.
Qed.
Lemma pendant_pairs_root_bound__constructive_returns : forall L c tl,
  1 <= c <= L -> L <= 2 * c -> NoDup (inl c :: tl) ->
  Forall
    (fun v : Z + Z =>
      match v with inl a => 0 <= a <= L | inr _ => True end) (inl c :: tl) ->
  Forall
    (fun q : (Z + Z) * (Z + Z) =>
      match fst q, snd q with
      | inl a, inl b => b = a + 1 \/ b = a - 1
      | inl a, inr _ => a = c
      | inr _, inl b => b = c
      | inr _, inr _ => False
      end)
    (combine (inl c :: tl) tl) ->
  Zlength (inl c :: tl) - 1 <= c.
Proof.
  intros L c tl Hc HL Hnd Hvalid Hwalk.
  pose proof (pendant_pairs_from_spine_form__constructive_returns
    c c tl Hnd Hwalk) as Hform.
  destruct Hform as [[coords [Heq Hunit]] |
    [coords [leaf [Heq [Hunit Hlast]]]]].
  - assert (Hndmap : NoDup (map (@inl Z Z) coords)) by
      (rewrite <- Heq; exact Hnd).
    pose proof (nodup_of_nodup_map__constructive_returns
      (@inl Z Z) coords Hndmap) as Hndcoords.
    destruct coords as [|z rest]; [discriminate|].
    inversion Heq; subst z.
    assert (Hb : forall x, In x (c :: rest) -> 0 <= x <= L).
    { intros x Hx. apply Forall_forall with (x := inl x) in Hvalid.
      - exact Hvalid.
      - rewrite Heq. apply in_map. exact Hx. }
    pose proof (unit_pairs_center_bound__constructive_returns
      L c rest ltac:(lia) HL Hndcoords Hunit Hb) as Hbound.
    rewrite Zlength_cons, Zlength_correct, length_map, <- Zlength_correct.
    rewrite Zlength_cons in Hbound. exact Hbound.
  - assert (Hndmap : NoDup (map (@inl Z Z) coords)).
    { rewrite Heq in Hnd. eapply NoDup_app_remove_r. exact Hnd. }
    pose proof (nodup_of_nodup_map__constructive_returns
      (@inl Z Z) coords Hndmap) as Hndcoords.
    destruct coords as [|z rest]; [discriminate|].
    inversion Heq; subst z.
    destruct (unit_pairs_monotone__constructive_returns
      (c :: rest) Hndcoords Hunit) as [Hup | Hdown].
    + pose proof (increasing_pairs_last_length__constructive_returns
        c rest Hup) as Hend.
      change (last (c :: rest) 0 = c) in Hlast. rewrite Hlast in Hend.
      assert (Hlen : Zlength (c :: rest) = 1) by lia.
      rewrite Zlength_cons, Zlength_app, Zlength_cons, Zlength_nil,
        Zlength_correct, length_map, <- Zlength_correct.
      rewrite Zlength_cons in Hlen. lia.
    + pose proof (decreasing_pairs_last_length__constructive_returns
        c rest Hdown) as Hend.
      change (last (c :: rest) 0 = c) in Hlast. rewrite Hlast in Hend.
      assert (Hlen : Zlength (c :: rest) = 1) by lia.
      rewrite Zlength_cons, Zlength_app, Zlength_cons, Zlength_nil,
        Zlength_correct, length_map, <- Zlength_correct.
      rewrite Zlength_cons in Hlen. lia.
Qed.
Lemma canonical_combine_edge_iff__constructive_returns : forall
    d h count (us vs : list Z) x y,
  0 <= count -> Zlength us = count -> Zlength vs = count ->
  (forall k, 0 <= k < count ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  In (x, y) (combine us vs) <->
  exists k, 0 <= k < count /\
    x = CanonicalParent d h k /\ y = k + 2.
Proof.
  intros d h count us vs x y Hcount Hus Hvs Hcanon. split.
  - intros Hin.
    destruct (@In_nth (Z * Z) (combine us vs) (x, y) (0, 0) Hin)
      as [j [Hj Hnth]].
    assert (Hlen : length us = length vs).
    { apply Nat2Z.inj. rewrite <- !Zlength_correct, Hus, Hvs. reflexivity. }
    rewrite length_combine, Hlen, Nat.min_id in Hj.
    assert (Hjc : 0 <= Z.of_nat j < count).
    { rewrite <- Hus, Zlength_correct. lia. }
    specialize (Hcanon (Z.of_nat j) Hjc).
    unfold CanonicalEndpoints in Hcanon.
    assert (Hzu : Znth (Z.of_nat j) us 0 = nth j us 0).
    { unfold Znth. rewrite Nat2Z.id. reflexivity. }
    assert (Hzv : Znth (Z.of_nat j) vs 0 = nth j vs 0).
    { unfold Znth. rewrite Nat2Z.id. reflexivity. }
    pose proof (combine_nth us vs j 0 0 Hlen) as Hcombine.
    rewrite Hnth in Hcombine. inversion Hcombine; subst x y.
    exists (Z.of_nat j). split; [exact Hjc|].
    rewrite Hzu, Hzv in Hcanon. tauto.
  - intros [k [Hk [Hx Hy]]].
    specialize (Hcanon k Hk). unfold CanonicalEndpoints in Hcanon.
    assert (Hlen : length us = length vs).
    { apply Nat2Z.inj. rewrite <- !Zlength_correct, Hus, Hvs. reflexivity. }
    rewrite Hx, Hy.
    replace (CanonicalParent d h k, k + 2) with
      (nth (Z.to_nat k) us 0, nth (Z.to_nat k) vs 0).
    2: { unfold Znth in Hcanon. destruct Hcanon as [Hu Hv].
         rewrite Hu, Hv. reflexivity. }
    rewrite <- (combine_nth us vs (Z.to_nat k) 0 0 Hlen).
    apply nth_In. rewrite length_combine, Hlen, Nat.min_id.
    apply Nat2Z.inj_lt.
    rewrite <- Zlength_correct, Hvs. lia.
Qed.
Lemma canonical_one_adjacency__constructive_returns : forall n us vs x y,
  Zlength us = 1 -> Zlength vs = 1 ->
  (forall k, 0 <= k < 1 ->
    CanonicalEndpoints 1 1 k (Znth k us 0) (Znth k vs 0)) ->
  ze (RememberedGraph n (combine us vs)) x y ->
  (x = 1 /\ y = 2) \/ (x = 2 /\ y = 1).
Proof.
  intros n us vs x y Hus Hvs Hcanon Hxy.
  unfold RememberedGraph in Hxy. simpl in Hxy.
  destruct Hxy as [Hxy | Hyx].
  - apply (proj1 (canonical_combine_edge_iff__constructive_returns
      1 1 1 us vs x y ltac:(lia) Hus Hvs Hcanon)) in Hxy.
    destruct Hxy as [k [Hk [Hx Hy]]]. left.
    unfold CanonicalParent in Hx. destruct (Z_lt_dec k 1),
      (Z.eq_dec 1 1), (Z.eq_dec k 1), (Z_lt_dec k 1); lia.
  - apply (proj1 (canonical_combine_edge_iff__constructive_returns
      1 1 1 us vs y x ltac:(lia) Hus Hvs Hcanon)) in Hyx.
    destruct Hyx as [k [Hk [Hy Hx]]]. right.
    unfold CanonicalParent in Hy. destruct (Z_lt_dec k 1),
      (Z.eq_dec 1 1), (Z.eq_dec k 1), (Z_lt_dec k 1); lia.
Qed.
Lemma canonical_encode_dne_injective__constructive_returns : forall d h,
  1 <= h <= d -> d <> h ->
  let enc := fun x : Z =>
    if Z_le_dec 1 x then
      if Z_le_dec x (d + 1) then
        inl (if Z_le_dec x (h + 1) then h + 1 - x else x - 1)
      else inr x
    else inr x in
  forall x y, enc x = enc y -> x = y.
Proof.
  intros d h Hhd Hdne enc x y Heq. unfold enc in Heq.
  destruct (Z_le_dec 1 x), (Z_le_dec x (d + 1)),
    (Z_le_dec x (h + 1));
  destruct (Z_le_dec 1 y), (Z_le_dec y (d + 1)),
    (Z_le_dec y (h + 1)); simpl in Heq; try discriminate; try lia.
  all: inversion Heq; lia.
Qed.
Lemma canonical_encode_dne_edge__constructive_returns : forall n d h k,
  2 <= n -> 1 <= h <= d -> d <= n - 1 -> d <> h ->
  0 <= k < n - 1 ->
  let enc := fun x : Z =>
    if Z_le_dec 1 x then
      if Z_le_dec x (d + 1) then
        inl (if Z_le_dec x (h + 1) then h + 1 - x else x - 1)
      else inr x
    else inr x in
  match enc (CanonicalParent d h k), enc (k + 2) with
  | inl a, inl b => b = a + 1 \/ b = a - 1
  | inl a, inr _ => a = h
  | inr _, inl b => b = h
  | inr _, inr _ => False
  end.
Proof.
  intros n d h k Hn Hhd Hdn Hdne Hk enc.
  unfold enc, CanonicalParent.
  destruct (Z_lt_dec k h) as [Hkh | Hkh].
  - destruct (Z_le_dec 1 (k + 1)), (Z_le_dec (k + 1) (d + 1)),
      (Z_le_dec (k + 1) (h + 1)), (Z_le_dec 1 (k + 2)),
      (Z_le_dec (k + 2) (d + 1)), (Z_le_dec (k + 2) (h + 1));
      simpl; try lia.
  - destruct (Z.eq_dec d h); [contradiction|].
    destruct (Z.eq_dec k h) as [Heq | Hneq].
    + subst k. destruct (Z_le_dec 1 1), (Z_le_dec 1 (d + 1)),
        (Z_le_dec 1 (h + 1)), (Z_le_dec 1 (h + 2)),
        (Z_le_dec (h + 2) (d + 1)), (Z_le_dec (h + 2) (h + 1));
        simpl; try lia.
    + destruct (Z_lt_dec k d) as [Hkd | Hkd].
      * destruct (Z_le_dec 1 (k + 1)), (Z_le_dec (k + 1) (d + 1)),
          (Z_le_dec (k + 1) (h + 1)), (Z_le_dec 1 (k + 2)),
          (Z_le_dec (k + 2) (d + 1)), (Z_le_dec (k + 2) (h + 1));
          simpl; try lia.
      * destruct (Z_le_dec 1 1), (Z_le_dec 1 (d + 1)),
          (Z_le_dec 1 (h + 1)), (Z_le_dec 1 (k + 2)),
          (Z_le_dec (k + 2) (d + 1)); simpl; try lia.
Qed.
Lemma canonical_encode_eq_injective__constructive_returns : forall h,
  1 <= h ->
  let enc := fun x : Z =>
    if Z_le_dec 1 x then
      if Z_le_dec x (h + 1) then inl (x - 1) else inr x
    else inr x in
  forall x y, enc x = enc y -> x = y.
Proof.
  intros h Hh enc x y Heq. unfold enc in Heq.
  destruct (Z_le_dec 1 x), (Z_le_dec x (h + 1));
  destruct (Z_le_dec 1 y), (Z_le_dec y (h + 1));
    simpl in Heq; try discriminate; try lia.
  all: inversion Heq; lia.
Qed.
Lemma canonical_encode_eq_edge__constructive_returns : forall n h k,
  2 <= n -> 1 <= h -> h <= n - 1 -> 0 <= k < n - 1 ->
  let enc := fun x : Z =>
    if Z_le_dec 1 x then
      if Z_le_dec x (h + 1) then inl (x - 1) else inr x
    else inr x in
  match enc (CanonicalParent h h k), enc (k + 2) with
  | inl a, inl b => b = a + 1 \/ b = a - 1
  | inl a, inr _ => a = 1
  | inr _, inl b => b = 1
  | inr _, inr _ => False
  end.
Proof.
  intros n h k Hn Hh Hhn Hk enc. unfold enc, CanonicalParent.
  destruct (Z_lt_dec k h) as [Hkh | Hkh].
  - destruct (Z_le_dec 1 (k + 1)), (Z_le_dec (k + 1) (h + 1)),
      (Z_le_dec 1 (k + 2)), (Z_le_dec (k + 2) (h + 1)); simpl; try lia.
  - destruct (Z.eq_dec h h); [|contradiction].
    destruct (Z_le_dec 1 2), (Z_le_dec 2 (h + 1)),
      (Z_le_dec 1 (k + 2)), (Z_le_dec (k + 2) (h + 1)); simpl; try lia.
Qed.
Lemma nodup_map_injective__constructive_returns : forall
    {A B : Type} (f : A -> B) l,
  (forall x y, f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd. induction Hnd; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply in_map_iff in Hin as [y [Heq Hy]].
      apply H. replace x with y; [exact Hy|exact (Hinj y x Heq)].
    + exact IHHnd.
Qed.
Lemma valid_vpath_adjacent_pairs__constructive_returns : forall g u p v,
  valid_vpath g u p v ->
  Forall (fun q : Z * Z => ze g (fst q) (snd q)) (combine p (tl p)).
Proof.
  intros g u p v Hv.
  revert u p v Hv.
  eapply valid_vpath_ind_1n with
    (P := fun _ p _ =>
      Forall (fun q : Z * Z => ze g (fst q) (snd q)) (combine p (tl p))).
  - intros x. simpl. constructor.
  - intros x y p z Hstep Hvp IH.
    apply valid_vpath_start in Hvp as [tlp Heq]. subst p.
    simpl. constructor.
    + destruct Hstep as [edge Haux].
      change (zstep_aux g edge x y) in Haux.
      unfold zstep_aux in Haux. tauto.
    + exact IH.
Qed.
Lemma Znth_last__constructive_returns : forall (l : list Z) d,
  l <> nil -> Znth (Zlength l - 1) l d = last l d.
Proof.
  intros l d Hne. induction l as [|x tl IH]; [contradiction|].
  destruct tl as [|y tl].
  - rewrite Zlength_cons, Zlength_nil. change (x = x). reflexivity.
  - rewrite Zlength_cons. rewrite Znth_cons by
      (rewrite Zlength_cons; pose proof (Zlength_nonneg tl); lia).
    replace (Z.succ (Zlength (y :: tl)) - 1 - 1)
      with (Zlength (y :: tl) - 1) by lia.
    simpl. apply IH. discriminate.
Qed.
Lemma remembered_walk_valid__constructive_returns : forall n e x tl,
  Forall (TreeVertex n) (x :: tl) ->
  Forall (fun q : Z * Z =>
    ze (RememberedGraph n e) (fst q) (snd q))
    (combine (x :: tl) tl) ->
  valid_vpath (RememberedGraph n e) x (x :: tl) (last (x :: tl) 0).
Proof.
  intros n e x tl. revert x. induction tl as [|y tl IH]; intros x Hvertices Hw.
  - simpl. apply valid_vpath_empty.
  - inversion Hvertices as [|? ? Hx Hvertices']; subst.
    inversion Hvertices' as [|? ? Hy Htailvertices]; subst.
    inversion Hw as [|? ? Hxy Htail]; subst.
    eapply valid_vpath_cons with (v := y).
    + exists (x, y).
      change (zstep_aux (RememberedGraph n e) (x, y) x y).
      unfold zstep_aux, RememberedGraph, TreeVertex in *. simpl in *. tauto.
    + apply IH; [exact Hvertices'|exact Htail].
Qed.
Lemma remembered_pair_walk_path__constructive_returns : forall n e x tl,
  NoDup (x :: tl) ->
  Forall (TreeVertex n) (x :: tl) ->
  Forall (fun q : Z * Z =>
    ze (RememberedGraph n e) (fst q) (snd q))
    (combine (x :: tl) tl) ->
  PathInEdges n e (x :: tl).
Proof.
  intros n e x tl Hnd Hvertices Hw. unfold PathInEdges. repeat split.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg tl). lia.
  - exact Hnd.
  - rewrite Znth0_cons, Znth_last__constructive_returns by discriminate.
    apply remembered_walk_valid__constructive_returns; assumption.
Qed.
Lemma remembered_walk_path__constructive_returns : forall n e p,
  p <> nil -> NoDup p ->
  Forall (TreeVertex n) p ->
  Forall (fun q : Z * Z =>
    ze (RememberedGraph n e) (fst q) (snd q)) (combine p (tl p)) ->
  PathInEdges n e p.
Proof.
  intros n e p Hne Hnd Hvertices Hw. destruct p as [|x tl]; [contradiction|].
  apply remembered_pair_walk_path__constructive_returns; auto.
Qed.
Lemma remembered_step_symmetric__constructive_returns : forall n e x y,
  GraphLib.reachable.reachable_basic.step (RememberedGraph n e) x y ->
  GraphLib.reachable.reachable_basic.step (RememberedGraph n e) y x.
Proof.
  intros n e x y [edge Hstep]. exists (y, x).
  change (zstep_aux (RememberedGraph n e) (y, x) y x).
  change (zstep_aux (RememberedGraph n e) edge x y) in Hstep.
  unfold zstep_aux, RememberedGraph, TreeVertex in *. simpl in *. tauto.
Qed.
Lemma remembered_valid_vpath_rev__constructive_returns : forall n e u p v,
  valid_vpath (RememberedGraph n e) u p v ->
  valid_vpath (RememberedGraph n e) v (rev p) u.
Proof.
  intros n e u p v Hv. pattern u, p, v. revert u p v Hv.
  eapply valid_vpath_ind_n1.
  - intros x. simpl. apply valid_vpath_empty.
  - intros x p y z Hxy IH Hyz.
    rewrite rev_app_distr. simpl.
    eapply valid_vpath_cons with (v := y).
    + apply remembered_step_symmetric__constructive_returns. exact Hyz.
    + exact IH.
Qed.
Lemma remembered_valid_to_path__constructive_returns : forall n e u p v,
  NoDup p -> valid_vpath (RememberedGraph n e) u p v -> PathInEdges n e p.
Proof.
  intros n e u p v Hnd Hv. unfold PathInEdges.
  pose proof (valid_vpath_start _ _ _ _ Hv) as [ps Hstart].
  pose proof (valid_vpath_end _ _ _ _ Hv) as [pe Hend].
  repeat split.
  - subst p. rewrite Zlength_cons. pose proof (Zlength_nonneg ps). lia.
  - exact Hnd.
  - assert (Hz0 : Znth 0 p 0 = u) by (rewrite Hstart, Znth0_cons; reflexivity).
    assert (Hzlast : Znth (Zlength p - 1) p 0 = v).
    { rewrite Znth_last__constructive_returns.
      - rewrite Hend, last_last. reflexivity.
      - rewrite Hstart. discriminate. }
    rewrite Hz0, Hzlast. exact Hv.
Qed.
Lemma Znth_Zrange_aux__constructive_returns : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia|].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia. rewrite IH by lia. lia.
Qed.
Lemma Znth_Zrange__constructive_returns : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__constructive_returns by lia. lia.
Qed.
Lemma zrange_aux_successor_pairs__constructive_returns : forall m lo,
  Forall (fun q : Z * Z => snd q = fst q + 1)
    (combine (Zrange_aux lo m) (tl (Zrange_aux lo m))).
Proof.
  induction m as [|[|m] IH]; intros lo; simpl.
  - constructor.
  - constructor.
  - constructor; [simpl; reflexivity|].
    apply IH.
Qed.
Lemma zrange_successor_pairs__constructive_returns : forall lo hi,
  Forall (fun q : Z * Z => snd q = fst q + 1)
    (combine (Zrange lo hi) (tl (Zrange lo hi))).
Proof.
  intros lo hi. unfold Zrange. apply zrange_aux_successor_pairs__constructive_returns.
Qed.
Lemma zrange_cons__constructive_returns : forall lo hi,
  lo < hi -> Zrange lo hi = lo :: Zrange (lo + 1) hi.
Proof.
  intros lo hi Hlt. unfold Zrange.
  replace (Z.to_nat (hi - lo))
    with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  reflexivity.
Qed.
Lemma canonical_first_arm_path__constructive_returns : forall
    n d h (us vs : list Z) v,
  2 <= n -> 1 <= h <= d -> d <= n - 1 ->
  1 <= v <= h + 1 ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  PathInEdges n (combine us vs) (Zrange 1 (v + 1)).
Proof.
  intros n d h us vs v Hn Hhd Hdn Hv Hus Hvs Hcanon.
  apply remembered_walk_path__constructive_returns.
  - intro Hnil. assert (Zlength (Zrange 1 (v + 1)) = 0) by
      (rewrite Hnil; apply Zlength_nil).
    rewrite Zlength_Zrange__constructive_returns in H by lia. lia.
  - apply NoDup_Zrange.
  - apply Forall_forall. intros x Hx. unfold TreeVertex.
    apply In_Zrange in Hx. lia.
  - pose proof (zrange_successor_pairs__constructive_returns 1 (v + 1)) as Hsucc.
    apply Forall_forall. intros [x y] Hin. simpl.
    apply Forall_forall with (x := (x, y)) in Hsucc; auto. simpl in Hsucc.
    assert (Hx : In x (Zrange 1 (v + 1))) by
      (eapply in_combine_l; exact Hin).
    assert (Hy : In y (tl (Zrange 1 (v + 1)))) by
      (eapply in_combine_r; exact Hin).
    assert (Hy' : In y (Zrange 1 (v + 1))).
    { destruct (Zrange 1 (v + 1)); simpl in *; auto. }
    apply <- In_Zrange in Hx. apply <- In_Zrange in Hy'.
    unfold RememberedGraph. simpl. left.
    apply (proj2 (canonical_combine_edge_iff__constructive_returns
      d h (n - 1) us vs x y ltac:(lia) Hus Hvs Hcanon)).
    exists (x - 1). split; [lia|]. split; [|lia].
    unfold CanonicalParent. destruct (Z_lt_dec (x - 1) h); [lia|lia].
Qed.
Lemma canonical_second_arm_path__constructive_returns : forall
    n d h (us vs : list Z) v,
  2 <= n -> 1 <= h < d -> d <= n - 1 ->
  h + 2 <= v <= d + 1 ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  PathInEdges n (combine us vs) (1 :: Zrange (h + 2) (v + 1)).
Proof.
  intros n d h us vs v Hn Hhd Hdn Hv Hus Hvs Hcanon.
  apply remembered_walk_path__constructive_returns.
  - discriminate.
  - constructor.
    + intro Hin. apply In_Zrange in Hin. lia.
    + apply NoDup_Zrange.
  - constructor; [unfold TreeVertex; lia|].
    apply Forall_forall. intros x Hx. unfold TreeVertex.
    apply In_Zrange in Hx. lia.
  - rewrite (zrange_cons__constructive_returns (h + 2) (v + 1)) by lia.
    simpl. constructor.
    + unfold RememberedGraph. simpl. left.
      apply (proj2 (canonical_combine_edge_iff__constructive_returns
        d h (n - 1) us vs 1 (h + 2) ltac:(lia) Hus Hvs Hcanon)).
      exists h. split; [lia|]. split; [|lia].
      unfold CanonicalParent. destruct (Z_lt_dec h h),
        (Z.eq_dec d h), (Z.eq_dec h h); try lia.
    + pose proof (zrange_successor_pairs__constructive_returns
        (h + 2) (v + 1)) as Hsucc.
      apply Forall_forall. intros [x y] Hin. simpl.
      assert (Hin0 : In (x, y)
        (combine (Zrange (h + 2) (v + 1))
          (tl (Zrange (h + 2) (v + 1))))).
      { rewrite (zrange_cons__constructive_returns (h + 2) (v + 1)) by lia.
        exact Hin. }
      apply Forall_forall with (x := (x, y)) in Hsucc; [|exact Hin0].
      simpl in Hsucc.
      assert (Hx : In x (Zrange (h + 2) (v + 1))) by
        (eapply in_combine_l; exact Hin0).
      assert (Hy : In y (tl (Zrange (h + 2) (v + 1)))) by
        (eapply in_combine_r; exact Hin0).
      assert (Hy' : In y (Zrange (h + 2) (v + 1))).
      { destruct (Zrange (h + 2) (v + 1)); simpl in *; auto. }
      apply <- In_Zrange in Hx. apply <- In_Zrange in Hy'.
      unfold RememberedGraph. simpl. left.
      apply (proj2 (canonical_combine_edge_iff__constructive_returns
        d h (n - 1) us vs x y ltac:(lia) Hus Hvs Hcanon)).
      exists (x - 1). split; [lia|]. split; [|lia].
      unfold CanonicalParent. destruct (Z_lt_dec (x - 1) h),
        (Z.eq_dec d h), (Z.eq_dec (x - 1) h),
        (Z_lt_dec (x - 1) d); lia.
Qed.
Lemma canonical_leaf_path_dne__constructive_returns : forall
    n d h (us vs : list Z) v,
  2 <= n -> 1 <= h < d -> d <= n - 1 -> d + 2 <= v <= n ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  PathInEdges n (combine us vs) (1 :: v :: nil).
Proof.
  intros n d h us vs v Hn Hhd Hdn Hv Hus Hvs Hcanon.
  apply remembered_pair_walk_path__constructive_returns.
  - repeat constructor; simpl; lia.
  - repeat constructor; unfold TreeVertex; lia.
  - simpl. constructor.
    + unfold RememberedGraph. simpl. left.
      apply (proj2 (canonical_combine_edge_iff__constructive_returns
        d h (n - 1) us vs 1 v ltac:(lia) Hus Hvs Hcanon)).
      exists (v - 2). split; [lia|]. split; [|lia].
      unfold CanonicalParent. destruct (Z_lt_dec (v - 2) h),
        (Z.eq_dec d h), (Z.eq_dec (v - 2) h),
        (Z_lt_dec (v - 2) d); lia.
    + constructor.
Qed.
Lemma canonical_leaf_path_eq__constructive_returns : forall
    n h (us vs : list Z) v,
  2 <= n -> 1 <= h -> h <= n - 1 -> h + 2 <= v <= n ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints h h k (Znth k us 0) (Znth k vs 0)) ->
  PathInEdges n (combine us vs) (1 :: 2 :: v :: nil).
Proof.
  intros n h us vs v Hn Hh Hhn Hv Hus Hvs Hcanon.
  apply remembered_pair_walk_path__constructive_returns.
  - repeat constructor; simpl; lia.
  - repeat constructor; unfold TreeVertex; lia.
  - simpl. constructor.
    + unfold RememberedGraph. simpl. left.
      apply (proj2 (canonical_combine_edge_iff__constructive_returns
        h h (n - 1) us vs 1 2 ltac:(lia) Hus Hvs Hcanon)).
      exists 0. split; [lia|]. split; [|lia].
      unfold CanonicalParent. destruct (Z_lt_dec 0 h); lia.
    + constructor.
      * unfold RememberedGraph. simpl. left.
        apply (proj2 (canonical_combine_edge_iff__constructive_returns
          h h (n - 1) us vs 2 v ltac:(lia) Hus Hvs Hcanon)).
        exists (v - 2). split; [lia|]. split; [|lia].
        unfold CanonicalParent. destruct (Z_lt_dec (v - 2) h),
          (Z.eq_dec h h); lia.
      * constructor.
Qed.
Lemma canonical_path_diameter_bound__constructive_returns : forall
    n d h (us vs : list Z) p,
  Pre n d h -> Feasible n d h ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  PathInEdges n (combine us vs) p ->
  Zlength p - 1 <= d.
Proof.
  intros n d h us vs p Hpre Hfeas Hus Hvs Hcanon Hp.
  destruct Hpre as [[Hn Hnmax] [[Hh Hhd] Hdn]].
  destruct Hfeas as [Htwice Hone].
  destruct Hp as [Hplen [Hpnd Hpvalid]].
  pose proof (valid_vpath_adjacent_pairs__constructive_returns
    _ _ _ _ Hpvalid) as Hpwalk.
  destruct (Z.eq_dec d h) as [Heq | Hdne].
  - subst d.
    set (enc := fun x : Z =>
      if Z_le_dec 1 x then
        if Z_le_dec x (h + 1) then inl (x - 1) else inr x
      else inr x).
    assert (Hinj : forall x y, enc x = enc y -> x = y).
    { apply canonical_encode_eq_injective__constructive_returns. exact Hh. }
    assert (Hmapnd : NoDup (map enc p)).
    { apply nodup_map_injective__constructive_returns; auto. }
    assert (Hmapvalid : Forall
      (fun v : Z + Z =>
        match v with inl a => 0 <= a <= h | inr _ => True end)
      (map enc p)).
    { apply Forall_forall. intros z Hz.
      apply in_map_iff in Hz as [x [Heqx Hx]]. subst z.
      unfold enc. destruct (Z_le_dec 1 x), (Z_le_dec x (h + 1)); simpl; lia. }
    assert (Hmapwalk : Forall
      (fun q : (Z + Z) * (Z + Z) =>
        match fst q, snd q with
        | inl a, inl b => b = a + 1 \/ b = a - 1
        | inl a, inr _ => a = 1
        | inr _, inl b => b = 1
        | inr _, inr _ => False
        end)
      (combine (map enc p) (tl (map enc p)))).
    { clear Hplen Hpnd Hpvalid Hmapnd Hmapvalid.
      revert Hpwalk. induction p as [|x [|y tl] IH]; intros Hpwalk; simpl in *.
      - constructor.
      - constructor.
      - inversion Hpwalk as [|? ? Hxy Hpwalk']; subst. constructor.
        + unfold RememberedGraph in Hxy. simpl in Hxy.
          destruct Hxy as [Hxy | Hyx].
        * apply (proj1 (canonical_combine_edge_iff__constructive_returns
            h h (n - 1) us vs x y ltac:(lia) Hus Hvs Hcanon)) in Hxy.
          destruct Hxy as [k [Hk [-> ->]]].
          exact (canonical_encode_eq_edge__constructive_returns
            n h k Hn Hh ltac:(lia) Hk).
        * apply (proj1 (canonical_combine_edge_iff__constructive_returns
            h h (n - 1) us vs y x ltac:(lia) Hus Hvs Hcanon)) in Hyx.
          destruct Hyx as [k [Hk [-> ->]]].
          pose proof (canonical_encode_eq_edge__constructive_returns
            n h k Hn Hh ltac:(lia) Hk) as Hstep.
          fold enc in Hstep.
          apply pendant_step_symmetric__constructive_returns. exact Hstep.
        + apply IH. exact Hpwalk'. }
    assert (Hmapne : map enc p <> nil).
    { intro Hnil. apply map_eq_nil in Hnil. subst p. rewrite Zlength_nil in Hplen. lia. }
    destruct (Z.eq_dec h 1) as [Hh1 | Hh1].
    + subst h. assert (Hn2 : n = 2) by (destruct Hone; [contradiction|lia]).
      subst n. destruct p as [|x [|y [|z tl]]]; simpl in *.
      * lia.
      * lia.
      * lia.
      * inversion Hpwalk as [|? ? Hxy Hpwalk']; subst.
        inversion Hpwalk' as [|? ? Hyz Hpwalk'']; subst.
        pose proof (canonical_one_adjacency__constructive_returns
          2 us vs x y Hus Hvs Hcanon Hxy) as Hxy'.
        pose proof (canonical_one_adjacency__constructive_returns
          2 us vs y z Hus Hvs Hcanon Hyz) as Hyz'.
        inversion Hpnd as [|? ? Hnotx Hpnd']; subst.
        exfalso. apply Hnotx. simpl.
        destruct Hxy' as [[-> ->] | [-> ->]];
          destruct Hyz' as [[? ?] | [? ?]]; subst; auto; lia.
    + pose proof (pendant_pairs_length_bound__constructive_returns
        h 1 (map enc p) ltac:(lia)
        Hmapne Hmapnd Hmapvalid Hmapwalk) as Hbound.
      rewrite Zlength_correct, length_map, <- Zlength_correct in Hbound.
      exact Hbound.
  - set (enc := fun x : Z =>
      if Z_le_dec 1 x then
        if Z_le_dec x (d + 1) then
          inl (if Z_le_dec x (h + 1) then h + 1 - x else x - 1)
        else inr x
      else inr x).
    assert (Hinj : forall x y, enc x = enc y -> x = y).
    { apply canonical_encode_dne_injective__constructive_returns; auto. }
    assert (Hmapnd : NoDup (map enc p)).
    { apply nodup_map_injective__constructive_returns; auto. }
    assert (Hmapvalid : Forall
      (fun v : Z + Z =>
        match v with inl a => 0 <= a <= d | inr _ => True end)
      (map enc p)).
    { apply Forall_forall. intros z Hz.
      apply in_map_iff in Hz as [x [Heqx Hx]]. subst z.
      unfold enc. destruct (Z_le_dec 1 x), (Z_le_dec x (d + 1)),
        (Z_le_dec x (h + 1)); simpl; lia. }
    assert (Hmapwalk : Forall
      (fun q : (Z + Z) * (Z + Z) =>
        match fst q, snd q with
        | inl a, inl b => b = a + 1 \/ b = a - 1
        | inl a, inr _ => a = h
        | inr _, inl b => b = h
        | inr _, inr _ => False
        end)
      (combine (map enc p) (tl (map enc p)))).
    { clear Hplen Hpnd Hpvalid Hmapnd Hmapvalid.
      revert Hpwalk. induction p as [|x [|y tl] IH]; intros Hpwalk; simpl in *.
      - constructor.
      - constructor.
      - inversion Hpwalk as [|? ? Hxy Hpwalk']; subst. constructor.
        + unfold RememberedGraph in Hxy. simpl in Hxy.
          destruct Hxy as [Hxy | Hyx].
        * apply (proj1 (canonical_combine_edge_iff__constructive_returns
            d h (n - 1) us vs x y ltac:(lia) Hus Hvs Hcanon)) in Hxy.
          destruct Hxy as [k [Hk [-> ->]]].
          exact (canonical_encode_dne_edge__constructive_returns
            n d h k Hn (conj Hh Hhd) Hdn Hdne Hk).
        * apply (proj1 (canonical_combine_edge_iff__constructive_returns
            d h (n - 1) us vs y x ltac:(lia) Hus Hvs Hcanon)) in Hyx.
          destruct Hyx as [k [Hk [-> ->]]].
          pose proof (canonical_encode_dne_edge__constructive_returns
            n d h k Hn (conj Hh Hhd) Hdn Hdne Hk) as Hstep.
          fold enc in Hstep.
          apply pendant_step_symmetric__constructive_returns. exact Hstep.
        + apply IH. exact Hpwalk'. }
    assert (Hmapne : map enc p <> nil).
    { intro Hnil. apply map_eq_nil in Hnil. subst p. rewrite Zlength_nil in Hplen. lia. }
    pose proof (pendant_pairs_length_bound__constructive_returns
      d h (map enc p) ltac:(lia) Hmapne Hmapnd Hmapvalid Hmapwalk) as Hbound.
    rewrite Zlength_correct, length_map, <- Zlength_correct in Hbound.
    exact Hbound.
Qed.
Lemma canonical_root_height_bound__constructive_returns : forall
    n d h (us vs : list Z) p,
  Pre n d h -> Feasible n d h ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  RootPathInEdges n (combine us vs) p ->
  Zlength p - 1 <= h.
Proof.
  intros n d h us vs p Hpre Hfeas Hus Hvs Hcanon [Hp Hroot].
  destruct (Z.eq_dec d h) as [-> | Hdne].
  - eapply canonical_path_diameter_bound__constructive_returns
      with (n := n) (h := h) (us := us) (vs := vs).
    + exact Hpre.
    + exact Hfeas.
    + exact Hus.
    + exact Hvs.
    + exact Hcanon.
    + exact Hp.
  - destruct Hpre as [[Hn Hnmax] [[Hh Hhd] Hdn]].
    destruct Hfeas as [Htwice Hone].
    destruct Hp as [Hplen [Hpnd Hpvalid]].
    pose proof (valid_vpath_adjacent_pairs__constructive_returns
      _ _ _ _ Hpvalid) as Hpwalk.
    destruct p as [|x tl]; [rewrite Zlength_nil in Hplen; lia|].
    rewrite Znth0_cons in Hroot. subst x.
    set (enc := fun x : Z =>
      if Z_le_dec 1 x then
        if Z_le_dec x (d + 1) then
          inl (if Z_le_dec x (h + 1) then h + 1 - x else x - 1)
        else inr x
      else inr x).
    assert (Hinj : forall x y, enc x = enc y -> x = y).
    { apply canonical_encode_dne_injective__constructive_returns; auto. }
    assert (Hmapnd : NoDup (map enc (1 :: tl))).
    { apply nodup_map_injective__constructive_returns; auto. }
    assert (Hmapvalid : Forall
      (fun v : Z + Z =>
        match v with inl a => 0 <= a <= d | inr _ => True end)
      (map enc (1 :: tl))).
    { apply Forall_forall. intros z Hz.
      apply in_map_iff in Hz as [x [Heqx Hx]]. subst z.
      unfold enc. destruct (Z_le_dec 1 x), (Z_le_dec x (d + 1)),
        (Z_le_dec x (h + 1)); simpl; lia. }
    assert (Hmapwalk : Forall
      (fun q : (Z + Z) * (Z + Z) =>
        match fst q, snd q with
        | inl a, inl b => b = a + 1 \/ b = a - 1
        | inl a, inr _ => a = h
        | inr _, inl b => b = h
        | inr _, inr _ => False
        end)
      (combine (map enc (1 :: tl)) (List.tl (map enc (1 :: tl))))).
    { clear Hplen Hpnd Hpvalid Hmapnd Hmapvalid.
      remember (1 :: tl) as p eqn:Heqp. clear Heqp tl.
      revert Hpwalk. induction p as [|a [|b rest] IH]; intros Hpwalk; simpl in *.
      - constructor.
      - constructor.
      - inversion Hpwalk as [|? ? Hab Hpwalk']; subst. constructor.
        + unfold RememberedGraph in Hab. simpl in Hab.
          destruct Hab as [Hab | Hba].
          * apply (proj1 (canonical_combine_edge_iff__constructive_returns
              d h (n - 1) us vs a b ltac:(lia) Hus Hvs Hcanon)) in Hab.
            destruct Hab as [k [Hk [-> ->]]].
            exact (canonical_encode_dne_edge__constructive_returns
              n d h k Hn (conj Hh Hhd) Hdn Hdne Hk).
          * apply (proj1 (canonical_combine_edge_iff__constructive_returns
              d h (n - 1) us vs b a ltac:(lia) Hus Hvs Hcanon)) in Hba.
            destruct Hba as [k [Hk [-> ->]]].
            pose proof (canonical_encode_dne_edge__constructive_returns
              n d h k Hn (conj Hh Hhd) Hdn Hdne Hk) as Hstep.
            fold enc in Hstep.
            apply pendant_step_symmetric__constructive_returns. exact Hstep.
        + apply IH. exact Hpwalk'. }
    assert (Henc1 : enc 1 = inl h).
    { unfold enc. destruct (Z_le_dec 1 1), (Z_le_dec 1 (d + 1)),
        (Z_le_dec 1 (h + 1)); simpl; try lia; f_equal; lia. }
    cbn [map List.tl] in Hmapnd, Hmapvalid, Hmapwalk.
    rewrite Henc1 in Hmapnd, Hmapvalid, Hmapwalk.
    pose proof (pendant_pairs_root_bound__constructive_returns
      d h (map enc tl) ltac:(lia) Htwice Hmapnd Hmapvalid Hmapwalk) as Hbound.
    rewrite Zlength_cons, Zlength_correct, length_map, <- Zlength_correct in Hbound.
    rewrite Zlength_cons. exact Hbound.
Qed.
Lemma canonical_diameter_witness_dne__constructive_returns : forall
    n d h (us vs : list Z),
  2 <= n -> 1 <= h < d -> d <= n - 1 ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  exists p, PathInEdges n (combine us vs) p /\ Zlength p - 1 = d.
Proof.
  intros n d h us vs Hn Hhd Hdn Hus Hvs Hcanon.
  set (p1 := Zrange 1 (h + 2)).
  set (p2 := 1 :: Zrange (h + 2) (d + 2)).
  pose proof (canonical_first_arm_path__constructive_returns
    n d h us vs (h + 1) Hn ltac:(lia) Hdn ltac:(lia)
    Hus Hvs Hcanon) as Hp1.
  pose proof (canonical_second_arm_path__constructive_returns
    n d h us vs (d + 1) Hn Hhd Hdn ltac:(lia)
    Hus Hvs Hcanon) as Hp2.
  fold p1 in Hp1. fold p2 in Hp2.
  destruct Hp1 as [Hp1len [Hp1nd Hp1valid]].
  destruct Hp2 as [Hp2len [Hp2nd Hp2valid]].
  assert (Hp1valid' : valid_vpath (RememberedGraph n (combine us vs))
    1 p1 (h + 1)).
  { unfold p1 in *. rewrite Zlength_Zrange__constructive_returns in Hp1valid by lia.
    rewrite Znth_Zrange__constructive_returns in Hp1valid by lia.
    rewrite Znth_Zrange__constructive_returns in Hp1valid by lia.
    replace (h + 1 + 1) with (h + 2) in Hp1valid by lia.
    replace (1 + 0) with 1 in Hp1valid by lia.
    replace (1 + (h + 2 - 1 - 1)) with (h + 1) in Hp1valid by lia.
    exact Hp1valid. }
  assert (Hp2valid' : valid_vpath (RememberedGraph n (combine us vs))
    1 p2 (d + 1)).
  { unfold p2 in *. rewrite Znth0_cons in Hp2valid.
    rewrite Zlength_cons, Zlength_Zrange__constructive_returns in Hp2valid by lia.
    rewrite Znth_cons in Hp2valid by lia.
    rewrite Znth_Zrange__constructive_returns in Hp2valid by lia.
    replace (d + 1 + 1) with (d + 2) in Hp2valid by lia.
    replace (h + 2 + (Z.succ (d + 2 - (h + 2)) - 1 - 1))
      with (d + 1) in Hp2valid by lia.
    exact Hp2valid. }
  pose proof (remembered_valid_vpath_rev__constructive_returns
    n (combine us vs) 1 p1 (h + 1) Hp1valid') as Hrev.
  pose proof (valid_vpath_app _ _ _ _ _ _ Hrev Hp2valid') as Happ.
  simpl in Happ.
  exists (rev p1 ++ Zrange (h + 2) (d + 2)). split.
  - apply remembered_valid_to_path__constructive_returns with
      (u := h + 1) (v := d + 1).
    + apply NoDup_app. repeat split.
      * apply NoDup_rev. unfold p1. apply NoDup_Zrange.
      * apply NoDup_Zrange.
      * intros x Hx1 Hx2. apply in_rev in Hx1.
        unfold p1 in Hx1. apply <- In_Zrange in Hx1.
        apply <- In_Zrange in Hx2. lia.
    + exact Happ.
  - unfold p1. rewrite Zlength_app, Zlength_correct, rev_length,
      <- Zlength_correct, !Zlength_Zrange__constructive_returns by lia.
    lia.
Qed.
Lemma zrange_endpoints__constructive_returns : forall lo hi,
  lo < hi ->
  Znth 0 (Zrange lo hi) 0 = lo /\
  Znth (Zlength (Zrange lo hi) - 1) (Zrange lo hi) 0 = hi - 1.
Proof.
  intros lo hi Hlt. split.
  - rewrite Znth_Zrange__constructive_returns by lia. lia.
  - rewrite Zlength_Zrange__constructive_returns by lia.
    rewrite Znth_Zrange__constructive_returns by lia. lia.
Qed.
Lemma prepended_zrange_endpoints__constructive_returns : forall root lo hi,
  lo < hi ->
  Znth 0 (root :: Zrange lo hi) 0 = root /\
  Znth (Zlength (root :: Zrange lo hi) - 1)
    (root :: Zrange lo hi) 0 = hi - 1.
Proof.
  intros root lo hi Hlt. split; [apply Znth0_cons|].
  rewrite Zlength_cons, Zlength_Zrange__constructive_returns by lia.
  rewrite Znth_cons by lia.
  rewrite Znth_Zrange__constructive_returns by lia. lia.
Qed.
Lemma Znth_combine_parent__constructive_returns : forall {B C : Type}
    i (l1 : list B) (l2 : list C) d1 d2,
  0 <= i < Zlength l1 -> Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) (d1, d2) =
    (Znth i l1 d1, Znth i l2 d2).
Proof.
  intros B C i l1. revert i. induction l1 as [|b l1 IH]; intros.
  - rewrite Zlength_correct in H. simpl in H. lia.
  - destruct l2 as [|c l2].
    + rewrite !Zlength_correct in H0. simpl in H0. lia.
    + simpl. destruct (Z_le_lt_eq_dec 0 i ltac:(lia)) as [Hi | Hi].
      * rewrite (Znth_cons (d1, d2) i (b, c) (combine l1 l2)) by lia.
        rewrite (Znth_cons d1 i b l1) by lia.
        rewrite (Znth_cons d2 i c l2) by lia.
        apply IH.
        -- rewrite Zlength_correct in *. simpl in *. lia.
        -- rewrite !Zlength_correct in *. simpl in *. lia.
      * subst i. rewrite (Znth0_cons (d1, d2) (b, c) (combine l1 l2)).
        rewrite (Znth0_cons d1 b l1), (Znth0_cons d2 c l2). reflexivity.
Qed.
Lemma canonical_valid_tree__constructive_returns : forall
    n d h (us vs : list Z),
  Pre n d h -> Feasible n d h ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  ValidRememberedTree n d h (combine us vs).
Proof.
  intros n d h us vs Hpre Hfeas Hus Hvs Hcanon.
  destruct Hpre as [[Hn Hnmax] [[Hh Hhd] Hdn]].
  destruct Hfeas as [Htwice Hone].
  assert (Hpre' : Pre n d h) by (unfold Pre; tauto).
  assert (Hfeas' : Feasible n d h) by (unfold Feasible; tauto).
  unfold ValidRememberedTree. repeat split.
  - rewrite Zlength_correct, length_combine.
    assert (Hlen : length us = length vs).
    { apply Nat2Z.inj. rewrite <- !Zlength_correct, Hus, Hvs. reflexivity. }
    rewrite Hlen, Nat.min_id, <- Zlength_correct, Hvs. reflexivity.
  - intros k Hk. exists (CanonicalParent d h k). split.
    + pose proof (Znth_combine_parent__constructive_returns
        k us vs 0 0 ltac:(rewrite Hus; exact Hk) ltac:(lia)) as Hcombine.
      specialize (Hcanon k Hk). unfold CanonicalEndpoints in Hcanon.
      rewrite Hcombine. destruct Hcanon as [Hu Hv]. rewrite Hu, Hv. reflexivity.
    + unfold CanonicalParent.
      destruct (Z_lt_dec k h), (Z.eq_dec d h), (Z.eq_dec k h),
        (Z_lt_dec k d); lia.
  - intros v Hv.
    destruct (Z.eq_dec d h) as [Heq | Hdne].
    + subst d. destruct (Z_le_dec v (h + 1)) as [Hvh | Hvh].
      * exists (Zrange 1 (v + 1)).
        pose proof (canonical_first_arm_path__constructive_returns
          n h h us vs v Hn ltac:(lia) Hdn ltac:(lia) Hus Hvs Hcanon) as Hp.
        pose proof (zrange_endpoints__constructive_returns 1 (v + 1) ltac:(lia))
          as [Hs He]. split; [exact Hp|]. split; [exact Hs|lia].
      * exists (1 :: 2 :: v :: nil).
        pose proof (canonical_leaf_path_eq__constructive_returns
          n h us vs v Hn Hh Hdn ltac:(lia) Hus Hvs Hcanon) as Hp.
        simpl. split; [exact Hp|]. split; reflexivity.
    + destruct (Z_le_dec v (h + 1)) as [Hvh | Hvh].
      * exists (Zrange 1 (v + 1)).
        pose proof (canonical_first_arm_path__constructive_returns
          n d h us vs v Hn ltac:(lia) Hdn ltac:(lia) Hus Hvs Hcanon) as Hp.
        pose proof (zrange_endpoints__constructive_returns 1 (v + 1) ltac:(lia))
          as [Hs He]. split; [exact Hp|]. split; [exact Hs|lia].
      * destruct (Z_le_dec v (d + 1)) as [Hvd | Hvd].
        -- exists (1 :: Zrange (h + 2) (v + 1)).
           pose proof (canonical_second_arm_path__constructive_returns
             n d h us vs v Hn ltac:(lia) Hdn ltac:(lia) Hus Hvs Hcanon) as Hp.
           pose proof (prepended_zrange_endpoints__constructive_returns
             1 (h + 2) (v + 1) ltac:(lia)) as [Hs He].
           split; [exact Hp|]. split; [exact Hs|lia].
        -- exists (1 :: v :: nil).
           pose proof (canonical_leaf_path_dne__constructive_returns
             n d h us vs v Hn ltac:(lia) Hdn ltac:(lia) Hus Hvs Hcanon) as Hp.
           simpl. split; [exact Hp|]. split; reflexivity.
  - unfold max_value_of_subset, max_object_of_subset.
    exists (Zrange 1 (h + 2)). split.
    + split.
      * unfold RootPathInEdges. split.
        -- pose proof (canonical_first_arm_path__constructive_returns
             n d h us vs (h + 1) Hn (conj Hh Hhd) Hdn ltac:(lia)
             Hus Hvs Hcanon) as Hpath.
           replace (h + 1 + 1) with (h + 2) in Hpath by lia. exact Hpath.
        -- pose proof (zrange_endpoints__constructive_returns 1 (h + 2) ltac:(lia))
             as [Hs He]. exact Hs.
      * intros p Hp.
        pose proof (canonical_root_height_bound__constructive_returns
          n d h us vs p Hpre' Hfeas' Hus Hvs Hcanon Hp) as Hbound.
        rewrite Zlength_Zrange__constructive_returns by lia. lia.
    + rewrite Zlength_Zrange__constructive_returns by lia. lia.
  - unfold max_value_of_subset, max_object_of_subset.
    destruct (Z.eq_dec d h) as [Heq | Hdne].
    + subst d. exists (Zrange 1 (h + 2)). split.
      * split.
        -- pose proof (canonical_first_arm_path__constructive_returns
             n h h us vs (h + 1) Hn ltac:(lia) Hdn ltac:(lia)
             Hus Hvs Hcanon) as Hpath.
           replace (h + 1 + 1) with (h + 2) in Hpath by lia. exact Hpath.
        -- intros p Hp.
           pose proof (canonical_path_diameter_bound__constructive_returns
             n h h us vs p Hpre' Hfeas' Hus Hvs Hcanon Hp) as Hbound.
           rewrite Zlength_Zrange__constructive_returns by lia. lia.
      * rewrite Zlength_Zrange__constructive_returns by lia. lia.
    + pose proof (canonical_diameter_witness_dne__constructive_returns
        n d h us vs Hn ltac:(lia) Hdn Hus Hvs Hcanon) as [p [Hp Hplen]].
      exists p. split.
      * split; [exact Hp|]. intros q Hq.
        pose proof (canonical_path_diameter_bound__constructive_returns
          n d h us vs q Hpre' Hfeas' Hus Hvs Hcanon Hq) as Hbound.
        lia.
      * exact Hplen.
  - unfold PathsControlledByRootHeight. intros p Hp.
    pose proof (canonical_path_diameter_bound__constructive_returns
      n d h us vs p Hpre' Hfeas' Hus Hvs Hcanon Hp) as Hbound.
    lia.
Qed.
Lemma Znth_combine__constructive_returns : forall {B C : Type}
    i (l1 : list B) (l2 : list C) d1 d2,
  0 <= i < Zlength l1 -> Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) (d1, d2) =
    (Znth i l1 d1, Znth i l2 d2).
Proof.
  intros B C i l1. revert i. induction l1 as [|b l1 IH]; intros.
  - rewrite Zlength_correct in H. simpl in H. lia.
  - destruct l2 as [|c l2].
    + rewrite !Zlength_correct in H0. simpl in H0. lia.
    + simpl. destruct (Z_le_lt_eq_dec 0 i ltac:(lia)) as [Hi | Hi].
      * rewrite (Znth_cons (d1, d2) i (b, c) (combine l1 l2)) by lia.
        rewrite (Znth_cons d1 i b l1) by lia.
        rewrite (Znth_cons d2 i c l2) by lia.
        apply IH.
        -- rewrite Zlength_correct in *. simpl in *. lia.
        -- rewrite !Zlength_correct in *. simpl in *. lia.
      * subst i. rewrite (Znth0_cons (d1, d2) (b, c) (combine l1 l2)).
        rewrite (Znth0_cons d1 b l1), (Znth0_cons d2 c l2). reflexivity.
Qed.
Lemma canonical_endpoint_arrays_realize_spec__constructive_returns : forall
    n d h (us vs : list Z),
  Pre n d h -> Feasible n d h ->
  Zlength us = n - 1 -> Zlength vs = n - 1 ->
  (forall k, 0 <= k < n - 1 ->
    CanonicalEndpoints d h k (Znth k us 0) (Znth k vs 0)) ->
  Spec n d h (Some (combine us vs)) /\
  Zlength (combine us vs) = n - 1 /\
  (forall i, 0 <= i < Zlength (combine us vs) ->
    Znth i us 0 = fst (Znth i (combine us vs) (0, 0)) /\
    Znth i vs 0 = snd (Znth i (combine us vs) (0, 0))).
Proof.
  intros n d h us vs Hpre Hfeas Hus Hvs Hcanon.
  pose proof (canonical_valid_tree__constructive_returns
    n d h us vs Hpre Hfeas Hus Hvs Hcanon) as Htree.
  assert (Hedges : Zlength (combine us vs) = n - 1) by
    (unfold ValidRememberedTree, IncreasingParentTree in Htree; tauto).
  repeat split.
  - unfold Spec. left. exists (combine us vs). split; [reflexivity|exact Htree].
  - exact Hedges.
  - match goal with
    | Hrange : 0 <= i < Zlength (combine us vs) |- _ =>
      pose proof (Znth_combine__constructive_returns
        i us vs 0 0 ltac:(rewrite Hus; rewrite Hedges in Hrange; exact Hrange)
        ltac:(lia)) as Hcombine
    end.
    rewrite Hcombine. reflexivity.
  - match goal with
    | Hrange : 0 <= i < Zlength (combine us vs) |- _ =>
      pose proof (Znth_combine__constructive_returns
        i us vs 0 0 ltac:(rewrite Hus; rewrite Hedges in Hrange; exact Hrange)
        ltac:(lia)) as Hcombine
    end.
    rewrite Hcombine. reflexivity.
Qed.
Lemma valid_remembered_tree_diameter_one_size_bound__infeasible_returns :
  forall n h e, ValidRememberedTree n 1 h e -> n <= 2.
Proof.
  intros n h e Htree.
  destruct Htree as [Hparents [_ [_ [Hdiam _]]]].
  destruct Hparents as [Hlen Hparents].
  unfold max_value_of_subset, max_object_of_subset in Hdiam.
  destruct Hdiam as [pmax [[Hpmax Hupper] Hmaxlen]].
  destruct (Z_le_gt_dec n 2) as [Hn | Hn]; [exact Hn|].
  pose proof (Hparents 0 ltac:(lia)) as [parent2 [Hedge2 Hparent2]].
  pose proof (Hparents 1 ltac:(lia)) as [parent3 [Hedge3 Hparent3]].
  destruct e as [|edge2 [|edge3 rest]].
  - rewrite Zlength_nil in Hlen. lia.
  - rewrite Zlength_cons, Zlength_nil in Hlen. lia.
  - rewrite Znth0_cons in Hedge2.
    rewrite Znth_cons in Hedge3 by lia.
    rewrite Znth0_cons in Hedge3.
    subst edge2 edge3.
    assert (Hparent2eq : parent2 = 1) by lia. subst parent2.
    assert (Hparent3cases : parent3 = 1 \/ parent3 = 2) by lia.
    destruct Hparent3cases as [-> | ->].
    + assert (Hpath : PathInEdges n ((1, 2) :: (1, 3) :: rest)
          (2 :: 1 :: 3 :: nil)).
      { unfold PathInEdges. split.
        - rewrite !Zlength_cons, Zlength_nil. lia.
        - split.
          * repeat constructor; simpl; lia.
          * change (valid_vpath
            (RememberedGraph n ((1, 2) :: (1, 3) :: rest))
            2 (2 :: 1 :: 3 :: nil) 3).
            eapply valid_vpath_cons with (v := 1).
            -- exists (2, 1). unfold zstep_aux, RememberedGraph, TreeVertex.
               simpl. repeat split; try reflexivity; try lia.
               right. simpl. auto.
            -- eapply valid_vpath_cons with (v := 3).
               ++ exists (1, 3). unfold zstep_aux, RememberedGraph, TreeVertex.
                  simpl. repeat split; try reflexivity; try lia.
                  left. simpl. auto.
               ++ apply valid_vpath_empty. }
      specialize (Hupper _ Hpath).
      rewrite !Zlength_cons, Zlength_nil in Hupper. lia.
    + assert (Hpath : PathInEdges n ((1, 2) :: (2, 3) :: rest)
          (1 :: 2 :: 3 :: nil)).
      { unfold PathInEdges. split.
        - rewrite !Zlength_cons, Zlength_nil. lia.
        - split.
          * repeat constructor; simpl; lia.
          * change (valid_vpath
            (RememberedGraph n ((1, 2) :: (2, 3) :: rest))
            1 (1 :: 2 :: 3 :: nil) 3).
            eapply valid_vpath_cons with (v := 2).
            -- exists (1, 2). unfold zstep_aux, RememberedGraph, TreeVertex.
               simpl. repeat split; try reflexivity; try lia.
               left. simpl. auto.
            -- eapply valid_vpath_cons with (v := 3).
               ++ exists (2, 3). unfold zstep_aux, RememberedGraph, TreeVertex.
                  simpl. repeat split; try reflexivity; try lia.
                  left. simpl. auto.
               ++ apply valid_vpath_empty. }
      specialize (Hupper _ Hpath).
      rewrite !Zlength_cons, Zlength_nil in Hupper. lia.
Qed.
