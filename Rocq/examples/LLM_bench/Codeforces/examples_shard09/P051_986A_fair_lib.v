Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphInstances.
Require Import GraphLib.reachable.reachable_basic.
Require Import SimpleC.EE.LLM_bench.Codeforces.GraphDistanceZ.

Import ListNotations.
Local Open Scope Z_scope.

(* The towns as a graph value: the towns 1 .. n and the roads between them. *)
Definition TownGraph (n : Z) (e : list (Z * Z)%type) : ZGraph :=
  {| zv := fun x => 1 <= x <= n ; ze := fun x y => In (x, y) e \/ In (y, x) e |}.

(* How many roads the shortest route between two towns uses.
   [zdistance] is the repository's Z-indexed graph distance: the least length
   of a walk from u to v, taken with MaxMinLib's minimum. *)
Definition Distance (n : Z) (e : list (Z * Z)%type) (u v d : Z) : Prop :=
  1 <= u <= n /\ 1 <= v <= n /\ zdistance (TownGraph n e) u v d.

(* How far the nearest town producing that type of goods lies. *)
Definition TypeDistance (n : Z) (e : list (Z * Z)%type) (goods : list Z) (town typ d : Z) : Prop :=
  min_value_of_subset Z.le
    (fun q => exists src, 1 <= src <= n /\ Znth (src - 1) goods 0 = typ /\
                Distance n e town src q)
    (fun x => x) d.

(* The s different types of goods a fair brings in. *)
Definition TypeChoice (s : Z) (types : list Z) : Prop :=
  Zlength types = s /\ NoDup types /\ Forall (fun x => 1 <= x) types.

(* What holding the fair in that town costs: the distances to the chosen types,
   added up. *)
Definition FairCost (n s : Z) (e : list (Z * Z)%type) (goods : list Z) (town cost : Z) : Prop :=
  exists types ds : list Z,
    TypeChoice s types /\ Zlength ds = s /\
    (forall i, 0 <= i < s -> TypeDistance n e goods town (Znth i types 0) (Znth i ds 0)) /\
    cost = fold_right Z.add 0 ds.
Definition Pre (k s : Z) (e : list (Z * Z)%type) (goods : list Z) : Prop :=
  (* Stated explicitly in the P051 solver Require, so dropped here:
       1 <= Zlength goods <= 100000 /\
       1 <= s <= k /\
       k <= Zlength goods /\
       Forall (fun x => 1 <= x <= k) goods /\
       Forall (fun p => 1 <= fst p <= (Zlength goods) /\ 1 <= snd p <= (Zlength goods) /\ fst p <> snd p) e  *)
  (forall typ, 1 <= typ <= k -> In typ goods) /\
  connected (TownGraph (Zlength goods) e) /\
  forall p q, In p e -> In q e -> (p = q \/ p = (snd q, fst q)) -> p = q.

Definition Spec (k s : Z) (e : list (Z * Z)%type) (goods out : list Z) : Prop :=
  Zlength out = Zlength goods /\ forall i, 0 <= i < Zlength goods ->
  min_value_of_subset Z.le (FairCost (Zlength goods) s e goods (i + 1))
    (fun x => x) (Znth i out 0).

(* ================================================================= *)
(*  Annotation interface: the mathematical states the C program       *)
(*  maintains, and the bridges from them to [Spec].                   *)
(* ================================================================= *)

From AUXLib Require Import ListLib.
Require Import Coq.micromega.Lia.

(* ---- multi-source distance ------------------------------------- *)

(* The towns that produce goods of type [c]: the BFS sources. *)
Definition SrcSet (n : Z) (goods : list Z) (c u : Z) : Prop :=
  1 <= u <= n /\ Znth (u - 1) goods 0 = c.

(* A walk of [d] roads reaching [v] from some town producing type [c]. *)
Definition MReach (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                  (c v d : Z) : Prop :=
  exists u, SrcSet n goods c u /\ path_of_zlen (TownGraph n e) u v d.

(* The shortest such walk: what one BFS run stores in [dist_[c][v]].
   This is the plain two-part form of [TypeDistance]. *)
Definition BfsDist (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                   (c v d : Z) : Prop :=
  MReach n e goods c v d /\ forall q, MReach n e goods c v q -> d <= q.

(* ---- adjacency arcs -------------------------------------------- *)

(* Road [i] contributes arc [2*i] (from [eu[i]] to [ev[i]]) and arc
   [2*i+1] (the reverse). *)
Definition ArcFrom (edges : list (Z * Z)%type) (j : Z) : Z :=
  if Z.even j then fst (Znth (j / 2) edges (0, 0))
              else snd (Znth (j / 2) edges (0, 0)).

Definition ArcTo (edges : list (Z * Z)%type) (j : Z) : Z :=
  if Z.even j then snd (Znth (j / 2) edges (0, 0))
              else fst (Znth (j / 2) edges (0, 0)).

(* [AdjChain nx cur l]: following [nxt_] from [cur] visits exactly [l].
   The recursion is on the derivation, so no decreasing measure on the
   index is needed. *)
Inductive AdjChain (nx : list Z) : Z -> list Z -> Prop :=
| AdjChain_nil : AdjChain nx (-1) nil
| AdjChain_cons : forall j l,
    0 <= j < Zlength nx ->
    AdjChain nx (Znth j nx 0) l ->
    AdjChain nx j (j :: l).

(* The chain hanging off [head_[u]] is exactly the set of arcs leaving [u]. *)
Definition AdjListAt (done : Z) (edges : list (Z * Z)%type)
                     (hd nx : list Z) (u : Z) (l : list Z) : Prop :=
  AdjChain nx (Znth (u - 1) hd 0) l /\ NoDup l /\
  (forall j, In j l -> 0 <= j < 2 * done /\ ArcFrom edges j = u) /\
  (forall j, 0 <= j < 2 * done -> ArcFrom edges j = u -> In j l).

(* After [done] roads have been inserted, the three work arrays are a
   faithful adjacency-list representation of those roads. *)
Definition AdjBuild (n done : Z) (edges : list (Z * Z)%type)
                    (hd nx tlst : list Z) : Prop :=
  Zlength hd = n /\ Zlength nx = 2 * done /\ Zlength tlst = 2 * done /\
  (forall j, 0 <= j < 2 * done -> Znth j tlst 0 = ArcTo edges j) /\
  (forall j, 0 <= j < 2 * done ->
     Znth j nx 0 = -1 \/ 0 <= Znth j nx 0 < 2 * done) /\
  (forall u, 1 <= u <= n ->
     Znth (u - 1) hd 0 = -1 \/ 0 <= Znth (u - 1) hd 0 < 2 * done) /\
  (forall u, 1 <= u <= n -> exists l, AdjListAt done edges hd nx u l).

(* ---- the BFS loop state ---------------------------------------- *)

(* What the queue and the distance row mean, independently of how far
   the expansion has progressed.  [dl] is the whole [dist_] row, read at
   the town index; [Q] is the live part of [queue_]. *)
Definition BfsCore (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                   (c : Z) (Q dl : list Z) : Prop :=
  (forall i, 0 <= i < Zlength Q -> 1 <= Znth i Q 0 <= n) /\
  NoDup Q /\
  (forall v, 1 <= v <= n -> (In v Q <-> 0 <= Znth v dl 0)) /\
  (forall v, 1 <= v <= n -> ~ In v Q -> Znth v dl 0 = -1) /\
  (forall i, 0 <= i < Zlength Q ->
     MReach n e goods c (Znth i Q 0) (Znth (Znth i Q 0) dl 0)) /\
  (forall i j, 0 <= i -> i <= j -> j < Zlength Q ->
     Znth (Znth i Q 0) dl 0 <= Znth (Znth j Q 0) dl 0) /\
  (forall i, 0 <= i < Zlength Q -> 0 <= Znth (Znth i Q 0) dl 0 <= i) /\
  (forall v, 1 <= v <= n -> Znth (v - 1) goods 0 = c ->
     In v Q /\ Znth v dl 0 = 0).

(* The first [qh] queue entries have had all their roads relaxed. *)
Definition BfsExpanded (n : Z) (e : list (Z * Z)%type)
                       (Q dl : list Z) (qh : Z) : Prop :=
  forall i w, 0 <= i < qh -> 1 <= w <= n ->
    (In (Znth i Q 0, w) e \/ In (w, Znth i Q 0) e) ->
    In w Q /\ Znth w dl 0 <= Znth (Znth i Q 0) dl 0 + 1.

(* Nothing in the queue is further out than [b]: the two-level property. *)
Definition BfsBounded (Q dl : list Z) (b : Z) : Prop :=
  forall j, 0 <= j < Zlength Q -> Znth (Znth j Q 0) dl 0 <= b.

(* The inner arc scan: every arc of [u] outside the remaining chain has
   already been relaxed. *)
Definition BfsScan (done : Z) (edges : list (Z * Z)%type)
                   (nx tlst Q dl : list Z) (u cur : Z) : Prop :=
  exists lrem,
    AdjChain nx cur lrem /\
    (forall j, In j lrem -> 0 <= j < 2 * done /\ ArcFrom edges j = u) /\
    (forall j, 0 <= j < 2 * done -> ArcFrom edges j = u -> ~ In j lrem ->
       In (Znth j tlst 0) Q /\
       Znth (Znth j tlst 0) dl 0 <= Znth u dl 0 + 1).

(* ---- the solver's own loop states ------------------------------ *)

(* The first [done - 1] rows of [dist_] hold real multi-source distances. *)
Definition BfsRows (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                   (rows : list (list Z)) (done : Z) : Prop :=
  forall c v, 1 <= c < done -> 1 <= v <= n ->
    0 <= Znth v (Znth c rows nil) 0 <= n - 1 /\
    BfsDist n e goods c v (Znth v (Znth c rows nil) 0).

(* [tmp_[0 .. done)] holds town [v]'s distances to types [1 .. done]. *)
Definition TmpPrefix (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                     (v : Z) (tmpl : list Z) (done : Z) : Prop :=
  forall j, 0 <= j < done ->
    0 <= Znth j tmpl 0 <= n - 1 /\
    BfsDist n e goods (j + 1) v (Znth j tmpl 0).

(* [cost[1 .. done]] already holds optimal fair costs. *)
Definition OutPrefix (n s : Z) (e : list (Z * Z)%type) (goods : list Z)
                     (out : list Z) (done : Z) : Prop :=
  forall i, 0 <= i < done ->
    min_value_of_subset Z.le (FairCost n s e goods (i + 1)) (fun x => x)
      (Znth i out 0).

(* The machine-level ranges the arc arrays satisfy; kept apart from
   [AdjBuild] because the C loop needs them at every array access. *)
Definition NxtRange (done : Z) (nx : list Z) : Prop :=
  forall j, 0 <= j < 2 * done -> -1 <= Znth j nx 0 < 2 * done.

Definition ArcToRange (n done : Z) (tlst : list Z) : Prop :=
  forall j, 0 <= j < 2 * done -> 1 <= Znth j tlst 0 <= n.

(* What one [bfs_type] run leaves in its row: every town is either
   unreachable from the type-[c] towns, or holds the true distance. *)
Definition BfsRowResult (n : Z) (e : list (Z * Z)%type) (goods : list Z)
                        (c : Z) (dl : list Z) : Prop :=
  forall v, 1 <= v <= n ->
    (Znth v dl 0 = -1 /\ ~ (exists q, MReach n e goods c v q)) \/
    (0 <= Znth v dl 0 <= n - 1 /\ BfsDist n e goods c v (Znth v dl 0)).

(* The source-collecting loop: towns below [done] are already classified,
   towns from [done] on still hold the initial [-1]. *)
Definition BfsInit (n : Z) (goods : list Z) (c : Z)
                   (Q dl : list Z) (done : Z) : Prop :=
  NoDup Q /\
  (forall w, 1 <= w < done -> Znth (w - 1) goods 0 = c ->
     In w Q /\ Znth w dl 0 = 0) /\
  (forall w, 1 <= w < done -> Znth (w - 1) goods 0 <> c -> Znth w dl 0 = -1) /\
  (forall w, done <= w <= n -> Znth w dl 0 = -1) /\
  (forall i, 0 <= i < Zlength Q ->
     1 <= Znth i Q 0 < done /\
     Znth (Znth i Q 0 - 1) goods 0 = c /\
     Znth (Znth i Q 0) dl 0 = 0).

(* [FairCost] adds the chosen distances with [fold_right Z.add 0]; the C
   accumulator does the same, under a name that does not clash with the
   local variable [sum]. *)
Definition ZSum (l : list Z) : Z := fold_right Z.add 0 l.

(* ================================================================= *)
(*  Bridge 0.  Roads have no direction, so distance is symmetric.     *)
(* ================================================================= *)

Lemma TownGraph_step_iff : forall n e x y,
  step (TownGraph n e) x y <->
  (In (x, y) e \/ In (y, x) e) /\ 1 <= x <= n /\ 1 <= y <= n.
Proof.
  intros n e x y. split.
  - intros [[p q] Hstep]. simpl in Hstep. unfold zstep_aux in Hstep.
    simpl in Hstep. destruct Hstep as [Hx [Hy [Hze [Hvx Hvy]]]].
    simpl in Hze, Hvx, Hvy. tauto.
  - intros [Hze [Hvx Hvy]]. exists (x, y). simpl. unfold zstep_aux.
    simpl. tauto.
Qed.

Lemma TownGraph_step_sym : forall n e x y,
  step (TownGraph n e) x y -> step (TownGraph n e) y x.
Proof.
  intros n e x y H. apply TownGraph_step_iff in H as [Hze [Hx Hy]].
  apply TownGraph_step_iff. split; [tauto | tauto].
Qed.

(* [path_of_zlen] only grows at the tail; this adds a step at the front. *)
Lemma pozl_front : forall n e u v w d,
  step (TownGraph n e) u v ->
  path_of_zlen (TownGraph n e) v w d ->
  path_of_zlen (TownGraph n e) u w (d + 1).
Proof.
  intros n e u v w d Hstep Hpath.
  induction Hpath as [x | x y z d0 Hpath IH Hstep0].
  - eapply pozl_step; [apply pozl_0 | exact Hstep].
  - replace (d0 + 1 + 1) with ((d0 + 1) + 1) by lia.
    eapply pozl_step; [apply IH; exact Hstep | exact Hstep0].
Qed.

Lemma pozl_sym : forall n e u v k,
  path_of_zlen (TownGraph n e) u v k ->
  path_of_zlen (TownGraph n e) v u k.
Proof.
  intros n e u v k Hpath.
  induction Hpath as [x | x y z d Hpath IH Hstep].
  - apply pozl_0.
  - apply TownGraph_step_sym in Hstep.
    eapply pozl_front; [exact Hstep | exact IH].
Qed.

Lemma zdistance_sym : forall n e u v d,
  zdistance (TownGraph n e) u v d <-> zdistance (TownGraph n e) v u d.
Proof.
  assert (Hone : forall n e u v d,
            zdistance (TownGraph n e) u v d ->
            zdistance (TownGraph n e) v u d).
  { intros n e u v d H. apply zdistance_iff in H as [Hpath Hmin].
    apply zdistance_iff. split.
    - apply pozl_sym. exact Hpath.
    - intros q Hq. apply Hmin. apply pozl_sym. exact Hq. }
  intros n e u v d. split; apply Hone.
Qed.

(* ================================================================= *)
(*  Bridge 1.  [TypeDistance] is the multi-source shortest distance.  *)
(* ================================================================= *)

Lemma BfsDist_unique : forall n e goods c v d1 d2,
  BfsDist n e goods c v d1 -> BfsDist n e goods c v d2 -> d1 = d2.
Proof.
  intros n e goods c v d1 d2 [H1 Hm1] [H2 Hm2].
  pose proof (Hm1 d2 H2). pose proof (Hm2 d1 H1). lia.
Qed.

Lemma BfsDist_min_value : forall n e goods c v d,
  BfsDist n e goods c v d <->
  min_value_of_subset Z.le (MReach n e goods c v) (fun x => x) d.
Proof.
  intros n e goods c v d. split.
  - intros [Hd Hmin]. exists d. split; [split | reflexivity].
    + sets_unfold. exact Hd.
    + intros b Hb. sets_unfold in Hb. simpl. apply (Hmin b Hb).
  - intros [a [[Ha Hmin] Hfa]]. simpl in Hfa. subst a.
    split; [exact Ha |]. intros q Hq. apply (Hmin q Hq).
Qed.

(* [TypeDistance] measures from the town to a source and takes the minimum
   over [zdistance]; [BfsDist] measures from a source to the town and takes
   the minimum over walk lengths.  Symmetry lines up the endpoints, and
   [path_of_zlen_min] lines up the two minima. *)
Theorem TypeDistance_BfsDist : forall n e goods v c d,
  1 <= v <= n ->
  (TypeDistance n e goods v c d <-> BfsDist n e goods c v d).
Proof.
  intros n e goods v c d Hv.
  unfold TypeDistance.
  rewrite BfsDist_min_value.
  split; intros Hmin.
  - eapply (min_eq_forward Z.le (fun x : Z => x) (fun x : Z => x)); [exact Hmin | |].
    + intros q [src [Hsrc [Hgood [_ [_ Hdist]]]]].
      exists q. split; [| reflexivity].
      exists src. split.
      * unfold SrcSet. tauto.
      * apply zdistance_path.
        apply (proj1 (zdistance_sym n e v src q)). exact Hdist.
    + intros q [u [[Hu Hgood] Hpath]].
      destruct (path_of_zlen_min (TownGraph n e) q v u
                  (pozl_sym n e u v q Hpath)) as [dm [Hdm Hle]].
      exists dm. split; [| exact Hle].
      exists u. unfold Distance.
      split; [lia | split; [tauto | split; [lia | split; [lia | exact Hdm]]]].
  - eapply (min_eq_forward Z.le (fun x : Z => x) (fun x : Z => x)); [exact Hmin | |].
    + intros q [u [[Hu Hgood] Hpath]].
      destruct (path_of_zlen_min (TownGraph n e) q v u
                  (pozl_sym n e u v q Hpath)) as [dm [Hdm Hle]].
      exists dm. split; [| exact Hle].
      exists u. unfold Distance.
      split; [lia | split; [tauto | split; [lia | split; [lia | exact Hdm]]]].
    + intros q [src [Hsrc [Hgood [_ [_ Hdist]]]]].
      exists q. split; [| reflexivity].
      exists src. split.
      * unfold SrcSet. tauto.
      * apply zdistance_path.
        apply (proj1 (zdistance_sym n e v src q)). exact Hdist.
Qed.

(* ================================================================= *)
(*  Bridge 4.  Summing the [s] smallest of a sorted list is optimal.  *)
(* ================================================================= *)

Lemma ZSum_cons : forall a l, ZSum (a :: l) = a + ZSum l.
Proof. intros. reflexivity. Qed.

Lemma ZSum_nil : ZSum nil = 0.
Proof. reflexivity. Qed.

Lemma ZSum_app : forall l1 l2, ZSum (l1 ++ l2) = ZSum l1 + ZSum l2.
Proof.
  induction l1 as [| a l1 IHl]; intros l2; simpl.
  - unfold ZSum; simpl; lia.
  - unfold ZSum in *; simpl; rewrite IHl; lia.
Qed.

(* The heart of the greedy step: no [p]-element sub-multiset of a
   non-decreasing list beats its own first [p] entries. *)
Lemma sorted_prefix_min : forall (l A B : list Z) (p : nat),
  mono_nondec l ->
  Permutation l (A ++ B) ->
  length A = p ->
  ZSum (firstn p l) <= ZSum A.
Proof.
  induction l as [| x l' IH]; intros A B p Hmono Hperm Hlen.
  - apply Permutation_nil in Hperm.
    apply app_eq_nil in Hperm as [HA _]. subst A. simpl in Hlen. subst p.
    simpl. lia.
  - destruct p as [| p'].
    + destruct A as [| a A']; [| simpl in Hlen; lia].
      simpl. lia.
    + assert (HmonoL : Forall (fun y => x <= y) l' /\ mono_nondec l')
        by (apply mono_nondec_cons; exact Hmono).
      destruct HmonoL as [Hall Hmono'].
      assert (Hin : In x (A ++ B))
        by (eapply Permutation_in; [exact Hperm | left; reflexivity]).
      apply in_app_or in Hin. destruct Hin as [HinA | HinB].
      * apply in_split in HinA as [A1 [A2 HA]]. subst A.
        assert (Hp : Permutation l' (A1 ++ A2 ++ B)).
        { apply (Permutation_cons_inv (a := x)).
          eapply Permutation_trans; [exact Hperm |].
          rewrite <- app_assoc. simpl.
          apply Permutation_sym, Permutation_middle. }
        assert (HlenA : length (A1 ++ A2) = p').
        { rewrite length_app. rewrite length_app in Hlen.
          simpl in Hlen. lia. }
        rewrite app_assoc in Hp.
        specialize (IH (A1 ++ A2) B p' Hmono' Hp HlenA).
        assert (HsumA : ZSum (A1 ++ x :: A2) = x + ZSum (A1 ++ A2)).
        { rewrite !ZSum_app, ZSum_cons. lia. }
        simpl firstn. rewrite ZSum_cons. rewrite HsumA. lia.
      * apply in_split in HinB as [B1 [B2 HB]]. subst B.
        destruct A as [| a A']; [simpl in Hlen; lia |].
        assert (Hmid : Permutation (((a :: A') ++ B1) ++ x :: B2)
                                   (x :: (((a :: A') ++ B1) ++ B2)))
          by (apply Permutation_sym, Permutation_middle).
        assert (Hp : Permutation l' ((a :: A') ++ B1 ++ B2)).
        { apply (Permutation_cons_inv (a := x)).
          eapply Permutation_trans; [exact Hperm |].
          rewrite (app_assoc (a :: A') B1 (x :: B2)).
          eapply Permutation_trans; [exact Hmid |].
          rewrite <- app_assoc. apply Permutation_refl. }
        assert (Hax : x <= a).
        { assert (Hina : In a (x :: l')).
          { eapply Permutation_in;
              [apply Permutation_sym; exact Hperm |].
            apply in_or_app. left. left. reflexivity. }
          destruct Hina as [Heq | Hina]; [lia |].
          rewrite Forall_forall in Hall. apply Hall. exact Hina. }
        assert (HlenA' : length A' = p') by (simpl in Hlen; lia).
        assert (Hp2 : Permutation l' (A' ++ (a :: B1 ++ B2))).
        { eapply Permutation_trans; [exact Hp |].
          simpl. apply Permutation_middle. }
        specialize (IH A' (a :: B1 ++ B2) p' Hmono' Hp2 HlenA').
        simpl firstn. rewrite ZSum_cons, ZSum_cons. lia.
Qed.

(* A list is the map of its own index range: this is what lets a
   permutation of the distance list be traced back to a choice of types. *)
Lemma Zrange_aux_shift : forall n low,
  Zrange_aux (low + 1) n = map (fun j => j + 1) (Zrange_aux low n).
Proof.
  induction n as [| n IH]; intros low; simpl; [reflexivity |].
  f_equal. apply IH.
Qed.

Lemma map_Znth_Zrange_aux : forall (n : nat) (l : list Z),
  length l = n -> map (fun j => Znth j l 0) (Zrange_aux 0 n) = l.
Proof.
  induction n as [| n IH]; intros l Hlen.
  - destruct l; simpl in *; [reflexivity | discriminate].
  - destruct l as [| x l']; simpl in Hlen; [discriminate |].
    simpl Zrange_aux. simpl map. f_equal.
    replace 1 with (0 + 1) by lia.
    rewrite Zrange_aux_shift, map_map.
    transitivity (map (fun j => Znth j l' 0) (Zrange_aux 0 n)).
    + apply map_ext_in. intros j Hj.
      apply In_Zrange_aux in Hj.
      rewrite Znth_cons by lia. f_equal. lia.
    + apply IH. lia.
Qed.

Lemma map_Znth_Zrange : forall (l : list Z),
  map (fun j => Znth j l 0) (Zrange 0 (Zlength l)) = l.
Proof.
  intros l. unfold Zrange.
  rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length l) - 0)) with (length l) by lia.
  apply map_Znth_Zrange_aux. reflexivity.
Qed.

(* A duplicate-free selection out of a duplicate-free pool splits the pool. *)
Lemma nodup_incl_split : forall (a b : list Z),
  NoDup a -> NoDup b -> incl a b -> exists r, Permutation b (a ++ r).
Proof.
  induction a as [| x a' IH]; intros b Ha Hb Hincl.
  - exists b. simpl. apply Permutation_refl.
  - assert (Hxb : In x b) by (apply Hincl; left; reflexivity).
    apply in_split in Hxb as [b1 [b2 Hb_eq]]. subst b.
    assert (Hperm : Permutation (b1 ++ x :: b2) (x :: (b1 ++ b2)))
      by (apply Permutation_sym, Permutation_middle).
    assert (Hb' : NoDup (x :: (b1 ++ b2)))
      by (eapply Permutation_NoDup; [exact Hperm | exact Hb]).
    inversion Ha as [| x0 a0 Hnotin Ha']; subst.
    inversion Hb' as [| x1 b0 Hxnot Hb2]; subst.
    assert (Hincl' : incl a' (b1 ++ b2)).
    { intros y Hy.
      assert (Hyb : In y (b1 ++ x :: b2)) by (apply Hincl; right; exact Hy).
      assert (Hy2 : In y (x :: (b1 ++ b2)))
        by (eapply Permutation_in; [exact Hperm | exact Hyb]).
      destruct Hy2 as [Heq | Hy2]; [subst y; contradiction | exact Hy2]. }
    destruct (IH (b1 ++ b2) Ha' Hb2 Hincl') as [r Hr].
    exists r. eapply Permutation_trans; [exact Hperm |].
    simpl. apply perm_skip. exact Hr.
Qed.

Lemma list_eq_Znth : forall (l1 l2 : list Z),
  Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 -> Znth i l1 0 = Znth i l2 0) ->
  l1 = l2.
Proof.
  intros l1 l2 Hlen Hnth.
  rewrite !Zlength_correct in Hlen.
  apply (nth_ext l1 l2 0 0); [lia |].
  intros p Hp.
  specialize (Hnth (Z.of_nat p)).
  unfold Znth in Hnth. rewrite Nat2Z.id in Hnth.
  apply Hnth. rewrite Zlength_correct. lia.
Qed.

Lemma firstn_map_Z : forall (f : Z -> Z) (l : list Z) (p : nat),
  firstn p (map f l) = map f (firstn p l).
Proof.
  induction l as [| a l IHl]; intros p; destruct p; simpl; try reflexivity.
  f_equal. apply IHl.
Qed.

Lemma NoDup_map_shift : forall (l : list Z),
  NoDup l -> NoDup (map (fun j => j + 1) l).
Proof.
  intros l H. apply FinFun.Injective_map_NoDup; [| exact H].
  intros a b Hab. lia.
Qed.

Lemma sublist_0_firstn : forall (l : list Z) (p : Z),
  sublist 0 p l = firstn (Z.to_nat p) l.
Proof. intros. reflexivity. Qed.

(* A type whose distance subset has a minimum is really produced somewhere,
   hence lies in [1, k]. *)
Lemma TypeDistance_type_range : forall n k e goods v t d,
  n = Zlength goods ->
  (forall i, 0 <= i < n -> 1 <= Znth i goods 0 <= k) ->
  TypeDistance n e goods v t d -> 1 <= t <= k.
Proof.
  intros n k e goods v t d Hn Hg Htd.
  destruct Htd as [q [[Hq _] _]]. sets_unfold in Hq.
  destruct Hq as [src [Hsrc [Hgood _]]].
  rewrite <- Hgood. apply Hg. lia.
Qed.

Lemma perm_Zlength : forall (l1 l2 : list Z),
  Permutation l1 l2 -> Zlength l1 = Zlength l2.
Proof.
  intros l1 l2 H. rewrite !Zlength_correct. f_equal.
  apply Permutation_length. exact H.
Qed.

Lemma In_prefix : forall (p : nat) (l : list Z) x,
  In x (firstn p l) -> In x l.
Proof.
  induction p as [| p IH]; intros l x H; simpl in H; [contradiction |].
  destruct l as [| a l]; simpl in *; [contradiction |].
  destruct H as [H | H]; [left; exact H | right; eapply IH; exact H].
Qed.

Lemma NoDup_prefix : forall (p : nat) (l : list Z),
  NoDup l -> NoDup (firstn p l).
Proof.
  induction p as [| p IH]; intros l H; simpl; [constructor |].
  destruct l as [| a l]; simpl; [constructor |].
  inversion H as [| x0 l0 Hnotin Hnd]; subst. constructor.
  - intros Hin. apply Hnotin. eapply In_prefix; exact Hin.
  - apply IH. exact Hnd.
Qed.

Lemma len_firstn_Z : forall (p : nat) (l : list Z),
  length (firstn p l) = Nat.min p (length l).
Proof.
  induction p as [| p IH]; intros l; simpl; [reflexivity |].
  destruct l as [| a l]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma len_map_Z : forall (f : Z -> Z) (l : list Z),
  length (map f l) = length l.
Proof. intros f l. induction l; simpl; [reflexivity | rewrite IHl; reflexivity]. Qed.

Lemma Zlength_map_Z : forall (f : Z -> Z) (l : list Z),
  Zlength (map f l) = Zlength l.
Proof. intros. rewrite !Zlength_correct. f_equal. apply len_map_Z. Qed.

Lemma Znth_map_Z : forall (f : Z -> Z) (l : list Z) i d,
  0 <= i < Zlength l -> Znth i (map f l) d = f (Znth i l 0).
Proof.
  intros f l i d Hi. unfold Znth.
  rewrite Zlength_correct in Hi.
  rewrite nth_indep with (d' := f 0) by (rewrite len_map_Z; lia).
  rewrite map_nth. reflexivity.
Qed.

Theorem fair_cost_achievable :
  forall n s k e goods v dlst l1,
    1 <= v <= n ->
    1 <= s <= k ->
    Zlength dlst = k ->
    (forall j, 0 <= j < k -> BfsDist n e goods (j + 1) v (Znth j dlst 0)) ->
    Permutation dlst l1 ->
    FairCost n s e goods v (ZSum (sublist 0 s l1)).
Proof.
  intros n s k e goods v dlst l1 Hv Hs Hk Hdist Hperm.
  assert (Hmap : map (fun j => Znth j dlst 0) (Zrange 0 k) = dlst).
  { rewrite <- Hk. apply map_Znth_Zrange. }
  assert (Hperm2 : Permutation l1 (map (fun j => Znth j dlst 0) (Zrange 0 k))).
  { rewrite Hmap. apply Permutation_sym. exact Hperm. }
  apply Permutation_map_inv in Hperm2.
  destruct Hperm2 as [l3 [Hl3eq Hl3perm]].
  assert (Hnd3 : NoDup l3)
    by (eapply Permutation_NoDup; [exact Hl3perm | apply NoDup_Zrange]).
  assert (Hlen3 : Zlength l3 = k).
  { rewrite <- (perm_Zlength _ _ Hl3perm).
    rewrite <- (Zlength_map_Z (fun j => Znth j dlst 0) (Zrange 0 k)).
    rewrite Hmap. exact Hk. }
  assert (Hin3 : forall j, In j l3 -> 0 <= j < k).
  { intros j Hj. apply In_Zrange.
    eapply Permutation_in; [apply Permutation_sym; exact Hl3perm | exact Hj]. }
  assert (Hlen1 : Zlength l1 = k) by (rewrite <- (perm_Zlength _ _ Hperm); exact Hk).
  assert (Hlenf : Zlength (firstn (Z.to_nat s) l3) = s).
  { rewrite Zlength_correct, len_firstn_Z.
    rewrite Zlength_correct in Hlen3. lia. }
  assert (Hlenf1 : Zlength (firstn (Z.to_nat s) l1) = s).
  { rewrite Zlength_correct, len_firstn_Z.
    rewrite Zlength_correct in Hlen1. lia. }
  assert (Hfmap : firstn (Z.to_nat s) l1
                  = map (fun j => Znth j dlst 0) (firstn (Z.to_nat s) l3)).
  { rewrite Hl3eq. apply firstn_map_Z. }
  exists (map (fun j => j + 1) (firstn (Z.to_nat s) l3)),
         (firstn (Z.to_nat s) l1).
  split; [| split; [exact Hlenf1 | split]].
  - split; [| split].
    + rewrite Zlength_map_Z. exact Hlenf.
    + apply NoDup_map_shift. apply NoDup_prefix. exact Hnd3.
    + rewrite Forall_forall. intros x Hx.
      apply in_map_iff in Hx as [j [Hj Hin]]. subst x.
      assert (Hj3 : In j l3) by (eapply In_prefix; exact Hin).
      specialize (Hin3 j Hj3). lia.
  - intros i Hi.
    assert (Hjr : 0 <= Znth i (firstn (Z.to_nat s) l3) 0 < k).
    { apply Hin3. eapply In_prefix with (p := Z.to_nat s).
      apply Znth_In_Zlength. lia. }
    rewrite (Znth_map_Z (fun j => j + 1) (firstn (Z.to_nat s) l3) i 0)
      by lia.
    rewrite Hfmap.
    rewrite (Znth_map_Z (fun j => Znth j dlst 0) (firstn (Z.to_nat s) l3) i 0)
      by lia.
    apply TypeDistance_BfsDist; [exact Hv |].
    apply Hdist. exact Hjr.
  - rewrite sublist_0_firstn. reflexivity.
Qed.

Lemma In_Znth_Z : forall (l : list Z) x,
  In x l -> exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros l x H. apply (In_nth l x 0) in H as [p [Hp Hnth]].
  exists (Z.of_nat p). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.

Theorem fair_cost_optimal :
  forall n s k e goods v dlst l1 cost,
    1 <= v <= n ->
    n = Zlength goods ->
    1 <= s <= k ->
    (forall i, 0 <= i < n -> 1 <= Znth i goods 0 <= k) ->
    Zlength dlst = k ->
    (forall j, 0 <= j < k -> BfsDist n e goods (j + 1) v (Znth j dlst 0)) ->
    Permutation dlst l1 ->
    mono_nondec l1 ->
    FairCost n s e goods v cost ->
    ZSum (sublist 0 s l1) <= cost.
Proof.
  intros n s k e goods v dlst l1 cost Hv Hn Hs Hg Hk Hdist Hperm Hmono Hfc.
  destruct Hfc as [types [ds [[Hlent [Hndt Hpost]] [Hlends [Hi Hcost]]]]].
  assert (Ht : forall i, 0 <= i < s -> 1 <= Znth i types 0 <= k).
  { intros i Hii.
    eapply TypeDistance_type_range; [exact Hn | exact Hg | apply Hi; exact Hii]. }
  assert (Hds : forall i, 0 <= i < s ->
                  Znth i ds 0 = Znth (Znth i types 0 - 1) dlst 0).
  { intros i Hii.
    assert (Hbd : BfsDist n e goods (Znth i types 0) v (Znth i ds 0))
      by (apply TypeDistance_BfsDist; [exact Hv | apply Hi; exact Hii]).
    specialize (Hdist (Znth i types 0 - 1)).
    specialize (Ht i Hii).
    replace (Znth i types 0 - 1 + 1) with (Znth i types 0) in Hdist by lia.
    eapply BfsDist_unique; [exact Hbd | apply Hdist; lia]. }
  assert (Hmapds : map (fun t => Znth (t - 1) dlst 0) types = ds).
  { apply list_eq_Znth.
    - rewrite Zlength_map_Z. lia.
    - intros i Hii. rewrite Zlength_map_Z in Hii.
      rewrite (Znth_map_Z (fun t => Znth (t - 1) dlst 0) types i 0) by lia.
      symmetry. apply Hds. lia. }
  assert (Hndi : NoDup (map (fun t => t - 1) types)).
  { apply FinFun.Injective_map_NoDup; [| exact Hndt].
    intros a b Hab. lia. }
  assert (Hincl : incl (map (fun t => t - 1) types) (Zrange 0 k)).
  { intros j Hj. apply in_map_iff in Hj as [t [Hteq Hin]]. subst j.
    apply In_Znth_Z in Hin as [i [Hii Hnth]].
    rewrite Hlent in Hii. specialize (Ht i Hii). rewrite Hnth in Ht.
    apply In_Zrange. lia. }
  destruct (nodup_incl_split (map (fun t => t - 1) types) (Zrange 0 k)
              Hndi (NoDup_Zrange 0 k) Hincl) as [r Hr].
  assert (Hmap : map (fun j => Znth j dlst 0) (Zrange 0 k) = dlst).
  { rewrite <- Hk. apply map_Znth_Zrange. }
  assert (Hp2 : Permutation dlst (ds ++ map (fun j => Znth j dlst 0) r)).
  { assert (Hstep : Permutation
              (map (fun j => Znth j dlst 0) (Zrange 0 k))
              (map (fun j => Znth j dlst 0)
                   (map (fun t => t - 1) types ++ r)))
      by (apply Permutation_map; exact Hr).
    rewrite Hmap in Hstep.
    rewrite map_app, map_map in Hstep.
    rewrite Hmapds in Hstep. exact Hstep. }
  assert (Hp3 : Permutation l1 (ds ++ map (fun j => Znth j dlst 0) r)).
  { eapply Permutation_trans; [apply Permutation_sym; exact Hperm | exact Hp2]. }
  rewrite sublist_0_firstn, Hcost.
  change (fold_right Z.add 0 ds) with (ZSum ds).
  eapply sorted_prefix_min; [exact Hmono | exact Hp3 |].
  rewrite Zlength_correct in Hlends. lia.
Qed.

Theorem fair_cost_min :
  forall n s k e goods v dlst l1,
    1 <= v <= n ->
    n = Zlength goods ->
    1 <= s <= k ->
    (forall i, 0 <= i < n -> 1 <= Znth i goods 0 <= k) ->
    Zlength dlst = k ->
    (forall j, 0 <= j < k -> BfsDist n e goods (j + 1) v (Znth j dlst 0)) ->
    Permutation dlst l1 ->
    mono_nondec l1 ->
    min_value_of_subset Z.le (FairCost n s e goods v) (fun x => x)
      (ZSum (sublist 0 s l1)).
Proof.
  intros n s k e goods v dlst l1 Hv Hn Hs Hg Hk Hdist Hperm Hmono.
  exists (ZSum (sublist 0 s l1)). split; [split | reflexivity].
  - sets_unfold.
    apply (fair_cost_achievable n s k e goods v dlst l1 Hv Hs Hk Hdist Hperm).
  - intros b Hb. sets_unfold in Hb. simpl.
    apply (fair_cost_optimal n s k e goods v dlst l1 b
             Hv Hn Hs Hg Hk Hdist Hperm Hmono Hb).
Qed.

(* ================================================================= *)
(*  Bridge 2.  The three work arrays are the road list.               *)
(* ================================================================= *)

Lemma In_Znth_gen : forall {A : Type} (d : A) (l : list A) x,
  In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A d l x H. apply (In_nth l x d) in H as [p [Hp Hnth]].
  exists (Z.of_nat p). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.

(* Arc [2i] runs along road [i], arc [2i+1] runs back. *)
Lemma arc_edge_iff : forall (edges : list (Z * Z)%type) (m : Z),
  Zlength edges = m ->
  forall u w,
    ((In (u, w) edges \/ In (w, u) edges) <->
     (exists j, 0 <= j < 2 * m /\ ArcFrom edges j = u /\ ArcTo edges j = w)).
Proof.
  intros edges m Hm u w. split.
  - intros [Hin | Hin].
    + apply (In_Znth_gen (0, 0)) in Hin as [i [Hi Hnth]].
      exists (2 * i).
      assert (Heven : Z.even (2 * i) = true)
        by (rewrite Z.even_mul; reflexivity).
      assert (Hdiv : 2 * i / 2 = i)
        by (rewrite Z.mul_comm; apply Z.div_mul; lia).
      unfold ArcFrom, ArcTo. rewrite Heven, Hdiv, Hnth.
      split; [lia | simpl; split; reflexivity].
    + apply (In_Znth_gen (0, 0)) in Hin as [i [Hi Hnth]].
      exists (2 * i + 1).
      assert (Heven : Z.even (2 * i + 1) = false)
        by (rewrite Z.even_add, Z.even_mul; reflexivity).
      assert (Hdiv : (2 * i + 1) / 2 = i).
      { replace (2 * i + 1) with (i * 2 + 1) by lia.
        rewrite Z.div_add_l by lia. change (1 / 2) with 0. lia. }
      unfold ArcFrom, ArcTo. rewrite Heven, Hdiv, Hnth.
      split; [lia | simpl; split; reflexivity].
  - intros [j [Hj [Hfrom Hto]]].
    assert (Hi : 0 <= j / 2 < m).
    { split; [apply Z.div_pos; lia |].
      apply Z.div_lt_upper_bound; lia. }
    assert (Hin : In (Znth (j / 2) edges (0, 0)) edges)
      by (apply Znth_In_Zlength; lia).
    unfold ArcFrom, ArcTo in Hfrom, Hto.
    destruct (Z.even j).
    + left. replace (u, w) with (Znth (j / 2) edges (0, 0)); [exact Hin |].
      rewrite <- Hfrom, <- Hto. apply surjective_pairing.
    + right. replace (w, u) with (Znth (j / 2) edges (0, 0)); [exact Hin |].
      rewrite <- Hfrom, <- Hto. apply surjective_pairing.
Qed.

(* The chain hanging off [head_[u]] enumerates exactly the neighbours of [u]. *)
Lemma AdjList_covers : forall n m edges hd nx tlst u l w,
  Zlength edges = m ->
  AdjBuild n m edges hd nx tlst ->
  AdjListAt m edges hd nx u l ->
  ((In (u, w) edges \/ In (w, u) edges) <->
   (exists j, In j l /\ Znth j tlst 0 = w)).
Proof.
  intros n m edges hd nx tlst u l w Hm Hbuild Hlist.
  destruct Hbuild as (_ & _ & _ & Htl & _ & _ & _).
  destruct Hlist as (_ & _ & Hsound & Hcomplete).
  split.
  - intros Hedge.
    apply (arc_edge_iff edges m Hm) in Hedge as [j [Hj [Hfrom Hto]]].
    exists j. split; [apply Hcomplete; assumption |].
    rewrite Htl by exact Hj. exact Hto.
  - intros [j [Hin Hnth]].
    specialize (Hsound j Hin) as [Hj Hfrom].
    apply (arc_edge_iff edges m Hm).
    exists j. split; [exact Hj | split; [exact Hfrom |]].
    rewrite <- Hnth. symmetry. apply Htl. exact Hj.
Qed.

Lemma AdjChain_neg_nil : forall nx l, AdjChain nx (-1) l -> l = nil.
Proof.
  intros nx l H. inversion H as [| j l0 Hj Hrest]; [reflexivity | lia].
Qed.

(* ================================================================= *)
(*  Bridge 3.  When every queued town has been expanded, the row      *)
(*  holds the true multi-source distances.                            *)
(* ================================================================= *)

Lemma Bfs_reach_in_queue : forall n e goods c Q dl x y q,
  BfsCore n e goods c Q dl ->
  BfsExpanded n e Q dl (Zlength Q) ->
  path_of_zlen (TownGraph n e) x y q ->
  SrcSet n goods c x ->
  1 <= y <= n ->
  In y Q /\ Znth y dl 0 <= q.
Proof.
  intros n e goods c Q dl x y q Hcore Hexp Hpath.
  induction Hpath as [z | z w y0 d Hpath IH Hstep]; intros Hsrc Hy.
  - destruct Hsrc as [Hz Hgood].
    destruct Hcore as (_ & _ & _ & _ & _ & _ & _ & Hsrcq).
    specialize (Hsrcq z Hz Hgood). split; [tauto | lia].
  - apply TownGraph_step_iff in Hstep as [Hedge [Hw Hy0]].
    destruct (IH Hsrc Hw) as [Hin Hle].
    apply In_Znth_Z in Hin as [i [Hi Hnth]].
    specialize (Hexp i y0 Hi Hy).
    rewrite Hnth in Hexp. specialize (Hexp Hedge).
    split; [tauto | lia].
Qed.

Theorem BfsCore_expanded_result : forall n e goods c Q dl,
  Zlength Q <= n ->
  BfsCore n e goods c Q dl ->
  BfsExpanded n e Q dl (Zlength Q) ->
  BfsRowResult n e goods c dl.
Proof.
  intros n e goods c Q dl Hqn Hcore Hexp v Hv.
  destruct (in_dec Z.eq_dec v Q) as [Hin | Hnotin].
  - right.
    pose proof Hcore as Hcore'.
    destruct Hcore' as (_ & _ & _ & _ & Hreal & _ & Hbnd & _).
    apply In_Znth_Z in Hin as [i [Hi Hnth]].
    assert (Hb : 0 <= Znth (Znth i Q 0) dl 0 <= i) by (apply Hbnd; exact Hi).
    rewrite Hnth in Hb.
    split; [lia |].
    split.
    + specialize (Hreal i Hi). rewrite Hnth in Hreal. exact Hreal.
    + intros q [u [Hsrc Hpath]].
      destruct (Bfs_reach_in_queue n e goods c Q dl u v q
                  Hcore Hexp Hpath Hsrc Hv) as [_ Hle]. exact Hle.
  - left.
    pose proof Hcore as Hcore'.
    destruct Hcore' as (_ & _ & _ & Hminus & _).
    split; [apply Hminus; assumption |].
    intros [q [u [Hsrc Hpath]]].
    destruct (Bfs_reach_in_queue n e goods c Q dl u v q
                Hcore Hexp Hpath Hsrc Hv) as [Hin _].
    contradiction.
Qed.

(* Every type is produced somewhere and the road network is connected, so
   no town is ever left at [-1]. *)
Lemma MReach_exists : forall k s n e goods c v,
  Pre k s e goods -> n = Zlength goods -> 1 <= c <= k -> 1 <= v <= n ->
  exists q, MReach n e goods c v q.
Proof.
  intros k s n e goods c v [Hall [Hconn _]] Hn Hc Hv.
  destruct (In_Znth_Z goods c (Hall c Hc)) as [i [Hi Hnth]].
  assert (Hsrc : SrcSet n goods c (i + 1)).
  { unfold SrcSet. split; [lia |].
    replace (i + 1 - 1) with i by lia. exact Hnth. }
  assert (Hreach : reachable (TownGraph n e) (i + 1) v).
  { rewrite Hn in *. apply Hconn; simpl; lia. }
  apply reachable_path_of_zlen in Hreach as [q Hpath].
  exists q, (i + 1). split; [exact Hsrc | exact Hpath].
Qed.

Theorem BfsRowResult_total : forall k s n e goods c dl v,
  Pre k s e goods -> n = Zlength goods -> 1 <= c <= k -> 1 <= v <= n ->
  BfsRowResult n e goods c dl ->
  0 <= Znth v dl 0 <= n - 1 /\ BfsDist n e goods c v (Znth v dl 0).
Proof.
  intros k s n e goods c dl v Hpre Hn Hc Hv Hres.
  destruct (Hres v Hv) as [[_ Hnone] | Hgood]; [| exact Hgood].
  exfalso. apply Hnone.
  eapply MReach_exists; eauto.
Qed.

(* Collecting the sources gives a legal initial BFS state. *)
Theorem BfsInit_BfsCore : forall n e goods c Q dl,
  BfsInit n goods c Q dl (n + 1) ->
  BfsCore n e goods c Q dl /\ BfsExpanded n e Q dl 0.
Proof.
  intros n e goods c Q dl [Hnd [Hsrc [Hoth [Hrest Hmem]]]].
  assert (Hz : forall i, 0 <= i < Zlength Q -> Znth (Znth i Q 0) dl 0 = 0)
    by (intros i Hi; apply (Hmem i Hi)).
  assert (Hb : forall i, 0 <= i < Zlength Q -> 1 <= Znth i Q 0 <= n).
  { intros i Hi. specialize (Hmem i Hi). lia. }
  assert (Hin : forall v, 1 <= v <= n -> In v Q -> Znth v dl 0 = 0).
  { intros v Hv Hv2. apply In_Znth_Z in Hv2 as [i [Hi Hnth]].
    rewrite <- Hnth. apply Hz. exact Hi. }
  split; [| intros i w Hi; lia].
  split; [exact Hb | split; [exact Hnd | split; [| split; [| split; [| split; [| split]]]]]].
  - intros v Hv. split.
    + intros Hv2. rewrite (Hin v Hv Hv2). lia.
    + intros Hge.
      destruct (Z.eq_dec (Znth (v - 1) goods 0) c) as [Heq | Hne].
      * apply (Hsrc v ltac:(lia) Heq).
      * specialize (Hoth v ltac:(lia) Hne). lia.
  - intros v Hv Hnotin.
    destruct (Z.eq_dec (Znth (v - 1) goods 0) c) as [Heq | Hne].
    + exfalso. apply Hnotin. apply (Hsrc v ltac:(lia) Heq).
    + apply Hoth; [lia | exact Hne].
  - intros i Hi. specialize (Hmem i Hi) as [Hr [Hg Hd]].
    rewrite Hd. exists (Znth i Q 0). split.
    + unfold SrcSet. split; [lia | exact Hg].
    + apply pozl_0.
  - intros i j Hi Hij Hj.
    rewrite (Hz i ltac:(lia)), (Hz j ltac:(lia)). lia.
  - intros i Hi. rewrite (Hz i Hi). lia.
  - intros v Hv Hg. split.
    + apply (Hsrc v ltac:(lia) Hg).
    + apply Hin; [lia | apply (Hsrc v ltac:(lia) Hg)].
Qed.

(* When the arc scan of [u] runs out, [u] joins the expanded prefix. *)
Theorem BfsScan_expand : forall n m edges hd nx tlst Q dl qh u,
  Zlength edges = m ->
  AdjBuild n m edges hd nx tlst ->
  1 <= qh <= Zlength Q ->
  u = Znth (qh - 1) Q 0 ->
  BfsExpanded n edges Q dl (qh - 1) ->
  BfsScan m edges nx tlst Q dl u (-1) ->
  BfsExpanded n edges Q dl qh.
Proof.
  intros n m edges hd nx tlst Q dl qh u Hm Hbuild Hqh Hu Hexp Hscan.
  intros i w Hi Hw Hedge.
  destruct (Z_lt_ge_dec i (qh - 1)) as [Hlt | Hge].
  - apply Hexp; [lia | exact Hw | exact Hedge].
  - assert (Hieq : i = qh - 1) by lia. subst i.
    rewrite <- Hu in *.
    destruct Hscan as [lrem [Hchain [_ Hrelaxed]]].
    apply AdjChain_neg_nil in Hchain. subst lrem.
    destruct Hbuild as (_ & _ & _ & Htl & _ & _ & Hlists).
    apply (arc_edge_iff edges m Hm) in Hedge as [j [Hj [Hfrom Hto]]].
    specialize (Hrelaxed j Hj Hfrom (fun H => H)).
    rewrite (Htl j Hj), Hto in Hrelaxed. exact Hrelaxed.
Qed.

(* The finished [cost] prefix is exactly the public [Spec]. *)
Theorem OutPrefix_Spec : forall n s k e goods out,
  n = Zlength goods ->
  Zlength out = n ->
  OutPrefix n s e goods out n ->
  Spec k s e goods out.
Proof.
  intros n s k e goods out Hn Hlen Hout.
  unfold Spec. split; [lia |].
  intros i Hi. rewrite <- Hn in *. apply Hout. exact Hi.
Qed.

(* Entry, step and exit of the inner arc scan. *)
Lemma AdjChain_cons_inv : forall nx j l,
  j <> -1 -> AdjChain nx j l ->
  exists l', l = j :: l' /\ 0 <= j < Zlength nx /\ AdjChain nx (Znth j nx 0) l'.
Proof.
  intros nx j l Hj H. destruct H as [| j0 l0 Hr Hrest].
  - contradiction.
  - exists l0. split; [reflexivity | split; [exact Hr | exact Hrest]].
Qed.

Lemma BfsScan_entry : forall n done edges hd nx tlst Q dl u,
  AdjBuild n done edges hd nx tlst ->
  1 <= u <= n ->
  BfsScan done edges nx tlst Q dl u (Znth (u - 1) hd 0).
Proof.
  intros n done edges hd nx tlst Q dl u Hbuild Hu.
  destruct Hbuild as (_ & _ & _ & _ & _ & _ & Hlists).
  destruct (Hlists u Hu) as [l [Hchain [_ [Hsound Hcomplete]]]].
  exists l. split; [exact Hchain | split; [exact Hsound |]].
  intros j Hj Hfrom Hnot. exfalso. apply Hnot. apply Hcomplete; assumption.
Qed.

(* One arc is relaxed and the cursor advances; the queue may have grown and
   the distance row may have been updated at the newly discovered town, which
   the frame hypotheses allow for. *)
Lemma BfsScan_step : forall done edges nx tlst Q dl Q' dl' u cur,
  cur <> -1 ->
  BfsScan done edges nx tlst Q dl u cur ->
  (forall w, In w Q -> In w Q') ->
  (forall w, In w Q -> Znth w dl' 0 = Znth w dl 0) ->
  Znth u dl' 0 = Znth u dl 0 ->
  In (Znth cur tlst 0) Q' ->
  Znth (Znth cur tlst 0) dl' 0 <= Znth u dl' 0 + 1 ->
  BfsScan done edges nx tlst Q' dl' u (Znth cur nx 0).
Proof.
  intros done edges nx tlst Q dl Q' dl' u cur Hcur Hscan
         HQ Hdl Hu Hin Hle.
  destruct Hscan as [lrem [Hchain [Hmem Hrelaxed]]].
  destruct (AdjChain_cons_inv nx cur lrem Hcur Hchain)
    as [l' [Heq [Hrange Hrest]]]. subst lrem.
  exists l'. split; [exact Hrest | split].
  - intros j Hj. apply Hmem. right. exact Hj.
  - intros j Hj Hfrom Hnot.
    destruct (Z.eq_dec j cur) as [Hjc | Hjc].
    + subst j. split; [exact Hin | exact Hle].
    + assert (Hnot2 : ~ In j (cur :: l'))
        by (intros [Hc | Hc]; [apply Hjc; symmetry; exact Hc | contradiction]).
      destruct (Hrelaxed j Hj Hfrom Hnot2) as [HinQ Hleq].
      split; [apply HQ; exact HinQ |].
      rewrite (Hdl _ HinQ), Hu. exact Hleq.
Qed.

Lemma AdjChain_ext__g1_adjacency_build : forall (nx ext : list Z) (j : Z) (l : list Z),
  AdjChain nx j l -> AdjChain (nx ++ ext) j l.
Proof.
  intros nx ext j l H.
  induction H.
  - apply AdjChain_nil.
  - apply AdjChain_cons.
    + rewrite Zlength_app.
      pose proof (Zlength_nonneg ext). lia.
    + rewrite (app_Znth1 0 nx ext j) by lia.
      exact IHAdjChain.
Qed.
Lemma ArcIdx_even__g1_adjacency_build : forall (edges : list (Z * Z)%type) (i : Z),
  0 <= i ->
  ArcFrom edges (2 * i) = fst (Znth i edges (0, 0)) /\
  ArcTo edges (2 * i) = snd (Znth i edges (0, 0)).
Proof.
  intros edges i Hi.
  assert (He : Z.even (2 * i) = true) by (rewrite Z.even_mul; reflexivity).
  assert (Hd : 2 * i / 2 = i) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
  unfold ArcFrom, ArcTo. rewrite He, Hd. split; reflexivity.
Qed.
Lemma ArcIdx_odd__g1_adjacency_build : forall (edges : list (Z * Z)%type) (i : Z),
  0 <= i ->
  ArcFrom edges (2 * i + 1) = snd (Znth i edges (0, 0)) /\
  ArcTo edges (2 * i + 1) = fst (Znth i edges (0, 0)).
Proof.
  intros edges i Hi.
  assert (He : Z.even (2 * i + 1) = false).
  { rewrite Z.even_add. rewrite Z.even_mul. reflexivity. }
  assert (Hd : (2 * i + 1) / 2 = i).
  { replace (2 * i + 1) with (i * 2 + 1) by lia.
    rewrite Z.div_add_l by lia.
    replace (1 / 2) with 0 by reflexivity. lia. }
  unfold ArcFrom, ArcTo. rewrite He, Hd. split; reflexivity.
Qed.
Lemma AdjBuild_insert__g1_adjacency_build :
  forall (n i : Z) (edges : list (Z * Z)%type) (hd nx tlst hd' : list Z) (u w a b : Z),
    0 <= i ->
    AdjBuild n i edges hd nx tlst ->
    1 <= u <= n -> 1 <= w <= n -> u <> w ->
    fst (Znth i edges (0, 0)) = u ->
    snd (Znth i edges (0, 0)) = w ->
    Zlength hd' = n ->
    Znth (u - 1) hd' 0 = 2 * i ->
    Znth (w - 1) hd' 0 = 2 * i + 1 ->
    (forall x, 1 <= x <= n -> x <> u -> x <> w ->
       Znth (x - 1) hd' 0 = Znth (x - 1) hd 0) ->
    Znth (u - 1) hd 0 = a ->
    Znth (w - 1) hd 0 = b ->
    AdjBuild n (i + 1) edges hd'
      ((nx ++ (a :: nil)) ++ (b :: nil))
      ((tlst ++ (w :: nil)) ++ (u :: nil)).
Proof.
  intros n i edges hd nx tlst hd' u w a b Hi HB Hu Hw Huw Hfst Hsnd
         Hlhd' Hhu Hhw Hother Ha Hb.
  destruct HB as [Hlhd [Hlnx [Hltl [Htl [Hnxr [Hhdr Hlists]]]]]].
  pose proof (ArcIdx_even__g1_adjacency_build edges i Hi) as [Hfe Hte].
  pose proof (ArcIdx_odd__g1_adjacency_build edges i Hi) as [Hfo Hto].
  rewrite Hfst in Hfe. rewrite Hsnd in Hte.
  rewrite Hsnd in Hfo. rewrite Hfst in Hto.
  assert (Hlnx' : Zlength ((nx ++ (a :: nil)) ++ (b :: nil)) = 2 * i + 2).
  { rewrite !Zlength_app_cons. lia. }
  assert (Hltl' : Zlength ((tlst ++ (w :: nil)) ++ (u :: nil)) = 2 * i + 2).
  { rewrite !Zlength_app_cons. lia. }
  assert (Hnx1 : forall j, 0 <= j < 2 * i ->
            Znth j ((nx ++ (a :: nil)) ++ (b :: nil)) 0 = Znth j nx 0).
  { intros j Hj.
    rewrite (app_Znth1 0 (nx ++ (a :: nil)) (b :: nil) j)
      by (rewrite Zlength_app_cons; lia).
    rewrite (app_Znth1 0 nx (a :: nil) j) by lia. reflexivity. }
  assert (Hnx2 : Znth (2 * i) ((nx ++ (a :: nil)) ++ (b :: nil)) 0 = a).
  { rewrite (app_Znth1 0 (nx ++ (a :: nil)) (b :: nil) (2 * i))
      by (rewrite Zlength_app_cons; lia).
    rewrite (app_Znth2 0 nx (a :: nil) (2 * i)) by lia.
    rewrite Hlnx. replace (2 * i - 2 * i) with 0 by lia. reflexivity. }
  assert (Hnx3 : Znth (2 * i + 1) ((nx ++ (a :: nil)) ++ (b :: nil)) 0 = b).
  { rewrite (app_Znth2 0 (nx ++ (a :: nil)) (b :: nil) (2 * i + 1))
      by (rewrite Zlength_app_cons; lia).
    rewrite Zlength_app_cons, Hlnx.
    replace (2 * i + 1 - (2 * i + 1)) with 0 by lia. reflexivity. }
  assert (Htl1 : forall j, 0 <= j < 2 * i ->
            Znth j ((tlst ++ (w :: nil)) ++ (u :: nil)) 0 = Znth j tlst 0).
  { intros j Hj.
    rewrite (app_Znth1 0 (tlst ++ (w :: nil)) (u :: nil) j)
      by (rewrite Zlength_app_cons; lia).
    rewrite (app_Znth1 0 tlst (w :: nil) j) by lia. reflexivity. }
  assert (Htl2 : Znth (2 * i) ((tlst ++ (w :: nil)) ++ (u :: nil)) 0 = w).
  { rewrite (app_Znth1 0 (tlst ++ (w :: nil)) (u :: nil) (2 * i))
      by (rewrite Zlength_app_cons; lia).
    rewrite (app_Znth2 0 tlst (w :: nil) (2 * i)) by lia.
    rewrite Hltl. replace (2 * i - 2 * i) with 0 by lia. reflexivity. }
  assert (Htl3 : Znth (2 * i + 1) ((tlst ++ (w :: nil)) ++ (u :: nil)) 0 = u).
  { rewrite (app_Znth2 0 (tlst ++ (w :: nil)) (u :: nil) (2 * i + 1))
      by (rewrite Zlength_app_cons; lia).
    rewrite Zlength_app_cons, Hltl.
    replace (2 * i + 1 - (2 * i + 1)) with 0 by lia. reflexivity. }
  assert (Hlift : forall j l, AdjChain nx j l ->
            AdjChain ((nx ++ (a :: nil)) ++ (b :: nil)) j l).
  { intros j l Hc.
    apply AdjChain_ext__g1_adjacency_build.
    apply AdjChain_ext__g1_adjacency_build. exact Hc. }
  unfold AdjBuild.
  split; [exact Hlhd' | ].
  split; [rewrite Hlnx'; lia | ].
  split; [rewrite Hltl'; lia | ].
  split.
  { intros j Hj.
    destruct (Z.lt_ge_cases j (2 * i)) as [Hlt | Hge].
    - rewrite Htl1 by lia. apply Htl. lia.
    - destruct (Z.eq_dec j (2 * i)) as [He | He].
      + subst j. rewrite Htl2. symmetry. exact Hte.
      + assert (Hj1 : j = 2 * i + 1) by lia. subst j.
        rewrite Htl3. symmetry. exact Hto. }
  split.
  { intros j Hj.
    destruct (Z.lt_ge_cases j (2 * i)) as [Hlt | Hge].
    - rewrite Hnx1 by lia.
      destruct (Hnxr j ltac:(lia)) as [Hc | Hc]; [left; exact Hc | right; lia].
    - destruct (Z.eq_dec j (2 * i)) as [He | He].
      + subst j. rewrite Hnx2. rewrite <- Ha.
        destruct (Hhdr u Hu) as [Hc | Hc]; [left; exact Hc | right; lia].
      + assert (Hj1 : j = 2 * i + 1) by lia. subst j.
        rewrite Hnx3. rewrite <- Hb.
        destruct (Hhdr w Hw) as [Hc | Hc]; [left; exact Hc | right; lia]. }
  split.
  { intros x Hx.
    destruct (Z.eq_dec x u) as [Hxu | Hxu].
    - subst x. rewrite Hhu. right. lia.
    - destruct (Z.eq_dec x w) as [Hxw | Hxw].
      + subst x. rewrite Hhw. right. lia.
      + rewrite (Hother x Hx Hxu Hxw).
        destruct (Hhdr x Hx) as [Hc | Hc]; [left; exact Hc | right; lia]. }
  intros x Hx.
  destruct (Hlists x Hx) as [l [Hchain [Hnd [Hsound Hcomp]]]].
  destruct (Z.eq_dec x u) as [Hxu | Hxu].
  - subst x. rewrite Ha in Hchain.
    exists (2 * i :: l). unfold AdjListAt.
    split.
    { rewrite Hhu. apply AdjChain_cons.
      - rewrite Hlnx'. lia.
      - rewrite Hnx2. apply Hlift. exact Hchain. }
    split.
    { constructor.
      - intros Hin. destruct (Hsound _ Hin) as [Hr _]. lia.
      - exact Hnd. }
    split.
    { intros j [Hj | Hj].
      - subst j. split; [lia | exact Hfe].
      - destruct (Hsound _ Hj) as [Hr Hf]. split; [lia | exact Hf]. }
    { intros j Hj Hf.
      destruct (Z.lt_ge_cases j (2 * i)) as [Hlt | Hge].
      - right. apply Hcomp; [lia | exact Hf].
      - destruct (Z.eq_dec j (2 * i)) as [He | He].
        + left. lia.
        + assert (Hj1 : j = 2 * i + 1) by lia. subst j.
          rewrite Hfo in Hf. exfalso. apply Huw. symmetry. exact Hf. }
  - destruct (Z.eq_dec x w) as [Hxw | Hxw].
    + subst x. rewrite Hb in Hchain.
      exists (2 * i + 1 :: l). unfold AdjListAt.
      split.
      { rewrite Hhw. apply AdjChain_cons.
        - rewrite Hlnx'. lia.
        - rewrite Hnx3. apply Hlift. exact Hchain. }
      split.
      { constructor.
        - intros Hin. destruct (Hsound _ Hin) as [Hr _]. lia.
        - exact Hnd. }
      split.
      { intros j [Hj | Hj].
        - subst j. split; [lia | exact Hfo].
        - destruct (Hsound _ Hj) as [Hr Hf]. split; [lia | exact Hf]. }
      { intros j Hj Hf.
        destruct (Z.lt_ge_cases j (2 * i)) as [Hlt | Hge].
        - right. apply Hcomp; [lia | exact Hf].
        - destruct (Z.eq_dec j (2 * i)) as [He | He].
          + subst j. rewrite Hfe in Hf. exfalso. apply Huw. exact Hf.
          + assert (Hj1 : j = 2 * i + 1) by lia. subst j. left. lia. }
    + exists l. unfold AdjListAt.
      split.
      { rewrite (Hother x Hx Hxu Hxw). apply Hlift. exact Hchain. }
      split; [exact Hnd | ].
      split.
      { intros j Hj. destruct (Hsound _ Hj) as [Hr Hf]. split; [lia | exact Hf]. }
      { intros j Hj Hf.
        destruct (Z.lt_ge_cases j (2 * i)) as [Hlt | Hge].
        - apply Hcomp; [lia | exact Hf].
        - destruct (Z.eq_dec j (2 * i)) as [He | He].
          + subst j. rewrite Hfe in Hf. exfalso. apply Hxu. symmetry. exact Hf.
          + assert (Hj1 : j = 2 * i + 1) by lia. subst j.
            rewrite Hfo in Hf. exfalso. apply Hxw. symmetry. exact Hf. }
Qed.
Lemma app2_Znth_lt__g1_adjacency_build : forall (l : list Z) (x y j : Z),
  0 <= j < Zlength l ->
  Znth j ((l ++ (x :: nil)) ++ (y :: nil)) 0 = Znth j l 0.
Proof.
  intros l x y j Hj.
  rewrite (app_Znth1 0 (l ++ (x :: nil)) (y :: nil) j)
    by (rewrite Zlength_app_cons; lia).
  rewrite (app_Znth1 0 l (x :: nil) j) by lia. reflexivity.
Qed.
Lemma app2_Znth_fst__g1_adjacency_build : forall (l : list Z) (x y : Z),
  Znth (Zlength l) ((l ++ (x :: nil)) ++ (y :: nil)) 0 = x.
Proof.
  intros l x y.
  pose proof (Zlength_nonneg l).
  rewrite (app_Znth1 0 (l ++ (x :: nil)) (y :: nil) (Zlength l))
    by (rewrite Zlength_app_cons; lia).
  rewrite (app_Znth2 0 l (x :: nil) (Zlength l)) by lia.
  replace (Zlength l - Zlength l) with 0 by lia. reflexivity.
Qed.
Lemma app2_Znth_snd__g1_adjacency_build : forall (l : list Z) (x y : Z),
  Znth (Zlength l + 1) ((l ++ (x :: nil)) ++ (y :: nil)) 0 = y.
Proof.
  intros l x y.
  pose proof (Zlength_nonneg l).
  rewrite (app_Znth2 0 (l ++ (x :: nil)) (y :: nil) (Zlength l + 1))
    by (rewrite Zlength_app_cons; lia).
  rewrite Zlength_app_cons.
  replace (Zlength l + 1 - (Zlength l + 1)) with 0 by lia. reflexivity.
Qed.
Lemma NoDup_app_single__g2_bfs_init : forall (l : list Z) (x : Z),
  NoDup l -> ~ In x l -> NoDup (l ++ x :: nil).
Proof.
  induction l as [| a l IH]; intros x Hnd Hnin; simpl.
  - apply NoDup_cons; [simpl; tauto | apply NoDup_nil].
  - inversion Hnd; subst. apply NoDup_cons.
    + intros Hin. apply in_app_iff in Hin as [Hin | Hin].
      * contradiction.
      * simpl in Hin. destruct Hin as [Heq | Hfalse].
        { apply Hnin. left. symmetry. exact Heq. }
        { destruct Hfalse. }
    + apply IH; [assumption |].
      intros Hin. apply Hnin. right. exact Hin.
Qed.
Lemma BfsInit_push__g2_bfs_init : forall n goods c Q dl v,
  BfsInit n goods c Q dl v ->
  1 <= v <= n ->
  n < Zlength dl ->
  Znth (v - 1) goods 0 = c ->
  BfsInit n goods c (Q ++ v :: nil) (replace_Znth v 0 dl) (v + 1).
Proof.
  intros n goods c Q dl v [Hnd [Hsrc [Hoth [Hrest Hmem]]]] Hv Hdl Hg.
  assert (Hvlt : 0 <= v < Zlength dl) by lia.
  assert (Hnotin : ~ In v Q).
  { intros Hin. apply In_Znth_Z in Hin as [i [Hi Hnth]].
    destruct (Hmem i Hi) as [Hb _]. rewrite Hnth in Hb. lia. }
  assert (Hlen : Zlength (Q ++ v :: nil) = Zlength Q + 1)
    by (apply Zlength_app_cons).
  split; [| split; [| split; [| split]]].
  - apply NoDup_app_single__g2_bfs_init; assumption.
  - intros w Hw Hwg.
    destruct (Z.eq_dec w v) as [Heq | Hne].
    + subst w. split.
      * apply in_or_app. right. left. reflexivity.
      * apply Znth_replace_Znth_Same. exact Hvlt.
    + destruct (Hsrc w ltac:(lia) Hwg) as [Hin Hd]. split.
      * apply in_or_app. left. exact Hin.
      * rewrite (Znth_replace_Znth_Diff 0 dl v w 0) by lia. exact Hd.
  - intros w Hw Hwg.
    destruct (Z.eq_dec w v) as [Heq | Hne].
    + subst w. contradiction.
    + rewrite (Znth_replace_Znth_Diff 0 dl v w 0) by lia.
      apply Hoth; [lia | exact Hwg].
  - intros w Hw.
    rewrite (Znth_replace_Znth_Diff 0 dl v w 0) by lia.
    apply Hrest. lia.
  - intros i Hi. rewrite Hlen in Hi.
    destruct (Z_lt_ge_dec i (Zlength Q)) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      destruct (Hmem i ltac:(lia)) as [Hb [Hgo Hd]].
      split; [lia | split; [exact Hgo |]].
      rewrite (Znth_replace_Znth_Diff 0 dl v (Znth i Q 0) 0) by lia.
      exact Hd.
    + assert (Hieq : i = Zlength Q) by lia. subst i.
      rewrite app_Znth2 by lia.
      rewrite Z.sub_diag.
      replace (Znth 0 (v :: nil) 0) with v by reflexivity.
      split; [lia | split; [exact Hg |]].
      apply Znth_replace_Znth_Same. exact Hvlt.
Qed.
Lemma BfsInit_skip__g2_bfs_init : forall n goods c Q dl v,
  BfsInit n goods c Q dl v ->
  1 <= v <= n ->
  Znth (v - 1) goods 0 <> c ->
  BfsInit n goods c Q dl (v + 1).
Proof.
  intros n goods c Q dl v [Hnd [Hsrc [Hoth [Hrest Hmem]]]] Hv Hg.
  split; [exact Hnd | split; [| split; [| split]]].
  - intros w Hw Hwg.
    destruct (Z.eq_dec w v) as [Heq | Hne].
    + subst w. contradiction.
    + apply Hsrc; [lia | exact Hwg].
  - intros w Hw Hwg.
    destruct (Z.eq_dec w v) as [Heq | Hne].
    + subst w. apply Hrest. lia.
    + apply Hoth; [lia | exact Hwg].
  - intros w Hw. apply Hrest. lia.
  - intros i Hi. destruct (Hmem i Hi) as [Hb [Hgo Hd]].
    split; [lia | split; [exact Hgo | exact Hd]].
Qed.
Lemma BfsInit_nil__g2_bfs_init : forall n goods c dl,
  (forall w, 1 <= w <= n -> Znth w dl 0 = -1) ->
  BfsInit n goods c nil dl 1.
Proof.
  intros n goods c dl Hall.
  split; [apply NoDup_nil | split; [| split; [| split]]].
  - intros w Hw Hwg. lia.
  - intros w Hw Hwg. lia.
  - intros w Hw. apply Hall. lia.
  - intros i Hi. rewrite Zlength_nil in Hi. lia.
Qed.
Lemma BfsInit_BfsBounded__g2_bfs_init : forall n goods c Q dl v b,
  BfsInit n goods c Q dl v ->
  0 <= b ->
  BfsBounded Q dl b.
Proof.
  intros n goods c Q dl v b [Hnd [Hsrc [Hoth [Hrest Hmem]]]] Hb.
  intros j Hj. destruct (Hmem j Hj) as [_ [_ Hd]]. lia.
Qed.
Lemma BfsInit_head_dist__g2_bfs_init : forall n goods c Q dl v,
  BfsInit n goods c Q dl v ->
  0 < Zlength Q ->
  Znth (Znth 0 Q 0) dl 0 = 0.
Proof.
  intros n goods c Q dl v [Hnd [Hsrc [Hoth [Hrest Hmem]]]] HQ.
  destruct (Hmem 0 ltac:(lia)) as [_ [_ Hd]]. exact Hd.
Qed.
Lemma Zlength_push__g3_bfs_scan_core : forall (Q : list Z) w,
  Zlength (Q ++ w :: nil) = Zlength Q + 1.
Proof. intros Q w. apply Zlength_app_cons. Qed.
Lemma Znth_prefix_push__g3_bfs_scan_core : forall (Q : list Z) w i,
  0 <= i < Zlength Q -> Znth i (Q ++ w :: nil) 0 = Znth i Q 0.
Proof. intros Q w i Hi. apply app_Znth1. exact Hi. Qed.
Lemma Znth_last_push__g3_bfs_scan_core : forall (Q : list Z) w,
  Znth (Zlength Q) (Q ++ w :: nil) 0 = w.
Proof.
  intros Q w. rewrite app_Znth2 by lia.
  replace (Zlength Q - Zlength Q) with 0 by lia.
  reflexivity.
Qed.
Lemma In_push__g3_bfs_scan_core : forall (Q : list Z) w v,
  In v (Q ++ w :: nil) <-> (In v Q \/ v = w).
Proof.
  intros Q w v. split.
  - intros HH. apply in_app_or in HH. destruct HH as [HH | HH].
    + left. exact HH.
    + simpl in HH. destruct HH as [HH | HH]; [right; symmetry; exact HH | contradiction].
  - intros [HH | HH].
    + apply in_or_app. left. exact HH.
    + apply in_or_app. right. left. symmetry. exact HH.
Qed.
Lemma Zlength_Zrange_aux__g3_bfs_scan_core : forall (k : nat) (lo : Z),
  Zlength (Zrange_aux lo k) = Z.of_nat k.
Proof.
  induction k as [| k IH]; intros lo; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__g3_bfs_scan_core : forall lo hi,
  lo <= hi -> Zlength (Zrange lo hi) = hi - lo.
Proof.
  intros lo hi H. unfold Zrange.
  rewrite Zlength_Zrange_aux__g3_bfs_scan_core.
  rewrite Z2Nat.id by lia. lia.
Qed.
Lemma queue_room__g3_bfs_scan_core : forall (Q : list Z) (n w : Z),
  (forall i, 0 <= i < Zlength Q -> 1 <= Znth i Q 0 <= n) ->
  NoDup Q -> 1 <= w <= n -> ~ In w Q -> Zlength Q < n.
Proof.
  intros Q n w Hb Hnd Hw Hnin.
  assert (Hincl : incl Q (Zrange 1 (n + 1))).
  { intros x Hx. rewrite <- In_Zrange.
    apply In_Znth_Z in Hx as [i [Hi Hnth]].
    specialize (Hb i Hi). lia. }
  destruct (nodup_incl_split Q (Zrange 1 (n + 1)) Hnd
              (NoDup_Zrange 1 (n + 1)) Hincl) as [r Hperm].
  assert (Hwin : In w (Zrange 1 (n + 1))) by (rewrite <- In_Zrange; lia).
  assert (Hwr : In w r).
  { pose proof (Permutation_in w Hperm Hwin) as HH.
    apply in_app_or in HH. destruct HH as [HH | HH]; [contradiction | exact HH]. }
  assert (Hrlen : 1 <= Zlength r).
  { destruct r as [| a r']; [simpl in Hwr; contradiction |].
    rewrite Zlength_cons. pose proof (Zlength_nonneg r'). lia. }
  pose proof (perm_Zlength _ _ Hperm) as Hlen.
  rewrite Zlength_app in Hlen.
  rewrite Zlength_Zrange__g3_bfs_scan_core in Hlen by lia.
  lia.
Qed.
Lemma MReach_step__g3_bfs_scan_core : forall n e goods c u v d,
  MReach n e goods c u d ->
  (In (u, v) e \/ In (v, u) e) ->
  1 <= u <= n -> 1 <= v <= n ->
  MReach n e goods c v (d + 1).
Proof.
  intros n e goods c u v d Hmr Hedge Hu Hv.
  destruct Hmr as [x [Hsrc Hpath]].
  exists x. split; [exact Hsrc |].
  eapply pozl_step; [exact Hpath |].
  apply TownGraph_step_iff.
  split; [exact Hedge | split; [exact Hu | exact Hv]].
Qed.
Lemma In_Znth_Q__g3_bfs_scan_core : forall (Q : list Z) i,
  0 <= i < Zlength Q -> In (Znth i Q 0) Q.
Proof.
  intros Q i Hi. apply Znth_In_Zlength. exact Hi.
Qed.
Lemma BfsCore_In_range__g3_bfs_scan_core : forall n e goods c Q dl v,
  BfsCore n e goods c Q dl -> In v Q -> 1 <= v <= n.
Proof.
  intros n e goods c Q dl v Hcore Hin.
  destruct Hcore as (Hb1 & _).
  apply In_Znth_Z in Hin as [i [Hi Hnth]].
  specialize (Hb1 i Hi). lia.
Qed.
Lemma BfsCore_notin__g3_bfs_scan_core : forall n e goods c Q dl w,
  BfsCore n e goods c Q dl -> 1 <= w <= n -> Znth w dl 0 < 0 -> ~ In w Q.
Proof.
  intros n e goods c Q dl w Hcore Hw Hneg Hin.
  destruct Hcore as (_ & _ & Hmem & _).
  pose proof (proj1 (Hmem w Hw) Hin). lia.
Qed.
Lemma dl_push_frame__g3_bfs_scan_core : forall n e goods c Q dl w v x,
  n < Zlength dl ->
  BfsCore n e goods c Q dl ->
  1 <= w <= n -> Znth w dl 0 < 0 ->
  In v Q ->
  Znth v (replace_Znth w x dl) 0 = Znth v dl 0.
Proof.
  intros n e goods c Q dl w v x Hlen Hcore Hw Hneg Hin.
  assert (Hv : 1 <= v <= n)
    by (eapply BfsCore_In_range__g3_bfs_scan_core; eauto).
  assert (Hne : v <> w).
  { intros Heq. subst v.
    eapply BfsCore_notin__g3_bfs_scan_core; eauto. }
  apply Znth_replace_Znth_Diff; lia.
Qed.
Lemma queue_room_core__g3_bfs_scan_core : forall n e goods c Q dl w,
  BfsCore n e goods c Q dl ->
  1 <= w <= n -> Znth w dl 0 < 0 ->
  Zlength Q < n.
Proof.
  intros n e goods c Q dl w Hcore Hw Hneg.
  assert (Hnin : ~ In w Q)
    by (eapply BfsCore_notin__g3_bfs_scan_core; eauto).
  destruct Hcore as (Hb1 & Hnd & _).
  eapply queue_room__g3_bfs_scan_core; eauto.
Qed.
Lemma BfsCore_push_bounds__g3_bfs_scan_core : forall n e goods c Q dl w,
  BfsCore n e goods c Q dl -> 1 <= w <= n ->
  (forall i, 0 <= i < Zlength (Q ++ w :: nil) ->
     1 <= Znth i (Q ++ w :: nil) 0 <= n).
Proof.
  intros n e goods c Q dl w Hcore Hw i Hi.
  destruct Hcore as (Hb1 & _).
  rewrite Zlength_push__g3_bfs_scan_core in Hi.
  destruct (Z_lt_ge_dec i (Zlength Q)) as [Hlt | Hge].
  - rewrite Znth_prefix_push__g3_bfs_scan_core by lia. apply Hb1. lia.
  - assert (Hie : i = Zlength Q) by lia. subst i.
    rewrite Znth_last_push__g3_bfs_scan_core. lia.
Qed.
Lemma BfsCore_push_nodup__g3_bfs_scan_core : forall n e goods c Q dl w,
  BfsCore n e goods c Q dl -> 1 <= w <= n -> Znth w dl 0 < 0 ->
  NoDup (Q ++ w :: nil).
Proof.
  intros n e goods c Q dl w Hcore Hw Hneg.
  assert (Hnin : ~ In w Q)
    by (eapply BfsCore_notin__g3_bfs_scan_core; eauto).
  destruct Hcore as (_ & Hnd & _).
  apply (Permutation_NoDup (Permutation_cons_append Q w)).
  apply NoDup_cons; assumption.
Qed.
Lemma queue_room_push__g3_bfs_scan_core : forall n e goods c Q dl w w1,
  BfsCore n e goods c Q dl ->
  1 <= w <= n -> Znth w dl 0 < 0 ->
  1 <= w1 <= n -> Znth w1 dl 0 < 0 ->
  w1 <> w ->
  Zlength Q + 1 < n.
Proof.
  intros n e goods c Q dl w w1 Hcore Hw Hwneg Hw1 Hw1neg Hne.
  assert (Hnin1 : ~ In w1 Q)
    by (eapply BfsCore_notin__g3_bfs_scan_core; eauto).
  assert (Hb1' := BfsCore_push_bounds__g3_bfs_scan_core n e goods c Q dl w Hcore Hw).
  assert (Hnd' := BfsCore_push_nodup__g3_bfs_scan_core n e goods c Q dl w Hcore Hw Hwneg).
  assert (Hnin1' : ~ In w1 (Q ++ w :: nil)).
  { intros HH. apply In_push__g3_bfs_scan_core in HH.
    destruct HH as [HH | HH]; [contradiction | lia]. }
  pose proof (queue_room__g3_bfs_scan_core (Q ++ w :: nil) n w1
                Hb1' Hnd' Hw1 Hnin1') as Hres.
  rewrite Zlength_push__g3_bfs_scan_core in Hres. lia.
Qed.
Lemma BfsBounded_push__g3_bfs_scan_core : forall n e goods c Q dl u w,
  n < Zlength dl ->
  BfsCore n e goods c Q dl ->
  BfsBounded Q dl (Znth u dl 0 + 1) ->
  In u Q ->
  1 <= w <= n -> Znth w dl 0 < 0 ->
  BfsBounded (Q ++ w :: nil) (replace_Znth w (Znth u dl 0 + 1) dl)
             (Znth u (replace_Znth w (Znth u dl 0 + 1) dl) 0 + 1).
Proof.
  intros n e goods c Q dl u w Hlen Hcore Hbnd Hu Hw Hwneg.
  rewrite (dl_push_frame__g3_bfs_scan_core n e goods c Q dl w u
             (Znth u dl 0 + 1) Hlen Hcore Hw Hwneg Hu).
  unfold BfsBounded. intros j Hj.
  rewrite Zlength_push__g3_bfs_scan_core in Hj.
  destruct (Z_lt_ge_dec j (Zlength Q)) as [Hlt | Hge].
  - rewrite Znth_prefix_push__g3_bfs_scan_core by lia.
    rewrite (dl_push_frame__g3_bfs_scan_core n e goods c Q dl w (Znth j Q 0)
               (Znth u dl 0 + 1) Hlen Hcore Hw Hwneg
               (In_Znth_Q__g3_bfs_scan_core Q j ltac:(lia))).
    apply Hbnd. lia.
  - assert (Hje : j = Zlength Q) by lia. subst j.
    rewrite Znth_last_push__g3_bfs_scan_core.
    rewrite Znth_replace_Znth_Same by lia.
    lia.
Qed.
Lemma BfsExpanded_push__g3_bfs_scan_core : forall n edges goods c Q dl u w qh,
  n < Zlength dl ->
  BfsCore n edges goods c Q dl ->
  BfsExpanded n edges Q dl qh ->
  0 <= qh <= Zlength Q ->
  1 <= w <= n -> Znth w dl 0 < 0 ->
  BfsExpanded n edges (Q ++ w :: nil) (replace_Znth w (Znth u dl 0 + 1) dl) qh.
Proof.
  intros n edges goods c Q dl u w qh Hlen Hcore Hexp Hqh Hw Hwneg.
  unfold BfsExpanded. intros i v Hi Hv Hedge.
  assert (Hi' : 0 <= i < Zlength Q) by lia.
  rewrite (Znth_prefix_push__g3_bfs_scan_core Q w i Hi') in Hedge |- *.
  destruct (Hexp i v Hi Hv Hedge) as [HinQ Hle].
  split.
  - apply In_push__g3_bfs_scan_core. left. exact HinQ.
  - rewrite (dl_push_frame__g3_bfs_scan_core n edges goods c Q dl w v
               (Znth u dl 0 + 1) Hlen Hcore Hw Hwneg HinQ).
    rewrite (dl_push_frame__g3_bfs_scan_core n edges goods c Q dl w (Znth i Q 0)
               (Znth u dl 0 + 1) Hlen Hcore Hw Hwneg
               (In_Znth_Q__g3_bfs_scan_core Q i Hi')).
    exact Hle.
Qed.
Lemma BfsCore_push__g3_bfs_scan_core : forall n e goods c Q dl u w,
  n < Zlength dl ->
  BfsCore n e goods c Q dl ->
  BfsBounded Q dl (Znth u dl 0 + 1) ->
  In u Q ->
  1 <= w <= n ->
  Znth w dl 0 < 0 ->
  Znth u dl 0 + 1 <= Zlength Q ->
  MReach n e goods c w (Znth u dl 0 + 1) ->
  BfsCore n e goods c (Q ++ w :: nil) (replace_Znth w (Znth u dl 0 + 1) dl).
Proof.
  intros n e goods c Q dl u w Hlen Hcore Hbnd Hu Hw Hwneg Hroom Hmr.
  assert (Hun : 1 <= u <= n)
    by (eapply BfsCore_In_range__g3_bfs_scan_core; eauto).
  assert (Hnotin : ~ In w Q)
    by (eapply BfsCore_notin__g3_bfs_scan_core; eauto).
  assert (Hb1' := BfsCore_push_bounds__g3_bfs_scan_core n e goods c Q dl w Hcore Hw).
  assert (Hnd' := BfsCore_push_nodup__g3_bfs_scan_core n e goods c Q dl w Hcore Hw Hwneg).
  assert (Hdlw : Znth w (replace_Znth w (Znth u dl 0 + 1) dl) 0 = Znth u dl 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdlo : forall v, 1 <= v <= n -> v <> w ->
            Znth v (replace_Znth w (Znth u dl 0 + 1) dl) 0 = Znth v dl 0)
    by (intros v Hv Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hfr : forall v, In v Q ->
            Znth v (replace_Znth w (Znth u dl 0 + 1) dl) 0 = Znth v dl 0)
    by (intros v Hv; eapply dl_push_frame__g3_bfs_scan_core; eauto).
  pose proof Hcore as Hcore'.
  destruct Hcore' as (Hb1 & Hnd & Hmem & Hneg & Hreal & Hmono & Hidx & Hsrc).
  assert (Hdu : 0 <= Znth u dl 0) by (apply (proj1 (Hmem u Hun)); exact Hu).
  split; [exact Hb1' | split; [exact Hnd' | split; [| split; [| split; [| split; [| split]]]]]].
  - intros v Hv. destruct (Z.eq_dec v w) as [Heq | Hne].
    + subst v. rewrite Hdlw. split; intros _.
      * lia.
      * apply In_push__g3_bfs_scan_core. right. reflexivity.
    + rewrite (Hdlo v Hv Hne). rewrite <- (Hmem v Hv).
      rewrite In_push__g3_bfs_scan_core.
      split; [intros [HH | HH]; [exact HH | lia] | intros HH; left; exact HH].
  - intros v Hv Hnin.
    assert (Hne : v <> w).
    { intros Heq. subst v. apply Hnin.
      apply In_push__g3_bfs_scan_core. right. reflexivity. }
    rewrite (Hdlo v Hv Hne). apply Hneg; [exact Hv |].
    intros HH. apply Hnin. apply In_push__g3_bfs_scan_core. left. exact HH.
  - intros i Hi. rewrite Zlength_push__g3_bfs_scan_core in Hi.
    destruct (Z_lt_ge_dec i (Zlength Q)) as [Hlt | Hge].
    + rewrite Znth_prefix_push__g3_bfs_scan_core by lia.
      rewrite (Hfr (Znth i Q 0) (In_Znth_Q__g3_bfs_scan_core Q i ltac:(lia))).
      apply Hreal. lia.
    + assert (Hie : i = Zlength Q) by lia. subst i.
      rewrite Znth_last_push__g3_bfs_scan_core, Hdlw. exact Hmr.
  - intros i j Hi Hij Hj. rewrite Zlength_push__g3_bfs_scan_core in Hj.
    destruct (Z_lt_ge_dec j (Zlength Q)) as [Hjlt | Hjge].
    + rewrite (Znth_prefix_push__g3_bfs_scan_core Q w i ltac:(lia)).
      rewrite (Znth_prefix_push__g3_bfs_scan_core Q w j ltac:(lia)).
      rewrite (Hfr (Znth i Q 0) (In_Znth_Q__g3_bfs_scan_core Q i ltac:(lia))).
      rewrite (Hfr (Znth j Q 0) (In_Znth_Q__g3_bfs_scan_core Q j ltac:(lia))).
      apply Hmono; lia.
    + assert (Hje : j = Zlength Q) by lia. subst j.
      rewrite Znth_last_push__g3_bfs_scan_core, Hdlw.
      destruct (Z_lt_ge_dec i (Zlength Q)) as [Hilt | Hige].
      * rewrite (Znth_prefix_push__g3_bfs_scan_core Q w i ltac:(lia)).
        rewrite (Hfr (Znth i Q 0) (In_Znth_Q__g3_bfs_scan_core Q i ltac:(lia))).
        apply Hbnd. lia.
      * assert (Hie : i = Zlength Q) by lia. subst i.
        rewrite Znth_last_push__g3_bfs_scan_core, Hdlw. lia.
  - intros i Hi. rewrite Zlength_push__g3_bfs_scan_core in Hi.
    destruct (Z_lt_ge_dec i (Zlength Q)) as [Hlt | Hge].
    + rewrite Znth_prefix_push__g3_bfs_scan_core by lia.
      rewrite (Hfr (Znth i Q 0) (In_Znth_Q__g3_bfs_scan_core Q i ltac:(lia))).
      apply Hidx. lia.
    + assert (Hie : i = Zlength Q) by lia. subst i.
      rewrite Znth_last_push__g3_bfs_scan_core, Hdlw. lia.
  - intros v Hv Hg. destruct (Hsrc v Hv Hg) as [HinQ Hd0].
    split.
    + apply In_push__g3_bfs_scan_core. left. exact HinQ.
    + rewrite (Hfr v HinQ). exact Hd0.
Qed.
Lemma Znth_indep__g5_dist_rows : forall {A} (l : list A) (i : Z) (d d' : A),
  0 <= i < Zlength l -> Znth i l d = Znth i l d'.
Proof.
  intros A l i d d' H.
  unfold Znth.
  apply nth_indep.
  rewrite Zlength_correct in H.
  lia.
Qed.
Lemma Znth_indep__g6_tmp_prefix : forall {A : Type} (l : list A) (i : Z) (d d' : A),
  0 <= i < Zlength l -> Znth i l d = Znth i l d'.
Proof.
  intros A l i d d' H. unfold Znth. apply nth_indep.
  rewrite Zlength_correct in H. lia.
Qed.
Lemma Znth_app_left__g6_tmp_prefix : forall {A : Type} (d : A) (l1 l2 : list A) (i : Z),
  0 <= i < Zlength l1 -> Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A d l1 l2 i Hi. unfold Znth. apply app_nth1.
  rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_right__g6_tmp_prefix : forall {A : Type} (d : A) (l1 l2 : list A) (i : Z),
  Zlength l1 <= i -> Znth i (l1 ++ l2) d = Znth (i - Zlength l1) l2 d.
Proof.
  intros A d l1 l2 i Hi. unfold Znth. rewrite app_nth2.
  - f_equal. rewrite Zlength_correct. lia.
  - rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_In__g7_fair_sum : forall (l : list Z) (j : Z),
  0 <= j < Zlength l -> In (Znth j l 0) l.
Proof.
  intros l j Hj. unfold Znth. apply nth_In.
  rewrite Zlength_correct in Hj. lia.
Qed.
Lemma Permutation_bound__g7_fair_sum : forall (l1 l2 : list Z) (lo hi : Z),
  Permutation l1 l2 ->
  (forall j, 0 <= j < Zlength l1 -> lo <= Znth j l1 0 <= hi) ->
  forall j, 0 <= j < Zlength l2 -> lo <= Znth j l2 0 <= hi.
Proof.
  intros l1 l2 lo hi Hperm Hb j Hj.
  assert (Hin : In (Znth j l2 0) l2) by (apply Znth_In__g7_fair_sum; exact Hj).
  assert (Hin1 : In (Znth j l2 0) l1).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin]. }
  apply In_Znth_Z in Hin1 as [i [Hi Heq]].
  rewrite <- Heq. apply Hb. exact Hi.
Qed.
Lemma ZSum_sublist_succ__g7_fair_sum : forall (l : list Z) (i : Z),
  0 <= i < Zlength l ->
  ZSum (sublist 0 (i + 1) l) = ZSum (sublist 0 i l) + Znth i l 0.
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite ZSum_app.
  rewrite (sublist_single 0 i l) by lia.
  rewrite ZSum_cons, ZSum_nil. lia.
Qed.
Lemma ZSum_sublist_bound__g7_fair_sum : forall (l : list Z) (i b : Z),
  0 <= b ->
  0 <= i <= Zlength l ->
  (forall j, 0 <= j < Zlength l -> 0 <= Znth j l 0 <= b) ->
  0 <= ZSum (sublist 0 i l) <= i * b.
Proof.
  intros l i b Hb Hi Hbd.
  assert (Hgen : forall x, 0 <= x -> x <= Zlength l ->
                   0 <= ZSum (sublist 0 x l) <= x * b).
  { apply (natlike_ind (fun x => x <= Zlength l ->
                          0 <= ZSum (sublist 0 x l) <= x * b)).
    - intros _. unfold sublist, ZSum. simpl. lia.
    - intros x Hx IH Hle.
      replace (Z.succ x) with (x + 1) by lia.
      rewrite ZSum_sublist_succ__g7_fair_sum by lia.
      assert (Hel : 0 <= Znth x l 0 <= b) by (apply Hbd; lia).
      assert (Hrec : 0 <= ZSum (sublist 0 x l) <= x * b) by (apply IH; lia).
      nia. }
  apply Hgen; lia.
Qed.
