Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition IsPositiveGcd (d : Z) (xs : list Z) : Prop :=
  d > 0 /\ xs <> [] /\ d = fold_right Z.gcd 0 xs.

(* The array b the statement builds from a matrix: the greatest common divisor
   of each row, and after them the greatest common divisor of each column. *)
Definition GcdArray (r c : Z) (g : list (list Z)) (b : list Z) : Prop :=
  Zlength b = r + c /\
  (forall i, 0 <= i < r -> IsPositiveGcd (Znth i b 0) (Znth i g [])) /\
  (forall j, 0 <= j < c ->
     IsPositiveGcd (Znth (r + j) b 0) (map (fun row => Znth j row 0) g)).

(* A matrix is diverse when those r + c divisors are pairwise distinct.  Its
   entries are the positive integers the output format allows. *)
Definition DiverseMatrix (r c : Z) (g : list (list Z)) : Prop :=
  Zlength g = r /\
  Forall (fun row => Zlength row = c) g /\
  Forall (Forall (fun x => 1 <= x <= 1000000000)) g /\
  exists b : list Z, GcdArray r c g b /\ NoDup b.

(* The magnitude of a matrix: the largest of those divisors. *)
Definition Magnitude (r c : Z) (g : list (list Z)) (mag : Z) : Prop :=
  exists b : list Z, GcdArray r c g b /\
    max_value_of_subset Z.le (fun x => In x b) (fun x => x) mag.

Definition Pre (r c : Z) : Prop :=
  (* Every clause below is stated explicitly in the P037 solver Require, which
     therefore omits the Pre(...) call:
       1 <= r <= 500 /\ 1 <= c <= 500. *)
  True.

(* Print a diverse matrix of least magnitude, or nothing at all when no diverse
   matrix of that shape exists. *)
Definition Spec (r c : Z) (out : option (list (list Z))) : Prop :=
  (out = None /\ ~ exists g, DiverseMatrix r c g) \/
  (exists (g : list (list Z)) (mag : Z),
     out = Some g /\ DiverseMatrix r c g /\ Magnitude r c g mag /\
     min_value_of_subset Z.le
       (fun m' => exists g', DiverseMatrix r c g' /\ Magnitude r c g' m')
       (fun x => x) mag).

(* Canonical zero-based indices used to state the constructive output without
   mirroring either C loop. *)
Definition ConstructionIndices (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).

Definition ConstructionCell (r c i j : Z) : Z :=
  if Z.eqb r 1 then j + 2 else (c + i + 1) * (j + 1).

Definition ConstructionMatrix (r c : Z) : list (list Z) :=
  map (fun i => map (fun j => ConstructionCell r c i j)
                    (ConstructionIndices c))
      (ConstructionIndices r).

Definition StagedConstructionCell
    (r c i j frontier : Z) : option Z :=
  if (i * c + j <? frontier)%Z
  then Some (ConstructionCell r c i j)
  else None.

Definition StagedConstructionRow
    (r c i frontier : Z) : list (option Z) :=
  map (fun j => StagedConstructionCell r c i j frontier)
      (ConstructionIndices c).

Definition StagedConstruction
    (r c frontier : Z) : list (list (option Z)) :=
  map (fun i => StagedConstructionRow r c i frontier)
      (ConstructionIndices r).

(* Stable body-level meaning of the partially initialized output.  Machine
   bounds and spatial ownership remain explicit in the C invariants. *)
Definition ConstructionPrefix
    (r c : Z) (rows : list (list (option Z))) (frontier : Z) : Prop :=
  rows = StagedConstruction r c frontier.

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Lemma staged_nat_values_before_start__initial_single_row :
  forall start n frontier,
    frontier <= Z.of_nat start ->
    map (fun k =>
      if (Z.of_nat k <? frontier)%Z
      then Some (Z.of_nat k + 2)
      else None) (seq start n) =
      repeat None n.
Proof.
  intros start n. revert start.
  induction n; intros start frontier Hfront; simpl.
  - reflexivity.
  - simpl.
    replace ((Z.of_nat start <? frontier)%Z) with false by
      (symmetry; apply Z.ltb_ge; lia).
    f_equal.
    apply IHn. lia.
Qed.
Lemma staged_nat_values_step__initial_single_row :
  forall start n k,
    (k < n)%nat ->
    replace_nth k
      (map (fun x =>
        if (Z.of_nat x <? Z.of_nat (start + k))%Z
        then Some (Z.of_nat x + 2)
        else None) (seq start n))
      (Some (Z.of_nat (start + k) + 2)) =
    map (fun x =>
      if (Z.of_nat x <? Z.of_nat (start + S k))%Z
      then Some (Z.of_nat x + 2)
      else None) (seq start n).
Proof.
  intros start n k. revert start n.
  induction k; intros start n Hkn; destruct n; simpl in Hkn; try lia.
  - simpl.
    replace ((Z.of_nat start <? Z.of_nat (start + 1))%Z) with true by
      (symmetry; apply Z.ltb_lt; lia).
    f_equal.
    + f_equal. lia.
    + rewrite !staged_nat_values_before_start__initial_single_row by lia.
      reflexivity.
  - simpl.
    replace ((Z.of_nat start <? Z.of_nat (start + S (S k)))%Z) with true by
      (symmetry; apply Z.ltb_lt; lia).
    replace ((Z.of_nat start <? Z.of_nat (start + S k))%Z) with true by
      (symmetry; apply Z.ltb_lt; lia).
    f_equal.
    replace (start + S k)%nat with (S start + k)%nat by lia.
    replace (start + S (S k))%nat with (S start + S k)%nat by lia.
    apply IHk. lia.
Qed.
Lemma staged_construction_row_single_step__initial_single_row : forall c j,
  1 <= j <= c ->
  replace_Znth (j - 1) (Some (j + 1))
    (StagedConstructionRow 1 c 0 (j - 1)) =
  StagedConstructionRow 1 c 0 j.
Proof.
  intros c j Hj.
  unfold StagedConstructionRow, ConstructionIndices, StagedConstructionCell,
    ConstructionCell, replace_Znth.
  rewrite !map_map.
  simpl.
  change (replace_nth (Z.to_nat (j - 1))
    (map (fun x =>
      if (Z.of_nat x <? j - 1)%Z
      then Some (Z.of_nat x + 2)
      else None) (seq 0 (Z.to_nat c))) (Some (j + 1)) =
    map (fun x =>
      if (Z.of_nat x <? j)%Z
      then Some (Z.of_nat x + 2)
      else None) (seq 0 (Z.to_nat c))).
  pose proof (staged_nat_values_step__initial_single_row
    0 (Z.to_nat c) (Z.to_nat (j - 1)) ltac:(lia)) as Hstep.
  simpl in Hstep.
  replace (Z.of_nat (Z.to_nat (j - 1))) with (j - 1) in Hstep by lia.
  replace (Z.pos (Pos.of_succ_nat (Z.to_nat (j - 1)))) with j in Hstep by lia.
  replace (j - 1 + 2) with (j + 1) in Hstep by lia.
  exact Hstep.
Qed.
Lemma construction_prefix_single_row_step__initial_single_row :
  forall c rows d j,
    1 <= j <= c ->
    ConstructionPrefix 1 c rows (j - 1) ->
    ConstructionPrefix 1 c
      [replace_Znth (j - 1) (Some (j + 1)) (Znth 0 rows d)] j.
Proof.
  intros c rows d j Hj Hprefix.
  unfold ConstructionPrefix in *.
  subst rows.
  unfold StagedConstruction at 1 2.
  unfold ConstructionIndices at 1 2.
  simpl.
  f_equal.
  apply staged_construction_row_single_step__initial_single_row.
  exact Hj.
Qed.
Lemma staged_construction_row_zero__initial_single_row :
  forall r c i,
    0 <= i ->
    StagedConstructionRow r c i 0 = repeat None (Z.to_nat c).
Proof.
  intros r c i Hi.
  unfold StagedConstructionRow, ConstructionIndices, StagedConstructionCell.
  destruct c as [|c|c]; simpl.
  - reflexivity.
  - rewrite map_map.
    assert (Hconst : forall start n,
      map (fun _ : nat => @None Z) (seq start n) = repeat None n).
    { intros start n. revert start.
      induction n; intros start; simpl; [reflexivity |].
      f_equal. apply IHn. }
    rewrite <- (Hconst O (Pos.to_nat c)).
    apply map_ext.
    intros k.
    replace ((i * Z.pos c + Z.of_nat k <? 0)%Z) with false by
      (symmetry; apply Z.ltb_ge; nia).
    reflexivity.
  - reflexivity.
Qed.
Lemma staged_construction_zero__initial_single_row :
  forall r c,
    StagedConstruction r c 0 =
      repeat (repeat None (Z.to_nat c)) (Z.to_nat r).
Proof.
  intros r c.
  unfold StagedConstruction, ConstructionIndices.
  rewrite map_map.
  assert (Hconst : forall start n,
    map (fun _ : nat => repeat (@None Z) (Z.to_nat c)) (seq start n) =
      repeat (repeat None (Z.to_nat c)) n).
  { intros start n. revert start.
    induction n; intros start; simpl; [reflexivity |].
    f_equal. apply IHn. }
  rewrite <- (Hconst O (Z.to_nat r)).
  apply map_ext.
  intros i.
  apply staged_construction_row_zero__initial_single_row.
  lia.
Qed.
Lemma map_seq_as_Zrange_aux__final_results : forall start count,
  map Z.of_nat (seq start count) = Zrange_aux (Z.of_nat start) count.
Proof.
  intros start count. revert start.
  induction count as [|count IH]; intros start; simpl.
  - reflexivity.
  - f_equal. rewrite IH. f_equal. lia.
Qed.
Lemma construction_indices_as_Zrange__final_results : forall n,
  0 <= n -> ConstructionIndices n = Zrange 0 n.
Proof.
  intros n Hn. unfold ConstructionIndices, Zrange.
  rewrite map_seq_as_Zrange_aux__final_results. simpl.
  f_equal. lia.
Qed.
Lemma Zlength_Zrange_aux__final_results : forall low count,
  Zlength (Zrange_aux low count) = Z.of_nat count.
Proof.
  intros low count. revert low.
  induction count as [|count IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__final_results : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__final_results. lia.
Qed.
Lemma Znth_Zrange_aux__final_results : forall count low i,
  0 <= i < Z.of_nat count ->
  Znth i (Zrange_aux low count) 0 = low + i.
Proof.
  induction count as [|count IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__final_results : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__final_results by lia. lia.
Qed.
Lemma construction_indices_characterization__final_results : forall n,
  0 <= n ->
  Zlength (ConstructionIndices n) = n /\
  (forall x, In x (ConstructionIndices n) <-> 0 <= x < n) /\
  (forall i, 0 <= i < n -> Znth i (ConstructionIndices n) 0 = i).
Proof.
  intros n Hn. rewrite construction_indices_as_Zrange__final_results by exact Hn.
  split.
  - rewrite Zlength_Zrange__final_results by lia. lia.
  - split.
    + intros x. symmetry. apply In_Zrange.
    + intros i Hi. rewrite Znth_Zrange__final_results by lia. lia.
Qed.
Lemma Zlength_map__final_results : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__final_results : forall {A B : Type}
    (f : A -> B) l (da : A) (db : B) i,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l. induction l as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia. apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_replace_Znth__multirow_transitions :
  forall {A : Type} n (a : A) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros A n a l. rewrite !Zlength_correct. unfold replace_Znth. f_equal.
  remember (Z.to_nat n) as m. clear Heqm n.
  revert l. induction m; intros l; destruct l; simpl; auto.
Qed.
Lemma construction_prefix_multirow_step__multirow_transitions :
  forall r c i j rows,
    2 <= r -> 1 <= c -> 1 <= i <= r -> 1 <= j <= c ->
    ConstructionPrefix r c rows ((i - 1) * c + (j - 1)) ->
    ConstructionPrefix r c
      (replace_Znth (i - 1)
        (replace_Znth (j - 1) (Some ((c + i) * j))
          (Znth (i - 1) rows [])) rows)
      ((i - 1) * c + j).
Proof.
  intros r c i j rows Hr Hc Hi Hj Hprefix.
  unfold ConstructionPrefix in *.
  subst rows.
  unfold StagedConstruction.
  apply (proj2 (list_eq_ext _ _ (@nil (option Z)))).
  split.
  - rewrite Zlength_replace_Znth__multirow_transitions,
      !Zlength_map__final_results.
    reflexivity.
  - intros k Hk.
    rewrite Zlength_replace_Znth__multirow_transitions,
      Zlength_map__final_results in Hk.
    pose proof (construction_indices_characterization__final_results r ltac:(lia))
      as [Hrlen [_ Hridx]].
    rewrite Hrlen in Hk.
    destruct (Z.eq_dec k (i - 1)) as [-> | Hki].
    + rewrite Znth_replace_Znth_Same by
        (rewrite Zlength_map__final_results, Hrlen; lia).
      rewrite (@Znth_map__final_results Z (list (option Z))
        (fun x => StagedConstructionRow r c x ((i - 1) * c + j))
        (ConstructionIndices r) 0 [] (i - 1)) by (rewrite Hrlen; lia).
      rewrite Hridx by lia.
      rewrite (@Znth_map__final_results Z (list (option Z))
        (fun x => StagedConstructionRow r c x ((i - 1) * c + (j - 1)))
        (ConstructionIndices r) 0 [] (i - 1)) by (rewrite Hrlen; lia).
      rewrite Hridx by lia.
      unfold StagedConstructionRow.
      apply (proj2 (list_eq_ext _ _ None)).
      split.
      * rewrite Zlength_replace_Znth__multirow_transitions,
          !Zlength_map__final_results.
        reflexivity.
      * intros q Hq.
        rewrite Zlength_replace_Znth__multirow_transitions,
          Zlength_map__final_results in Hq.
        pose proof (construction_indices_characterization__final_results c ltac:(lia))
          as [Hclen [_ Hcidx]].
        rewrite Hclen in Hq.
        destruct (Z.eq_dec q (j - 1)) as [-> | Hqj].
        -- rewrite Znth_replace_Znth_Same by
             (rewrite Zlength_map__final_results, Hclen; lia).
           rewrite (@Znth_map__final_results Z (option Z)
             (fun x => StagedConstructionCell r c (i - 1) x
               ((i - 1) * c + j))
             (ConstructionIndices c) 0 None (j - 1)) by (rewrite Hclen; lia).
           rewrite Hcidx by lia.
           unfold StagedConstructionCell, ConstructionCell.
           replace ((((i - 1) * c + (j - 1) <? (i - 1) * c + j))%Z)
             with true by (symmetry; apply Z.ltb_lt; nia).
           destruct (Z.eqb_spec r 1); [lia |].
           f_equal. ring.
        -- rewrite Znth_replace_Znth_Diff by
             (try rewrite Zlength_map__final_results, Hclen; lia).
           rewrite !(@Znth_map__final_results Z (option Z)
             (fun x => StagedConstructionCell r c (i - 1) x _)
             (ConstructionIndices c) 0 None q) by (rewrite Hclen; lia).
           rewrite !Hcidx by lia.
           unfold StagedConstructionCell.
           destruct (Z_lt_dec q (j - 1)).
           ++ replace (((i - 1) * c + q <? (i - 1) * c + (j - 1))%Z)
                with true by (symmetry; apply Z.ltb_lt; nia).
              replace (((i - 1) * c + q <? (i - 1) * c + j)%Z)
                with true by (symmetry; apply Z.ltb_lt; nia).
              reflexivity.
           ++ replace (((i - 1) * c + q <? (i - 1) * c + (j - 1))%Z)
                with false by (symmetry; apply Z.ltb_ge; lia).
              replace (((i - 1) * c + q <? (i - 1) * c + j)%Z)
                with false by (symmetry; apply Z.ltb_ge; lia).
              reflexivity.
    + rewrite Znth_replace_Znth_Diff by
        (try rewrite Zlength_map__final_results, Hrlen; lia).
      rewrite !(@Znth_map__final_results Z (list (option Z))
        (fun x => StagedConstructionRow r c x _)
        (ConstructionIndices r) 0 [] k) by (rewrite Hrlen; lia).
      rewrite !Hridx by lia.
      unfold StagedConstructionRow.
      apply (proj2 (list_eq_ext _ _ None)).
      split; [rewrite !Zlength_map__final_results; reflexivity |].
      intros q Hq.
      rewrite Zlength_map__final_results in Hq.
      pose proof (construction_indices_characterization__final_results c ltac:(lia))
        as [Hclen [_ Hcidx]].
      rewrite Hclen in Hq.
      rewrite !(@Znth_map__final_results Z (option Z)
        (fun x => StagedConstructionCell r c k x _)
        (ConstructionIndices c) 0 None q) by (rewrite Hclen; lia).
      rewrite !Hcidx by lia.
      unfold StagedConstructionCell.
      destruct (Z_lt_dec k (i - 1)).
      * replace ((k * c + q <? (i - 1) * c + (j - 1))%Z)
          with true by (symmetry; apply Z.ltb_lt; nia).
        replace ((k * c + q <? (i - 1) * c + j)%Z)
          with true by (symmetry; apply Z.ltb_lt; nia).
        reflexivity.
      * assert (i - 1 < k) by lia.
        replace ((k * c + q <? (i - 1) * c + (j - 1))%Z)
          with false by (symmetry; apply Z.ltb_ge; nia).
        replace ((k * c + q <? (i - 1) * c + j)%Z)
          with false by (symmetry; apply Z.ltb_ge; nia).
        reflexivity.
Qed.
Lemma no_diverse_one_by_one__degenerate_result : Spec 1 1 None.
Proof.
  unfold Spec. left. split; [reflexivity |].
  intros [g [Hglen [Hgrows [_ [b [[Hblen [Hbrow Hbcol]] Hbnd]]]]]].
  rewrite Zlength_correct in Hglen.
  destruct g as [|row gt]; simpl in Hglen; [lia |].
  destruct gt as [|row2 gt]; simpl in Hglen; [|lia].
  inversion Hgrows as [|? ? Hrowlen _]; subst.
  rewrite Zlength_correct in Hrowlen.
  destruct row as [|x xt]; simpl in Hrowlen; [lia |].
  destruct xt as [|x2 xt]; simpl in Hrowlen; [|lia].
  specialize (Hbrow 0 ltac:(lia)).
  specialize (Hbcol 0 ltac:(lia)).
  destruct Hbrow as [_ [_ Hbrow]].
  destruct Hbcol as [_ [_ Hbcol]].
  simpl in Hbrow, Hbcol.
  rewrite Zlength_correct in Hblen.
  destruct b as [|u bt]; simpl in Hblen; [lia |].
  destruct bt as [|v bt]; simpl in Hblen; [lia |].
  destruct bt as [|w bt]; simpl in Hblen; [|lia].
  rewrite Znth0_cons in Hbrow.
  rewrite Znth_cons in Hbcol by lia.
  rewrite Znth0_cons in Hbcol.
  rewrite Znth0_cons in Hbcol.
  inversion Hbnd as [|? ? Hnotin Htail]; subst.
  inversion Htail as [|? ? _ _]; subst.
  apply Hnotin. simpl. left. congruence.
Qed.
Lemma construction_prefix_completion__final_results : forall r c rows,
  1 <= r -> 1 <= c -> ConstructionPrefix r c rows (r * c) ->
  rows = map (map (@Some Z)) (ConstructionMatrix r c).
Proof.
  intros r c rows Hr Hc Hprefix. unfold ConstructionPrefix in Hprefix.
  subst rows. unfold StagedConstruction, ConstructionMatrix.
  rewrite map_map. apply map_ext_in. intros i Hi.
  unfold StagedConstructionRow. rewrite map_map. apply map_ext_in.
  intros j Hj. unfold StagedConstructionCell.
  pose proof (construction_indices_characterization__final_results r ltac:(lia))
    as [_ [Hri _]].
  pose proof (construction_indices_characterization__final_results c ltac:(lia))
    as [_ [Hcj _]].
  apply Hri in Hi. apply Hcj in Hj.
  assert (Hltb : (i * c + j <? r * c)%Z = true).
  { apply Z.ltb_lt. nia. }
  rewrite Hltb. reflexivity.
Qed.
Lemma no_diverse_one_by_one_core__final_results :
  ~ exists g, DiverseMatrix 1 1 g.
Proof.
  intros [g [Hglen [Hgrows [_ [b [[Hblen [Hbrow Hbcol]] Hbnd]]]]]].
  rewrite Zlength_correct in Hglen.
  destruct g as [|row gt]; simpl in Hglen; [lia |].
  destruct gt as [|row2 gt]; simpl in Hglen; [|lia].
  inversion Hgrows as [|? ? Hrowlen _]; subst.
  rewrite Zlength_correct in Hrowlen.
  destruct row as [|x xt]; simpl in Hrowlen; [lia |].
  destruct xt as [|x2 xt]; simpl in Hrowlen; [|lia].
  specialize (Hbrow 0 ltac:(lia)). specialize (Hbcol 0 ltac:(lia)).
  destruct Hbrow as [_ [_ Hbrow]]. destruct Hbcol as [_ [_ Hbcol]].
  simpl in Hbrow, Hbcol.
  rewrite Zlength_correct in Hblen.
  destruct b as [|u bt]; simpl in Hblen; [lia |].
  destruct bt as [|v bt]; simpl in Hblen; [lia |].
  destruct bt as [|w bt]; simpl in Hblen; [|lia].
  rewrite Znth0_cons in Hbrow.
  rewrite Znth_cons in Hbcol by lia.
  rewrite Znth0_cons in Hbcol.
  rewrite Znth0_cons in Hbcol.
  inversion Hbnd as [|? ? Hnotin Htail]; subst.
  inversion Htail as [|? ? _ _]; subst.
  apply Hnotin. simpl. left. congruence.
Qed.
Lemma no_diverse_one_by_one__final_results : Spec 1 1 None.
Proof.
  unfold Spec. left. split; [reflexivity |].
  exact no_diverse_one_by_one_core__final_results.
Qed.
Lemma Zrange_head__final_results : forall low high,
  low < high -> Zrange low high = low :: Zrange (low + 1) high.
Proof.
  intros low high Hlt. unfold Zrange.
  replace (Z.to_nat (high - low))
    with (S (Z.to_nat (high - (low + 1)))) by lia.
  simpl. reflexivity.
Qed.
Lemma fold_gcd_map_mul__final_results : forall a (f : Z -> Z) l,
  0 <= a ->
  fold_right Z.gcd 0 (map (fun x => a * f x) l) =
  a * fold_right Z.gcd 0 (map f l).
Proof.
  intros a f l Ha. induction l as [|x xs IH]; simpl.
  - ring.
  - rewrite IH. apply Z.gcd_mul_mono_l_nonneg. exact Ha.
Qed.
Lemma fold_gcd_Zrange_from_one__final_results : forall n,
  1 <= n -> fold_right Z.gcd 0 (Zrange 1 (n + 1)) = 1.
Proof.
  intros n Hn. rewrite Zrange_head__final_results by lia. simpl.
  apply Z.gcd_1_l.
Qed.
Lemma fold_gcd_Zrange_two_or_more__final_results : forall low n,
  0 <= low -> 2 <= n ->
  fold_right Z.gcd 0 (Zrange low (low + n)) = 1.
Proof.
  intros low n Hlow Hn.
  rewrite Zrange_head__final_results by lia.
  rewrite Zrange_head__final_results by lia. simpl.
  rewrite Z.gcd_assoc.
  replace (low + 1) with (1 + low) by ring.
  rewrite Z.gcd_add_diag_r, Z.gcd_1_r, Z.gcd_1_l.
  reflexivity.
Qed.
Lemma map_ConstructionCell_row__final_results : forall r c i,
  0 <= c -> r <> 1 ->
  map (fun j => ConstructionCell r c i j) (ConstructionIndices c) =
  map (fun j => (c + i + 1) * (j + 1)) (Zrange 0 c).
Proof.
  intros r c i Hc Hr. rewrite construction_indices_as_Zrange__final_results by lia.
  apply map_ext. intros j. unfold ConstructionCell.
  destruct (Z.eqb_spec r 1); congruence.
Qed.
Lemma construction_row_gcd_many__final_results : forall r c i,
  2 <= r -> 1 <= c -> 0 <= i < r ->
  fold_right Z.gcd 0
    (map (fun j => ConstructionCell r c i j) (ConstructionIndices c)) =
  c + i + 1.
Proof.
  intros r c i Hr Hc Hi.
  rewrite map_ConstructionCell_row__final_results by lia.
  rewrite <- (construction_indices_as_Zrange__final_results c) by lia.
  rewrite fold_gcd_map_mul__final_results by lia.
  rewrite construction_indices_as_Zrange__final_results by lia.
  replace (map (fun x : Z => x + 1) (Zrange 0 c))
    with (Zrange 1 (c + 1)).
  - rewrite fold_gcd_Zrange_from_one__final_results by lia. ring.
  - symmetry. apply (proj2 (list_eq_ext _ _ 0)). split.
    + rewrite Zlength_map__final_results, !Zlength_Zrange__final_results by lia. lia.
    + intros k Hk. rewrite Zlength_map__final_results,
        Zlength_Zrange__final_results in Hk by lia.
      rewrite (@Znth_map__final_results Z Z (fun x => x + 1)
        (Zrange 0 c) 0 0 k) by
        (rewrite Zlength_Zrange__final_results by lia; lia).
      rewrite !Znth_Zrange__final_results by lia. lia.
Qed.
Lemma construction_row_gcd_one__final_results : forall c,
  2 <= c ->
  fold_right Z.gcd 0
    (map (fun j => ConstructionCell 1 c 0 j) (ConstructionIndices c)) = 1.
Proof.
  intros c Hc. rewrite construction_indices_as_Zrange__final_results by lia.
  replace (map (fun j : Z => ConstructionCell 1 c 0 j) (Zrange 0 c))
    with (Zrange 2 (c + 2)).
  - replace (c + 2) with (2 + c) by ring.
    apply (fold_gcd_Zrange_two_or_more__final_results 2 c); lia.
  - symmetry. apply (proj2 (list_eq_ext _ _ 0)). split.
    + rewrite Zlength_map__final_results, !Zlength_Zrange__final_results by lia. lia.
    + intros k Hk. rewrite Zlength_map__final_results,
        Zlength_Zrange__final_results in Hk by lia.
      rewrite (@Znth_map__final_results Z Z
        (fun j => ConstructionCell 1 c 0 j) (Zrange 0 c) 0 0 k) by
        (rewrite Zlength_Zrange__final_results by lia; lia).
      rewrite !Znth_Zrange__final_results by lia.
      unfold ConstructionCell. rewrite Z.eqb_refl. ring.
Qed.
Lemma construction_matrix_row_Znth__final_results : forall r c i,
  0 <= r -> 0 <= c -> 0 <= i < r ->
  Znth i (ConstructionMatrix r c) [] =
  map (fun j => ConstructionCell r c i j) (ConstructionIndices c).
Proof.
  intros r c i Hr Hc Hi. unfold ConstructionMatrix.
  rewrite (@Znth_map__final_results Z (list Z)
    (fun i => map (fun j => ConstructionCell r c i j) (ConstructionIndices c))
    (ConstructionIndices r) 0 [] i) by
    (pose proof (construction_indices_characterization__final_results r Hr)
       as [Hlen _]; rewrite Hlen; lia).
  pose proof (construction_indices_characterization__final_results r Hr)
    as [_ [_ Hz]]. rewrite Hz by lia. reflexivity.
Qed.
Lemma construction_matrix_column__final_results : forall r c j,
  0 <= r -> 0 <= c -> 0 <= j < c ->
  map (fun row => Znth j row 0) (ConstructionMatrix r c) =
  map (fun i => ConstructionCell r c i j) (ConstructionIndices r).
Proof.
  intros r c j Hr Hc Hj. unfold ConstructionMatrix. rewrite map_map.
  apply map_ext_in. intros i Hi.
  rewrite (@Znth_map__final_results Z Z
    (fun j => ConstructionCell r c i j) (ConstructionIndices c) 0 0 j) by
    (pose proof (construction_indices_characterization__final_results c Hc)
       as [Hlen _]; rewrite Hlen; lia).
  pose proof (construction_indices_characterization__final_results c Hc)
    as [_ [_ Hz]]. rewrite Hz by lia. reflexivity.
Qed.
Lemma construction_column_gcd_many__final_results : forall r c j,
  2 <= r -> 1 <= c -> 0 <= j < c ->
  fold_right Z.gcd 0
    (map (fun row => Znth j row 0) (ConstructionMatrix r c)) = j + 1.
Proof.
  intros r c j Hr Hc Hj.
  rewrite construction_matrix_column__final_results by lia.
  rewrite construction_indices_as_Zrange__final_results by lia.
  replace (map (fun i : Z => ConstructionCell r c i j) (Zrange 0 r))
    with (map (fun i => (j + 1) * (c + 1 + i)) (Zrange 0 r)).
  - rewrite fold_gcd_map_mul__final_results by lia.
    assert (Hrange : map (Z.add (c + 1)) (Zrange 0 r) =
        Zrange (c + 1) (c + 1 + r)).
    { apply (proj2 (list_eq_ext _ _ 0)). split.
      - rewrite Zlength_map__final_results, !Zlength_Zrange__final_results by lia. lia.
      - intros k Hk. rewrite Zlength_map__final_results,
          Zlength_Zrange__final_results in Hk by lia.
        rewrite (@Znth_map__final_results Z Z (Z.add (c + 1))
          (Zrange 0 r) 0 0 k) by
          (rewrite Zlength_Zrange__final_results by lia; lia).
        rewrite !Znth_Zrange__final_results by lia. lia. }
    rewrite Hrange.
    pose proof (fold_gcd_Zrange_two_or_more__final_results
      (c + 1) r ltac:(lia) ltac:(lia)) as Hgcd.
    rewrite Hgcd. ring.
  - apply map_ext. intros i. unfold ConstructionCell.
    destruct (Z.eqb_spec r 1); [lia |]. ring.
Qed.
Lemma Znth_app_left__final_results : forall {A : Type}
    (d : A) (l1 l2 : list A) i,
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A d l1 l2 i Hi. unfold Znth. apply app_nth1.
  rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_right__final_results : forall {A : Type}
    (d : A) (l1 l2 : list A) i,
  Zlength l1 <= i ->
  Znth i (l1 ++ l2) d = Znth (i - Zlength l1) l2 d.
Proof.
  intros A d l1 l2 i Hi. unfold Znth. rewrite app_nth2.
  - f_equal. rewrite Zlength_correct. lia.
  - rewrite Zlength_correct in Hi. lia.
Qed.
Lemma construction_matrix_gcd_array_many__final_results : forall r c,
  2 <= r -> 1 <= c ->
  GcdArray r c (ConstructionMatrix r c)
    (Zrange (c + 1) (c + r + 1) ++ Zrange 1 (c + 1)).
Proof.
  intros r c Hr Hc. unfold GcdArray. split.
  - rewrite Zlength_app, !Zlength_Zrange__final_results by lia. lia.
  - split.
    + intros i Hi. unfold IsPositiveGcd.
      rewrite Znth_app_left__final_results by
        (rewrite Zlength_Zrange__final_results by lia; lia).
      rewrite Znth_Zrange__final_results by lia.
      rewrite construction_matrix_row_Znth__final_results by lia.
      split; [lia |]. split.
      * intro Hem. assert (Hz : Zlength
          (map (fun j => ConstructionCell r c i j) (ConstructionIndices c)) = 0).
        { rewrite Hem. reflexivity. }
        rewrite Zlength_map__final_results,
          (proj1 (construction_indices_characterization__final_results c ltac:(lia)))
          in Hz. lia.
      * replace (c + 1 + i) with (c + i + 1) by ring.
        symmetry. apply construction_row_gcd_many__final_results; lia.
    + intros j Hj. unfold IsPositiveGcd.
      rewrite Znth_app_right__final_results by
        (rewrite Zlength_Zrange__final_results by lia; lia).
      rewrite Zlength_Zrange__final_results by lia.
      replace (r + j - r) with j by lia.
      rewrite Znth_Zrange__final_results by lia.
      split; [lia |]. split.
      * intro Hem. assert (Hz : Zlength
          (map (fun row => Znth j row 0) (ConstructionMatrix r c)) = 0).
        { rewrite Hem. reflexivity. }
        rewrite Zlength_map__final_results in Hz.
        unfold ConstructionMatrix in Hz.
        rewrite Zlength_map__final_results,
          (proj1 (construction_indices_characterization__final_results r ltac:(lia)))
          in Hz. lia.
      * replace (1 + (r + j - (c + r + 1 - (c + 1)))) with (j + 1) by lia.
        symmetry. apply construction_column_gcd_many__final_results; lia.
Qed.
Lemma construction_matrix_column_one__final_results : forall c j,
  0 <= c -> 0 <= j < c ->
  fold_right Z.gcd 0
    (map (fun row => Znth j row 0) (ConstructionMatrix 1 c)) = j + 2.
Proof.
  intros c j Hc Hj.
  rewrite construction_matrix_column__final_results by lia.
  change (ConstructionIndices 1) with [0]. simpl.
  unfold ConstructionCell. rewrite Z.eqb_refl, Z.gcd_0_r.
  rewrite Z.abs_eq by lia. lia.
Qed.
Lemma construction_matrix_gcd_array_one__final_results : forall c,
  2 <= c ->
  GcdArray 1 c (ConstructionMatrix 1 c) (1 :: Zrange 2 (c + 2)).
Proof.
  intros c Hc. unfold GcdArray. split.
  - rewrite Zlength_cons, Zlength_Zrange__final_results by lia. lia.
  - split.
    + intros i Hi. assert (i = 0) by lia. subst i.
      unfold IsPositiveGcd. rewrite Znth0_cons.
      rewrite construction_matrix_row_Znth__final_results by lia.
      split; [lia |]. split.
      * intro Hem. assert (Hz : Zlength
          (map (fun j => ConstructionCell 1 c 0 j) (ConstructionIndices c)) = 0).
        { rewrite Hem. reflexivity. }
        rewrite Zlength_map__final_results,
          (proj1 (construction_indices_characterization__final_results c ltac:(lia)))
          in Hz. lia.
      * symmetry. apply construction_row_gcd_one__final_results. exact Hc.
    + intros j Hj. unfold IsPositiveGcd.
      rewrite Znth_cons by lia. replace (1 + j - 1) with j by lia.
      rewrite Znth_Zrange__final_results by lia.
      split; [lia |]. split.
      * intro Hem. assert (Hz : Zlength
          (map (fun row => Znth j row 0) (ConstructionMatrix 1 c)) = 0).
        { rewrite Hem. reflexivity. }
        rewrite Zlength_map__final_results in Hz.
        unfold ConstructionMatrix in Hz.
        rewrite Zlength_map__final_results,
          (proj1 (construction_indices_characterization__final_results 1 ltac:(lia)))
          in Hz. lia.
      * replace (2 + j) with (j + 2) by ring.
        symmetry. apply construction_matrix_column_one__final_results; lia.
Qed.
Lemma construction_gcds_nodup_many__final_results : forall r c,
  2 <= r -> 1 <= c ->
  NoDup (Zrange (c + 1) (c + r + 1) ++ Zrange 1 (c + 1)).
Proof.
  intros r c Hr Hc. apply NoDup_app.
  - apply NoDup_Zrange.
  - apply NoDup_Zrange.
  - intros x Hx1 Hx2. rewrite <- In_Zrange in Hx1, Hx2. lia.
Qed.
Lemma construction_gcds_nodup_one__final_results : forall c,
  2 <= c -> NoDup (1 :: Zrange 2 (c + 2)).
Proof.
  intros c Hc. constructor.
  - rewrite <- In_Zrange. lia.
  - apply NoDup_Zrange.
Qed.
Lemma construction_matrix_shape_bounds__final_results : forall r c,
  1 <= r <= 500 -> 1 <= c <= 500 ->
  Zlength (ConstructionMatrix r c) = r /\
  Forall (fun row => Zlength row = c) (ConstructionMatrix r c) /\
  Forall (Forall (fun x => 1 <= x <= 1000000000))
    (ConstructionMatrix r c).
Proof.
  intros r c Hr Hc. unfold ConstructionMatrix. split.
  - rewrite Zlength_map__final_results.
    apply (proj1 (construction_indices_characterization__final_results r ltac:(lia))).
  - split.
    + rewrite Forall_map, Forall_forall. intros i Hi.
      rewrite Zlength_map__final_results.
      apply (proj1 (construction_indices_characterization__final_results c ltac:(lia))).
    + rewrite Forall_map, Forall_forall. intros i Hi.
      rewrite Forall_map, Forall_forall. intros j Hj.
      pose proof (proj1 (proj2
        (construction_indices_characterization__final_results r ltac:(lia))) i) as Hri.
      pose proof (proj1 (proj2
        (construction_indices_characterization__final_results c ltac:(lia))) j) as Hcj.
      apply Hri in Hi. apply Hcj in Hj.
      unfold ConstructionCell. destruct (Z.eqb_spec r 1).
      * nia.
      * nia.
Qed.
Lemma construction_matrix_gcd_array__final_results : forall r c,
  1 <= r <= 500 -> 1 <= c <= 500 -> (r, c) <> (1, 1) ->
  exists b, GcdArray r c (ConstructionMatrix r c) b /\ NoDup b.
Proof.
  intros r c Hr Hc Hneq.
  destruct (Z.eqb_spec r 1) as [-> | Hr1].
  - assert (Hc1 : c <> 1) by (intro; subst; apply Hneq; reflexivity).
    exists (1 :: Zrange 2 (c + 2)). split.
    + apply construction_matrix_gcd_array_one__final_results. lia.
    + apply construction_gcds_nodup_one__final_results. lia.
  - exists (Zrange (c + 1) (c + r + 1) ++ Zrange 1 (c + 1)). split.
    + apply construction_matrix_gcd_array_many__final_results; lia.
    + apply construction_gcds_nodup_many__final_results; lia.
Qed.
Lemma construction_matrix_magnitude__final_results : forall r c,
  1 <= r <= 500 -> 1 <= c <= 500 -> (r, c) <> (1, 1) ->
  Magnitude r c (ConstructionMatrix r c) (r + c).
Proof.
  intros r c Hr Hc Hneq. unfold Magnitude.
  destruct (Z.eqb_spec r 1) as [-> | Hr1].
  - assert (Hc1 : c <> 1) by (intro; subst; apply Hneq; reflexivity).
    exists (1 :: Zrange 2 (c + 2)). split.
    + apply construction_matrix_gcd_array_one__final_results. lia.
    + unfold max_value_of_subset, max_object_of_subset.
      exists (1 + c). split.
      * split.
        -- right. rewrite <- In_Zrange. lia.
        -- intros x Hx. simpl in Hx. destruct Hx as [-> | Hx]; [lia |].
           rewrite <- In_Zrange in Hx. lia.
      * reflexivity.
  - exists (Zrange (c + 1) (c + r + 1) ++ Zrange 1 (c + 1)). split.
    + apply construction_matrix_gcd_array_many__final_results; lia.
    + unfold max_value_of_subset, max_object_of_subset.
      exists (r + c). split.
      * split.
        -- apply in_or_app. left. rewrite <- In_Zrange. lia.
        -- intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx];
             rewrite <- In_Zrange in Hx; lia.
      * reflexivity.
Qed.
Lemma construction_matrix_diverse__final_results : forall r c,
  1 <= r <= 500 -> 1 <= c <= 500 -> (r, c) <> (1, 1) ->
  DiverseMatrix r c (ConstructionMatrix r c).
Proof.
  intros r c Hr Hc Hneq. unfold DiverseMatrix.
  pose proof (construction_matrix_shape_bounds__final_results r c Hr Hc)
    as [Hlen [Hrows Hbounds]].
  repeat split; try assumption.
  destruct (construction_matrix_gcd_array__final_results r c Hr Hc Hneq)
    as [b [Hgcd Hnd]].
  exists b. split; assumption.
Qed.
Lemma gcd_array_unique__final_results : forall r c g b1 b2,
  0 <= r -> 0 <= c -> GcdArray r c g b1 -> GcdArray r c g b2 -> b1 = b2.
Proof.
  intros r c g b1 b2 Hr Hc H1 H2.
  destruct H1 as [Hlen1 [Hrow1 Hcol1]].
  destruct H2 as [Hlen2 [Hrow2 Hcol2]].
  apply (proj2 (list_eq_ext _ _ 0)). split; [lia |].
  intros i Hi. destruct (Z_lt_dec i r) as [Hir | Hir].
  - specialize (Hrow1 i ltac:(lia)). specialize (Hrow2 i ltac:(lia)).
    destruct Hrow1 as [_ [_ E1]]. destruct Hrow2 as [_ [_ E2]]. congruence.
  - specialize (Hcol1 (i - r) ltac:(lia)).
    specialize (Hcol2 (i - r) ltac:(lia)).
    destruct Hcol1 as [_ [_ E1]]. destruct Hcol2 as [_ [_ E2]].
    replace (r + (i - r)) with i in E1, E2 by lia. congruence.
Qed.
Lemma In_Znth_index__final_results : forall {A : Type} (l : list A) x d,
  In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l. induction l as [|a l IH]; intros x d Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + exists 0. split; [rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia |].
      rewrite Znth0_cons. reflexivity.
    + destruct (IH x d Hin) as [i [Hi Hz]]. exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia. exact Hz.
Qed.
Lemma gcd_array_entries_positive__final_results : forall r c g b,
  0 <= r -> 0 <= c -> GcdArray r c g b ->
  forall x, In x b -> 0 < x.
Proof.
  intros r c g b Hr Hc [Hlen [Hrow Hcol]] x Hin.
  destruct (In_Znth_index__final_results b x 0 Hin) as [i [Hi Hz]].
  destruct (Z_lt_dec i r) as [Hir | Hir].
  - specialize (Hrow i ltac:(lia)). destruct Hrow as [Hpos _].
    rewrite Hz in Hpos. lia.
  - specialize (Hcol (i - r) ltac:(lia)). destruct Hcol as [Hpos _].
    replace (r + (i - r)) with i in Hpos by lia.
    rewrite Hz in Hpos. lia.
Qed.
Lemma distinct_positive_max_lower_bound__final_results : forall b mag,
  NoDup b -> 0 <= mag ->
  (forall x, In x b -> 1 <= x <= mag) -> Zlength b <= mag.
Proof.
  intros b mag Hnd Hmag Hb.
  assert (Hincl : incl b (Zrange 1 (mag + 1))).
  { intros x Hx. rewrite <- In_Zrange. specialize (Hb x Hx). lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hnat.
  apply Nat2Z.inj_le in Hnat.
  rewrite <- !Zlength_correct in Hnat.
  rewrite Zlength_Zrange__final_results in Hnat by lia. lia.
Qed.
Lemma diverse_magnitude_lower_bound__final_results : forall r c g mag,
  1 <= r -> 1 <= c -> DiverseMatrix r c g -> Magnitude r c g mag ->
  r + c <= mag.
Proof.
  intros r c g mag Hr Hc Hdiv Hmag.
  destruct Hdiv as [_ [_ [_ [bd [Hgd Hnd]]]]].
  destruct Hmag as [bm [Hgm Hmax]].
  assert (Heq : bd = bm).
  { eapply gcd_array_unique__final_results; eauto; lia. }
  subst bd.
  unfold max_value_of_subset, max_object_of_subset in Hmax.
  destruct Hmax as [a [[Ha Hupper] Hmag_eq]]. subst a.
  assert (Hmag0 : 0 <= mag).
  { pose proof (gcd_array_entries_positive__final_results r c g bm
      ltac:(lia) ltac:(lia) Hgm mag Ha). lia. }
  assert (Hbound : forall x, In x bm -> 1 <= x <= mag).
  { intros x Hx. split.
    - pose proof (gcd_array_entries_positive__final_results r c g bm
        ltac:(lia) ltac:(lia) Hgm x Hx). lia.
    - apply Hupper. exact Hx. }
  pose proof (distinct_positive_max_lower_bound__final_results
    bm mag Hnd Hmag0 Hbound) as Hlenbound.
  destruct Hgm as [Hlen _]. lia.
Qed.
Lemma construction_matrix_optimal_spec__final_results : forall r c,
  1 <= r <= 500 -> 1 <= c <= 500 -> (r, c) <> (1, 1) ->
  Spec r c (Some (ConstructionMatrix r c)).
Proof.
  intros r c Hr Hc Hneq. unfold Spec. right.
  exists (ConstructionMatrix r c), (r + c). split; [reflexivity |].
  split.
  - apply construction_matrix_diverse__final_results; assumption.
  - split.
    + apply construction_matrix_magnitude__final_results; assumption.
    + unfold min_value_of_subset, min_object_of_subset.
      exists (r + c). split.
      * split.
        -- exists (ConstructionMatrix r c). split.
           ++ apply construction_matrix_diverse__final_results; assumption.
           ++ apply construction_matrix_magnitude__final_results; assumption.
        -- intros m' [g' [Hdiv Hmag]].
           eapply diverse_magnitude_lower_bound__final_results; eauto; lia.
      * reflexivity.
Qed.
