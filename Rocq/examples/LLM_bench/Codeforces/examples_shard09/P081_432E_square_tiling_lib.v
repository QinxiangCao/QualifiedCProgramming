Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

Definition Cell := (Z * Z)%type.
Definition AdjCell (p q : Cell) : Prop :=
  Z.abs (fst p - fst q) + Z.abs (snd p - snd q) = 1.
Definition SameColorPath (g : list (list Z)) (p q : Cell) : Prop :=
  exists path : list Cell, path <> [] /\ Znth 0 path (0, 0) = p /\ Znth (Zlength path - 1) path (0, 0) = q /\
  Forall (fun x => 0 <= fst x < Zlength g /\ 0 <= snd x < Zlength (Znth 0 g []) /\
    Znth (snd x) (Znth (fst x) g []) 0 = Znth (snd p) (Znth (fst p) g []) 0) path /\
  forall i, 0 <= i < Zlength path - 1 -> AdjCell (Znth i path (0, 0)) (Znth (i + 1) path (0, 0)).
Definition SquareTiling (n m : Z) (g : list (list Z)) : Prop :=
  (Zlength g = n /\ Forall (fun row => Zlength row = m) g) /\ Forall (Forall (fun c => 65 <= c <= 90)) g /\
  forall p, 0 <= fst p < n -> 0 <= snd p < m -> exists r c side,
    side >= 1 /\ r <= fst p < r + side /\ c <= snd p < c + side /\ r >= 0 /\ c >= 0 /\ r + side <= n /\ c + side <= m /\
    forall q, 0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath g p q <-> r <= fst q < r + side /\ c <= snd q < c + side).
Definition Flatten (g : list (list Z)) : list Z := concat g.
Definition Pre (n m : Z) : Prop :=
  (* Every clause below is stated explicitly in the P081 solver Require, which
     therefore omits the Pre(...) call:
       1 <= n <= 100 /\ 1 <= m <= 100. *)
  True.
Definition Spec (n m : Z) (out : list (list Z)) : Prop :=
  SquareTiling n m out /\ forall q, SquareTiling n m q -> ((Flatten out) = (Flatten q) \/ ((exists i, 0 <= i < Z.min (Zlength (Flatten out)) (Zlength (Flatten q)) /\
    (forall j, 0 <= j < i -> Znth j (Flatten out) 0 = Znth j (Flatten q) 0) /\
    Znth i (Flatten out) 0 < Znth i (Flatten q) 0) \/
  (Zlength (Flatten out) < Zlength (Flatten q) /\ is_prefix (Flatten out) (Flatten q)))).

(* Mathematical interfaces for the three read-only helper functions.  The
   grid is represented row-major, exactly as it is in C. *)
Definition NeighborConflict
    (flat : list Z) (n m i j c left_override : Z) : Prop :=
  (0 < i /\ Znth ((i - 1) * m + j) flat 0 = c) \/
  (i + 1 < n /\ Znth ((i + 1) * m + j) flat 0 = c) \/
  (j + 1 < m /\ Znth (i * m + j + 1) flat 0 = c) \/
  (0 < j /\
    (if Z.eq_dec left_override 0
     then Znth (i * m + j - 1) flat 0
     else left_override) = c) \/
  (j = 0 /\ left_override = c).

Definition LegalColor
    (flat : list Z) (n m i j left_override c : Z) : Prop :=
  65 <= c <= 90 /\
  ~ NeighborConflict flat n m i j c left_override.

Definition LeastLegalColor
    (flat : list Z) (n m i j left_override c : Z) : Prop :=
  LegalColor flat n m i j left_override c /\
  forall d, 65 <= d < c ->
    ~ LegalColor flat n m i j left_override d.

Definition CanPlace
    (flat : list Z) (n m i j side color : Z) : Prop :=
  1 <= side /\ i + side <= n /\ j + side <= m /\
  (forall r q,
      i <= r < i + side -> j <= q < j + side ->
      Znth (r * m + q) flat 0 = 0) /\
  (forall q,
      j <= q < j + side ->
      (0 < i -> Znth ((i - 1) * m + q) flat 0 <> color) /\
      (i + side < n -> Znth ((i + side) * m + q) flat 0 <> color)) /\
  (forall r,
      i <= r < i + side ->
      (0 < j -> Znth (r * m + j - 1) flat 0 <> color) /\
      (j + side < m -> Znth (r * m + j + side) flat 0 <> color)).

Definition ZeroPrefix (flat : list Z) (upto : Z) : Prop :=
  forall k, 0 <= k < upto -> Znth k flat 0 = 0.

Definition NoConflictBelow
    (flat : list Z) (n m i j left_override next : Z) : Prop :=
  forall color, 65 <= color < next ->
    NeighborConflict flat n m i j color left_override.

Definition EmptySquarePrefix
    (flat : list Z) (m i j side done : Z) : Prop :=
  forall off, 0 <= off < done ->
    Znth ((i + off / side) * m + (j + off mod side)) flat 0 = 0.

Definition HorizontalBoundaryClearPrefix
    (flat : list Z) (n m i j side color done : Z) : Prop :=
  forall off, 0 <= off < done ->
    (0 < i -> Znth ((i - 1) * m + (j + off)) flat 0 <> color) /\
    (i + side < n -> Znth ((i + side) * m + (j + off)) flat 0 <> color).

Definition VerticalBoundaryClearPrefix
    (flat : list Z) (n m i j side color done : Z) : Prop :=
  forall off, 0 <= off < done ->
    (0 < j -> Znth ((i + off) * m + j - 1) flat 0 <> color) /\
    (j + side < m -> Znth ((i + off) * m + j + side) flat 0 <> color).

Definition RowsOfFlat (n m : Z) (flat : list Z) (grid : list (list Z)) : Prop :=
  Zlength grid = n /\
  Forall (fun row => Zlength row = m) grid /\
  Flatten grid = flat.

Definition LexPrefixLe (upto : Z) (left right : list Z) : Prop :=
  (forall k, 0 <= k < upto -> Znth k left 0 = Znth k right 0) \/
  exists first,
    0 <= first < upto /\
    (forall k, 0 <= k < first -> Znth k left 0 = Znth k right 0) /\
    Znth first left 0 < Znth first right 0.

Definition PartialSquareComponents
    (n m : Z) (grid : list (list Z)) : Prop :=
  forall p,
    0 <= fst p < n -> 0 <= snd p < m ->
    Znth (snd p) (Znth (fst p) grid []) 0 <> 0 ->
    exists r c side,
      1 <= side /\
      0 <= r /\ 0 <= c /\ r + side <= n /\ c + side <= m /\
      r <= fst p < r + side /\ c <= snd p < c + side /\
      forall q,
        0 <= fst q < n -> 0 <= snd q < m ->
        (SameColorPath grid p q <->
         r <= fst q < r + side /\ c <= snd q < c + side).

Definition PartialTilingState
    (n m next : Z) (flat : list Z) : Prop :=
  exists grid,
    RowsOfFlat n m flat grid /\
    (forall k, 0 <= k < next -> 65 <= Znth k flat 0 <= 90) /\
    (forall k, 0 <= k < n * m ->
       Znth k flat 0 = 0 \/ 65 <= Znth k flat 0 <= 90) /\
    PartialSquareComponents n m grid /\
    (forall candidate,
       SquareTiling n m candidate ->
       LexPrefixLe next flat (Flatten candidate)).

Definition NoPlaceableColorBelow
    (flat : list Z) (n m i j next : Z) : Prop :=
  forall color, 65 <= color < next ->
    ~ CanPlace flat n m i j 1 color.

Definition GreedySideState
    (flat : list Z) (n m i j color side : Z) : Prop :=
  CanPlace flat n m i j side color /\
  forall previous_side,
    1 <= previous_side < side ->
    CanPlace flat n m i j (previous_side + 1) color /\
    exists fallback,
      LeastLegalColor flat n m i (j + previous_side) color fallback /\
      color < fallback.

Definition PaintRectanglePrefix
    (before after : list Z) (m i j side color done : Z) : Prop :=
  Zlength after = Zlength before /\
  forall index,
    0 <= index < Zlength before ->
    ((exists off,
        0 <= off < done /\
        index = (i + off / side) * m + (j + off mod side)) /\
      Znth index after 0 = color) \/
    ((forall off,
        0 <= off < done ->
        index <> (i + off / side) * m + (j + off mod side)) /\
      Znth index after 0 = Znth index before 0).

Definition CanonicalGrid (flat : list Z) : Prop :=
  forall k, 0 <= k < Zlength flat ->
    Znth k flat 0 = 0 \/ 65 <= Znth k flat 0 <= 90.

Definition CommittedFrontierState
    (n m next : Z) (flat : list Z) : Prop :=
  forall upto,
    next <= upto <= n * m ->
    (forall k, next <= k < upto -> 65 <= Znth k flat 0 <= 90) ->
    PartialTilingState n m upto flat.

Definition ChosenSquareState
    (flat : list Z) (n m i j color side : Z) : Prop :=
  LeastLegalColor flat n m i j 0 color /\
  GreedySideState flat n m i j color side.

Definition SettledSquareState
    (flat : list Z) (n m i j color side : Z) : Prop :=
  ChosenSquareState flat n m i j color side /\
  (j + side = m \/
   ~ CanPlace flat n m i j (side + 1) color \/
   exists fallback,
     LeastLegalColor flat n m i (j + side) color fallback /\
     fallback <= color).

Inductive GreedyPlacementTrace (n m : Z) : Z -> list Z -> Prop :=
| GreedyTrace_zero : forall flat,
    Zlength flat = n * m ->
    ZeroPrefix flat (n * m) ->
    GreedyPlacementTrace n m 0 flat
| GreedyTrace_skip : forall next flat,
    GreedyPlacementTrace n m next flat ->
    0 <= next < n * m ->
    65 <= Znth next flat 0 <= 90 ->
    GreedyPlacementTrace n m (next + 1) flat
| GreedyTrace_place : forall next before after i j color side,
    GreedyPlacementTrace n m next before ->
    next = i * m + j ->
    0 <= i < n ->
    0 <= j < m ->
    Znth next before 0 = 0 ->
    SettledSquareState before n m i j color side ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    GreedyPlacementTrace n m (next + 1) after.

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Lemma neighbor_conflict_five_colour_choice__colour_selection :
  forall flat n m i j left_override,
    exists color,
      65 <= color <= 69 /\
      ~ NeighborConflict flat n m i j color left_override.
Proof.
  intros flat n m i j left_override.
  destruct (classic (~ NeighborConflict flat n m i j 65 left_override)) as [H65 | H65].
  - exists 65. intuition lia.
  - apply NNPP in H65.
    destruct (classic (~ NeighborConflict flat n m i j 66 left_override)) as [H66 | H66].
    + exists 66. intuition lia.
    + apply NNPP in H66.
      destruct (classic (~ NeighborConflict flat n m i j 67 left_override)) as [H67 | H67].
      * exists 67. intuition lia.
      * apply NNPP in H67.
        destruct (classic (~ NeighborConflict flat n m i j 68 left_override)) as [H68 | H68].
        -- exists 68. intuition lia.
        -- apply NNPP in H68.
           destruct (classic (~ NeighborConflict flat n m i j 69 left_override)) as [H69 | H69].
           ++ exists 69. intuition lia.
           ++ apply NNPP in H69.
              exfalso.
              unfold NeighborConflict in *.
              repeat match goal with
                     | H : _ \/ _ |- _ => destruct H as [H | H]
                     | H : _ /\ _ |- _ => destruct H
                     end; congruence || lia.
Qed.
Lemma can_place_one_iff_legal_color__solver_colour_search :
  forall flat n m i j color,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    Znth (i * m + j) flat 0 = 0 ->
    65 <= color <= 90 ->
    (CanPlace flat n m i j 1 color <->
     LegalColor flat n m i j 0 color).
Proof.
  intros flat n m i j color Hn Hm Hi Hj Hzero Hcolor.
  split.
  - intros Hplace.
    split; [exact Hcolor |].
    unfold CanPlace in Hplace.
    destruct Hplace as [_ [_ [_ [_ [Hhorizontal Hvertical]]]]].
    unfold NeighborConflict.
    intros Hconflict.
    destruct Hconflict as
        [[Hitop Htop] |
         [[Hibottom Hbottom] |
          [[Hjright Hright] |
           [[Hjleft Hleft] | [Hjzero Hoverride]]]]].
    + specialize (Hhorizontal j ltac:(lia)).
      destruct Hhorizontal as [Hclear _].
      exact (Hclear Hitop Htop).
    + specialize (Hhorizontal j ltac:(lia)).
      destruct Hhorizontal as [_ Hclear].
      apply (Hclear ltac:(lia)).
      exact Hbottom.
    + specialize (Hvertical i ltac:(lia)).
      destruct Hvertical as [_ Hclear].
      apply (Hclear ltac:(lia)).
      exact Hright.
    + specialize (Hvertical i ltac:(lia)).
      destruct Hvertical as [Hclear _].
      apply (Hclear Hjleft).
      destruct (Z.eq_dec 0 0); [exact Hleft | contradiction].
    + lia.
  - intros [_ Hfree].
    unfold CanPlace.
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    + intros row column Hrow Hcolumn.
      assert (row = i) by lia.
      assert (column = j) by lia.
      subst row column.
      exact Hzero.
    + split.
      * intros column Hcolumn.
        assert (column = j) by lia.
        subst column.
        split.
        -- intros Hitop Htop.
           apply Hfree.
           unfold NeighborConflict.
           left. split; assumption.
        -- intros Hibottom Hbottom.
           apply Hfree.
           unfold NeighborConflict.
           right; left. split; [lia | exact Hbottom].
      * intros row Hrow.
        assert (row = i) by lia.
        subst row.
        split.
        -- intros Hjleft Hleft.
           apply Hfree.
           unfold NeighborConflict.
           right; right; right; left.
           split; [exact Hjleft |].
           destruct (Z.eq_dec 0 0); [exact Hleft | contradiction].
        -- intros Hjright Hright.
           apply Hfree.
           unfold NeighborConflict.
           right; right; left.
           split; [lia | exact Hright].
Qed.
Lemma five_colour_neighbour_available__solver_colour_search :
  forall flat n m i j,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    Znth (i * m + j) flat 0 = 0 ->
    exists color,
      65 <= color <= 69 /\
      CanPlace flat n m i j 1 color.
Proof.
  intros flat n m i j Hn Hm Hi Hj Hzero.
  assert (Hchoice :
      exists color,
        65 <= color <= 69 /\
        ~ NeighborConflict flat n m i j color 0).
  {
    destruct (classic (~ NeighborConflict flat n m i j 65 0)) as [H65 | H65].
    - exists 65. intuition lia.
    - apply NNPP in H65.
      destruct (classic (~ NeighborConflict flat n m i j 66 0)) as [H66 | H66].
      + exists 66. intuition lia.
      + apply NNPP in H66.
        destruct (classic (~ NeighborConflict flat n m i j 67 0)) as [H67 | H67].
        * exists 67. intuition lia.
        * apply NNPP in H67.
          destruct (classic (~ NeighborConflict flat n m i j 68 0)) as [H68 | H68].
          -- exists 68. intuition lia.
          -- apply NNPP in H68.
             destruct (classic (~ NeighborConflict flat n m i j 69 0)) as [H69 | H69].
             ++ exists 69. intuition lia.
             ++ apply NNPP in H69.
                exfalso.
                unfold NeighborConflict in *.
                repeat match goal with
                       | H : _ \/ _ |- _ => destruct H as [H | H]
                       | H : _ /\ _ |- _ => destruct H
                       end; congruence || lia.
  }
  destruct Hchoice as [color [[Hlo Hhi] Hfree]].
  exists color.
  split; [lia |].
  apply (proj2
    (can_place_one_iff_legal_color__solver_colour_search
       flat n m i j color Hn Hm Hi Hj Hzero ltac:(lia))).
  split; [lia | exact Hfree].
Qed.
Lemma greedy_side_extend__solver_greedy_side :
  forall flat n m i j color side fallback,
    GreedySideState flat n m i j color side ->
    CanPlace flat n m i j (side + 1) color ->
    LeastLegalColor flat n m i (j + side) color fallback ->
    color < fallback ->
    GreedySideState flat n m i j color (side + 1).
Proof.
  intros flat n m i j color side fallback Hstate Hnext Hfallback Hlt.
  unfold GreedySideState in *.
  destruct Hstate as [Hcurrent Hprevious].
  split; [exact Hnext |].
  intros previous_side Hrange.
  destruct (Z_lt_ge_dec previous_side side) as [Hbefore | Hlast].
  - apply Hprevious. lia.
  - assert (previous_side = side) by lia.
    subst previous_side.
    split; [exact Hnext |].
    exists fallback.
    split; assumption.
Qed.
Lemma replace_nth_length__solver_paint :
  forall (A : Type) (n : nat) (l : list A) (value : A),
    length (replace_nth n l value) = length l.
Proof.
  intros A n l.
  revert n.
  induction l as [|head tail IH]; intros n value; destruct n; simpl; auto.
Qed.
Lemma zlength_replace_Znth__solver_paint :
  forall (A : Type) (index : Z) (value : A) (l : list A),
    Zlength (replace_Znth index value l) = Zlength l.
Proof.
  intros A index value l.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite replace_nth_length__solver_paint.
  reflexivity.
Qed.
Lemma paint_rectangle_prefix_replace_step__solver_paint :
  forall before current m i j side color done,
    0 <= done ->
    0 <= (i + done / side) * m + (j + done mod side) < Zlength current ->
    PaintRectanglePrefix before current m i j side color done ->
    PaintRectanglePrefix before
      (replace_Znth ((i + done / side) * m + (j + done mod side))
         color current)
      m i j side color (done + 1).
Proof.
  intros before current m i j side color done Hdone Hnew Hpaint.
  destruct Hpaint as [Hlen Hpaint].
  split.
  - rewrite zlength_replace_Znth__solver_paint. exact Hlen.
  - intros index Hindex.
    set (new_index := (i + done / side) * m + (j + done mod side)).
    destruct (Z.eq_dec index new_index) as [Heq | Hneq].
    + subst index.
      left.
      split.
      * exists done. split; [lia | reflexivity].
      * rewrite Znth_replace_Znth_Same by exact Hnew.
        reflexivity.
    + specialize (Hpaint index Hindex).
      destruct Hpaint as [[[off [Hoff Hoff_index]] Hcolor] |
                          [Houtside Hsame]].
      * left.
        split.
        -- exists off. split; [lia | exact Hoff_index].
        -- rewrite Znth_replace_Znth_Diff.
           ++ exact Hcolor.
           ++ exact Hnew.
           ++ rewrite Hlen. exact Hindex.
           ++ exact (not_eq_sym Hneq).
      * right.
        split.
        -- intros off Hoff.
           destruct (Z.lt_ge_cases off done) as [Hlt | Hge].
           ++ apply Houtside. lia.
           ++ assert (off = done) by lia. subst off. exact Hneq.
        -- rewrite Znth_replace_Znth_Diff.
           ++ exact Hsame.
           ++ exact Hnew.
           ++ rewrite Hlen. exact Hindex.
           ++ exact (not_eq_sym Hneq).
Qed.
Lemma canonical_grid_replace__solver_paint :
  forall flat index color,
    0 <= index < Zlength flat ->
    65 <= color <= 90 ->
    CanonicalGrid flat ->
    CanonicalGrid (replace_Znth index color flat).
Proof.
  intros flat index color Hindex Hcolor Hcanonical.
  unfold CanonicalGrid in *.
  intros k Hk.
  rewrite zlength_replace_Znth__solver_paint in Hk.
  destruct (Z.eq_dec k index) as [Heq | Hneq].
  - subst k.
    right.
    rewrite Znth_replace_Znth_Same by exact Hindex.
    exact Hcolor.
  - specialize (Hcanonical k Hk).
    destruct Hcanonical as [Hzero | Hrange].
    + left.
      rewrite Znth_replace_Znth_Diff.
      * exact Hzero.
      * exact Hindex.
      * exact Hk.
      * exact (not_eq_sym Hneq).
    + right.
      rewrite Znth_replace_Znth_Diff.
      * exact Hrange.
      * exact Hindex.
      * exact Hk.
      * exact (not_eq_sym Hneq).
Qed.
Lemma paint_prefix_replace__solver_paint :
  forall before current m i j side color r q,
    1 <= side ->
    i <= r < i + side ->
    j <= q < j + side ->
    0 <= r * m + q < Zlength current ->
    PaintRectanglePrefix before current m i j side color
      ((r - i) * side + (q - j)) ->
    PaintRectanglePrefix before (replace_Znth (r * m + q) color current)
      m i j side color ((r - i) * side + ((q + 1) - j)).
Proof.
  intros before current m i j side color r q
    Hside Hr Hq Hindex Hpaint.
  assert (Hdiv :
      ((r - i) * side + (q - j)) / side = r - i).
  {
    replace ((r - i) * side + (q - j))
      with ((q - j) + (r - i) * side) by ring.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by lia.
    lia.
  }
  assert (Hmod :
      ((r - i) * side + (q - j)) mod side = q - j).
  {
    replace ((r - i) * side + (q - j))
      with ((q - j) + (r - i) * side) by ring.
    rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
  }
  assert (Hcoordinate :
      (i + ((r - i) * side + (q - j)) / side) * m +
        (j + ((r - i) * side + (q - j)) mod side) =
      r * m + q) by (rewrite Hdiv, Hmod; ring).
  replace ((r - i) * side + ((q + 1) - j))
    with (((r - i) * side + (q - j)) + 1) by ring.
  rewrite <- Hcoordinate.
  apply paint_rectangle_prefix_replace_step__solver_paint.
  - nia.
  - rewrite Hcoordinate. exact Hindex.
  - exact Hpaint.
Qed.
Lemma Znth_In_range__solver_final :
  forall {A : Type} (l : list A) i (d : A),
    0 <= i < Zlength l ->
    In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

(* Deferred until its supporting component lemmas have been declared.
Lemma candidate_boundary_cell_cannot_match__solver_final :
  forall n m anchor next before output output_grid candidate first
      current_i current_j color current_side candidate_side x y,
    1 <= n -> 1 <= m ->
    anchor = current_i * m + current_j ->
    anchor < first < next ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= current_i < n -> 0 <= current_j < m ->
    1 <= current_side ->
    current_i + current_side <= n -> current_j + current_side <= m ->
    1 <= candidate_side ->
    current_i + candidate_side <= n -> current_j + candidate_side <= m ->
    current_side < candidate_side ->
    first = current_i * m + (current_j + current_side) ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath candidate (current_i, current_j) z <->
       current_i <= fst z < current_i + candidate_side /\
       current_j <= snd z < current_j + candidate_side)) ->
    65 <= color ->
    65 <= color ->
    Znth (current_i * m + current_j) output 0 = color ->
    Znth (fst x * m + snd x) before 0 = color ->
    0 <= fst x < n -> 0 <= snd x < m ->
    0 <= fst y < n -> 0 <= snd y < m ->
    current_i <= fst y < current_i + candidate_side ->
    current_j <= snd y < current_j + candidate_side ->
    AdjCell y x -> False.
Proof.
  intros n m anchor next before output output_grid candidate first current_i
    current_j color current_side candidate_side x y Hn Hm Hanchor Hrange
    Hbefore Houtput Hrows Hcandidate Hci Hcj Hcurrent_side Hcurrent_i
    Hcurrent_j Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst
    Hprefix Hcurrent_component Hcolor Houtanchor Hbefore_x Hxrow Hxcol Hyrow Hycol
    Hyinside_r Hyinside_c Hadj.
  assert (Hbefore_x_nonzero : Znth (fst x * m + snd x) before 0 <> 0).
  { rewrite Hbefore_x. lia. }
  destruct (trace_existing_component_origin_before__solver_final n m anchor
    before next output output_grid x Hn Hm Hbefore Houtput ltac:(lia) Hrows
    Hxrow Hxcol Hbefore_x_nonzero) as
    [earlier [origin_before [painted [oi [oj [found [oside Horigin]]]]]]].
  destruct Horigin as [Hearlier [Hearlier_anchor [Hearlier_trace
    [Hearlier_settled [Hearlier_paint [Hoi [Hoj [Hxoi [Hxoj
      [Hx_found Hout_component]]]]]]]]]].
  destruct Hearlier_settled as [[Hearlier_least [Hearlier_place Hearlier_prev]]
    Hearlier_stop].
  destruct Hearlier_place as [Hoside [Hoi_bound [Hoj_bound Hearlier_rest]]].
  assert (Hfound_color : found = color).
  { assert (Houtput_x : Znth (fst x * m + snd x) output 0 = color).
    { rewrite (greedy_trace_prefix_persistence__solver_final n m anchor next
        before output Hn Hm ltac:(lia) Hbefore Houtput
        (fst x * m + snd x) ltac:(nia) Hbefore_x_nonzero).
      exact Hbefore_x. }
    rewrite <- Hx_found.
    rewrite (rows_of_flat_Znth__solver_final n m output output_grid
      (fst x) (snd x) Hrows Hxrow Hxcol).
    exact Houtput_x. }
  destruct (earlier_candidate_component_not_short__solver_final n m output
    output_grid candidate first current_i current_j current_side candidate_side
    x oi oj oside Hn Hm Hrows Hcandidate Hci Hcj Hcurrent_side Hcurrent_i
    Hcurrent_j Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst
    Hprefix Hcurrent_component Hoi Hoj Hoside Hoi_bound Hoj_bound Hxoi Hxoj
    ltac:(rewrite <- Hanchor, <- Hearlier; exact Hearlier_anchor)
    Hout_component) as
    [other_side [Hother_side [Hother_i [Hother_j
      [Hoside_le Hother_component]]]]].
  assert (Hcandidate_earlier_x : SameColorPath candidate (oi, oj) x).
  { apply (proj2 (Hother_component x Hxrow Hxcol)). split; lia. }
  assert (Houtput_origin_color :
      Znth (oi * m + oj) output 0 = found).
  { assert (Hpath_x_origin : SameColorPath output_grid x (oi, oj)).
    { apply (proj2 (Hout_component (oi, oj) ltac:(simpl; lia)
        ltac:(simpl; lia))). simpl. split; lia. }
    pose proof (same_color_path_endpoint_color__solver_final output_grid x
      (oi, oj) Hpath_x_origin) as Hcolors.
    simpl in Hcolors.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid oi oj Hrows
      Hoi Hoj).
    rewrite Hcolors. exact Hx_found. }
  assert (Hcandidate_origin_color :
      Znth oj (Znth oi candidate []) 0 = found).
  { rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate oi oj (square_tiling_rows__solver_final n m candidate
        Hcandidate) Hoi Hoj).
    rewrite <- Hprefix by (rewrite <- Hearlier; nia).
    exact Houtput_origin_color. }
  assert (Hcandidate_x_color :
      Znth (snd x) (Znth (fst x) candidate []) 0 = found).
  { rewrite (same_color_path_endpoint_color__solver_final candidate (oi, oj) x
      Hcandidate_earlier_x). exact Hcandidate_origin_color. }
  assert (Hcandidate_current_color :
      Znth current_j (Znth current_i candidate []) 0 = color).
  { rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate current_i current_j (square_tiling_rows__solver_final n m
        candidate Hcandidate) Hci Hcj).
    rewrite <- Hprefix by (rewrite <- Hanchor; lia).
    exact Houtanchor. }
  assert (Hcandidate_current_y :
      SameColorPath candidate (current_i, current_j) y).
  { apply (proj2 (Hcurrent_component y Hyrow Hycol)). tauto. }
  assert (Hcandidate_y_color :
      Znth (snd y) (Znth (fst y) candidate []) 0 = color).
  { rewrite (same_color_path_endpoint_color__solver_final candidate
      (current_i, current_j) y Hcandidate_current_y).
    exact Hcandidate_current_color. }
  assert (Hcandidate_x_current_color :
      Znth (snd x) (Znth (fst x) candidate []) 0 =
      Znth current_j (Znth current_i candidate []) 0).
  { rewrite Hcandidate_x_color, Hcandidate_current_color, Hfound_color.
    reflexivity. }
  pose proof (square_tiling_rows__solver_final n m candidate Hcandidate)
    as Hcandidate_rows.
  destruct Hcandidate_rows as [Hcandidate_len [Hcandidate_row_len Hflat]].
  assert (Hrow0_len : Zlength (Znth 0 candidate []) = m).
  { rewrite Forall_forall in Hcandidate_row_len.
    apply Hcandidate_row_len, Znth_In_range__solver_final.
    rewrite Hcandidate_len. lia. }
  destruct (classic (current_i <= fst x < current_i + candidate_side /\
      current_j <= snd x < current_j + candidate_side)) as [Hxinside | Hxoutside].
  - eapply exact_components_rectangles_disjoint__solver_final with
      (grid := candidate) (n := n) (m := m) (ai := oi) (aj := oj)
      (aside := other_side) (bi := current_i) (bj := current_j)
      (bside := candidate_side) (x := x); eauto; lia.
  - assert (Hcurrent_x : SameColorPath candidate (current_i, current_j) x).
    { exact (same_color_path_append__solver_final candidate (current_i, current_j)
        y x Hcandidate_current_y ltac:(rewrite Hcandidate_len; exact Hxrow)
        ltac:(rewrite Hrow0_len; exact Hxcol) Hcandidate_x_current_color Hadj). }
    apply Hxoutside.
    exact (proj1 (Hcurrent_component x Hxrow Hxcol) Hcurrent_x).
(* inactive deferred copy ends here *)
Qed.

Lemma extension_candidate_can_place__solver_final :
  forall n m anchor next before output output_grid candidate first i j color
      side candidate_side,
    1 <= n -> 1 <= m ->
    anchor = i * m + j -> anchor < first < next ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= i < n -> 0 <= j < m ->
    65 <= color ->
    CanPlace before n m i j side color ->
    1 <= candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    side < candidate_side ->
    first = i * m + (j + side) ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath candidate (i, j) z <->
       i <= fst z < i + candidate_side /\
       j <= snd z < j + candidate_side)) ->
    Znth (i * m + j) output 0 = color ->
    CanPlace before n m i j (side + 1) color.
Proof.
  intros n m anchor next before output output_grid candidate first i j color
    side candidate_side Hn Hm Hanchor Hrange Hbefore Houtput Hrows Hcandidate
    Hi Hj Hcolor Hplace Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt
    Hfirst Hprefix Hcomponent Houtanchor.
  pose proof Hplace as Hplace_full.
  destruct Hplace as [Hside [Hibound [Hjbound
    [Hempty [Hhorizontal Hvertical]]]]].
  unfold CanPlace.
  split; [lia |]. split; [lia |]. split; [lia |].
  split.
  - intros r q Hr Hq.
    exact (extension_candidate_square_empty__solver_final n m anchor next
      before output output_grid candidate first i j color side candidate_side
      Hn Hm Hanchor Hrange Hbefore Houtput Hrows Hcandidate Hi Hj Hplace_full
      Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
      Hcomponent r q ltac:(lia) ltac:(lia)).
  - split.
    + intros q Hq. split.
      * intro Hitop.
        destruct (Z.lt_ge_cases q (j + side)) as [Hqold | Hqnew].
        -- exact (proj1 (Hhorizontal q ltac:(lia)) Hitop).
        -- assert (Hqeq : q = j + side) by lia. subst q.
           intro Hmatch. exfalso.
           exact (candidate_boundary_cell_cannot_match__solver_final n m anchor
             next before output output_grid candidate first i j color side
             candidate_side (i - 1, j + side) (i, j + side) Hn Hm Hanchor
             Hrange Hbefore Houtput Hrows Hcandidate Hi Hj Hside Hibound Hjbound
             Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
             Hcomponent Hcolor Houtanchor Hmatch ltac:(simpl; lia)
             ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; lia)
             ltac:(simpl; lia) ltac:(simpl; lia)
             ltac:(unfold AdjCell; simpl; lia)).
      * intros Hibottom Hmatch. exfalso.
        exact (candidate_boundary_cell_cannot_match__solver_final n m anchor
          next before output output_grid candidate first i j color side
          candidate_side (i + side + 1, q) (i + side, q) Hn Hm Hanchor Hrange
          Hbefore Houtput Hrows Hcandidate Hi Hj Hside Hibound Hjbound
          Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
          Hcomponent Hcolor Houtanchor
          ltac:(simpl; replace ((i + side + 1) * m + q) with
            ((i + (side + 1)) * m + q) by ring; exact Hmatch)
          ltac:(simpl; lia)
          ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; lia)
          ltac:(simpl; lia) ltac:(simpl; lia)
          ltac:(unfold AdjCell; simpl; lia)).
    + intros r Hr. split.
      * intro Hileft.
        destruct (Z.lt_ge_cases r (i + side)) as [Hrold | Hrnew].
        -- exact (proj1 (Hvertical r ltac:(lia)) Hileft).
        -- assert (Hreq : r = i + side) by lia. subst r.
           intro Hmatch. exfalso.
           exact (candidate_boundary_cell_cannot_match__solver_final n m anchor
             next before output output_grid candidate first i j color side
             candidate_side (i + side, j - 1) (i + side, j) Hn Hm Hanchor
             Hrange Hbefore Houtput Hrows Hcandidate Hi Hj Hside Hibound Hjbound
             Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
             Hcomponent Hcolor Houtanchor
             ltac:(simpl; replace ((i + side) * m + (j - 1)) with
               ((i + side) * m + j - 1) by ring; exact Hmatch)
             ltac:(simpl; lia)
             ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; lia)
             ltac:(simpl; lia) ltac:(simpl; lia)
             ltac:(unfold AdjCell; simpl; lia)).
      * intros Hiright Hmatch. exfalso.
        exact (candidate_boundary_cell_cannot_match__solver_final n m anchor
          next before output output_grid candidate first i j color side
          candidate_side (r, j + side + 1) (r, j + side) Hn Hm Hanchor Hrange
          Hbefore Houtput Hrows Hcandidate Hi Hj Hside Hibound Hjbound
          Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
          Hcomponent Hcolor Houtanchor
          ltac:(simpl; replace (r * m + (j + side + 1)) with
            (r * m + j + (side + 1)) by ring; exact Hmatch)
          ltac:(simpl; lia)
          ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; lia)
          ltac:(simpl; lia) ltac:(simpl; lia)
          ltac:(unfold AdjCell; simpl; lia)).
(* inactive deferred extension copy ends here *)
Qed.
*)
Lemma rows_of_flat_nat__solver_final :
  forall (count width : nat) (flat : list Z),
    length flat = (count * width)%nat ->
    exists grid,
      length grid = count /\
      Forall (fun row => length row = width) grid /\
      concat grid = flat.
Proof.
  induction count as [|count IH]; intros width flat Hlen.
  - simpl in Hlen.
    apply length_zero_iff_nil in Hlen.
    subst flat.
    exists []. repeat split; simpl; auto.
  - assert (Hwidth : (width <= length flat)%nat) by (rewrite Hlen; lia).
    assert (Htail : length (skipn width flat) = (count * width)%nat).
    { rewrite length_skipn, Hlen. lia. }
    destruct (IH width (skipn width flat) Htail)
      as [rows [Hrows_len [Hrows_width Hrows_concat]]].
    exists (firstn width flat :: rows).
    split.
    + simpl. lia.
    + split.
      * constructor.
        -- rewrite length_firstn. lia.
        -- exact Hrows_width.
      * simpl. rewrite Hrows_concat, firstn_skipn. reflexivity.
Qed.
Lemma rows_of_flat_from_length__solver_final :
  forall n m flat,
    1 <= n ->
    1 <= m ->
    Zlength flat = n * m ->
    exists grid, RowsOfFlat n m flat grid.
Proof.
  intros n m flat Hn Hm Hlen.
  assert (Hlen_nat :
      length flat = (Z.to_nat n * Z.to_nat m)%nat).
  { apply Nat2Z.inj.
    rewrite Nat2Z.inj_mul, !Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    exact Hlen. }
  destruct (rows_of_flat_nat__solver_final
      (Z.to_nat n) (Z.to_nat m) flat Hlen_nat)
    as [grid [Hgrid_len [Hrow_len Hconcat]]].
  exists grid.
  unfold RowsOfFlat.
  split.
  - rewrite Zlength_correct, Hgrid_len, Z2Nat.id by lia. reflexivity.
  - split.
    + rewrite Forall_forall in *.
      intros row Hin.
      specialize (Hrow_len row Hin).
      rewrite Zlength_correct, Hrow_len, Z2Nat.id by lia.
      reflexivity.
    + exact Hconcat.
Qed.
Lemma paint_rectangle_index_ge_anchor__solver_final :
  forall m i j side off,
    1 <= m ->
    0 <= j ->
    1 <= side ->
    0 <= off ->
    i * m + j <=
      (i + off / side) * m + (j + off mod side).
Proof.
  intros m i j side off Hm Hj Hside Hoff.
  assert (Hdiv : 0 <= off / side) by (apply Z.div_pos; lia).
  assert (Hmod : 0 <= off mod side < side) by
    (apply Z.mod_pos_bound; lia).
  nia.
Qed.
Lemma paint_rectangle_membership__solver_final :
  forall before after n m i j side color,
    1 <= m ->
    0 <= i < n ->
    0 <= j < m ->
    Zlength before = n * m ->
    CanPlace before n m i j side color ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    Zlength after = n * m /\
    (forall index,
       0 <= index < i * m + j ->
       Znth index after 0 = Znth index before 0) /\
    Znth (i * m + j) after 0 = color.
Proof.
  intros before after n m i j side color Hm Hi Hj Hlen Hplace Hpaint.
  destruct Hplace as [Hside [Hibound [Hjbound
    [Hempty [Hhorizontal Hvertical]]]]].
  destruct Hpaint as [Hafter_len Hpaint].
  split.
  - lia.
  - split.
    + intros index Hindex.
      specialize (Hpaint index).
      assert (Hanchor_bound : 0 <= i * m + j < n * m) by nia.
      assert (Hindex_len : 0 <= index < Zlength before) by lia.
      specialize (Hpaint Hindex_len).
      destruct Hpaint as [[[off [Hoff Hoff_index]] Hcolor] |
                           [Houtside Hsame]].
      * exfalso.
        subst index.
        pose proof (paint_rectangle_index_ge_anchor__solver_final
          m i j side off Hm ltac:(lia) Hside ltac:(lia)).
        lia.
      * exact Hsame.
    + specialize (Hpaint (i * m + j)).
      assert (Hanchor_bound : 0 <= i * m + j < n * m) by nia.
      assert (Hanchor_len : 0 <= i * m + j < Zlength before) by lia.
      specialize (Hpaint Hanchor_len).
      destruct Hpaint as [[[off [Hoff Hoff_index]] Hcolor] |
                           [Houtside Hsame]].
      * exact Hcolor.
      * exfalso.
        specialize (Houtside 0).
        assert (Hsq : 0 < side * side) by nia.
        specialize (Houtside ltac:(lia)).
        rewrite Z.div_0_l, Z.mod_0_l in Houtside by lia.
        lia.
Qed.
Lemma trace_bounds_and_canonical__solver_final :
  forall n m next flat,
    1 <= n ->
    1 <= m ->
    GreedyPlacementTrace n m next flat ->
    0 <= next <= n * m /\
    Zlength flat = n * m /\
    CanonicalGrid flat /\
    (forall k, 0 <= k < next -> 65 <= Znth k flat 0 <= 90).
Proof.
  intros n m next flat Hn Hm Htrace.
  induction Htrace as
      [flat Hlen Hzero
      |next flat Htrace IH Hnext Hcell
      |next before after i j color side Htrace IH Hnext Hi Hj
         Hanchor Hsettled Hpaint].
  - split; [lia |].
    split; [exact Hlen |].
    split.
    + unfold CanonicalGrid.
      intros k Hk. left. apply Hzero. lia.
    + intros k Hk. lia.
  - destruct IH as [IHbounds [IHlen [IHcanonical IHprefix]]].
    split; [lia |].
    split; [exact IHlen |].
    split; [exact IHcanonical |].
    intros index Hindex.
    destruct (Z.eq_dec index next) as [-> | Hneq].
    + exact Hcell.
    + apply IHprefix. lia.
  - subst next.
    destruct IH as [IHbounds [IHlen [IHcanonical IHprefix]]].
    destruct Hsettled as [Hchosen Hstop].
    destruct Hchosen as [Hleast Hgreedy].
    destruct Hleast as [Hlegal Hleast].
    destruct Hlegal as [Hcolor_bounds Hconflict].
    destruct Hcolor_bounds as [Hcolor_lo Hcolor_hi].
    destruct Hgreedy as [Hplace Hprevious].
    pose proof (paint_rectangle_membership__solver_final
      before after n m i j side color Hm Hi Hj IHlen Hplace Hpaint)
      as [Hafter_len [Hbefore_anchor Hafter_anchor]].
    split; [nia |].
    split; [exact Hafter_len |].
    split.
    + unfold CanonicalGrid.
      intros k Hk.
      destruct Hpaint as [Hpaint_len Hpaint_cells].
      specialize (Hpaint_cells k).
      assert (Hk_before : 0 <= k < Zlength before) by lia.
      specialize (Hpaint_cells Hk_before).
      destruct Hpaint_cells as [[Hmember Hpainted] | [Houtside Hsame]].
      * right. rewrite Hpainted. lia.
      * rewrite Hsame. apply IHcanonical. lia.
    + intros k Hk.
      destruct (Z.eq_dec k (i * m + j)) as [-> | Hneq].
      * rewrite Hafter_anchor. lia.
      * rewrite Hbefore_anchor by lia.
        apply IHprefix. lia.
Qed.
Lemma Znth_concat_rect__solver_final :
  forall grid m r c,
    0 <= r < Zlength grid ->
    0 <= c < m ->
    Forall (fun row => Zlength row = m) grid ->
    Znth c (Znth r grid []) 0 = Znth (r * m + c) (concat grid) 0.
Proof.
  induction grid as [|row rows IH]; intros m r c Hr Hc Hrows.
  - rewrite Zlength_nil in Hr. lia.
  - apply Forall_cons_iff in Hrows as [Hrow Hrows].
    simpl concat.
    destruct (Z.eq_dec r 0) as [-> | Hr0].
    + rewrite Znth0_cons.
      rewrite app_Znth1.
      * replace (0 * m + c) with c by ring. reflexivity.
      * rewrite Hrow. lia.
    + rewrite Znth_cons by lia.
      rewrite app_Znth2.
      * replace (r * m + c - Zlength row) with ((r - 1) * m + c)
          by (rewrite Hrow; ring).
        apply IH; try assumption.
        rewrite Zlength_cons in Hr. lia.
      * rewrite Hrow. nia.
Qed.
Lemma rows_of_flat_Znth__solver_final :
  forall n m flat grid r c,
    RowsOfFlat n m flat grid ->
    0 <= r < n ->
    0 <= c < m ->
    Znth c (Znth r grid []) 0 = Znth (r * m + c) flat 0.
Proof.
  intros n m flat grid r c Hrows Hr Hc.
  destruct Hrows as [Hgrid_len [Hrow_len Hflatten]].
  rewrite <- Hflatten.
  apply Znth_concat_rect__solver_final; try assumption.
  rewrite Hgrid_len. exact Hr.
Qed.
Lemma rows_of_flat_unique__solver_final :
  forall n m flat left right,
    RowsOfFlat n m flat left ->
    RowsOfFlat n m flat right ->
    left = right.
Proof.
  intros n m flat left right Hleft Hright.
  destruct Hleft as [Hleft_len [Hleft_rows Hleft_flat]].
  destruct Hright as [Hright_len [Hright_rows Hright_flat]].
  unfold Flatten in Hleft_flat, Hright_flat.
  apply (proj2 (list_eq_ext left right [])).
  split.
  - lia.
  - intros r Hr.
    assert (Hr_left : 0 <= r < Zlength left) by exact Hr.
    assert (Hr_right : 0 <= r < Zlength right) by lia.
    apply (proj2 (list_eq_ext (Znth r left []) (Znth r right []) 0)).
    assert (Hrow_left : Zlength (Znth r left []) = m).
    { rewrite Forall_forall in Hleft_rows.
      apply Hleft_rows.
      apply Znth_In_range__solver_final with (d := []); exact Hr_left. }
    assert (Hrow_right : Zlength (Znth r right []) = m).
    { rewrite Forall_forall in Hright_rows.
      apply Hright_rows.
      apply Znth_In_range__solver_final with (d := []); exact Hr_right. }
    split; [lia |].
    intros c Hc.
    rewrite (Znth_concat_rect__solver_final left m r c Hr_left ltac:(lia)
      Hleft_rows).
    rewrite (Znth_concat_rect__solver_final right m r c Hr_right ltac:(lia)
      Hright_rows).
    rewrite Hleft_flat, Hright_flat.
    reflexivity.
Qed.
Lemma paint_rectangle_coordinate__solver_final :
  forall before after n m i j side color r c,
    1 <= m ->
    0 <= i < n ->
    0 <= j < m ->
    0 <= r < n ->
    0 <= c < m ->
    CanPlace before n m i j side color ->
    Zlength before = n * m ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    ((i <= r < i + side /\ j <= c < j + side) ->
       Znth (r * m + c) after 0 = color) /\
    (~ (i <= r < i + side /\ j <= c < j + side) ->
       Znth (r * m + c) after 0 = Znth (r * m + c) before 0).
Proof.
  intros before after n m i j side color r c Hm Hi Hj Hr Hc Hplace Hlen Hpaint.
  destruct Hplace as [Hside [Hibound [Hjbound
    [Hempty [Hhorizontal Hvertical]]]]].
  destruct Hpaint as [Hafter_len Hpaint].
  assert (Hindex : 0 <= r * m + c < Zlength before) by nia.
  specialize (Hpaint (r * m + c) Hindex).
  split.
  - intros [[Hri Hrs] [Hcj Hcs]].
    destruct Hpaint as [[Hmember Hcolor] | [Houtside Hsame]].
    + exact Hcolor.
    + exfalso.
      set (off := (r - i) * side + (c - j)).
      assert (Hoff : 0 <= off < side * side) by (unfold off; nia).
      specialize (Houtside off Hoff).
      assert (Hdiv : off / side = r - i).
      { symmetry. apply Z.div_unique with (c - j); unfold off; nia. }
      assert (Hmod : off mod side = c - j).
      { symmetry. apply Z.mod_unique with (r - i); unfold off; nia. }
      rewrite Hdiv, Hmod in Houtside.
      nia.
  - intros Houtside_rect.
    destruct Hpaint as [[Hmember Hcolor] | [Houtside Hsame]].
    + exfalso.
      destruct Hmember as [off [[Hoff0 Hoffmax] Hoffeq]].
      assert (Hdiv0 : 0 <= off / side) by (apply Z.div_pos; lia).
      assert (Hdivlt : off / side < side).
      { apply (Z.div_lt_upper_bound off side side); nia. }
      assert (Hmod : 0 <= off mod side < side) by
        (apply Z.mod_pos_bound; lia).
      assert (Hmapped_col : 0 <= j + off mod side < m) by nia.
      assert (Hrow_left : (r * m + c) / m = r).
      { symmetry. apply Z.div_unique with c; nia. }
      assert (Hrow_right :
          ((i + off / side) * m + (j + off mod side)) / m =
          i + off / side).
      { symmetry. apply Z.div_unique with (j + off mod side); nia. }
      apply Houtside_rect.
      rewrite Hoffeq in Hrow_left.
      split; nia.
    + exact Hsame.
Qed.
Lemma lex_first_difference__solver_final :
  forall next left right,
    0 <= next ->
    LexPrefixLe next left right ->
    Znth next left 0 <= Znth next right 0 ->
    LexPrefixLe (next + 1) left right.
Proof.
  intros next left right Hnext Hlex Hcell.
  unfold LexPrefixLe in *.
  destruct Hlex as [Hequal | Hstrict].
  - destruct (Z.eq_dec (Znth next left 0) (Znth next right 0))
      as [Hat | Hat].
    + left. intros k Hk.
      destruct (Z.eq_dec k next) as [-> | Hneq]; [exact Hat |].
      apply Hequal. lia.
    + right. exists next.
      split; [lia |].
      split; [exact Hequal | lia].
  - right.
    destruct Hstrict as [first [Hfirst [Hsame Hless]]].
    exists first.
    split; [lia |].
    split; assumption.
Qed.
Lemma adjcell_cases__solver_final :
  forall p q,
    AdjCell p q ->
    (fst q = fst p + 1 /\ snd q = snd p) \/
    (fst q = fst p - 1 /\ snd q = snd p) \/
    (fst q = fst p /\ snd q = snd p + 1) \/
    (fst q = fst p /\ snd q = snd p - 1).
Proof.
  intros [pr pc] [qr qc] Hadj.
  unfold AdjCell in Hadj. simpl in *.
  destruct (Z_le_gt_dec 0 (pr - qr)) as [Hr | Hr];
  destruct (Z_le_gt_dec 0 (pc - qc)) as [Hc | Hc].
  - rewrite !Z.abs_eq in Hadj by lia.
    destruct (Z.eq_dec pr qr) as [Heq | Hneq].
    + right; right; right. lia.
    + right; left. lia.
  - rewrite Z.abs_eq in Hadj by lia.
    rewrite Z.abs_neq in Hadj by lia.
    destruct (Z.eq_dec pr qr) as [Heq | Hneq].
    + right; right; left. lia.
    + right; left. lia.
  - rewrite Z.abs_neq in Hadj by lia.
    rewrite Z.abs_eq in Hadj by lia.
    destruct (Z.eq_dec pr qr) as [Heq | Hneq].
    + right; right; right. lia.
    + left. lia.
  - rewrite !Z.abs_neq in Hadj by lia.
    destruct (Z.eq_dec pr qr) as [Heq | Hneq].
    + right; right; left. lia.
    + left. lia.
Qed.
Lemma same_color_path_step__solver_final :
  forall grid p q,
    0 <= fst p < Zlength grid ->
    0 <= snd p < Zlength (Znth 0 grid []) ->
    0 <= fst q < Zlength grid ->
    0 <= snd q < Zlength (Znth 0 grid []) ->
    Znth (snd q) (Znth (fst q) grid []) 0 =
      Znth (snd p) (Znth (fst p) grid []) 0 ->
    AdjCell p q ->
    SameColorPath grid p q.
Proof.
  intros grid p q Hp_row Hp_col Hq_row Hq_col Hcolor Hadj.
  unfold SameColorPath.
  exists [p; q].
  split; [discriminate |].
  split; [reflexivity |].
  split; [reflexivity |].
  split.
  - repeat constructor; simpl; try tauto.
  - intros k Hk.
    assert (k = 0) by (cbn in Hk; lia).
    subst k. exact Hadj.
Qed.
Lemma same_color_path_refl__solver_final :
  forall grid p,
    0 <= fst p < Zlength grid ->
    0 <= snd p < Zlength (Znth 0 grid []) ->
    SameColorPath grid p p.
Proof.
  intros grid p Hp_row Hp_col.
  unfold SameColorPath.
  exists [p].
  split; [discriminate |].
  split; [reflexivity |].
  split; [reflexivity |].
  split.
  - repeat constructor; simpl; try tauto.
  - intros k Hk. cbn in Hk. lia.
Qed.
Lemma same_color_path_prepend__solver_final :
  forall grid p p' q,
    0 <= fst p < Zlength grid ->
    0 <= snd p < Zlength (Znth 0 grid []) ->
    Znth (snd p') (Znth (fst p') grid []) 0 =
      Znth (snd p) (Znth (fst p) grid []) 0 ->
    AdjCell p p' ->
    SameColorPath grid p' q ->
    SameColorPath grid p q.
Proof.
  intros grid p p' q Hp_row Hp_col Hcolor Hadj Hpath.
  destruct Hp_row as [Hp_row0 Hp_rowN].
  destruct Hp_col as [Hp_col0 Hp_colN].
  unfold SameColorPath in *.
  destruct Hpath as [path [Hnonempty [Hfirst [Hlast [Hforall Hsteps]]]]].
  exists (p :: path).
  split; [discriminate |].
  split; [reflexivity |].
  assert (Hpath_pos : 0 < Zlength path).
  { destruct path as [|x xs]; [contradiction |].
    rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
  split.
  - rewrite Zlength_cons.
    transitivity (Znth (Zlength path) (p :: path) (0, 0)).
    + apply (f_equal (fun idx : Z =>
        Znth idx (p :: path) (0, 0))).
      change (Zlength path + 1 - 1 = Zlength path).
      lia.
    + rewrite Znth_cons by lia. exact Hlast.
  - split.
    + constructor.
      * repeat split; try assumption; reflexivity.
      * eapply Forall_impl; [| exact Hforall].
        intros x [Hxrow [Hxcol Hxcolor]].
        destruct Hxrow as [Hxrow0 HxrowN].
        destruct Hxcol as [Hxcol0 HxcolN].
        repeat split; try assumption.
        rewrite <- Hcolor. exact Hxcolor.
    + intros k Hk.
      rewrite Zlength_cons in Hk.
      change (0 <= k < Zlength path + 1 - 1) in Hk.
      destruct (Z.eq_dec k 0) as [-> | Hk0].
      * change (AdjCell p (Znth 0 path (0, 0))).
        rewrite Hfirst. exact Hadj.
      * rewrite Znth_cons by lia.
        rewrite Znth_cons by lia.
        replace (k + 1 - 1) with k by lia.
        specialize (Hsteps (k - 1) ltac:(lia)).
        replace (k - 1 + 1) with k in Hsteps by lia.
        exact Hsteps.
Qed.
Lemma manhattan_row_up__solver_final :
  forall pr pc qr qc,
    pr < qr ->
    Z.abs (pr + 1 - qr) + Z.abs (pc - qc) <
    Z.abs (pr - qr) + Z.abs (pc - qc).
Proof.
  intros. rewrite <- (Z.abs_opp (pr + 1 - qr)).
  rewrite <- (Z.abs_opp (pr - qr)).
  rewrite !Z.abs_eq by lia. lia.
Qed.
Lemma manhattan_row_down__solver_final :
  forall pr pc qr qc,
    qr < pr ->
    Z.abs (pr - 1 - qr) + Z.abs (pc - qc) <
    Z.abs (pr - qr) + Z.abs (pc - qc).
Proof.
  intros. rewrite !Z.abs_eq by lia. lia.
Qed.
Lemma manhattan_col_up__solver_final :
  forall pr pc qr qc,
    pc < qc ->
    Z.abs (pr - qr) + Z.abs (pc + 1 - qc) <
    Z.abs (pr - qr) + Z.abs (pc - qc).
Proof.
  intros. rewrite <- (Z.abs_opp (pc + 1 - qc)).
  rewrite <- (Z.abs_opp (pc - qc)).
  replace (-(pc + 1 - qc)) with (qc - pc - 1) by ring.
  replace (-(pc - qc)) with (qc - pc) by ring.
  rewrite (Z.abs_eq (qc - pc - 1)) by lia.
  rewrite (Z.abs_eq (qc - pc)) by lia. lia.
Qed.
Lemma manhattan_col_down__solver_final :
  forall pr pc qr qc,
    qc < pc ->
    Z.abs (pr - qr) + Z.abs (pc - 1 - qc) <
    Z.abs (pr - qr) + Z.abs (pc - qc).
Proof.
  intros.
  rewrite (Z.abs_eq (pc - 1 - qc)) by lia.
  rewrite (Z.abs_eq (pc - qc)) by lia. lia.
Qed.
Lemma rectangle_connected__solver_final :
  forall grid r c side color p q,
    1 <= side ->
    0 <= r -> 0 <= c ->
    r + side <= Zlength grid ->
    c + side <= Zlength (Znth 0 grid []) ->
    r <= fst p < r + side -> c <= snd p < c + side ->
    r <= fst q < r + side -> c <= snd q < c + side ->
    (forall x,
       r <= fst x < r + side -> c <= snd x < c + side ->
       Znth (snd x) (Znth (fst x) grid []) 0 = color) ->
    SameColorPath grid p q.
Proof.
  intros grid r c side color.
  assert (Hwalk : forall fuel p q,
      Z.to_nat (Z.abs (fst p - fst q) + Z.abs (snd p - snd q)) = fuel ->
      1 <= side -> 0 <= r -> 0 <= c ->
      r + side <= Zlength grid ->
      c + side <= Zlength (Znth 0 grid []) ->
      r <= fst p < r + side -> c <= snd p < c + side ->
      r <= fst q < r + side -> c <= snd q < c + side ->
      (forall x,
         r <= fst x < r + side -> c <= snd x < c + side ->
         Znth (snd x) (Znth (fst x) grid []) 0 = color) ->
      SameColorPath grid p q).
  { induction fuel using lt_wf_ind.
    intros p q Hfuel Hside Hr Hc Hrbound Hcbound
      Hp_row Hp_col Hq_row Hq_col Hpaint.
    destruct (Z.eq_dec (fst p) (fst q)) as [Hroweq | Hrowneq].
    - destruct (Z.eq_dec (snd p) (snd q)) as [Hcoleq | Hcolneq].
      + assert (p = q) by (destruct p, q; simpl in *; congruence).
        subst q. apply same_color_path_refl__solver_final; lia.
      + destruct (Z_lt_ge_dec (snd p) (snd q)) as [Hlt | Hgt]; [|].
        * set (p' := (fst p, snd p + 1)).
          eapply same_color_path_prepend__solver_final with (p' := p').
          -- unfold p'; simpl; lia.
          -- unfold p'; simpl; lia.
          -- rewrite (Hpaint p') by (unfold p'; simpl; lia).
             rewrite (Hpaint p) by lia. reflexivity.
          -- unfold AdjCell, p'; simpl.
             replace (fst p - fst p) with 0 by lia.
             replace (snd p - (snd p + 1)) with (-1) by lia.
             reflexivity.
          -- apply (H (Z.to_nat
                (Z.abs (fst p' - fst q) + Z.abs (snd p' - snd q))));
               try assumption; try (unfold p'; simpl; lia).
        * set (p' := (fst p, snd p - 1)).
          eapply same_color_path_prepend__solver_final with (p' := p');
            try (unfold p'; simpl; lia).
          -- rewrite (Hpaint p') by (unfold p'; simpl; lia).
             rewrite (Hpaint p) by lia. reflexivity.
          -- unfold AdjCell, p'; simpl.
             replace (fst p - fst p) with 0 by lia.
             replace (snd p - (snd p - 1)) with 1 by lia.
             reflexivity.
          -- apply (H (Z.to_nat
                (Z.abs (fst p' - fst q) + Z.abs (snd p' - snd q))));
               try assumption; try (unfold p'; simpl; lia).
    - destruct (Z_lt_ge_dec (fst p) (fst q)) as [Hlt | Hgt]; [|].
      + set (p' := (fst p + 1, snd p)).
        eapply same_color_path_prepend__solver_final with (p' := p');
          try (unfold p'; simpl; lia).
        * rewrite (Hpaint p') by (unfold p'; simpl; lia).
          rewrite (Hpaint p) by lia. reflexivity.
        * unfold AdjCell, p'; simpl.
          replace (fst p - (fst p + 1)) with (-1) by lia.
          replace (snd p - snd p) with 0 by lia. reflexivity.
        * apply (H (Z.to_nat
              (Z.abs (fst p' - fst q) + Z.abs (snd p' - snd q))));
             try assumption; try (unfold p'; simpl; lia).
      + set (p' := (fst p - 1, snd p)).
        eapply same_color_path_prepend__solver_final with (p' := p');
          try (unfold p'; simpl; lia).
        * rewrite (Hpaint p') by (unfold p'; simpl; lia).
          rewrite (Hpaint p) by lia. reflexivity.
        * unfold AdjCell, p'; simpl.
          replace (fst p - (fst p - 1)) with 1 by lia.
          replace (snd p - snd p) with 0 by lia. reflexivity.
        * apply (H (Z.to_nat
              (Z.abs (fst p' - fst q) + Z.abs (snd p' - snd q))));
             try assumption; try (unfold p'; simpl; lia).
          }
  intros p q Hside Hr Hc Hrbound Hcbound Hp_row Hp_col Hq_row Hq_col Hpaint.
  eapply Hwalk; eauto.
Qed.
Lemma path_region_induction__solver_final :
  forall grid color (region : Cell -> Prop) path,
    path <> [] ->
    Forall (fun x =>
      0 <= fst x < Zlength grid /\
      0 <= snd x < Zlength (Znth 0 grid []) /\
      Znth (snd x) (Znth (fst x) grid []) 0 = color) path ->
    region (Znth 0 path (0, 0)) ->
    (forall x y,
      region x ->
      0 <= fst y < Zlength grid ->
      0 <= snd y < Zlength (Znth 0 grid []) ->
      Znth (snd y) (Znth (fst y) grid []) 0 = color ->
      AdjCell x y -> region y) ->
    (forall k, 0 <= k < Zlength path - 1 ->
      AdjCell (Znth k path (0, 0)) (Znth (k + 1) path (0, 0))) ->
    Forall region path.
Proof.
  intros grid color region path.
  induction path as [|x tail IH]; intros Hnonempty Hforall Hfirst Hclosed Hsteps.
  - contradiction.
  - constructor.
    + exact Hfirst.
    + destruct tail as [|y ys].
      * constructor.
      * apply IH.
        -- discriminate.
        -- inversion Hforall; assumption.
        -- inversion Hforall as [|? ? Hx Htail].
           inversion Htail as [|? ? Hy Hys].
           destruct Hy as [Hyrow [Hycol Hycolor]].
           apply (Hclosed x y Hfirst); try assumption.
           specialize (Hsteps 0).
           assert (Hbound0 : 0 <= 0 < Zlength (x :: y :: ys) - 1).
           { repeat rewrite Zlength_cons. pose proof (Zlength_nonneg ys). lia. }
           specialize (Hsteps Hbound0).
           exact Hsteps.
        -- exact Hclosed.
        -- intros k Hk.
           specialize (Hsteps (k + 1)).
           assert (Hboundk : 0 <= k + 1 < Zlength (x :: y :: ys) - 1).
           { repeat rewrite Zlength_cons in *. lia. }
           specialize (Hsteps Hboundk).
           assert (Hshift1 : Znth (k + 1) (x :: y :: ys) (0, 0) =
               Znth k (y :: ys) (0, 0)).
           { rewrite Znth_cons by lia. replace (k + 1 - 1) with k by lia.
             reflexivity. }
           assert (Hshift2 : Znth (k + 1 + 1) (x :: y :: ys) (0, 0) =
               Znth (k + 1) (y :: ys) (0, 0)).
           { rewrite Znth_cons by lia.
             replace (k + 1 + 1 - 1) with (k + 1) by lia. reflexivity. }
           rewrite Hshift1, Hshift2 in Hsteps.
           exact Hsteps.
Qed.
Lemma same_color_path_closed__solver_final :
  forall grid color (region : Cell -> Prop) p q,
    SameColorPath grid p q ->
    region p ->
    (forall x y,
      region x ->
      0 <= fst y < Zlength grid ->
      0 <= snd y < Zlength (Znth 0 grid []) ->
      Znth (snd y) (Znth (fst y) grid []) 0 = color ->
      AdjCell x y -> region y) ->
    Znth (snd p) (Znth (fst p) grid []) 0 = color ->
    region q.
Proof.
  intros grid color region p q Hpath Hp Hclosed Hpcolor.
  unfold SameColorPath in Hpath.
  destruct Hpath as [path [Hnonempty [Hfirst [Hlast [Hforall Hsteps]]]]].
  assert (Hforall_color : Forall (fun x =>
      0 <= fst x < Zlength grid /\
      0 <= snd x < Zlength (Znth 0 grid []) /\
      Znth (snd x) (Znth (fst x) grid []) 0 = color) path).
  { eapply Forall_impl; [| exact Hforall].
    intros x [Hxrow [Hxcol Hxcolor]].
    destruct Hxrow as [Hxrow0 HxrowN].
    destruct Hxcol as [Hxcol0 HxcolN].
    repeat split; try assumption. rewrite Hxcolor. exact Hpcolor. }
  assert (Hregions : Forall region path).
  { eapply path_region_induction__solver_final.
    - exact Hnonempty.
    - exact Hforall_color.
    - exact (eq_rect p region Hp (Znth 0 path (0, 0)) (eq_sym Hfirst)).
    - exact Hclosed.
    - exact Hsteps. }
  rewrite Forall_forall in Hregions.
  rewrite <- Hlast.
  apply Hregions.
  apply Znth_In_range__solver_final.
  destruct path; [contradiction |].
  rewrite Zlength_cons. pose proof (Zlength_nonneg path). lia.
Qed.
Lemma sealed_component_unique__solver_final :
  forall before after n m i j side color grid p q,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    Zlength before = n * m ->
    CanPlace before n m i j side color ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    RowsOfFlat n m after grid ->
    i <= fst p < i + side -> j <= snd p < j + side ->
    0 <= fst q < n -> 0 <= snd q < m ->
    (SameColorPath grid p q <->
     i <= fst q < i + side /\ j <= snd q < j + side).
Proof.
  intros before after n m i j side color grid p q Hn Hm Hi Hj Hlen
    Hplace Hpaint Hrows Hp_row Hp_col Hq_row Hq_col.
  destruct Hplace as [Hside [Hibound [Hjbound
    [Hempty [Hhorizontal Hvertical]]]]].
  assert (Hplace' : CanPlace before n m i j side color).
  { unfold CanPlace.
    exact (conj Hside (conj Hibound (conj Hjbound
      (conj Hempty (conj Hhorizontal Hvertical))))). }
  assert (Hpainted : forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      i <= fst x < i + side -> j <= snd x < j + side ->
      Znth (snd x) (Znth (fst x) grid []) 0 = color).
  { intros x Hxrow Hxcol Hxinrow Hxincol.
    rewrite (rows_of_flat_Znth__solver_final n m after grid
      (fst x) (snd x) Hrows Hxrow Hxcol).
    apply (proj1 (paint_rectangle_coordinate__solver_final before after n m
      i j side color (fst x) (snd x) Hm Hi Hj Hxrow Hxcol Hplace'
      Hlen Hpaint)).
    tauto. }
  split.
  - intros Hpath.
    eapply same_color_path_closed__solver_final with
      (color := color)
      (region := fun x =>
        i <= fst x < i + side /\ j <= snd x < j + side) in Hpath.
    + exact Hpath.
    + tauto.
    + intros x y Hxin Hyrow_grid Hycol_grid Hycolor Hadj.
      pose proof Hrows as Hrows_parts.
      destruct Hrows_parts as [Hgrid_len [Hrow_len Hflat]].
      assert (Hyrow : 0 <= fst y < n) by lia.
      assert (Hrow0_len : Zlength (Znth 0 grid []) = m).
      { rewrite Forall_forall in Hrow_len.
        apply Hrow_len.
        apply Znth_In_range__solver_final.
        rewrite Hgrid_len. lia. }
      assert (Hycol : 0 <= snd y < m) by lia.
      destruct (classic
        (i <= fst y < i + side /\ j <= snd y < j + side)) as [Hin | Hout].
      * exact Hin.
      * exfalso.
        assert (Hafter_before :
          Znth (fst y * m + snd y) after 0 =
          Znth (fst y * m + snd y) before 0).
        { apply (proj2 (paint_rectangle_coordinate__solver_final before after
            n m i j side color (fst y) (snd y) Hm Hi Hj Hyrow Hycol
            Hplace' Hlen Hpaint)). exact Hout. }
        assert (Hyflat : Znth (fst y * m + snd y) after 0 = color).
        { rewrite <- (rows_of_flat_Znth__solver_final n m after grid
            (fst y) (snd y) Hrows Hyrow Hycol).
          exact Hycolor. }
        rewrite Hafter_before in Hyflat.
        destruct (adjcell_cases__solver_final x y Hadj) as
          [[Hy_r Hy_c] | [[Hy_r Hy_c] | [[Hy_r Hy_c] | [Hy_r Hy_c]]]].
        -- destruct Hxin as [[Hxi0 Hxi1] [Hxj0 Hxj1]].
           assert (Hboundary : fst y = i + side) by lia.
           specialize (Hhorizontal (snd y) ltac:(lia)).
           destruct Hhorizontal as [_ Hbottom]. specialize (Hbottom ltac:(lia)).
           rewrite Hboundary in Hyflat. exact (Hbottom Hyflat).
        -- destruct Hxin as [[Hxi0 Hxi1] [Hxj0 Hxj1]].
           assert (Hboundary : fst y = i - 1) by lia.
           specialize (Hhorizontal (snd y) ltac:(lia)).
           destruct Hhorizontal as [Htop _]. specialize (Htop ltac:(lia)).
           rewrite Hboundary in Hyflat. exact (Htop Hyflat).
        -- destruct Hxin as [[Hxi0 Hxi1] [Hxj0 Hxj1]].
           assert (Hboundary : snd y = j + side) by lia.
           specialize (Hvertical (fst y) ltac:(lia)).
           destruct Hvertical as [_ Hright]. specialize (Hright ltac:(lia)).
           rewrite Hboundary in Hyflat. apply Hright.
           replace (fst y * m + j + side) with
             (fst y * m + (j + side)) by ring. exact Hyflat.
        -- destruct Hxin as [[Hxi0 Hxi1] [Hxj0 Hxj1]].
           assert (Hboundary : snd y = j - 1) by lia.
           specialize (Hvertical (fst y) ltac:(lia)).
           destruct Hvertical as [Hleft _]. specialize (Hleft ltac:(lia)).
           rewrite Hboundary in Hyflat. apply Hleft.
           replace (fst y * m + j - 1) with
             (fst y * m + (j - 1)) by ring. exact Hyflat.
    + apply Hpainted; try lia.
  - intros Hqin.
    destruct Hrows as [Hgrid_len [Hrow_len Hflat]].
    assert (Hrow0_len : Zlength (Znth 0 grid []) = m).
    { rewrite Forall_forall in Hrow_len.
      apply Hrow_len.
      apply Znth_In_range__solver_final.
      rewrite Hgrid_len. lia. }
    eapply rectangle_connected__solver_final with
      (r := i) (c := j) (side := side) (color := color);
      try lia; try tauto.
    intros x Hxrow Hxcol.
    apply Hpainted; try lia.
Qed.
Lemma same_color_path_append__solver_final :
  forall grid p x y,
    SameColorPath grid p x ->
    0 <= fst y < Zlength grid ->
    0 <= snd y < Zlength (Znth 0 grid []) ->
    Znth (snd y) (Znth (fst y) grid []) 0 =
      Znth (snd p) (Znth (fst p) grid []) 0 ->
    AdjCell x y ->
    SameColorPath grid p y.
Proof.
  intros grid p x y Hpath Hyrow Hycol Hycolor Hadj.
  unfold SameColorPath in *.
  destruct Hpath as [path [Hnonempty [Hfirst [Hlast [Hforall Hsteps]]]]].
  assert (Hpath_pos : 0 < Zlength path).
  { destruct path; [contradiction |].
    rewrite Zlength_cons. pose proof (Zlength_nonneg path). lia. }
  exists (path ++ [y]).
  split.
  - intro Hnil. apply app_eq_nil in Hnil as [_ Hbad]. discriminate.
  - split.
    + rewrite app_Znth1 by lia. exact Hfirst.
    + split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil.
        replace (Zlength path + (0 + 1) - 1) with (Zlength path) by lia.
        rewrite app_Znth2 by lia.
        replace (Zlength path + Z.succ 0 - 1 - Zlength path) with 0 by lia.
        reflexivity.
      * split.
        -- apply Forall_app. split; [exact Hforall |].
           constructor.
           ++ exact (conj Hyrow (conj Hycol Hycolor)).
           ++ constructor.
        -- intros k Hk.
           rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
           destruct (Z.eq_dec k (Zlength path - 1)) as [Hlastk | Hbefore].
           ++ subst k.
              rewrite app_Znth1 by lia.
              replace (Zlength path - 1 + 1) with (Zlength path) by lia.
              rewrite app_Znth2 by lia.
              replace (Zlength path - Zlength path) with 0 by lia.
              change (AdjCell (Znth (Zlength path - 1) path (0, 0)) y).
              rewrite Hlast. exact Hadj.
           ++ rewrite app_Znth1 by lia.
              rewrite app_Znth1 by lia.
              apply Hsteps. lia.
Qed.
Lemma same_color_path_endpoint_color__solver_final :
  forall grid p q,
    SameColorPath grid p q ->
    Znth (snd q) (Znth (fst q) grid []) 0 =
      Znth (snd p) (Znth (fst p) grid []) 0.
Proof.
  intros grid p q Hpath.
  unfold SameColorPath in Hpath.
  destruct Hpath as [path [Hnonempty [Hfirst [Hlast [Hforall Hsteps]]]]].
  rewrite Forall_forall in Hforall.
  specialize (Hforall (Znth (Zlength path - 1) path (0, 0))).
  assert (Hin : In (Znth (Zlength path - 1) path (0, 0)) path).
  { apply Znth_In_range__solver_final.
    destruct path; [contradiction |].
    rewrite Zlength_cons. pose proof (Zlength_nonneg path). lia. }
  specialize (Hforall Hin).
  destruct Hforall as [_ [_ Hcolor]].
  rewrite Hlast in Hcolor. exact Hcolor.
Qed.
Lemma old_component_preserved__solver_final :
  forall before after n m i j side color before_grid after_grid p
      r c old_side,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    Zlength before = n * m ->
    CanPlace before n m i j side color ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    RowsOfFlat n m before before_grid ->
    RowsOfFlat n m after after_grid ->
    0 <= fst p < n -> 0 <= snd p < m ->
    ~ (i <= fst p < i + side /\ j <= snd p < j + side) ->
    Znth (snd p) (Znth (fst p) after_grid []) 0 <> 0 ->
    1 <= old_side ->
    0 <= r -> 0 <= c -> r + old_side <= n -> c + old_side <= m ->
    r <= fst p < r + old_side -> c <= snd p < c + old_side ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath before_grid p q <->
       r <= fst q < r + old_side /\ c <= snd q < c + old_side)) ->
    forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath after_grid p q <->
       r <= fst q < r + old_side /\ c <= snd q < c + old_side).
Proof.
  intros before after n m i j side color before_grid after_grid p
    r c old_side Hn Hm Hi Hj Hlen Hplace Hpaint Hbefore_rows Hafter_rows
    Hp_row Hp_col Hp_out Hp_nonzero Hold_side Hr0 Hc0 Hrbound Hcbound
    Hp_oldrow Hp_oldcol Holdcomponent q Hq_row Hq_col.
  destruct Hplace as [Hside [Hibound [Hjbound
    [Hempty [Hhorizontal Hvertical]]]]].
  assert (Hplace' : CanPlace before n m i j side color).
  { unfold CanPlace.
    exact (conj Hside (conj Hibound (conj Hjbound
      (conj Hempty (conj Hhorizontal Hvertical))))). }
  assert (Hp_after_flat :
      Znth (fst p * m + snd p) after 0 =
      Znth (snd p) (Znth (fst p) after_grid []) 0).
  { symmetry. apply rows_of_flat_Znth__solver_final with (n := n) (m := m);
      assumption. }
  assert (Hp_same : Znth (fst p * m + snd p) after 0 =
      Znth (fst p * m + snd p) before 0).
  { apply (proj2 (paint_rectangle_coordinate__solver_final before after n m
      i j side color (fst p) (snd p) Hm Hi Hj Hp_row Hp_col Hplace'
      Hlen Hpaint)). exact Hp_out. }
  assert (Hp_before_nonzero :
      Znth (snd p) (Znth (fst p) before_grid []) 0 <> 0).
  { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
      (fst p) (snd p) Hbefore_rows Hp_row Hp_col).
    rewrite <- Hp_same, Hp_after_flat. exact Hp_nonzero. }
  assert (Hbefore_grid_len : Zlength before_grid = n) by
    (destruct Hbefore_rows as [? [? ?]]; assumption).
  assert (Hafter_grid_len : Zlength after_grid = n) by
    (destruct Hafter_rows as [? [? ?]]; assumption).
  assert (Hbefore_row0 : Zlength (Znth 0 before_grid []) = m).
  { destruct Hbefore_rows as [Hgl [Hrl Hfl]].
    rewrite Forall_forall in Hrl. apply Hrl.
    apply Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hafter_row0 : Zlength (Znth 0 after_grid []) = m).
  { destruct Hafter_rows as [Hgl [Hrl Hfl]].
    rewrite Forall_forall in Hrl. apply Hrl.
    apply Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hold_out : forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      r <= fst x < r + old_side -> c <= snd x < c + old_side ->
      ~ (i <= fst x < i + side /\ j <= snd x < j + side)).
  { intros x Hxrow Hxcol Hxoldrow Hxoldcol Hxin.
    assert (Hpath_before : SameColorPath before_grid p x).
    { apply (proj2 (Holdcomponent x Hxrow Hxcol)). tauto. }
    pose proof (same_color_path_endpoint_color__solver_final before_grid p x
      Hpath_before) as Hxcolor.
    assert (Hxzero : Znth (snd x) (Znth (fst x) before_grid []) 0 = 0).
    { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
        (fst x) (snd x) Hbefore_rows Hxrow Hxcol).
      apply Hempty; tauto. }
    rewrite Hxzero in Hxcolor. exact (Hp_before_nonzero (eq_sym Hxcolor)). }
  assert (Hold_after_color : forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      r <= fst x < r + old_side -> c <= snd x < c + old_side ->
      Znth (snd x) (Znth (fst x) after_grid []) 0 =
      Znth (snd p) (Znth (fst p) after_grid []) 0).
  { intros x Hxrow Hxcol Hxoldrow Hxoldcol.
    assert (Hxout := Hold_out x Hxrow Hxcol Hxoldrow Hxoldcol).
    assert (Hxsame : Znth (fst x * m + snd x) after 0 =
        Znth (fst x * m + snd x) before 0).
    { apply (proj2 (paint_rectangle_coordinate__solver_final before after n m
        i j side color (fst x) (snd x) Hm Hi Hj Hxrow Hxcol Hplace'
        Hlen Hpaint)). exact Hxout. }
    assert (Hpath_before : SameColorPath before_grid p x).
    { apply (proj2 (Holdcomponent x Hxrow Hxcol)). tauto. }
    pose proof (same_color_path_endpoint_color__solver_final before_grid p x
      Hpath_before) as Hxcolor.
    rewrite (rows_of_flat_Znth__solver_final n m after after_grid
      (fst x) (snd x) Hafter_rows Hxrow Hxcol).
    rewrite (rows_of_flat_Znth__solver_final n m after after_grid
      (fst p) (snd p) Hafter_rows Hp_row Hp_col).
    rewrite Hxsame, Hp_same.
    rewrite <- (rows_of_flat_Znth__solver_final n m before before_grid
      (fst x) (snd x) Hbefore_rows Hxrow Hxcol).
    rewrite <- (rows_of_flat_Znth__solver_final n m before before_grid
      (fst p) (snd p) Hbefore_rows Hp_row Hp_col).
    exact Hxcolor. }
  split.
  - intros Hpath_after.
    eapply same_color_path_closed__solver_final with
      (color := Znth (snd p) (Znth (fst p) after_grid []) 0)
      (region := fun x =>
        r <= fst x < r + old_side /\ c <= snd x < c + old_side)
      in Hpath_after.
    + exact Hpath_after.
    + tauto.
    + intros x y Hxold Hyrow_grid Hycol_grid Hycolor Hadj.
      assert (Hyrow : 0 <= fst y < n) by lia.
      assert (Hycol : 0 <= snd y < m) by lia.
      destruct (classic
        (r <= fst y < r + old_side /\ c <= snd y < c + old_side))
        as [Hyold | Hyoutold]; [exact Hyold |].
      exfalso.
      assert (Hxrow : 0 <= fst x < n) by lia.
      assert (Hxcol : 0 <= snd x < m) by lia.
      destruct Hxold as [Hxoldrow Hxoldcol].
      destruct (classic
        (i <= fst y < i + side /\ j <= snd y < j + side))
        as [Hynew | Hyoutnew].
      * assert (Hynewcolor :
          Znth (snd y) (Znth (fst y) after_grid []) 0 = color).
        { rewrite (rows_of_flat_Znth__solver_final n m after after_grid
            (fst y) (snd y) Hafter_rows Hyrow Hycol).
          apply (proj1 (paint_rectangle_coordinate__solver_final before after
            n m i j side color (fst y) (snd y) Hm Hi Hj Hyrow Hycol
            Hplace' Hlen Hpaint)). exact Hynew. }
        assert (Hxoutnew := Hold_out x Hxrow Hxcol Hxoldrow Hxoldcol).
        assert (Hxbefore :
          Znth (fst x * m + snd x) before 0 =
          Znth (snd p) (Znth (fst p) after_grid []) 0).
        { pose proof (Hold_after_color x Hxrow Hxcol Hxoldrow Hxoldcol) as Hxc.
          rewrite (rows_of_flat_Znth__solver_final n m after after_grid
            (fst x) (snd x) Hafter_rows Hxrow Hxcol) in Hxc.
          rewrite (proj2 (paint_rectangle_coordinate__solver_final before after
            n m i j side color (fst x) (snd x) Hm Hi Hj Hxrow Hxcol
            Hplace' Hlen Hpaint) Hxoutnew) in Hxc.
          exact Hxc. }
        rewrite Hynewcolor in Hycolor.
        rewrite <- Hycolor in Hxbefore.
        destruct (adjcell_cases__solver_final x y Hadj) as
          [[Hy_r Hy_c] | [[Hy_r Hy_c] | [[Hy_r Hy_c] | [Hy_r Hy_c]]]].
        -- assert (Hboundary : fst x = i - 1) by lia.
           specialize (Hhorizontal (snd x) ltac:(lia)).
           destruct Hhorizontal as [Htop _]. specialize (Htop ltac:(lia)).
           rewrite Hboundary in Hxbefore. exact (Htop Hxbefore).
        -- assert (Hboundary : fst x = i + side) by lia.
           specialize (Hhorizontal (snd x) ltac:(lia)).
           destruct Hhorizontal as [_ Hbottom]. specialize (Hbottom ltac:(lia)).
           rewrite Hboundary in Hxbefore. exact (Hbottom Hxbefore).
        -- assert (Hboundary : snd x = j - 1) by lia.
           specialize (Hvertical (fst x) ltac:(lia)).
           destruct Hvertical as [Hleft _]. specialize (Hleft ltac:(lia)).
           rewrite Hboundary in Hxbefore. apply Hleft.
           replace (fst x * m + j - 1) with (fst x * m + (j - 1)) by ring.
           exact Hxbefore.
        -- assert (Hboundary : snd x = j + side) by lia.
           specialize (Hvertical (fst x) ltac:(lia)).
           destruct Hvertical as [_ Hright]. specialize (Hright ltac:(lia)).
           rewrite Hboundary in Hxbefore. apply Hright.
           replace (fst x * m + j + side) with
             (fst x * m + (j + side)) by ring. exact Hxbefore.
      * assert (Hysame : Znth (fst y * m + snd y) after 0 =
            Znth (fst y * m + snd y) before 0).
        { apply (proj2 (paint_rectangle_coordinate__solver_final before after
            n m i j side color (fst y) (snd y) Hm Hi Hj Hyrow Hycol
            Hplace' Hlen Hpaint)). exact Hyoutnew. }
        assert (Hy_before_color :
          Znth (snd y) (Znth (fst y) before_grid []) 0 =
          Znth (snd p) (Znth (fst p) before_grid []) 0).
        { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
            (fst y) (snd y) Hbefore_rows Hyrow Hycol).
          rewrite (rows_of_flat_Znth__solver_final n m before before_grid
            (fst p) (snd p) Hbefore_rows Hp_row Hp_col).
          rewrite <- Hysame, <- Hp_same.
          rewrite <- (rows_of_flat_Znth__solver_final n m after after_grid
            (fst y) (snd y) Hafter_rows Hyrow Hycol).
          rewrite <- (rows_of_flat_Znth__solver_final n m after after_grid
            (fst p) (snd p) Hafter_rows Hp_row Hp_col).
          exact Hycolor. }
        assert (Hpx_before : SameColorPath before_grid p x).
        { apply (proj2 (Holdcomponent x Hxrow Hxcol)). tauto. }
        assert (Hpy_before : SameColorPath before_grid p y).
        { eapply same_color_path_append__solver_final; eauto; lia. }
        apply Hyoutold. apply (proj1 (Holdcomponent y Hyrow Hycol)).
        exact Hpy_before.
    + reflexivity.
  - intros Hqold.
    eapply rectangle_connected__solver_final with
      (r := r) (c := c) (side := old_side)
      (color := Znth (snd p) (Znth (fst p) after_grid []) 0);
      try lia; try tauto.
    intros x Hxoldrow Hxoldcol.
    apply Hold_after_color; try lia.
Qed.
Lemma partial_components_place__solver_final :
  forall before after n m i j side color before_grid after_grid,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    Zlength before = n * m ->
    CanPlace before n m i j side color ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    RowsOfFlat n m before before_grid ->
    RowsOfFlat n m after after_grid ->
    PartialSquareComponents n m before_grid ->
    PartialSquareComponents n m after_grid.
Proof.
  intros before after n m i j side color before_grid after_grid Hn Hm
    Hi Hj Hlen Hplace Hpaint Hbefore_rows Hafter_rows Hcomponents.
  intros p Hp_row Hp_col Hp_nonzero.
  destruct (classic
    (i <= fst p < i + side /\ j <= snd p < j + side)) as [Hpnew | Hpold].
  - destruct Hplace as [Hside [Hibound [Hjbound Hrest]]].
    destruct Hrest as [Hempty [Hhorizontal Hvertical]].
    assert (Hplace' : CanPlace before n m i j side color).
    { unfold CanPlace.
      exact (conj Hside (conj Hibound (conj Hjbound
        (conj Hempty (conj Hhorizontal Hvertical))))). }
    exists i, j, side.
    split; [exact Hside |].
    split; [lia |].
    split; [lia |].
    split; [exact Hibound |].
    split; [exact Hjbound |].
    split; [exact (proj1 Hpnew) |].
    split; [exact (proj2 Hpnew) |].
    intros q Hqrow Hqcol.
    exact (sealed_component_unique__solver_final before after n m i j side
      color after_grid p q Hn Hm Hi Hj Hlen Hplace' Hpaint Hafter_rows
      (proj1 Hpnew) (proj2 Hpnew) Hqrow Hqcol).
  - assert (Hp_same : Znth (fst p * m + snd p) after 0 =
        Znth (fst p * m + snd p) before 0).
    { apply (proj2 (paint_rectangle_coordinate__solver_final before after n m
        i j side color (fst p) (snd p) Hm Hi Hj Hp_row Hp_col Hplace
        Hlen Hpaint)). exact Hpold. }
    assert (Hp_before_nonzero :
        Znth (snd p) (Znth (fst p) before_grid []) 0 <> 0).
    { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
        (fst p) (snd p) Hbefore_rows Hp_row Hp_col).
      rewrite <- Hp_same.
      rewrite <- (rows_of_flat_Znth__solver_final n m after after_grid
        (fst p) (snd p) Hafter_rows Hp_row Hp_col).
      exact Hp_nonzero. }
    specialize (Hcomponents p Hp_row Hp_col Hp_before_nonzero).
    destruct Hcomponents as [r [c [old_side
      [Hold_side [Hr0 [Hc0 [Hrbound [Hcbound
        [Hp_oldrow [Hp_oldcol Holdcomponent]]]]]]]]]].
    exists r, c, old_side.
    split; [exact Hold_side |].
    split; [exact Hr0 |].
    split; [exact Hc0 |].
    split; [exact Hrbound |].
    split; [exact Hcbound |].
    split; [exact Hp_oldrow |].
    split; [exact Hp_oldcol |].
    exact (old_component_preserved__solver_final before after n m i j side
      color before_grid after_grid p r c old_side Hn Hm Hi Hj Hlen Hplace
      Hpaint Hbefore_rows Hafter_rows Hp_row Hp_col Hpold Hp_nonzero
      Hold_side Hr0 Hc0 Hrbound Hcbound Hp_oldrow Hp_oldcol Holdcomponent).
Qed.
Lemma greedy_trace_components__solver_final :
  forall n m next flat,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next flat ->
    exists grid,
      RowsOfFlat n m flat grid /\
      PartialSquareComponents n m grid.
Proof.
  intros n m next flat Hn Hm Htrace.
  induction Htrace as
      [flat Hlen Hzero
      |next flat Htrace IH Hnext Hcell
      |next before after i j color side Htrace IH Hnext Hi Hj Hanchor
         Hsettled Hpaint].
  - destruct (rows_of_flat_from_length__solver_final n m flat Hn Hm Hlen)
      as [grid Hrows].
    exists grid. split; [exact Hrows |].
    intros p Hp_row Hp_col Hp_nonzero.
    exfalso. apply Hp_nonzero.
    rewrite (rows_of_flat_Znth__solver_final n m flat grid
      (fst p) (snd p) Hrows Hp_row Hp_col).
    apply Hzero. nia.
  - exact IH.
  - destruct IH as [before_grid [Hbefore_rows Hbefore_components]].
    pose proof (trace_bounds_and_canonical__solver_final n m next before
      Hn Hm Htrace) as [Hbounds [Hbefore_len Hrest]].
    destruct Hsettled as [Hchosen Hstop].
    destruct Hchosen as [Hleast Hgreedy].
    destruct Hgreedy as [Hplace Hprevious].
    assert (Hafter_len : Zlength after = n * m).
    { destruct Hpaint as [Hpaint_len Hpaint_cells]. lia. }
    destruct (rows_of_flat_from_length__solver_final n m after Hn Hm Hafter_len)
      as [after_grid Hafter_rows].
    exists after_grid. split; [exact Hafter_rows |].
    exact (partial_components_place__solver_final before after n m i j side
      color before_grid after_grid Hn Hm Hi Hj Hbefore_len Hplace Hpaint
      Hbefore_rows Hafter_rows Hbefore_components).
Qed.
Lemma Forall_from_Znth__solver_final :
  forall {A : Type} (P : A -> Prop) (l : list A) (d : A),
    (forall i, 0 <= i < Zlength l -> P (Znth i l d)) ->
    Forall P l.
Proof.
  intros A P l d Hall.
  rewrite Forall_forall.
  intros x Hin.
  destruct (In_nth l x d Hin) as [k [Hk Hnth]].
  specialize (Hall (Z.of_nat k)).
  unfold Znth in Hall.
  rewrite Nat2Z.id in Hall.
  rewrite <- Hnth.
  apply Hall.
  rewrite Zlength_correct.
  lia.
Qed.
Lemma Zlength_concat_rect__solver_final :
  forall {A : Type} (rows : list (list A)) m,
    Forall (fun row => Zlength row = m) rows ->
    Zlength (concat rows) = Zlength rows * m.
Proof.
  intros A rows.
  induction rows as [|row rows IH]; intros m Hrows.
  - rewrite !Zlength_nil. lia.
  - apply Forall_cons_iff in Hrows as [Hrow Hrest].
    simpl.
    rewrite Zlength_app, Zlength_cons, Hrow, (IH m Hrest).
    lia.
Qed.
Lemma complete_partial_tiling_implies_spec__solver_final :
  forall n m flat,
    1 <= n ->
    1 <= m ->
    Zlength flat = n * m ->
    PartialTilingState n m (n * m) flat ->
    exists out, Flatten out = flat /\ Spec n m out.
Proof.
  intros n m flat Hn Hm Hflatlen Hstate.
  unfold PartialTilingState in Hstate.
  destruct Hstate as
      [out [Hrows [Hcolored_prefix [Hcolored_or_zero
             [Hcomponents Hlex]]]]].
  destruct Hrows as [Houtlen [Hrowlen Hflatten]].
  subst flat.
  assert (Hcolors_flat :
      Forall (fun c => 65 <= c <= 90) (Flatten out)).
  { apply Forall_from_Znth__solver_final with (d := 0).
    intros k Hk.
    apply Hcolored_prefix.
    rewrite Hflatlen in Hk.
    exact Hk. }
  assert (Hcolors_rows :
      Forall (Forall (fun c => 65 <= c <= 90)) out).
  { apply (proj1 (Forall_concat (fun c : Z => 65 <= c <= 90) out)).
    exact Hcolors_flat. }
  exists out.
  split; [reflexivity |].
  unfold Spec.
  split.
  - unfold SquareTiling.
    split.
    + split; assumption.
    + split; [exact Hcolors_rows |].
      intros p Hp_row Hp_col.
      assert (Hin_row : In (Znth (fst p) out []) out).
      { apply Znth_In_range__solver_final. rewrite Houtlen. exact Hp_row. }
      assert (Hselected_row_len : Zlength (Znth (fst p) out []) = m).
      { rewrite Forall_forall in Hrowlen.
        apply Hrowlen. exact Hin_row. }
      assert (Hin_cell :
          In (Znth (snd p) (Znth (fst p) out []) 0)
             (Znth (fst p) out [])).
      { apply Znth_In_range__solver_final.
        rewrite Hselected_row_len. exact Hp_col. }
      assert (Hcell_color :
          65 <= Znth (snd p) (Znth (fst p) out []) 0 <= 90).
      { rewrite Forall_forall in Hcolors_rows.
        specialize (Hcolors_rows _ Hin_row).
        rewrite Forall_forall in Hcolors_rows.
        apply Hcolors_rows. exact Hin_cell. }
      specialize (Hcomponents p Hp_row Hp_col ltac:(lia)).
      destruct Hcomponents as
          [r [c [side [Hside [Hr0 [Hc0 [Hrbound [Hcbound
             [Hprow [Hpcol Hcomponent]]]]]]]]]].
      exists r, c, side.
      split; [lia |].
      split; [exact Hprow |].
      split; [exact Hpcol |].
      split; [lia |].
      split; [lia |].
      split; [exact Hrbound |].
      split; [exact Hcbound |].
      exact Hcomponent.
  - intros candidate Hcandidate.
    specialize (Hlex candidate Hcandidate).
    assert (Hcandidate_flat_len :
        Zlength (Flatten candidate) = n * m).
    { unfold SquareTiling in Hcandidate.
      destruct Hcandidate as [[Hcandidate_len Hcandidate_rows] _].
      unfold Flatten.
      rewrite (Zlength_concat_rect__solver_final candidate m Hcandidate_rows).
      rewrite Hcandidate_len.
      reflexivity. }
    unfold LexPrefixLe in Hlex.
    destruct Hlex as [Hequal_prefix | Hstrict].
    + left.
      apply (proj2 (list_eq_ext (Flatten out) (Flatten candidate) 0)).
      split.
      * rewrite Hflatlen. symmetry. exact Hcandidate_flat_len.
      * intros k Hk. apply Hequal_prefix.
        rewrite Hflatlen in Hk. exact Hk.
    + right. left.
      destruct Hstrict as [first [Hfirst [Hsame Hless]]].
      exists first.
      split.
      * split; [lia |].
        rewrite Hflatlen, Hcandidate_flat_len, Z.min_id.
        lia.
      * split; assumption.
Qed.
Lemma square_tiling_rows__solver_final :
  forall n m grid,
    SquareTiling n m grid ->
    RowsOfFlat n m (Flatten grid) grid.
Proof.
  intros n m grid Htiling.
  unfold SquareTiling in Htiling.
  destruct Htiling as [[Hlen Hrows] Hrest].
  unfold RowsOfFlat. tauto.
Qed.
Lemma square_tiling_flat_color__solver_final :
  forall n m grid k,
    SquareTiling n m grid ->
    0 <= k < n * m ->
    65 <= Znth k (Flatten grid) 0 <= 90.
Proof.
  intros n m grid k Htiling Hk.
  destruct Htiling as [[Hlen Hrows] [Hcolors Hcomponents]].
  assert (Hflatlen : Zlength (Flatten grid) = n * m).
  { unfold Flatten.
    rewrite (Zlength_concat_rect__solver_final grid m Hrows), Hlen.
    reflexivity. }
  assert (Hflatcolors :
      Forall (fun c => 65 <= c <= 90) (Flatten grid)).
  { apply (proj2 (Forall_concat (fun c : Z => 65 <= c <= 90) grid)).
    exact Hcolors. }
  rewrite Forall_forall in Hflatcolors.
  apply Hflatcolors, Znth_In_range__solver_final.
  rewrite Hflatlen. exact Hk.
Qed.
Lemma paint_preserves_nonzero__solver_final :
  forall before after n m i j side color,
    CanPlace before n m i j side color ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    forall k,
      0 <= k < Zlength before ->
      Znth k before 0 <> 0 ->
      Znth k after 0 = Znth k before 0.
Proof.
  intros before after n m i j side color Hplace Hpaint k Hk Hnonzero.
  destruct Hplace as [Hside [Hibound [Hjbound
    [Hempty [Hhorizontal Hvertical]]]]].
  destruct Hpaint as [Hlen Hcells].
  specialize (Hcells k Hk).
  destruct Hcells as [[[off [Hoff Hmap]] Hpainted] | [Houtside Hsame]].
  - exfalso. apply Hnonzero.
    rewrite Hmap.
    apply Hempty.
    + assert (Hdiv0 : 0 <= off / side) by (apply Z.div_pos; lia).
      assert (Hdivlt : off / side < side).
      { apply (Z.div_lt_upper_bound off side side); nia. }
      lia.
    + assert (Hmod : 0 <= off mod side < side) by
        (apply Z.mod_pos_bound; lia).
      lia.
  - exact Hsame.
Qed.
Lemma trace_colored_origin__solver_final :
  forall n m next flat k,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next flat ->
    0 <= k < n * m ->
    Znth k flat 0 <> 0 ->
    exists anchor before painted i j color side off,
      anchor = i * m + j /\
      anchor < next /\
      GreedyPlacementTrace n m anchor before /\
      SettledSquareState before n m i j color side /\
      PaintRectanglePrefix before painted m i j side color (side * side) /\
      0 <= off < side * side /\
      k = (i + off / side) * m + (j + off mod side) /\
      Znth k flat 0 = color.
Proof.
  intros n m next flat k Hn Hm Htrace.
  induction Htrace as
      [flat Hlen Hzero
      |next flat Htrace IH Hnext Hcell
      |next before after i j color side Htrace IH Hnext Hi Hj Hanchor
         Hsettled Hpaint]; intros Hk Hcolored.
  - exfalso. apply Hcolored. apply Hzero. exact Hk.
  - destruct (IH Hk Hcolored) as
      [anchor [before [painted [i [j [color [side [off Horigin]]]]]]]].
    exists anchor, before, painted, i, j, color, side, off.
    destruct Horigin as [Ha [Hlt [Ht [Hs [Hp [Ho [Hmap Hcolor]]]]]]].
    assert (Hlt' : anchor < next + 1) by lia.
    exact (conj Ha (conj Hlt' (conj Ht (conj Hs
      (conj Hp (conj Ho (conj Hmap Hcolor))))))).
  - pose proof (trace_bounds_and_canonical__solver_final n m next before
      Hn Hm Htrace) as [Hbounds [Hbefore_len Hcanonical]].
    pose proof Hpaint as Hpaint_full.
    destruct Hpaint as [Hafter_len Hpaint_cells].
    assert (Hk_before : 0 <= k < Zlength before) by lia.
    specialize (Hpaint_cells k Hk_before).
    destruct Hpaint_cells as
      [[[off [Hoff Hmap]] Hcolor_after] | [Houtside Hsame]].
    + exists (i * m + j), before, after, i, j, color, side, off.
      assert (Hlt : i * m + j < next + 1) by lia.
      assert (Htrace_anchor : GreedyPlacementTrace n m (i * m + j) before).
      { rewrite <- Hnext. exact Htrace. }
      exact (conj eq_refl (conj Hlt (conj Htrace_anchor
        (conj Hsettled (conj Hpaint_full
          (conj Hoff (conj Hmap Hcolor_after))))))).
    + assert (Hbefore_colored : Znth k before 0 <> 0).
      { rewrite <- Hsame. exact Hcolored. }
      destruct (IH Hk Hbefore_colored) as
        [anchor [origin_before [painted [oi [oj [ocolor [oside [off Horigin]]]]]]]].
      exists anchor, origin_before, painted, oi, oj, ocolor, oside, off.
      destruct Horigin as [Ha [Hlt [Ht [Hs [Hp [Ho [Hmap Hcolor]]]]]]].
      assert (Hlt' : anchor < next + 1) by lia.
      assert (Hcolor' : Znth k after 0 = ocolor).
      { rewrite Hsame. exact Hcolor. }
      exact (conj Ha (conj Hlt' (conj Ht (conj Hs
        (conj Hp (conj Ho (conj Hmap Hcolor'))))))).
Qed.
Lemma trace_colored_component_origin__solver_final :
  forall n m next flat grid p,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next flat ->
    RowsOfFlat n m flat grid ->
    0 <= fst p < n -> 0 <= snd p < m ->
    Znth (snd p) (Znth (fst p) grid []) 0 <> 0 ->
    exists anchor before painted i j color side,
      anchor = i * m + j /\
      anchor < next /\
      GreedyPlacementTrace n m anchor before /\
      SettledSquareState before n m i j color side /\
      PaintRectanglePrefix before painted m i j side color (side * side) /\
      0 <= i < n /\ 0 <= j < m /\
      i <= fst p < i + side /\ j <= snd p < j + side /\
      Znth (snd p) (Znth (fst p) grid []) 0 = color /\
      (forall q,
        0 <= fst q < n -> 0 <= snd q < m ->
        (SameColorPath grid p q <->
         i <= fst q < i + side /\ j <= snd q < j + side)) /\
      (forall k,
        0 <= k < n * m ->
        Znth k before 0 <> 0 ->
        Znth k flat 0 = Znth k before 0).
Proof.
  intros n m next flat grid p Hn Hm Htrace.
  revert grid p.
  induction Htrace as
      [flat Hlen Hzero
      |next flat Htrace IH Hnext Hcell
      |next before after i j color side Htrace IH Hnext Hi Hj Hanchor
         Hsettled Hpaint]; intros grid p Hrows Hp_row Hp_col Hp_nonzero.
  - exfalso. apply Hp_nonzero.
    rewrite (rows_of_flat_Znth__solver_final n m flat grid
      (fst p) (snd p) Hrows Hp_row Hp_col).
    apply Hzero. nia.
  - destruct (IH grid p Hrows Hp_row Hp_col Hp_nonzero) as
      [anchor [before [painted [i [j [color [side Horigin]]]]]]].
    exists anchor, before, painted, i, j, color, side.
    destruct Horigin as [Ha [Hlt [Ht [Hs [Hp [Hoi [Hoj [Hprow [Hpcol
      [Hcolor [Hcomponent Hpersist]]]]]]]]]]].
    assert (Hlt' : anchor < next + 1) by lia.
    refine (conj Ha (conj Hlt' (conj Ht (conj Hs (conj Hp _))))).
    refine (conj Hoi (conj Hoj (conj Hprow (conj Hpcol _)))).
    exact (conj Hcolor (conj Hcomponent Hpersist)).
  - pose proof (trace_bounds_and_canonical__solver_final n m next before
      Hn Hm Htrace) as [Hbounds [Hbefore_len Hcanonical]].
    destruct Hsettled as [Hchosen Hstop].
    destruct Hchosen as [Hleast Hgreedy].
    destruct Hgreedy as [Hplace Hprevious].
    assert (Hsettled' : SettledSquareState before n m i j color side).
    { unfold SettledSquareState, ChosenSquareState, GreedySideState.
      tauto. }
    destruct (classic
      (i <= fst p < i + side /\ j <= snd p < j + side)) as [Hpnew | Hpold].
    + exists (i * m + j), before, after, i, j, color, side.
      assert (Htrace_anchor : GreedyPlacementTrace n m (i * m + j) before).
      { rewrite <- Hnext. exact Htrace. }
      assert (Hcolor :
          Znth (snd p) (Znth (fst p) grid []) 0 = color).
      { rewrite (rows_of_flat_Znth__solver_final n m after grid
          (fst p) (snd p) Hrows Hp_row Hp_col).
        apply (proj1 (paint_rectangle_coordinate__solver_final before after
          n m i j side color (fst p) (snd p) Hm Hi Hj Hp_row Hp_col
          Hplace Hbefore_len Hpaint)). exact Hpnew. }
      assert (Hcomponent' : forall q,
          0 <= fst q < n -> 0 <= snd q < m ->
          (SameColorPath grid p q <->
           i <= fst q < i + side /\ j <= snd q < j + side)).
      { intros q Hqrow Hqcol.
        exact (sealed_component_unique__solver_final before after n m i j side
          color grid p q Hn Hm Hi Hj Hbefore_len Hplace Hpaint Hrows
          (proj1 Hpnew) (proj2 Hpnew) Hqrow Hqcol). }
      assert (Hpersist : forall k,
          0 <= k < n * m ->
          Znth k before 0 <> 0 ->
          Znth k after 0 = Znth k before 0).
      { intros k Hk Hnonzero.
        apply (paint_preserves_nonzero__solver_final before after n m i j
          side color Hplace Hpaint k); lia. }
      assert (Hlt : i * m + j < next + 1) by lia.
      refine (conj eq_refl (conj Hlt (conj Htrace_anchor
        (conj Hsettled' (conj Hpaint _))))).
      exact (conj Hi (conj Hj (conj (proj1 Hpnew)
        (conj (proj2 Hpnew) (conj Hcolor
          (conj Hcomponent' Hpersist)))))).
    + assert (Hpsame : Znth (fst p * m + snd p) after 0 =
          Znth (fst p * m + snd p) before 0).
      { apply (proj2 (paint_rectangle_coordinate__solver_final before after
          n m i j side color (fst p) (snd p) Hm Hi Hj Hp_row Hp_col Hplace
          Hbefore_len Hpaint)). exact Hpold. }
      destruct (rows_of_flat_from_length__solver_final n m before Hn Hm
        Hbefore_len) as [before_grid Hbefore_rows].
      assert (Hp_before_nonzero :
          Znth (snd p) (Znth (fst p) before_grid []) 0 <> 0).
      { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
          (fst p) (snd p) Hbefore_rows Hp_row Hp_col).
        rewrite <- Hpsame.
        rewrite <- (rows_of_flat_Znth__solver_final n m after grid
          (fst p) (snd p) Hrows Hp_row Hp_col).
        exact Hp_nonzero. }
      destruct (IH before_grid p Hbefore_rows Hp_row Hp_col Hp_before_nonzero)
        as [anchor [origin_before [painted [oi [oj [ocolor [oside Horigin]]]]]]].
      destruct Horigin as [Ha [Hlt [Ht [Hs [Hopaint [Hoi [Hoj [Hprow [Hpcol
        [Hpcolor [Hcomponent Hpersist_origin]]]]]]]]]]].
      exists anchor, origin_before, painted, oi, oj, ocolor, oside.
      assert (Hlt' : anchor < next + 1) by lia.
      assert (Hpcolor' :
          Znth (snd p) (Znth (fst p) grid []) 0 = ocolor).
      { rewrite (rows_of_flat_Znth__solver_final n m after grid
          (fst p) (snd p) Hrows Hp_row Hp_col).
        rewrite Hpsame.
        rewrite <- (rows_of_flat_Znth__solver_final n m before before_grid
          (fst p) (snd p) Hbefore_rows Hp_row Hp_col).
        exact Hpcolor. }
      pose proof Hs as Hs_bounds.
      destruct Hs_bounds as [[Hleast_origin [Hplace_origin Hprev_origin]] Hstop_origin].
      destruct Hplace_origin as [Hoside [Hoirbound [Hojcbound Hplace_rest]]].
      assert (Hcomponent' : forall q,
          0 <= fst q < n -> 0 <= snd q < m ->
          (SameColorPath grid p q <->
           oi <= fst q < oi + oside /\ oj <= snd q < oj + oside)).
      { exact (old_component_preserved__solver_final before after n m i j side
          color before_grid grid p oi oj oside Hn Hm Hi Hj Hbefore_len
          Hplace Hpaint Hbefore_rows Hrows Hp_row Hp_col Hpold Hp_nonzero
          Hoside (proj1 Hoi) (proj1 Hoj) Hoirbound Hojcbound
          Hprow Hpcol Hcomponent). }
      assert (Hpersist : forall k,
          0 <= k < n * m ->
          Znth k origin_before 0 <> 0 ->
          Znth k after 0 = Znth k origin_before 0).
      { intros k Hk Hnonzero.
        assert (Hbefore_eq : Znth k before 0 = Znth k origin_before 0).
        { apply Hpersist_origin; assumption. }
        assert (Hbefore_nonzero : Znth k before 0 <> 0).
        { rewrite Hbefore_eq. exact Hnonzero. }
        rewrite (paint_preserves_nonzero__solver_final before after n m i j
          side color Hplace Hpaint k ltac:(lia) Hbefore_nonzero).
        exact Hbefore_eq. }
      refine (conj Ha (conj Hlt' (conj Ht (conj Hs (conj Hopaint _))))).
      exact (conj Hoi (conj Hoj (conj Hprow
        (conj Hpcol (conj Hpcolor' (conj Hcomponent' Hpersist)))))).
Qed.
Lemma paint_frontier_conflict_equiv__solver_final :
  forall before after n m i j side color tested,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    65 <= color ->
    j + side < m ->
    Zlength before = n * m ->
    CanPlace before n m i j side color ->
    PaintRectanglePrefix before after m i j side color (side * side) ->
    (NeighborConflict after n m i (j + side) tested 0 <->
     NeighborConflict before n m i (j + side) tested color).
Proof.
  intros before after n m i j side color tested Hn Hm Hi Hj Hcolor
    Hfrontier Hlen Hplace Hpaint.
  destruct Hplace as [Hside [Hirbound [Hicbound Hrest]]].
  assert (Hplace' : CanPlace before n m i j side color) by
    (unfold CanPlace; tauto).
  assert (Htop : 0 < i ->
      Znth ((i - 1) * m + (j + side)) after 0 =
      Znth ((i - 1) * m + (j + side)) before 0).
  { intros Hitop.
    apply (proj2 (paint_rectangle_coordinate__solver_final before after n m
      i j side color (i - 1) (j + side) Hm Hi Hj ltac:(lia) ltac:(lia)
      Hplace' Hlen Hpaint)).
    intros [Hr Hc]. lia. }
  assert (Hbottom : i + 1 < n ->
      Znth ((i + 1) * m + (j + side)) after 0 =
      Znth ((i + 1) * m + (j + side)) before 0).
  { intros Hibottom.
    apply (proj2 (paint_rectangle_coordinate__solver_final before after n m
      i j side color (i + 1) (j + side) Hm Hi Hj ltac:(lia) ltac:(lia)
      Hplace' Hlen Hpaint)).
    intros [Hr Hc]. lia. }
  assert (Hright : j + side + 1 < m ->
      Znth (i * m + (j + side) + 1) after 0 =
      Znth (i * m + (j + side) + 1) before 0).
  { intros Hiright.
    replace (i * m + (j + side) + 1) with
      (i * m + (j + side + 1)) by lia.
    apply (proj2 (paint_rectangle_coordinate__solver_final before after n m
      i j side color i (j + side + 1) Hm Hi Hj ltac:(lia) ltac:(lia)
      Hplace' Hlen Hpaint)).
    intros [Hr Hc]. lia. }
  assert (Hleft :
      Znth (i * m + (j + side) - 1) after 0 = color).
  { replace (i * m + (j + side) - 1) with
      (i * m + (j + side - 1)) by lia.
    apply (proj1 (paint_rectangle_coordinate__solver_final before after n m
      i j side color i (j + side - 1) Hm Hi Hj ltac:(lia) ltac:(lia)
      Hplace' Hlen Hpaint)).
    split; lia. }
  unfold NeighborConflict.
  destruct (Z.eq_dec color 0) as [Hcolor0 | Hcolor0]; [lia |].
  destruct (Z.eq_dec 0 0) as [_ | Hbad]; [|contradiction].
  rewrite Hleft.
  split; intros Hconflict;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H
    end;
    try (left; split; [lia | congruence]);
    try (right; left; split; [lia | congruence]);
    try (right; right; left; split; [lia | congruence]);
    try (right; right; right; left; split; [lia | congruence]);
    try (right; right; right; right; split; [lia | congruence]);
    try lia;
    rewrite ?Htop, ?Hbottom, ?Hright in * by lia;
    congruence.
Qed.
Lemma least_legal_color_unique__solver_final :
  forall flat n m i j left c1 c2,
    LeastLegalColor flat n m i j left c1 ->
    LeastLegalColor flat n m i j left c2 ->
    c1 = c2.
Proof.
  intros flat n m i j left c1 c2 [Hlegal1 Hleast1] [Hlegal2 Hleast2].
  destruct Hlegal1 as [[Hlo1 Hhi1] Hfree1].
  destruct Hlegal2 as [[Hlo2 Hhi2] Hfree2].
  destruct (Z.lt_trichotomy c1 c2) as [Hlt | [Heq | Hgt]];
    [exfalso; exact (Hleast2 c1 ltac:(lia)
      (conj (conj Hlo1 Hhi1) Hfree1))
    | exact Heq
    | exfalso; exact (Hleast1 c2 ltac:(lia)
      (conj (conj Hlo2 Hhi2) Hfree2))].
Qed.
Lemma settled_side_unique__solver_final :
  forall flat n m i j color side1 side2,
    SettledSquareState flat n m i j color side1 ->
    SettledSquareState flat n m i j color side2 ->
    side1 = side2.
Proof.
  intros flat n m i j color side1 side2 Hsettled1 Hsettled2.
  destruct Hsettled1 as [[Hleast1 [Hplace1 Hprevious1]] Hstop1].
  destruct Hsettled2 as [[Hleast2 [Hplace2 Hprevious2]] Hstop2].
  destruct (Z.lt_trichotomy side1 side2) as [Hlt | [Heq | Hgt]];
    [|exact Heq|].
  - destruct (Hprevious2 side1 ltac:(destruct Hplace1; lia)) as
      [Hextend [fallback [Hfallback Hgreater]]].
    destruct Hstop1 as [Hboundary | [Hcannot | [stopped [Hstopped Hle]]]].
    + destruct Hextend as [Hs [Hi [Hj Hrest]]]. lia.
    + contradiction.
    + assert (fallback = stopped) by
        (eapply least_legal_color_unique__solver_final; eauto).
      lia.
  - destruct (Hprevious1 side2 ltac:(destruct Hplace2; lia)) as
      [Hextend [fallback [Hfallback Hgreater]]].
    destruct Hstop2 as [Hboundary | [Hcannot | [stopped [Hstopped Hle]]]].
    + destruct Hextend as [Hs [Hi [Hj Hrest]]]. lia.
    + contradiction.
    + assert (fallback = stopped) by
        (eapply least_legal_color_unique__solver_final; eauto).
      lia.
Qed.
Lemma paint_rectangle_unique__solver_final :
  forall before after1 after2 m i j side color done,
    PaintRectanglePrefix before after1 m i j side color done ->
    PaintRectanglePrefix before after2 m i j side color done ->
    after1 = after2.
Proof.
  intros before after1 after2 m i j side color done Hpaint1 Hpaint2.
  destruct Hpaint1 as [Hlen1 Hcells1].
  destruct Hpaint2 as [Hlen2 Hcells2].
  apply (proj2 (list_eq_ext after1 after2 0)).
  split; [lia |].
  intros k Hk.
  assert (Hkbefore : 0 <= k < Zlength before) by lia.
  specialize (Hcells1 k Hkbefore).
  specialize (Hcells2 k Hkbefore).
  destruct Hcells1 as [[Hmember1 Hcolor1] | [Houtside1 Hsame1]];
  destruct Hcells2 as [[Hmember2 Hcolor2] | [Houtside2 Hsame2]].
  - congruence.
  - exfalso. destruct Hmember1 as [off [Hoff Hindex]].
    exact (Houtside2 off Hoff Hindex).
  - exfalso. destruct Hmember2 as [off [Hoff Hindex]].
    exact (Houtside1 off Hoff Hindex).
  - congruence.
Qed.
Lemma greedy_side_length_exchange__solver_final :
  forall chosen fallback candidate,
    chosen < fallback ->
    fallback <= candidate ->
    chosen <= candidate.
Proof.
  intros. lia.
Qed.
Lemma lex_prefix_skip__solver_final :
  forall next flat candidate,
    0 <= next ->
    LexPrefixLe next flat candidate ->
    Znth next flat 0 <= Znth next candidate 0 ->
    LexPrefixLe (next + 1) flat candidate.
Proof.
  intros. eapply lex_first_difference__solver_final; eauto.
Qed.
Lemma lex_prefix_place__solver_final :
  forall next before after candidate,
    0 <= next ->
    LexPrefixLe next before candidate ->
    (forall k, 0 <= k < next -> Znth k after 0 = Znth k before 0) ->
    Znth next after 0 <= Znth next candidate 0 ->
    LexPrefixLe (next + 1) after candidate.
Proof.
  intros next before after candidate Hnext Hlex Hsame Hcell.
  unfold LexPrefixLe in Hlex |- *.
  destruct Hlex as [Hequal | [first [Hfirst [Hprefix Hless]]]].
  - destruct (Z.eq_dec (Znth next after 0) (Znth next candidate 0))
      as [Hat | Hat].
    + left. intros k Hk.
      destruct (Z.eq_dec k next) as [-> | Hneq]; [exact Hat |].
      rewrite Hsame by lia. apply Hequal. lia.
    + right. exists next. split; [lia |]. split.
      * intros k Hk. rewrite Hsame by lia. apply Hequal. exact Hk.
      * lia.
  - right. exists first. split; [lia |]. split.
    + intros k Hk. rewrite Hsame by lia. apply Hprefix. exact Hk.
    + rewrite Hsame by lia. exact Hless.
Qed.
Lemma greedy_trace_structural_state__solver_final :
  forall n m next flat,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next flat ->
    exists grid,
      RowsOfFlat n m flat grid /\
      (forall k, 0 <= k < next -> 65 <= Znth k flat 0 <= 90) /\
      (forall k, 0 <= k < n * m ->
         Znth k flat 0 = 0 \/ 65 <= Znth k flat 0 <= 90) /\
      PartialSquareComponents n m grid.
Proof.
  intros n m next flat Hn Hm Htrace.
  pose proof (trace_bounds_and_canonical__solver_final n m next flat
    Hn Hm Htrace) as [Hbounds [Hlen [Hcanonical Hprefix]]].
  destruct (greedy_trace_components__solver_final n m next flat
    Hn Hm Htrace) as [grid [Hrows Hcomponents]].
  assert (Hglobal : forall k, 0 <= k < n * m ->
      Znth k flat 0 = 0 \/ 65 <= Znth k flat 0 <= 90).
  { intros k Hk. apply Hcanonical. rewrite Hlen. exact Hk. }
  exists grid.
  exact (conj Hrows (conj Hprefix (conj Hglobal Hcomponents))).
Qed.
Lemma greedy_trace_partial_from_lex__solver_final :
  forall n m next flat,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next flat ->
    (forall candidate,
      SquareTiling n m candidate ->
      LexPrefixLe next flat (Flatten candidate)) ->
    PartialTilingState n m next flat.
Proof.
  intros n m next flat Hn Hm Htrace Hlex.
  destruct (greedy_trace_structural_state__solver_final n m next flat
    Hn Hm Htrace) as [grid [Hrows [Hprefix [Hcanonical Hcomponents]]]].
  exists grid.
  exact (conj Hrows (conj Hprefix
    (conj Hcanonical (conj Hcomponents Hlex)))).
Qed.
Lemma smaller_conflict_has_painted_neighbour__solver_final :
  forall flat n m i j smaller override,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    0 <= smaller ->
    smaller < override ->
    NeighborConflict flat n m i j smaller override ->
    exists q,
      0 <= fst q < n /\ 0 <= snd q < m /\
      AdjCell (i, j) q /\
      q <> (i, j - 1) /\
      Znth (fst q * m + snd q) flat 0 = smaller.
Proof.
  intros flat n m i j smaller override Hn Hm Hi Hj Hsmaller Hlt Hconflict.
  unfold NeighborConflict in Hconflict.
  destruct Hconflict as
      [[Hitop Htop] |
       [[Hibottom Hbottom] |
        [[Hjright Hright] |
         [[Hjleft Hleft] | [Hjzero Hoverride]]]]].
  - exists (i - 1, j). simpl.
    repeat split; try lia.
    + unfold AdjCell. simpl.
      replace (i - (i - 1)) with 1 by lia.
      replace (j - j) with 0 by lia. reflexivity.
    + intros Heq. inversion Heq. lia.
  - exists (i + 1, j). simpl.
    repeat split; try lia.
    + unfold AdjCell. simpl.
      replace (i - (i + 1)) with (-1) by lia.
      replace (j - j) with 0 by lia. reflexivity.
    + intros Heq. inversion Heq. lia.
  - exists (i, j + 1). simpl.
    repeat split; try lia.
    + unfold AdjCell. simpl.
      replace (i - i) with 0 by lia.
      replace (j - (j + 1)) with (-1) by lia. reflexivity.
    + intros Heq. inversion Heq. lia.
    + replace (i * m + (j + 1)) with (i * m + j + 1) by lia.
      exact Hright.
  - destruct (Z.eq_dec override 0); lia.
  - lia.
Qed.
Lemma smaller_conflict_has_earlier_component__solver_final :
  forall n m anchor before before_grid i j smaller override,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m anchor before ->
    RowsOfFlat n m before before_grid ->
    0 <= i < n -> 0 <= j < m ->
    65 <= smaller ->
    smaller < override ->
    NeighborConflict before n m i j smaller override ->
    exists (q : Cell) earlier origin_before painted oi oj oside,
      earlier = oi * m + oj /\
      earlier < anchor /\
      GreedyPlacementTrace n m earlier origin_before /\
      SettledSquareState origin_before n m oi oj smaller oside /\
      PaintRectanglePrefix origin_before painted m oi oj oside smaller
        (oside * oside) /\
      0 <= oi < n /\ 0 <= oj < m /\
      oi <= fst q < oi + oside /\ oj <= snd q < oj + oside /\
      AdjCell (i, j) q /\
      q <> (i, j - 1) /\
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath before_grid q x <->
         oi <= fst x < oi + oside /\ oj <= snd x < oj + oside)) /\
      (forall k,
        0 <= k < n * m ->
        Znth k origin_before 0 <> 0 ->
        Znth k before 0 = Znth k origin_before 0).
Proof.
  intros n m anchor before before_grid i j smaller override Hn Hm Htrace
    Hrows Hi Hj Hsmaller Hlt Hconflict.
  destruct (smaller_conflict_has_painted_neighbour__solver_final before n m
    i j smaller override Hn Hm Hi Hj ltac:(lia) Hlt Hconflict) as
    [q [Hqrow [Hqcol [Hadj [Hnotleft Hqflat]]]]].
  assert (Hqgrid :
      Znth (snd q) (Znth (fst q) before_grid []) 0 = smaller).
  { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
      (fst q) (snd q) Hrows Hqrow Hqcol).
    exact Hqflat. }
  assert (Hqnonzero :
      Znth (snd q) (Znth (fst q) before_grid []) 0 <> 0) by lia.
  destruct (trace_colored_component_origin__solver_final n m anchor before
    before_grid q Hn Hm Htrace Hrows Hqrow Hqcol Hqnonzero) as
    [earlier [origin_before [painted [oi [oj [color [oside Horigin]]]]]]].
  destruct Horigin as [Ha [Hearlier [Horigin_trace [Hsettled [Hpaint
    [Hoi [Hoj [Hqoi [Hqoj [Hqcolor [Hcomponent Hpersist]]]]]]]]]]].
  subst smaller.
  assert (Hcolor : color = Znth (fst q * m + snd q) before 0) by
    congruence.
  subst color.
  rewrite Hcolor in Hsettled, Hpaint.
  exists q, earlier, origin_before, painted, oi, oj, oside.
  refine (conj Ha (conj Hearlier (conj Horigin_trace
    (conj Hsettled (conj Hpaint _))))).
  refine (conj Hoi (conj Hoj (conj Hqoi (conj Hqoj _)))).
  exact (conj Hadj (conj Hnotleft (conj Hcomponent Hpersist))).
Qed.
Lemma nonnegative_anchor_strong_induction__solver_final :
  forall (P : Z -> Prop),
    (forall anchor,
      0 <= anchor ->
      (forall earlier, 0 <= earlier < anchor -> P earlier) ->
      P anchor) ->
    forall anchor, 0 <= anchor -> P anchor.
Proof.
  intros P Hstep anchor Hanchor.
  remember (Z.to_nat anchor) as fuel eqn:Hfuel.
  revert anchor Hanchor Hfuel.
  induction fuel using lt_wf_ind.
  intros anchor Hanchor Hfuel.
  apply Hstep; [exact Hanchor |].
  intros earlier Hearlier.
  apply (H (Z.to_nat earlier)); try lia.
Qed.
Lemma local_first_difference_implies_lex__solver_final :
  forall upto left right,
    0 <= upto ->
    (forall first,
      0 <= first < upto ->
      (forall k, 0 <= k < first ->
        Znth k left 0 = Znth k right 0) ->
      Znth first left 0 <= Znth first right 0) ->
    LexPrefixLe upto left right.
Proof.
  intros upto left right Hupto Hlocal.
  revert left right Hlocal.
  apply (nonnegative_anchor_strong_induction__solver_final
    (fun current => forall left right,
      (forall first,
        0 <= first < current ->
        (forall k, 0 <= k < first ->
          Znth k left 0 = Znth k right 0) ->
        Znth first left 0 <= Znth first right 0) ->
      LexPrefixLe current left right)); [|exact Hupto].
  intros current Hcurrent IH left right Hlocal.
  destruct (Z.eq_dec current 0) as [-> | Hpositive].
  - left. intros k Hk. lia.
  - assert (Hprevious : 0 <= current - 1 < current) by lia.
    specialize (IH (current - 1) Hprevious left right).
    assert (Hlocal_previous : forall first,
        0 <= first < current - 1 ->
        (forall k, 0 <= k < first ->
          Znth k left 0 = Znth k right 0) ->
        Znth first left 0 <= Znth first right 0).
    { intros first Hfirst Hprefix.
      apply Hlocal; [lia | exact Hprefix]. }
    specialize (IH Hlocal_previous).
    unfold LexPrefixLe in IH |- *.
    destruct IH as [Hequal | [first [Hfirst [Hsame Hless]]]].
    + destruct (Z.eq_dec (Znth (current - 1) left 0)
          (Znth (current - 1) right 0)) as [Hcell | Hcell].
      * left. intros k Hk.
        destruct (Z.eq_dec k (current - 1)) as [-> | Hneq].
        -- exact Hcell.
        -- apply Hequal. lia.
      * right. exists (current - 1).
        split; [lia |]. split; [exact Hequal |].
        pose proof (Hlocal (current - 1) ltac:(lia) Hequal).
        lia.
    + right. exists first. split; [lia |]. split; assumption.
Qed.
Lemma square_tiling_component__solver_final :
  forall n m grid p,
    SquareTiling n m grid ->
    0 <= fst p < n -> 0 <= snd p < m ->
    exists r c side,
      1 <= side /\
      0 <= r /\ 0 <= c /\ r + side <= n /\ c + side <= m /\
      r <= fst p < r + side /\ c <= snd p < c + side /\
      forall q,
        0 <= fst q < n -> 0 <= snd q < m ->
        (SameColorPath grid p q <->
         r <= fst q < r + side /\ c <= snd q < c + side).
Proof.
  intros n m grid p Htiling Hp_row Hp_col.
  destruct Htiling as [[Hlen Hrows] [Hcolors Hcomponents]].
  destruct (Hcomponents p Hp_row Hp_col) as
    [r [c [side [Hside [Hprow [Hpcol [Hr0 [Hc0 [Hrbound
      [Hcbound Hcomponent]]]]]]]]]].
  exists r, c, side.
  assert (Hside' : 1 <= side) by lia.
  assert (Hr0' : 0 <= r) by lia.
  assert (Hc0' : 0 <= c) by lia.
  exact (conj Hside' (conj Hr0' (conj Hc0' (conj Hrbound
    (conj Hcbound (conj Hprow (conj Hpcol Hcomponent))))))).
Qed.
Lemma exact_component_boundary_color__solver_final :
  forall grid anchor inside outside r c side n m,
    Zlength grid = n ->
    Zlength (Znth 0 grid []) = m ->
    0 <= fst anchor < n -> 0 <= snd anchor < m ->
    0 <= fst inside < n -> 0 <= snd inside < m ->
    0 <= fst outside < n -> 0 <= snd outside < m ->
    r <= fst inside < r + side ->
    c <= snd inside < c + side ->
    ~ (r <= fst outside < r + side /\
       c <= snd outside < c + side) ->
    AdjCell inside outside ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath grid anchor q <->
       r <= fst q < r + side /\ c <= snd q < c + side)) ->
    Znth (snd outside) (Znth (fst outside) grid []) 0 <>
      Znth (snd anchor) (Znth (fst anchor) grid []) 0.
Proof.
  intros grid anchor inside outside r c side n m Hgrid_len Hrow_len
    Hanchor_row Hanchor_col
    Hinside_row Hinside_col Houtside_row Houtside_col Hinside_r Hinside_c
    Houtside Hadj Hcomponent Hequal.
  assert (Hinside_path : SameColorPath grid anchor inside).
  { apply (proj2 (Hcomponent inside Hinside_row Hinside_col)). tauto. }
  assert (Hinside_color :
      Znth (snd inside) (Znth (fst inside) grid []) 0 =
      Znth (snd anchor) (Znth (fst anchor) grid []) 0).
  { exact (same_color_path_endpoint_color__solver_final grid anchor inside
      Hinside_path). }
  assert (Houtside_path : SameColorPath grid anchor outside).
  { exact (same_color_path_append__solver_final grid anchor inside outside
      Hinside_path ltac:(rewrite Hgrid_len; exact Houtside_row)
      ltac:(rewrite Hrow_len; exact Houtside_col) ltac:(congruence) Hadj). }
  apply (proj1 (Hcomponent outside Houtside_row Houtside_col)) in Houtside_path.
  tauto.
Qed.
Lemma square_anchor_le_member__solver_final :
  forall m i j side r c,
    1 <= m ->
    0 <= j -> c < m ->
    i <= r < i + side ->
    j <= c < j + side ->
    i * m + j <= r * m + c.
Proof.
  intros. nia.
Qed.
Lemma candidate_component_not_short_before__solver_final :
  forall n m output candidate output_grid candidate_grid
      i j side candidate_side first,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    RowsOfFlat n m candidate candidate_grid ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    1 <= candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    i * m + (j + candidate_side) < first ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k candidate 0) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid (i, j) q <->
       i <= fst q < i + side /\ j <= snd q < j + side)) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath candidate_grid (i, j) q <->
       i <= fst q < i + candidate_side /\
       j <= snd q < j + candidate_side)) ->
    side <= candidate_side.
Proof.
  intros n m output candidate output_grid candidate_grid i j side
    candidate_side first Hn Hm Houtrows Hcandrows Hi Hj Hside
    Hirbound Hicbound Hcandidate_side Hcrbound Hccbound Hboundary
    Hprefix Houtcomponent Hcandcomponent.
  destruct (Z_lt_ge_dec candidate_side side) as [Hshort | Hlong];
    [|lia].
  set (inside := (i, j + candidate_side - 1)).
  set (outside := (i, j + candidate_side)).
  assert (Hinside_row : 0 <= fst inside < n) by
    (unfold inside; simpl; lia).
  assert (Hinside_col : 0 <= snd inside < m) by
    (unfold inside; simpl; lia).
  assert (Houtside_row : 0 <= fst outside < n) by
    (unfold outside; simpl; lia).
  assert (Houtside_col : 0 <= snd outside < m) by
    (unfold outside; simpl; lia).
  assert (Hout_path : SameColorPath output_grid (i, j) outside).
  { apply (proj2 (Houtcomponent outside Houtside_row Houtside_col)).
    unfold outside; simpl. split; lia. }
  pose proof (same_color_path_endpoint_color__solver_final output_grid
    (i, j) outside Hout_path) as Houtcolor.
  destruct Hcandrows as [Hcand_grid_len [Hcand_row_lengths Hcand_flat]].
  assert (Hcand_row0 : Zlength (Znth 0 candidate_grid []) = m).
  { rewrite Forall_forall in Hcand_row_lengths.
    apply Hcand_row_lengths, Znth_In_range__solver_final.
    rewrite Hcand_grid_len. lia. }
  assert (Hcand_boundary_diff :
      Znth (snd outside) (Znth (fst outside) candidate_grid []) 0 <>
      Znth j (Znth i candidate_grid []) 0).
  { apply (exact_component_boundary_color__solver_final candidate_grid
      (i, j) inside outside i j candidate_side n m Hcand_grid_len
      Hcand_row0); try (unfold inside, outside; simpl; lia).
    - unfold AdjCell, inside, outside. simpl.
      replace (i - i) with 0 by lia.
      replace (j + candidate_side - 1 - (j + candidate_side)) with (-1)
        by lia. reflexivity.
    - exact Hcandcomponent. }
  destruct Houtrows as [Hout_grid_len [Hout_row_lengths Hout_flat]].
  assert (Houtside_index : 0 <= i * m + (j + candidate_side) < first)
    by nia.
  assert (Hanchor_index : 0 <= i * m + j < first) by nia.
  pose proof (Hprefix (i * m + (j + candidate_side)) Houtside_index)
    as Hprefix_outside.
  pose proof (Hprefix (i * m + j) Hanchor_index) as Hprefix_anchor.
  rewrite <- Hout_flat, <- Hcand_flat in Hprefix_outside, Hprefix_anchor.
  rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten output_grid)
    output_grid i (j + candidate_side)
    (conj Hout_grid_len (conj Hout_row_lengths eq_refl)))
    in Hprefix_outside by lia.
  rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate_grid)
    candidate_grid i (j + candidate_side)
    (conj Hcand_grid_len (conj Hcand_row_lengths eq_refl)))
    in Hprefix_outside by lia.
  rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten output_grid)
    output_grid i j (conj Hout_grid_len (conj Hout_row_lengths eq_refl)))
    in Hprefix_anchor by lia.
  rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate_grid)
    candidate_grid i j
    (conj Hcand_grid_len (conj Hcand_row_lengths eq_refl)))
    in Hprefix_anchor by lia.
  unfold outside in Hcand_boundary_diff, Houtcolor. simpl in *.
  exfalso. apply Hcand_boundary_diff.
  rewrite <- Hprefix_outside, <- Hprefix_anchor.
  exact Houtcolor.
Qed.
Lemma component_top_left_prefix__solver_final :
  forall n m output candidate output_grid candidate_grid
      i j side r c candidate_side first,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    RowsOfFlat n m candidate candidate_grid ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    1 <= candidate_side -> 0 <= r -> 0 <= c ->
    r + candidate_side <= n -> c + candidate_side <= m ->
    r <= i < r + candidate_side -> c <= j < c + candidate_side ->
    i * m + j < first ->
    (forall k, 0 <= k < first -> Znth k output 0 = Znth k candidate 0) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid (i, j) q <->
       i <= fst q < i + side /\ j <= snd q < j + side)) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath candidate_grid (i, j) q <->
       r <= fst q < r + candidate_side /\
       c <= snd q < c + candidate_side)) ->
    r = i /\ c = j.
Proof.
  intros n m output candidate output_grid candidate_grid i j side r c
    candidate_side first Hn Hm Hout_rows Hcand_rows Hi Hj Hside
    Hirbound Hijbound Hcandidate_side Hr Hc Hrrbound Hccbound
    Hi_candidate Hj_candidate Hanchor Hprefix Hout_component Hcand_component.
  assert (Hout_grid_len : Zlength output_grid = n) by
    (destruct Hout_rows as [? [? ?]]; assumption).
  assert (Hcand_grid_len : Zlength candidate_grid = n) by
    (destruct Hcand_rows as [? [? ?]]; assumption).
  assert (Hout_row0 : Zlength (Znth 0 output_grid []) = m).
  { destruct Hout_rows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hcand_row0 : Zlength (Znth 0 candidate_grid []) = m).
  { destruct Hcand_rows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hr_eq : r = i).
  { destruct (Z.eq_dec r i) as [Heq | Hneq]; [exact Heq |].
    assert (Hrlt : r < i) by lia.
    set (q := (i - 1, j)).
    assert (Hqrow : 0 <= fst q < n) by (unfold q; simpl; lia).
    assert (Hqcol : 0 <= snd q < m) by (unfold q; simpl; lia).
    assert (Hq_candidate :
        r <= fst q < r + candidate_side /\
        c <= snd q < c + candidate_side) by (unfold q; simpl; lia).
    assert (Hcand_path : SameColorPath candidate_grid (i, j) q).
    { apply (proj2 (Hcand_component q Hqrow Hqcol)). exact Hq_candidate. }
    pose proof (same_color_path_endpoint_color__solver_final candidate_grid
      (i, j) q Hcand_path) as Hcand_color.
    assert (Hqindex : 0 <= (i - 1) * m + j < first) by nia.
    assert (Hanchor_index : 0 <= i * m + j < first) by nia.
    pose proof (Hprefix ((i - 1) * m + j) Hqindex) as Hprefix_q.
    pose proof (Hprefix (i * m + j) Hanchor_index) as Hprefix_anchor.
    assert (Hout_color :
        Znth (snd q) (Znth (fst q) output_grid []) 0 =
        Znth j (Znth i output_grid []) 0).
    { unfold q in *. simpl in *.
      rewrite (rows_of_flat_Znth__solver_final n m output output_grid
        (i - 1) j Hout_rows) by lia.
      rewrite (rows_of_flat_Znth__solver_final n m output output_grid
        i j Hout_rows) by lia.
      rewrite Hprefix_q.
      rewrite Hprefix_anchor.
      rewrite <- (rows_of_flat_Znth__solver_final n m candidate candidate_grid
        (i - 1) j Hcand_rows) by lia.
      rewrite <- (rows_of_flat_Znth__solver_final n m candidate candidate_grid
        i j Hcand_rows) by lia.
      exact Hcand_color. }
    assert (Hout_path : SameColorPath output_grid (i, j) q).
    { assert (Hadj : AdjCell (i, j) q).
      { unfold AdjCell, q. simpl.
        replace (i - (i - 1)) with 1 by lia.
        replace (j - j) with 0 by lia. reflexivity. }
      exact (same_color_path_step__solver_final output_grid (i, j) q
        ltac:(simpl; lia) ltac:(simpl; lia) ltac:(lia) ltac:(lia)
        Hout_color Hadj). }
    specialize (Hout_component q Hqrow Hqcol).
    apply (proj1 Hout_component) in Hout_path.
    unfold q in Hout_path. simpl in Hout_path. lia. }
  assert (Hc_eq : c = j).
  { destruct (Z.eq_dec c j) as [Heq | Hneq]; [exact Heq |].
    assert (Hclt : c < j) by lia.
    set (q := (i, j - 1)).
    assert (Hqrow : 0 <= fst q < n) by (unfold q; simpl; lia).
    assert (Hqcol : 0 <= snd q < m) by (unfold q; simpl; lia).
    assert (Hq_candidate :
        r <= fst q < r + candidate_side /\
        c <= snd q < c + candidate_side).
    { unfold q; simpl. rewrite Hr_eq. lia. }
    assert (Hcand_path : SameColorPath candidate_grid (i, j) q).
    { apply (proj2 (Hcand_component q Hqrow Hqcol)). exact Hq_candidate. }
    pose proof (same_color_path_endpoint_color__solver_final candidate_grid
      (i, j) q Hcand_path) as Hcand_color.
    assert (Hqindex : 0 <= i * m + (j - 1) < first) by nia.
    assert (Hanchor_index : 0 <= i * m + j < first) by nia.
    pose proof (Hprefix (i * m + (j - 1)) Hqindex) as Hprefix_q.
    pose proof (Hprefix (i * m + j) Hanchor_index) as Hprefix_anchor.
    assert (Hout_color :
        Znth (snd q) (Znth (fst q) output_grid []) 0 =
        Znth j (Znth i output_grid []) 0).
    { unfold q in *. simpl in *.
      rewrite (rows_of_flat_Znth__solver_final n m output output_grid
        i (j - 1) Hout_rows) by lia.
      rewrite (rows_of_flat_Znth__solver_final n m output output_grid
        i j Hout_rows) by lia.
      rewrite Hprefix_q.
      rewrite Hprefix_anchor.
      rewrite <- (rows_of_flat_Znth__solver_final n m candidate candidate_grid
        i (j - 1) Hcand_rows) by lia.
      rewrite <- (rows_of_flat_Znth__solver_final n m candidate candidate_grid
        i j Hcand_rows) by lia.
      exact Hcand_color. }
    assert (Hout_path : SameColorPath output_grid (i, j) q).
    { assert (Hadj : AdjCell (i, j) q).
      { unfold AdjCell, q. simpl.
        replace (i - i) with 0 by lia.
        replace (j - (j - 1)) with 1 by lia. reflexivity. }
      exact (same_color_path_step__solver_final output_grid (i, j) q
        ltac:(simpl; lia) ltac:(simpl; lia) ltac:(lia) ltac:(lia)
        Hout_color Hadj). }
    specialize (Hout_component q Hqrow Hqcol).
    apply (proj1 Hout_component) in Hout_path.
    unfold q in Hout_path. simpl in Hout_path. lia. }
  tauto.
Qed.
Lemma component_prefix_cut__solver_final :
  forall n m output candidate output_grid candidate_grid
      i j side r c candidate_side first p,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    RowsOfFlat n m candidate candidate_grid ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    1 <= candidate_side -> 0 <= r -> 0 <= c ->
    r + candidate_side <= n -> c + candidate_side <= m ->
    r <= i < r + candidate_side -> c <= j < c + candidate_side ->
    i <= fst p < i + side -> j <= snd p < j + side ->
    first = fst p * m + snd p ->
    i * m + j < first ->
    (forall k, 0 <= k < first -> Znth k output 0 = Znth k candidate 0) ->
    Znth first output 0 <> Znth first candidate 0 ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid (i, j) q <->
       i <= fst q < i + side /\ j <= snd q < j + side)) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath candidate_grid (i, j) q <->
       r <= fst q < r + candidate_side /\
       c <= snd q < c + candidate_side)) ->
    candidate_side < side /\ fst p = i /\ snd p = j + candidate_side.
Proof.
  intros n m output candidate output_grid candidate_grid i j side r c
    candidate_side first p Hn Hm Hout_rows Hcand_rows Hi Hj Hside
    Hirbound Hijbound Hcandidate_side Hr Hc Hrrbound Hccbound
    Hi_candidate Hj_candidate Hp_row Hp_col Hfirst Hanchor Hprefix Hdiff
    Hout_component Hcand_component.
  destruct (component_top_left_prefix__solver_final n m output candidate
    output_grid candidate_grid i j side r c candidate_side first Hn Hm
    Hout_rows Hcand_rows Hi Hj Hside Hirbound Hijbound Hcandidate_side Hr Hc
    Hrrbound Hccbound Hi_candidate Hj_candidate Hanchor Hprefix
    Hout_component Hcand_component) as [Hr_eq Hc_eq].
  subst r c.
  assert (Hp_bounds : 0 <= fst p < n /\ 0 <= snd p < m) by
    (split; lia).
  assert (Hcand_grid_len : Zlength candidate_grid = n) by
    (destruct Hcand_rows as [? [? ?]]; assumption).
  assert (Hcand_row0 : Zlength (Znth 0 candidate_grid []) = m).
  { destruct Hcand_rows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hp_not_candidate :
      ~ (i <= fst p < i + candidate_side /\
         j <= snd p < j + candidate_side)).
  { intros Hp_candidate.
    assert (Hcand_path : SameColorPath candidate_grid (i, j) p).
    { apply (proj2 (Hcand_component p (proj1 Hp_bounds) (proj2 Hp_bounds))).
      exact Hp_candidate. }
    pose proof (same_color_path_endpoint_color__solver_final candidate_grid
      (i, j) p Hcand_path) as Hcand_color.
    assert (Hout_path : SameColorPath output_grid (i, j) p).
    { apply (proj2 (Hout_component p (proj1 Hp_bounds) (proj2 Hp_bounds))).
      tauto. }
    pose proof (same_color_path_endpoint_color__solver_final output_grid
      (i, j) p Hout_path) as Hout_color.
    apply Hdiff.
    rewrite Hfirst.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
      (fst p) (snd p) Hout_rows) by lia.
    rewrite <- (rows_of_flat_Znth__solver_final n m candidate candidate_grid
      (fst p) (snd p) Hcand_rows) by lia.
    rewrite Hout_color, Hcand_color.
    assert (Hanchor_index : 0 <= i * m + j < first) by nia.
    pose proof (Hprefix (i * m + j) Hanchor_index) as Hanchor_eq.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
      i j Hout_rows) in Hanchor_eq by lia.
    rewrite <- (rows_of_flat_Znth__solver_final n m candidate candidate_grid
      i j Hcand_rows) in Hanchor_eq by lia.
    exact Hanchor_eq. }
  assert (Hcandidate_short : candidate_side < side).
  { destruct (Z_lt_ge_dec candidate_side side); [assumption |].
    exfalso. apply Hp_not_candidate. split; lia. }
  set (boundary := (i, j + candidate_side)).
  assert (Hboundary_row : 0 <= fst boundary < n) by
    (unfold boundary; simpl; lia).
  assert (Hboundary_col : 0 <= snd boundary < m) by
    (unfold boundary; simpl; lia).
  assert (Hboundary_index : 0 <= i * m + (j + candidate_side)) by nia.
  assert (Hfirst_le_boundary : first <= i * m + (j + candidate_side)).
  { destruct (Z_le_gt_dec first (i * m + (j + candidate_side)));
      [assumption |].
    assert (Hbprefix : 0 <= i * m + (j + candidate_side) < first) by nia.
    pose proof (Hprefix (i * m + (j + candidate_side)) Hbprefix) as Hb_eq.
    assert (Houtput_boundary_color :
        Znth (snd boundary) (Znth (fst boundary) output_grid []) 0 =
        Znth j (Znth i output_grid []) 0).
    { assert (Hpath : SameColorPath output_grid (i, j) boundary).
      { apply (proj2 (Hout_component boundary Hboundary_row Hboundary_col)).
        unfold boundary; simpl. split; lia. }
      exact (same_color_path_endpoint_color__solver_final output_grid
        (i, j) boundary Hpath). }
    assert (Hcandidate_boundary_color :
        Znth (snd boundary) (Znth (fst boundary) candidate_grid []) 0 =
        Znth j (Znth i candidate_grid []) 0).
    { assert (Hanchor_idx : 0 <= i * m + j < first) by nia.
      pose proof (Hprefix (i * m + j) Hanchor_idx) as Hanchor_eq.
      unfold boundary in *. simpl in *.
      rewrite (rows_of_flat_Znth__solver_final n m candidate candidate_grid
        i (j + candidate_side) Hcand_rows) by lia.
      rewrite (rows_of_flat_Znth__solver_final n m candidate candidate_grid
        i j Hcand_rows) by lia.
      rewrite <- Hb_eq, <- Hanchor_eq.
      rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
        i (j + candidate_side) Hout_rows) by lia.
      rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
        i j Hout_rows) by lia.
      exact Houtput_boundary_color. }
    assert (Hcandidate_path : SameColorPath candidate_grid (i, j) boundary).
    { set (inside := (i, j + candidate_side - 1)).
      assert (Hinside_row : 0 <= fst inside < n) by
        (unfold inside; simpl; lia).
      assert (Hinside_col : 0 <= snd inside < m) by
        (unfold inside; simpl; lia).
      assert (Hinside_path : SameColorPath candidate_grid (i, j) inside).
      { apply (proj2 (Hcand_component inside Hinside_row Hinside_col)).
        unfold inside; simpl. split; lia. }
      assert (Hadj : AdjCell inside boundary).
      { unfold AdjCell, inside, boundary. simpl.
        replace (i - i) with 0 by lia.
        replace (j + candidate_side - 1 - (j + candidate_side)) with (-1)
          by lia. reflexivity. }
      exact (same_color_path_append__solver_final candidate_grid (i, j)
        inside boundary Hinside_path ltac:(lia) ltac:(lia)
        Hcandidate_boundary_color Hadj). }
    apply (proj1 (Hcand_component boundary Hboundary_row Hboundary_col))
      in Hcandidate_path.
    unfold boundary in Hcandidate_path. simpl in Hcandidate_path. lia. }
  assert (Hboundary_le_first : i * m + (j + candidate_side) <= first).
  { rewrite Hfirst.
    destruct Hp_row as [Hp_row0 Hp_row1].
    destruct Hp_col as [Hp_col0 Hp_col1].
    destruct (Z.eq_dec (fst p) i) as [Hpr | Hpr].
    - assert (j + candidate_side <= snd p) by
        (destruct (Z_lt_ge_dec (snd p) (j + candidate_side));
         [exfalso; apply Hp_not_candidate; split; lia | lia]).
      nia.
    - assert (i < fst p) by lia. nia. }
  assert (Hindex_eq : first = i * m + (j + candidate_side)) by lia.
  assert (Hp_row_eq : fst p = i).
  { rewrite Hfirst in Hindex_eq.
    destruct Hp_row as [Hp_row0 Hp_row1].
    destruct Hp_col as [Hp_col0 Hp_col1].
    assert (j + candidate_side < m) by lia.
    destruct (Z.eq_dec (fst p) i); [assumption |].
    assert (i < fst p) by lia. nia. }
  assert (Hp_col_eq : snd p = j + candidate_side) by
    (rewrite Hfirst, Hp_row_eq in Hindex_eq; nia).
  tauto.
Qed.
Lemma candidate_component_at_output_anchor__solver_final :
  forall n m output candidate output_grid i j side first,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    i * m + j < first ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid (i, j) q <->
       i <= fst q < i + side /\ j <= snd q < j + side)) ->
    exists candidate_side,
      1 <= candidate_side /\
      i + candidate_side <= n /\ j + candidate_side <= m /\
      (forall q,
        0 <= fst q < n -> 0 <= snd q < m ->
        (SameColorPath candidate (i, j) q <->
         i <= fst q < i + candidate_side /\
         j <= snd q < j + candidate_side)).
Proof.
  intros n m output candidate output_grid i j side first Hn Hm Houtrows
    Hcandidate Hi Hj Hside Hirbound Hicbound Hanchor Hprefix Houtcomponent.
  pose proof (square_tiling_rows__solver_final n m candidate Hcandidate)
    as Hcandrows.
  assert (Hcand_grid_len_fd : Zlength candidate = n) by
    (destruct Hcandrows as [? [? ?]]; assumption).
  assert (Hcand_row0_fd : Zlength (Znth 0 candidate []) = m).
  { destruct Hcandrows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hcand_grid_len : Zlength candidate = n) by
    (destruct Hcandrows as [? [? ?]]; assumption).
  assert (Hcand_row0 : Zlength (Znth 0 candidate []) = m).
  { destruct Hcandrows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  destruct (square_tiling_component__solver_final n m candidate (i, j)
    Hcandidate ltac:(simpl; lia) ltac:(simpl; lia)) as
    [r [c [candidate_side [Hcandidate_side [Hr [Hc [Hrn [Hcm
      [Hi_candidate [Hj_candidate Hcandcomponent]]]]]]]]]].
  destruct (component_top_left_prefix__solver_final n m output
    (Flatten candidate) output_grid candidate i j side r c candidate_side
    first Hn Hm Houtrows Hcandrows Hi Hj Hside Hirbound Hicbound
    Hcandidate_side Hr Hc Hrn Hcm Hi_candidate Hj_candidate Hanchor
    Hprefix Houtcomponent Hcandcomponent) as [Hr_eq Hc_eq].
  subst r c.
  exists candidate_side.
  exact (conj Hcandidate_side (conj Hrn (conj Hcm Hcandcomponent))).
Qed.
Lemma candidate_component_covers_output_prefix__solver_final :
  forall n m output candidate output_grid i j side candidate_side first q,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    1 <= candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    i * m + (j + candidate_side) < first ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath output_grid (i, j) x <->
       i <= fst x < i + side /\ j <= snd x < j + side)) ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath candidate (i, j) x <->
       i <= fst x < i + candidate_side /\
       j <= snd x < j + candidate_side)) ->
    i <= fst q < i + side -> j <= snd q < j + side ->
    i <= fst q < i + candidate_side /\
    j <= snd q < j + candidate_side.
Proof.
  intros n m output candidate output_grid i j side candidate_side first q
    Hn Hm Houtrows Hcandidate Hi Hj Hside Hirbound Hicbound
    Hcandidate_side Hcrbound Hccbound Hboundary Hprefix Houtcomponent
    Hcandcomponent Hqrow Hqcol.
  pose proof (square_tiling_rows__solver_final n m candidate Hcandidate)
    as Hcandrows.
  pose proof (candidate_component_not_short_before__solver_final n m
    output (Flatten candidate) output_grid candidate i j side candidate_side
    first Hn Hm Houtrows Hcandrows Hi Hj Hside Hirbound Hicbound
    Hcandidate_side Hcrbound Hccbound Hboundary Hprefix Houtcomponent
    Hcandcomponent) as Hside_le.
  split; lia.
Qed.
Lemma first_cell_component_dichotomy__solver_final :
  forall n m output candidate output_grid first p anchor i j color side,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= fst p < n -> 0 <= snd p < m ->
    first = fst p * m + snd p ->
    anchor = i * m + j ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    i <= fst p < i + side -> j <= snd p < j + side ->
    Znth first output 0 = color ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid p q <->
       i <= fst q < i + side /\ j <= snd q < j + side)) ->
    anchor <= first ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    Znth first output 0 <> Znth first (Flatten candidate) 0 ->
    anchor = first \/
    exists candidate_side,
      1 <= candidate_side /\
      i + candidate_side <= n /\ j + candidate_side <= m /\
      candidate_side < side /\
      fst p = i /\ snd p = j + candidate_side /\
      (forall q,
        0 <= fst q < n -> 0 <= snd q < m ->
        (SameColorPath candidate (i, j) q <->
         i <= fst q < i + candidate_side /\
         j <= snd q < j + candidate_side)).
Proof.
  intros n m output candidate output_grid first p anchor i j color side
    Hn Hm Houtrows Hcandidate Hp_row Hp_col Hfirst Ha Hi Hj Hside
    Hirbound Hicbound Hp_i Hp_j Hcolor Houtcomponent Hanchor_le Hprefix
    Hdiff.
  destruct (Z.eq_dec anchor first) as [Heq | Hneq]; [left; exact Heq |].
  right.
  assert (Hanchor : i * m + j < first) by lia.
  pose proof (square_tiling_rows__solver_final n m candidate Hcandidate)
    as Hcandrows.
  assert (Hcand_grid_len_dichotomy : Zlength candidate = n) by
    (destruct Hcandrows as [? [? ?]]; assumption).
  assert (Hcand_row0_dichotomy : Zlength (Znth 0 candidate []) = m).
  { destruct Hcandrows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  destruct (square_tiling_component__solver_final n m candidate (i, j)
    Hcandidate ltac:(simpl; lia) ltac:(simpl; lia)) as
    [r [c [candidate_side [Hcandidate_side [Hr [Hc [Hcrbound [Hccbound
      [Hi_candidate [Hj_candidate Hcandcomponent0]]]]]]]]]].
  destruct Hi_candidate as [Hri Hir].
  destruct Hj_candidate as [Hcj Hjc].
  simpl in Hri, Hir, Hcj, Hjc.
  assert (Hout_anchor_path : SameColorPath output_grid p (i, j)).
  { apply (proj2 (Houtcomponent (i, j) ltac:(simpl; lia)
      ltac:(simpl; lia))). simpl. split; lia. }
  assert (Hout_grid_len : Zlength output_grid = n) by
    (destruct Houtrows as [? [? ?]]; assumption).
  assert (Hout_row0 : Zlength (Znth 0 output_grid []) = m).
  { destruct Houtrows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hr_eq : r = i).
  { destruct (Z.eq_dec r i) as [Heq | Hneq_r]; [exact Heq |].
    assert (Hrlt : r < i) by lia.
    set (q := (i - 1, j)).
    assert (Hqrow : 0 <= fst q < n) by (unfold q; simpl; lia).
    assert (Hqcol : 0 <= snd q < m) by (unfold q; simpl; lia).
    assert (Hcand_path : SameColorPath candidate (i, j) q).
    { apply (proj2 (Hcandcomponent0 q Hqrow Hqcol)).
      unfold q; simpl. split; lia. }
    pose proof (same_color_path_endpoint_color__solver_final candidate
      (i, j) q Hcand_path) as Hcand_color.
    assert (Hqindex : 0 <= (i - 1) * m + j < first) by nia.
    assert (Hanchor_index : 0 <= i * m + j < first) by nia.
    pose proof (Hprefix ((i - 1) * m + j) Hqindex) as Hprefix_q.
    pose proof (Hprefix (i * m + j) Hanchor_index) as Hprefix_anchor.
    assert (Hout_color :
        Znth (snd q) (Znth (fst q) output_grid []) 0 =
        Znth j (Znth i output_grid []) 0).
    { unfold q in *. simpl in *.
      rewrite (rows_of_flat_Znth__solver_final n m output output_grid
        (i - 1) j Houtrows) by lia.
      rewrite (rows_of_flat_Znth__solver_final n m output output_grid
        i j Houtrows) by lia.
      rewrite Hprefix_q, Hprefix_anchor.
      rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
        candidate (i - 1) j Hcandrows) by lia.
      rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
        candidate i j Hcandrows) by lia.
      exact Hcand_color. }
    assert (Hout_q_path : SameColorPath output_grid p q).
    { eapply same_color_path_append__solver_final with (x := (i, j)) (y := q).
      - exact Hout_anchor_path.
      - rewrite Hout_grid_len. exact Hqrow.
      - rewrite Hout_row0. exact Hqcol.
      - rewrite Hout_color.
        exact (same_color_path_endpoint_color__solver_final output_grid
          p (i, j) Hout_anchor_path).
      - unfold AdjCell, q. simpl.
        replace (i - (i - 1)) with 1 by lia.
        replace (j - j) with 0 by lia. reflexivity. }
    apply (proj1 (Houtcomponent q Hqrow Hqcol)) in Hout_q_path.
    unfold q in Hout_q_path. simpl in Hout_q_path. lia. }
  assert (Hc_eq : c = j).
  { destruct (Z.eq_dec c j) as [Heq | Hneq_c]; [exact Heq |].
    assert (Hclt : c < j) by lia.
    set (q := (i, j - 1)).
    assert (Hqrow : 0 <= fst q < n) by (unfold q; simpl; lia).
    assert (Hqcol : 0 <= snd q < m) by (unfold q; simpl; lia).
    assert (Hcand_path : SameColorPath candidate (i, j) q).
    { apply (proj2 (Hcandcomponent0 q Hqrow Hqcol)).
      unfold q; simpl. rewrite Hr_eq. split; lia. }
    pose proof (same_color_path_endpoint_color__solver_final candidate
      (i, j) q Hcand_path) as Hcand_color.
    assert (Hqindex : 0 <= i * m + (j - 1) < first) by nia.
    assert (Hanchor_index : 0 <= i * m + j < first) by nia.
    pose proof (Hprefix (i * m + (j - 1)) Hqindex) as Hprefix_q.
    pose proof (Hprefix (i * m + j) Hanchor_index) as Hprefix_anchor.
    assert (Hout_color :
        Znth (snd q) (Znth (fst q) output_grid []) 0 =
        Znth j (Znth i output_grid []) 0).
    { unfold q in *. simpl in *.
      rewrite (rows_of_flat_Znth__solver_final n m output output_grid
        i (j - 1) Houtrows) by lia.
      rewrite (rows_of_flat_Znth__solver_final n m output output_grid
        i j Houtrows) by lia.
      rewrite Hprefix_q, Hprefix_anchor.
      rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
        candidate i (j - 1) Hcandrows) by lia.
      rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
        candidate i j Hcandrows) by lia.
      exact Hcand_color. }
    assert (Hout_q_path : SameColorPath output_grid p q).
    { eapply same_color_path_append__solver_final with (x := (i, j)) (y := q).
      - exact Hout_anchor_path.
      - rewrite Hout_grid_len. exact Hqrow.
      - rewrite Hout_row0. exact Hqcol.
      - rewrite Hout_color.
        exact (same_color_path_endpoint_color__solver_final output_grid
          p (i, j) Hout_anchor_path).
      - unfold AdjCell, q. simpl.
        replace (i - i) with 0 by lia.
        replace (j - (j - 1)) with 1 by lia. reflexivity. }
    apply (proj1 (Houtcomponent q Hqrow Hqcol)) in Hout_q_path.
    unfold q in Hout_q_path. simpl in Hout_q_path. lia. }
  subst r c.
  rename Hcandcomponent0 into Hcandcomponent.
  assert (Hcandidate_short : candidate_side < side).
  { destruct (Z_lt_ge_dec candidate_side side) as [Hlt | Hge]; [exact Hlt |].
    exfalso. apply Hdiff.
    rewrite Hfirst.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
      (fst p) (snd p) Houtrows Hp_row Hp_col).
    rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate (fst p) (snd p) Hcandrows Hp_row Hp_col).
    assert (Houtpath : SameColorPath output_grid p p).
    { apply (proj2 (Houtcomponent p Hp_row Hp_col)). tauto. }
    assert (Hcandpath : SameColorPath candidate (i, j) p).
    { apply (proj2 (Hcandcomponent p Hp_row Hp_col)). split; lia. }
    rewrite <- (same_color_path_endpoint_color__solver_final output_grid
      p (i, j) Hout_anchor_path).
    rewrite (same_color_path_endpoint_color__solver_final candidate
      (i, j) p Hcandpath).
    assert (Hanchor_index : 0 <= i * m + j < first) by nia.
    pose proof (Hprefix (i * m + j) Hanchor_index) as Hanchor_eq.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid i j
      Houtrows Hi Hj) in Hanchor_eq.
    rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate i j Hcandrows Hi Hj) in Hanchor_eq.
    exact Hanchor_eq. }
  assert (Hp_not_candidate :
      ~ (i <= fst p < i + candidate_side /\
         j <= snd p < j + candidate_side)).
  { intros Hp_candidate.
    assert (Hcand_path : SameColorPath candidate (i, j) p).
    { apply (proj2 (Hcandcomponent p Hp_row Hp_col)). exact Hp_candidate. }
    pose proof (same_color_path_endpoint_color__solver_final candidate
      (i, j) p Hcand_path) as Hcand_color.
    apply Hdiff.
    rewrite Hfirst.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
      (fst p) (snd p) Houtrows Hp_row Hp_col).
    rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate (fst p) (snd p) Hcandrows Hp_row Hp_col).
    rewrite <- (same_color_path_endpoint_color__solver_final output_grid
      p (i, j) Hout_anchor_path).
    rewrite Hcand_color.
    assert (Hanchor_index : 0 <= i * m + j < first) by nia.
    pose proof (Hprefix (i * m + j) Hanchor_index) as Hanchor_eq.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid i j
      Houtrows Hi Hj) in Hanchor_eq.
    rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate i j Hcandrows Hi Hj) in Hanchor_eq.
    exact Hanchor_eq. }
  set (boundary := (i, j + candidate_side)).
  assert (Hboundary_row : 0 <= fst boundary < n) by
    (unfold boundary; simpl; lia).
  assert (Hboundary_col : 0 <= snd boundary < m) by
    (unfold boundary; simpl; lia).
  assert (Hfirst_le_boundary : first <= i * m + (j + candidate_side)).
  { destruct (Z_le_gt_dec first (i * m + (j + candidate_side)));
      [assumption |].
    assert (Hbprefix : 0 <= i * m + (j + candidate_side) < first) by nia.
    pose proof (Hprefix (i * m + (j + candidate_side)) Hbprefix) as Hb_eq.
    assert (Houtput_boundary_color :
        Znth (snd boundary) (Znth (fst boundary) output_grid []) 0 =
        Znth j (Znth i output_grid []) 0).
    { assert (Hpath : SameColorPath output_grid p boundary).
      { apply (proj2 (Houtcomponent boundary Hboundary_row Hboundary_col)).
        unfold boundary; simpl. split; lia. }
      transitivity (Znth (snd p) (Znth (fst p) output_grid []) 0).
      - exact (same_color_path_endpoint_color__solver_final output_grid
          p boundary Hpath).
      - symmetry. exact (same_color_path_endpoint_color__solver_final
          output_grid p (i, j) Hout_anchor_path). }
    assert (Hcandidate_boundary_color :
        Znth (snd boundary) (Znth (fst boundary) candidate []) 0 =
        Znth j (Znth i candidate []) 0).
    { unfold boundary in *. simpl in *.
      rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
        candidate i (j + candidate_side) Hcandrows) by lia.
      rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
        candidate i j Hcandrows) by lia.
      rewrite <- Hb_eq.
      assert (Hanchor_index : 0 <= i * m + j < first) by nia.
      rewrite <- (Hprefix (i * m + j) Hanchor_index).
      rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
        i (j + candidate_side) Houtrows) by lia.
      rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
        i j Houtrows) by lia.
      exact Houtput_boundary_color. }
    set (inside := (i, j + candidate_side - 1)).
    assert (Hinside_row : 0 <= fst inside < n) by
      (unfold inside; simpl; lia).
    assert (Hinside_col : 0 <= snd inside < m) by
      (unfold inside; simpl; lia).
    assert (Hinside_path : SameColorPath candidate (i, j) inside).
    { apply (proj2 (Hcandcomponent inside Hinside_row Hinside_col)).
      unfold inside; simpl. split; lia. }
    assert (Hboundary_path : SameColorPath candidate (i, j) boundary).
    { eapply same_color_path_append__solver_final with (x := inside)
        (y := boundary).
      - exact Hinside_path.
      - rewrite Hcand_grid_len_dichotomy. exact Hboundary_row.
      - rewrite Hcand_row0_dichotomy. exact Hboundary_col.
      - exact Hcandidate_boundary_color.
      - unfold AdjCell, inside, boundary. simpl.
        replace (i - i) with 0 by lia.
        replace (j + candidate_side - 1 - (j + candidate_side)) with (-1)
          by lia. reflexivity. }
    apply (proj1 (Hcandcomponent boundary Hboundary_row Hboundary_col))
      in Hboundary_path.
    unfold boundary in Hboundary_path. simpl in Hboundary_path. lia. }
  assert (Hboundary_le_first : i * m + (j + candidate_side) <= first).
  { rewrite Hfirst.
    destruct (Z.eq_dec (fst p) i) as [Hpr | Hpr].
    - assert (j + candidate_side <= snd p) by
        (destruct (Z_lt_ge_dec (snd p) (j + candidate_side));
         [exfalso; apply Hp_not_candidate; split; lia | lia]).
      nia.
    - assert (i < fst p) by lia. nia. }
  assert (Hindex_eq : first = i * m + (j + candidate_side)) by lia.
  assert (Hp_i_eq : fst p = i).
  { rewrite Hfirst in Hindex_eq.
    assert (j + candidate_side < m) by lia.
    destruct (Z.eq_dec (fst p) i); [assumption |].
    assert (i < fst p) by lia. nia. }
  assert (Hp_j_eq : snd p = j + candidate_side) by
    (rewrite Hfirst, Hp_i_eq in Hindex_eq; nia).
  exists candidate_side.
  exact (conj Hcandidate_side (conj Hcrbound (conj Hccbound
    (conj Hcandidate_short (conj Hp_i_eq (conj Hp_j_eq Hcandcomponent)))))).
Qed.
Lemma exact_component_reanchor__solver_final :
  forall grid n m p anchor r c side,
    Zlength grid = n ->
    Zlength (Znth 0 grid []) = m ->
    1 <= side -> 0 <= r -> 0 <= c ->
    r + side <= n -> c + side <= m ->
    0 <= fst p < n -> 0 <= snd p < m ->
    r <= fst p < r + side -> c <= snd p < c + side ->
    0 <= fst anchor < n -> 0 <= snd anchor < m ->
    r <= fst anchor < r + side -> c <= snd anchor < c + side ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath grid p q <->
       r <= fst q < r + side /\ c <= snd q < c + side)) ->
    forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath grid anchor q <->
       r <= fst q < r + side /\ c <= snd q < c + side).
Proof.
  intros grid n m p anchor r c side Hgrid_len Hrow_len Hside Hr Hc
    Hrbound Hcbound Hp_row Hp_col Hp_r Hp_c Ha_row Ha_col Ha_r Ha_c
    Hcomponent q Hqrow Hqcol.
  assert (Hregion_color : forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      r <= fst x < r + side -> c <= snd x < c + side ->
      Znth (snd x) (Znth (fst x) grid []) 0 =
      Znth (snd p) (Znth (fst p) grid []) 0).
  { intros x Hxrow Hxcol Hxr Hxc.
    apply same_color_path_endpoint_color__solver_final.
    apply (proj2 (Hcomponent x Hxrow Hxcol)). tauto. }
  assert (Hanchor_color :
      Znth (snd anchor) (Znth (fst anchor) grid []) 0 =
      Znth (snd p) (Znth (fst p) grid []) 0).
  { apply Hregion_color; assumption. }
  split; intros Hpath.
  - eapply same_color_path_closed__solver_final with
      (color := Znth (snd p) (Znth (fst p) grid []) 0)
      (region := fun x =>
        r <= fst x < r + side /\ c <= snd x < c + side).
    + exact Hpath.
    + tauto.
    + intros x y Hx Hyrow Hycol Hycolor Hadj.
      assert (Hxrow : 0 <= fst x < n) by lia.
      assert (Hxcol : 0 <= snd x < m) by lia.
      assert (Hpx : SameColorPath grid p x).
      { apply (proj2 (Hcomponent x Hxrow Hxcol)). exact Hx. }
      assert (Hpy : SameColorPath grid p y).
      { eapply same_color_path_append__solver_final with (x := x) (y := y).
        - exact Hpx.
        - exact Hyrow.
        - exact Hycol.
        - exact Hycolor.
        - exact Hadj. }
      apply (proj1 (Hcomponent y ltac:(rewrite <- Hgrid_len; exact Hyrow)
        ltac:(rewrite <- Hrow_len; exact Hycol))). exact Hpy.
    + exact Hanchor_color.
  - eapply rectangle_connected__solver_final with
      (r := r) (c := c) (side := side)
      (color := Znth (snd p) (Znth (fst p) grid []) 0).
    + exact Hside.
    + exact Hr.
    + exact Hc.
    + rewrite Hgrid_len. exact Hrbound.
    + rewrite Hrow_len. exact Hcbound.
    + exact Ha_r.
    + exact Ha_c.
    + exact (proj1 Hpath).
    + exact (proj2 Hpath).
    + intros x Hxr Hxc.
      apply Hregion_color; lia.
Qed.
Lemma candidate_component_at_output_member__solver_final :
  forall n m output candidate output_grid p i j side first,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= fst p < n -> 0 <= snd p < m ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    i <= fst p < i + side -> j <= snd p < j + side ->
    i * m + j < first ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid p q <->
       i <= fst q < i + side /\ j <= snd q < j + side)) ->
    exists candidate_side,
      1 <= candidate_side /\
      i + candidate_side <= n /\ j + candidate_side <= m /\
      (forall q,
        0 <= fst q < n -> 0 <= snd q < m ->
        (SameColorPath candidate (i, j) q <->
         i <= fst q < i + candidate_side /\
         j <= snd q < j + candidate_side)).
Proof.
  intros n m output candidate output_grid p i j side first Hn Hm Houtrows
    Hcandidate Hp_row Hp_col Hi Hj Hside Hirbound Hicbound Hp_i Hp_j
    Hanchor Hprefix Hcomponent.
  assert (Hgrid_len : Zlength output_grid = n) by
    (destruct Houtrows as [? [? ?]]; assumption).
  assert (Hrow_len : Zlength (Znth 0 output_grid []) = m).
  { destruct Houtrows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hcomponent_anchor : forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid (i, j) q <->
       i <= fst q < i + side /\ j <= snd q < j + side)).
  { intros q Hqrow Hqcol.
    eapply exact_component_reanchor__solver_final with
      (p := p) (r := i) (c := j) (side := side); eauto; simpl; lia. }
  eapply candidate_component_at_output_anchor__solver_final; eauto.
Qed.
Lemma candidate_component_not_short_before_member__solver_final :
  forall n m output candidate output_grid p i j side candidate_side first,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= fst p < n -> 0 <= snd p < m ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    i <= fst p < i + side -> j <= snd p < j + side ->
    1 <= candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    i * m + (j + candidate_side) < first ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid p q <->
       i <= fst q < i + side /\ j <= snd q < j + side)) ->
    (forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath candidate (i, j) q <->
       i <= fst q < i + candidate_side /\
       j <= snd q < j + candidate_side)) ->
    side <= candidate_side.
Proof.
  intros n m output candidate output_grid p i j side candidate_side first
    Hn Hm Houtrows Hcandidate Hp_row Hp_col Hi Hj Hside Hirbound Hicbound
    Hp_i Hp_j Hcandidate_side Hcrbound Hccbound Hboundary Hprefix
    Hcomponent Hcandcomponent.
  assert (Hgrid_len : Zlength output_grid = n) by
    (destruct Houtrows as [? [? ?]]; assumption).
  assert (Hrow_len : Zlength (Znth 0 output_grid []) = m).
  { destruct Houtrows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hcomponent_anchor : forall q,
      0 <= fst q < n -> 0 <= snd q < m ->
      (SameColorPath output_grid (i, j) q <->
       i <= fst q < i + side /\ j <= snd q < j + side)).
  { intros q Hqrow Hqcol.
    eapply exact_component_reanchor__solver_final with
      (p := p) (r := i) (c := j) (side := side); eauto; simpl; lia. }
  exact (candidate_component_not_short_before__solver_final n m output
    (Flatten candidate) output_grid candidate i j side candidate_side first
    Hn Hm Houtrows
    (square_tiling_rows__solver_final n m candidate Hcandidate) Hi Hj Hside
    Hirbound Hicbound Hcandidate_side Hcrbound Hccbound Hboundary Hprefix
    Hcomponent_anchor Hcandcomponent).
Qed.
Lemma conflict_zero_has_earlier_component__solver_final :
  forall n m anchor before before_grid i j color,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m anchor before ->
    RowsOfFlat n m before before_grid ->
    0 <= i < n -> 0 <= j < m ->
    65 <= color ->
    NeighborConflict before n m i j color 0 ->
    exists (q : Cell) earlier origin_before painted oi oj oside,
      earlier = oi * m + oj /\
      earlier < anchor /\
      GreedyPlacementTrace n m earlier origin_before /\
      SettledSquareState origin_before n m oi oj color oside /\
      PaintRectanglePrefix origin_before painted m oi oj oside color
        (oside * oside) /\
      0 <= oi < n /\ 0 <= oj < m /\
      oi <= fst q < oi + oside /\ oj <= snd q < oj + oside /\
      AdjCell (i, j) q /\
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath before_grid q x <->
         oi <= fst x < oi + oside /\ oj <= snd x < oj + oside)) /\
      (forall k,
        0 <= k < n * m ->
        Znth k origin_before 0 <> 0 ->
        Znth k before 0 = Znth k origin_before 0).
Proof.
  intros n m anchor before before_grid i j color Hn Hm Htrace Hrows Hi Hj
    Hcolor Hconflict.
  unfold NeighborConflict in Hconflict.
  destruct Hconflict as
      [[Hitop Htop] |
       [[Hibottom Hbottom] |
        [[Hjright Hright] |
         [[Hjleft Hleft] | [Hjzero Hoverride]]]]].
  - set (q := (i - 1, j)).
    assert (Hqrow : 0 <= fst q < n) by (unfold q; simpl; lia).
    assert (Hqcol : 0 <= snd q < m) by (unfold q; simpl; lia).
    assert (Hqflat : Znth (fst q * m + snd q) before 0 = color).
    { unfold q; simpl. exact Htop. }
    assert (Hadj : AdjCell (i, j) q).
    { unfold AdjCell, q; simpl.
      replace (i - (i - 1)) with 1 by lia.
      replace (j - j) with 0 by lia. reflexivity. }
    assert (Hqgrid :
        Znth (snd q) (Znth (fst q) before_grid []) 0 = color).
    { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
        (fst q) (snd q) Hrows Hqrow Hqcol). exact Hqflat. }
    assert (Hqnonzero :
        Znth (snd q) (Znth (fst q) before_grid []) 0 <> 0) by lia.
    destruct (trace_colored_component_origin__solver_final n m anchor before
      before_grid q Hn Hm Htrace Hrows Hqrow Hqcol Hqnonzero) as
      [earlier [origin_before [painted [oi [oj [found [oside Horigin]]]]]]].
    destruct Horigin as [Ha [Hearlier [Horigin_trace [Hsettled [Hpaint
      [Hoi [Hoj [Hqoi [Hqoj [Hqcolor [Hcomponent Hpersist]]]]]]]]]]].
    assert (Hfound : found = color) by congruence. subst found.
    rewrite Hqgrid in Hsettled, Hpaint.
    exists q, earlier, origin_before, painted, oi, oj, oside.
    refine (conj Ha (conj Hearlier (conj Horigin_trace
      (conj Hsettled (conj Hpaint _))))).
    refine (conj Hoi (conj Hoj (conj Hqoi (conj Hqoj (conj Hadj _))))).
    exact (conj Hcomponent Hpersist).
  - set (q := (i + 1, j)).
    assert (Hqrow : 0 <= fst q < n) by (unfold q; simpl; lia).
    assert (Hqcol : 0 <= snd q < m) by (unfold q; simpl; lia).
    assert (Hqflat : Znth (fst q * m + snd q) before 0 = color).
    { unfold q; simpl. exact Hbottom. }
    assert (Hadj : AdjCell (i, j) q).
    { unfold AdjCell, q; simpl.
      replace (i - (i + 1)) with (-1) by lia.
      replace (j - j) with 0 by lia. reflexivity. }
    assert (Hqgrid :
        Znth (snd q) (Znth (fst q) before_grid []) 0 = color).
    { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
        (fst q) (snd q) Hrows Hqrow Hqcol). exact Hqflat. }
    assert (Hqnonzero :
        Znth (snd q) (Znth (fst q) before_grid []) 0 <> 0) by lia.
    destruct (trace_colored_component_origin__solver_final n m anchor before
      before_grid q Hn Hm Htrace Hrows Hqrow Hqcol Hqnonzero) as
      [earlier [origin_before [painted [oi [oj [found [oside Horigin]]]]]]].
    destruct Horigin as [Ha [Hearlier [Horigin_trace [Hsettled [Hpaint
      [Hoi [Hoj [Hqoi [Hqoj [Hqcolor [Hcomponent Hpersist]]]]]]]]]]].
    assert (Hfound : found = color) by congruence. subst found.
    rewrite Hqgrid in Hsettled, Hpaint.
    exists q, earlier, origin_before, painted, oi, oj, oside.
    refine (conj Ha (conj Hearlier (conj Horigin_trace
      (conj Hsettled (conj Hpaint _))))).
    refine (conj Hoi (conj Hoj (conj Hqoi (conj Hqoj (conj Hadj _))))).
    exact (conj Hcomponent Hpersist).
  - set (q := (i, j + 1)).
    assert (Hqrow : 0 <= fst q < n) by (unfold q; simpl; lia).
    assert (Hqcol : 0 <= snd q < m) by (unfold q; simpl; lia).
    assert (Hqflat : Znth (fst q * m + snd q) before 0 = color).
    { unfold q; simpl. replace (i * m + (j + 1)) with (i * m + j + 1)
        by lia. exact Hright. }
    assert (Hadj : AdjCell (i, j) q).
    { unfold AdjCell, q; simpl.
      replace (i - i) with 0 by lia.
      replace (j - (j + 1)) with (-1) by lia. reflexivity. }
    assert (Hqgrid :
        Znth (snd q) (Znth (fst q) before_grid []) 0 = color).
    { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
        (fst q) (snd q) Hrows Hqrow Hqcol). exact Hqflat. }
    assert (Hqnonzero :
        Znth (snd q) (Znth (fst q) before_grid []) 0 <> 0) by lia.
    destruct (trace_colored_component_origin__solver_final n m anchor before
      before_grid q Hn Hm Htrace Hrows Hqrow Hqcol Hqnonzero) as
      [earlier [origin_before [painted [oi [oj [found [oside Horigin]]]]]]].
    destruct Horigin as [Ha [Hearlier [Horigin_trace [Hsettled [Hpaint
      [Hoi [Hoj [Hqoi [Hqoj [Hqcolor [Hcomponent Hpersist]]]]]]]]]]].
    assert (Hfound : found = color) by congruence. subst found.
    rewrite Hqgrid in Hsettled, Hpaint.
    exists q, earlier, origin_before, painted, oi, oj, oside.
    refine (conj Ha (conj Hearlier (conj Horigin_trace
      (conj Hsettled (conj Hpaint _))))).
    refine (conj Hoi (conj Hoj (conj Hqoi (conj Hqoj (conj Hadj _))))).
    exact (conj Hcomponent Hpersist).
  - destruct (Z.eq_dec 0 0) as [_ | Hbad]; [|contradiction].
    set (q := (i, j - 1)).
    assert (Hqrow : 0 <= fst q < n) by (unfold q; simpl; lia).
    assert (Hqcol : 0 <= snd q < m) by (unfold q; simpl; lia).
    assert (Hqflat : Znth (fst q * m + snd q) before 0 = color).
    { unfold q; simpl. replace (i * m + (j - 1)) with (i * m + j - 1)
        by lia. exact Hleft. }
    assert (Hadj : AdjCell (i, j) q).
    { unfold AdjCell, q; simpl.
      replace (i - i) with 0 by lia.
      replace (j - (j - 1)) with 1 by lia. reflexivity. }
    assert (Hqgrid :
        Znth (snd q) (Znth (fst q) before_grid []) 0 = color).
    { rewrite (rows_of_flat_Znth__solver_final n m before before_grid
        (fst q) (snd q) Hrows Hqrow Hqcol). exact Hqflat. }
    assert (Hqnonzero :
        Znth (snd q) (Znth (fst q) before_grid []) 0 <> 0) by lia.
    destruct (trace_colored_component_origin__solver_final n m anchor before
      before_grid q Hn Hm Htrace Hrows Hqrow Hqcol Hqnonzero) as
      [earlier [origin_before [painted [oi [oj [found [oside Horigin]]]]]]].
    destruct Horigin as [Ha [Hearlier [Horigin_trace [Hsettled [Hpaint
      [Hoi [Hoj [Hqoi [Hqoj [Hqcolor [Hcomponent Hpersist]]]]]]]]]]].
    assert (Hfound : found = color) by congruence. subst found.
    rewrite Hqgrid in Hsettled, Hpaint.
    exists q, earlier, origin_before, painted, oi, oj, oside.
    refine (conj Ha (conj Hearlier (conj Horigin_trace
      (conj Hsettled (conj Hpaint _))))).
    refine (conj Hoi (conj Hoj (conj Hqoi (conj Hqoj (conj Hadj _))))).
    exact (conj Hcomponent Hpersist).
  - lia.
Qed.
Lemma greedy_trace_state_unique__solver_final :
  forall n m next left right,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next left ->
    GreedyPlacementTrace n m next right ->
    left = right.
Proof.
  intros n m next left right Hn Hm Hleft.
  revert right.
  induction Hleft as
      [left Hleft_len Hleft_zero
      |next left Hleft IH Hnext Hcell
      |next before after i j color side Hleft IH Hnext Hi Hj Hzero
         Hsettled Hpaint]; intros right Hright.
  - inversion Hright as
      [right0 Hright_len Hright_zero
      |next0 flat0 Htrace0 Hnext0 Hcell0
      |next0 before0 after0 i0 j0 color0 side0 Htrace0 Hnext0 Hi0 Hj0
         Hzero0 Hsettled0 Hpaint0]; subst.
    + apply (proj2 (list_eq_ext left right 0)).
      split; [lia |]. intros k Hk.
      rewrite Hleft_zero by lia. rewrite Hright_zero by lia. reflexivity.
    + pose proof (trace_bounds_and_canonical__solver_final n m _ _
        Hn Hm Htrace0) as [Hbounds Hrest]. lia.
    + pose proof (trace_bounds_and_canonical__solver_final n m _ _
        Hn Hm Htrace0) as [Hbounds Hrest]. lia.
  - inversion Hright as
      [right0 Hright_len Hright_zero
      |next0 flat0 Htrace0 Hnext0 Hcell0
      |next0 before0 after0 i0 j0 color0 side0 Htrace0 Hnext0 Hi0 Hj0
         Hzero0 Hsettled0 Hpaint0]; subst.
    + pose proof (trace_bounds_and_canonical__solver_final n m next left
        Hn Hm Hleft) as [Hbounds Hrest]. lia.
    + lazymatch type of Htrace0 with
      | GreedyPlacementTrace _ _ ?k _ =>
          lazymatch type of Hleft with
          | GreedyPlacementTrace _ _ ?cur _ =>
              replace k with cur in Htrace0 by lia
          end
      end.
      apply IH. exact Htrace0.
    + lazymatch type of Htrace0 with
      | GreedyPlacementTrace _ _ ?k _ =>
          lazymatch type of Hleft with
          | GreedyPlacementTrace _ _ ?cur _ =>
              replace k with cur in Htrace0 by lia
          end
      end.
      pose proof (IH _ Htrace0) as Heq.
      rewrite <- Heq in Hzero0.
      replace (i0 * m + j0) with next in Hzero0 by lia. lia.
  - inversion Hright as
      [right0 Hright_len Hright_zero
      |next0 flat0 Htrace0 Hnext0 Hcell0
      |next0 before0 after0 i0 j0 color0 side0 Htrace0 Hnext0 Hi0 Hj0
         Hzero0 Hsettled0 Hpaint0]; subst.
    + pose proof (trace_bounds_and_canonical__solver_final n m _ before
        Hn Hm Hleft) as [Hbounds Hrest]. lia.
    + lazymatch type of Htrace0 with
      | GreedyPlacementTrace _ _ ?k _ =>
          lazymatch type of Hleft with
          | GreedyPlacementTrace _ _ ?cur _ =>
              replace k with cur in Htrace0 by lia
          end
      end.
      pose proof (IH _ Htrace0) as Heq.
      rewrite <- Heq in Hcell0.
      lazymatch type of Hcell0 with
      | 65 <= Znth ?idx before 0 <= 90 =>
          replace idx with (i * m + j) in Hcell0 by lia
      end.
      lia.
    + lazymatch type of Htrace0 with
      | GreedyPlacementTrace _ _ ?k _ =>
          lazymatch type of Hleft with
          | GreedyPlacementTrace _ _ ?cur _ =>
              replace k with cur in Htrace0 by lia
          end
      end.
      pose proof (IH _ Htrace0) as Hbefore_eq.
      rewrite <- Hbefore_eq in Hzero0, Hsettled0, Hpaint0.
      assert (Hi_eq : i = i0 /\ j = j0).
      { assert (Hindex_eq : i * m + j = i0 * m + j0) by lia.
        assert (Hrow_eq : i = i0).
        { destruct (Z.lt_trichotomy i i0) as [Hlt | [Heq | Hgt]];
            [exfalso; nia | exact Heq | exfalso; nia]. }
        split; [exact Hrow_eq |]. subst i0. lia. }
      destruct Hi_eq as [-> ->].
      assert (Hcolor_eq : color = color0).
      { destruct Hsettled as [[Hleast Hgreedy] Hstop].
        destruct Hsettled0 as [[Hleast0 Hgreedy0] Hstop0].
        eapply least_legal_color_unique__solver_final; eauto. }
      subst color0.
      assert (Hside_eq : side = side0).
      { eapply settled_side_unique__solver_final; eauto. }
      subst side0.
      eapply paint_rectangle_unique__solver_final; eauto.
Qed.
Lemma greedy_trace_prefix_persistence__solver_final :
  forall n m start final before output,
    1 <= n -> 1 <= m ->
    start <= final ->
    GreedyPlacementTrace n m start before ->
    GreedyPlacementTrace n m final output ->
    forall k,
      0 <= k < n * m ->
      Znth k before 0 <> 0 ->
      Znth k output 0 = Znth k before 0.
Proof.
  intros n m start final before output Hn Hm Hle Hstart Hfinal.
  revert start before Hle Hstart.
  induction Hfinal as
      [output Hlen Hzero
      |next output Htrace IH Hnext Hcell
      |next current output i j color side Htrace IH Hnext Hi Hj Hanchor
         Hsettled Hpaint]; intros start before Hle Hstart k Hk Hnonzero.
  - pose proof (trace_bounds_and_canonical__solver_final n m start before
      Hn Hm Hstart) as [Hbounds Hrest].
    assert (start = 0) by lia. subst start.
    assert (before = output).
    { exact (greedy_trace_state_unique__solver_final n m 0 before output
        Hn Hm Hstart (@GreedyTrace_zero n m output Hlen Hzero)). }
    subst before. reflexivity.
  - destruct (Z.eq_dec start (next + 1)) as [Heq | Hneq].
    + subst start.
      assert (before = output).
      { exact (greedy_trace_state_unique__solver_final n m (next + 1)
          before output Hn Hm Hstart
          (@GreedyTrace_skip n m next output Htrace Hnext Hcell)). }
      subst before. reflexivity.
    + apply IH with (start := start); try assumption. lia.
  - destruct (Z.eq_dec start (next + 1)) as [Heq | Hneq].
    + subst start.
      assert (before = output).
      { exact (greedy_trace_state_unique__solver_final n m (next + 1)
          before output Hn Hm Hstart
          (@GreedyTrace_place n m next current output i j color side Htrace
            Hnext Hi Hj Hanchor Hsettled Hpaint)). }
      subst before. reflexivity.
    + assert (Hstart_next : start <= next) by lia.
      assert (Hcurrent : Znth k current 0 = Znth k before 0).
      { apply IH with (start := start); assumption. }
      assert (Hcurrent_nonzero : Znth k current 0 <> 0).
      { rewrite Hcurrent. exact Hnonzero. }
      destruct Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
      rewrite (paint_preserves_nonzero__solver_final current output n m i j
        side color Hplace Hpaint k ltac:(
          pose proof (trace_bounds_and_canonical__solver_final n m next current
            Hn Hm Htrace) as [Hb [Hlength Hcanon]]; lia) Hcurrent_nonzero).
      exact Hcurrent.
Qed.
Lemma earlier_rectangle_crossing_geometry__solver_final :
  forall m oi oj side candidate_side first p q,
    1 <= m ->
    0 <= oj -> oj + side <= m ->
    1 <= candidate_side -> oj + candidate_side <= m ->
    oi * m + oj < first ->
    first = fst p * m + snd p ->
    0 <= snd p < m ->
    oi <= fst q < oi + side ->
    oj <= snd q < oj + side ->
    AdjCell p q ->
    q <> (fst p, snd p - 1) ->
    first <= oi * m + (oj + candidate_side) ->
    (oi <= fst p < oi + candidate_side /\
     oj <= snd p < oj + candidate_side) \/
    first = oi * m + (oj + candidate_side).
Proof.
  intros m oi oj side candidate_side first p q Hm Hoj Hside
    Hcandidate_side Hcandidate_bound Hanchor Hfirst Hpcol Hqrow Hqcol
    Hadj Hnotleft Hboundary.
  destruct (classic (oi <= fst p < oi + candidate_side /\
      oj <= snd p < oj + candidate_side)) as [Hinside | Houtside].
  - left. exact Hinside.
  - right.
    destruct (adjcell_cases__solver_final p q Hadj) as
      [[Hqr Hqc] | [[Hqr Hqc] | [[Hqr Hqc] | [Hqr Hqc]]]].
    + destruct p as [pr pc], q as [qr qc]; simpl in *; subst qr qc.
      assert (Hprlo : oi <= pr).
      { destruct (Z_lt_ge_dec pr oi); [exfalso | lia].
        assert (pr <= oi - 1) by lia.
        nia. }
      assert (Hpclo : oj <= pc) by lia.
      assert (Hprhi : pr < oi + candidate_side).
      { destruct (Z_lt_ge_dec pr (oi + candidate_side)); [lia | exfalso].
        nia. }
      assert (Hpchi : oj + candidate_side <= pc).
      { destruct (Z_lt_ge_dec pc (oj + candidate_side)); [exfalso | lia].
        apply Houtside. split; lia. }
      assert (pr = oi) by nia.
      nia.
    + destruct p as [pr pc], q as [qr qc]; simpl in *; subst qr qc.
      nia.
    + destruct p as [pr pc], q as [qr qc]; simpl in *; subst qr qc.
      assert (Hprlo : oi <= pr).
      { destruct (Z_lt_ge_dec pr oi); [exfalso | lia]. nia. }
      destruct (Z.eq_dec pr oi) as [Hpreq | Hprneq].
      * subst pr.
        assert (Hpclo : oj <= pc) by nia.
        assert (Hpchi : oj + candidate_side <= pc).
        { destruct (Z_lt_ge_dec pc (oj + candidate_side)); [exfalso | lia].
          apply Houtside. split; nia. }
        nia.
      * assert (oi < pr) by lia.
        nia.
    + exfalso. apply Hnotleft. destruct p, q; simpl in *; f_equal; lia.
Qed.
Lemma conflict_component_crosses_candidate__solver_final :
  forall n m output output_grid candidate first p q oi oj color oside,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= fst p < n -> 0 <= snd p < m ->
    0 <= fst q < n -> 0 <= snd q < m ->
    first = fst p * m + snd p ->
    0 <= oi < n -> 0 <= oj < m ->
    1 <= oside -> oi + oside <= n -> oj + oside <= m ->
    oi <= fst q < oi + oside -> oj <= snd q < oj + oside ->
    oi * m + oj < first ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    Znth (oi * m + oj) output 0 = color ->
    Znth first (Flatten candidate) 0 = color ->
    Znth first output 0 <> color ->
    AdjCell p q ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath output_grid q x <->
       oi <= fst x < oi + oside /\ oj <= snd x < oj + oside)) ->
    exists candidate_side,
      1 <= candidate_side /\
      oi + candidate_side <= n /\ oj + candidate_side <= m /\
      oside < candidate_side /\
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (oi, oj) x <->
         oi <= fst x < oi + candidate_side /\
         oj <= snd x < oj + candidate_side)) /\
      oi <= fst p < oi + candidate_side /\
      oj <= snd p < oj + candidate_side.
Proof.
  intros n m output output_grid candidate first p q oi oj color oside
    Hn Hm Houtrows Hcandidate Hprow Hpcol Hqrow Hqcol Hfirst Hoi Hoj
    Hoside Hoibound Hojbound Hqoi Hqoj Hanchor Hprefix Houtanchor
    Hcandfirst Houtfirst Hadj Houtcomponent.
  destruct (candidate_component_at_output_member__solver_final n m output
    candidate output_grid q oi oj oside first Hn Hm Houtrows Hcandidate
    Hqrow Hqcol Hoi Hoj Hoside Hoibound Hojbound Hqoi Hqoj Hanchor
    Hprefix Houtcomponent) as
    [candidate_side [Hcandidate_side [Hcandidate_i
      [Hcandidate_j Hcandcomponent]]]].
  assert (Hcandidate_anchor :
      Znth oj (Znth oi candidate []) 0 = color).
  { rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate oi oj
      (square_tiling_rows__solver_final n m candidate Hcandidate)) by lia.
    rewrite <- (Hprefix (oi * m + oj) ltac:(nia)).
    exact Houtanchor. }
  assert (Hcandidate_p :
      Znth (snd p) (Znth (fst p) candidate []) 0 = color).
  { rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate (fst p) (snd p)
      (square_tiling_rows__solver_final n m candidate Hcandidate)) by lia.
    rewrite <- Hfirst. exact Hcandfirst. }
  assert (Hp_not_output :
      ~ (oi <= fst p < oi + oside /\ oj <= snd p < oj + oside)).
  { intros Hpinside.
    assert (Houtpath : SameColorPath output_grid q p).
    { apply (proj2 (Houtcomponent p Hprow Hpcol)). exact Hpinside. }
    assert (Houtpcolor :
        Znth (snd p) (Znth (fst p) output_grid []) 0 = color).
    { transitivity (Znth (snd q) (Znth (fst q) output_grid []) 0).
      - exact (same_color_path_endpoint_color__solver_final output_grid q p
          Houtpath).
      - assert (Hqpath : SameColorPath output_grid q (oi, oj)).
        { apply (proj2 (Houtcomponent (oi, oj) ltac:(simpl; lia)
            ltac:(simpl; lia))). simpl. split; lia. }
        transitivity (Znth oj (Znth oi output_grid []) 0).
        + symmetry. exact (same_color_path_endpoint_color__solver_final
            output_grid q (oi, oj) Hqpath).
        + rewrite (rows_of_flat_Znth__solver_final n m output output_grid
            oi oj Houtrows) by lia. exact Houtanchor. }
    apply Houtfirst. rewrite Hfirst.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
      (fst p) (snd p) Houtrows) by lia. exact Houtpcolor. }
  destruct (Z_lt_ge_dec candidate_side oside) as [Hshort | Hnotshort].
  - assert (Hboundary_not_before :
        first <= oi * m + (oj + candidate_side)).
    { destruct (Z_le_gt_dec first (oi * m + (oj + candidate_side)));
        [lia | exfalso].
      pose proof (candidate_component_not_short_before_member__solver_final
        n m output candidate output_grid q oi oj oside candidate_side first
        Hn Hm Houtrows Hcandidate Hqrow Hqcol Hoi Hoj Hoside Hoibound
        Hojbound Hqoi Hqoj Hcandidate_side Hcandidate_i Hcandidate_j
        ltac:(lia) Hprefix Houtcomponent Hcandcomponent).
      lia. }
    destruct (classic (q = (fst p, snd p - 1))) as [Hleft | Hnotleft].
    + destruct p as [pr pc], q as [qr qc]; simpl in *.
      inversion Hleft; subst qr qc.
      exfalso. apply Hboundary_not_before. nia.
    + destruct (earlier_rectangle_crossing_geometry__solver_final m oi oj
        oside candidate_side first p q Hm (proj1 Hoj) Hojbound
        Hcandidate_side Hcandidate_j Hanchor Hfirst Hpcol Hqoi Hqoj Hadj
        Hnotleft Hboundary_not_before) as [Hpinside | Hboundary].
      * exfalso. apply Hp_not_output.
        destruct Hpinside as [Hpir Hpic]. split; lia.
      * assert (Hcandidate_strict_col : oj + candidate_side < m) by lia.
      assert (Hpcoords : fst p = oi /\ snd p = oj + candidate_side).
      { rewrite Hfirst in Hboundary.
        destruct p as [pr pc]; simpl in *.
        assert (pr = oi).
        { destruct (Z.eq_dec pr oi); [lia |].
          destruct (Z_lt_ge_dec pr oi); nia. }
        split; nia. }
      destruct Hpcoords as [Hpi Hpj].
      destruct p as [pr pc]; simpl in *; subst pr pc.
      set (inside := (oi, oj + candidate_side - 1)).
      assert (Hinside_row : 0 <= fst inside < n) by
        (unfold inside; simpl; lia).
      assert (Hinside_col : 0 <= snd inside < m) by
        (unfold inside; simpl; lia).
      assert (Houtside_component :
          ~ (oi <= oi < oi + candidate_side /\
             oj <= oj + candidate_side < oj + candidate_side)) by lia.
      assert (Hboundary_color :
          Znth (oj + candidate_side) (Znth oi candidate []) 0 <> color).
      { rewrite <- Hcandidate_anchor.
        pose proof (square_tiling_rows__solver_final n m candidate Hcandidate)
          as [Hcandlen [Hcandrows Hcandflat]].
        assert (Hcandrow0 : Zlength (Znth 0 candidate []) = m).
        { rewrite Forall_forall in Hcandrows.
          apply Hcandrows, Znth_In_range__solver_final.
          rewrite Hcandlen. lia. }
        eapply (exact_component_boundary_color__solver_final candidate
          (oi, oj) inside (oi, oj + candidate_side) oi oj candidate_side
          n m); try eassumption; try (unfold inside; simpl; lia). }
      contradiction.
  - assert (Hstrict : oside < candidate_side).
    { destruct (Z.eq_dec oside candidate_side) as [Heq | Hneq]; [|lia].
      subst candidate_side.
      assert (Hcandidate_q :
          Znth (snd q) (Znth (fst q) candidate []) 0 = color).
      { assert (Hqpath : SameColorPath candidate (oi, oj) q).
        { apply (proj2 (Hcandcomponent q Hqrow Hqcol)). split; lia. }
        transitivity (Znth oj (Znth oi candidate []) 0).
        - exact (same_color_path_endpoint_color__solver_final candidate
            (oi, oj) q Hqpath).
        - exact Hcandidate_anchor. }
      assert (Hpath : SameColorPath candidate (oi, oj) p).
      { assert (Hanchor_q : SameColorPath candidate (oi, oj) q).
        { apply (proj2 (Hcandcomponent q Hqrow Hqcol)). split; lia. }
        eapply same_color_path_append__solver_final with (x := q) (y := p).
        - exact Hanchor_q.
        - pose proof (square_tiling_rows__solver_final n m candidate
            Hcandidate) as [Hlen [? ?]]. rewrite Hlen. exact Hprow.
        - pose proof (square_tiling_rows__solver_final n m candidate
            Hcandidate) as [Hlen [Hrows ?]].
          rewrite Forall_forall in Hrows.
          assert (Hrow0 : Zlength (Znth 0 candidate []) = m).
          { apply Hrows, Znth_In_range__solver_final. rewrite Hlen. lia. }
          rewrite Hrow0. exact Hpcol.
        - simpl. rewrite Hcandidate_p, Hcandidate_anchor. reflexivity.
        - unfold AdjCell in Hadj |- *.
          replace (fst q - fst p) with (-(fst p - fst q)) by ring.
          replace (snd q - snd p) with (-(snd p - snd q)) by ring.
          rewrite !Z.abs_opp. exact Hadj. }
      apply (proj1 (Hcandcomponent p Hprow Hpcol)) in Hpath.
      assert (Houtpath : SameColorPath output_grid q p).
      { apply (proj2 (Houtcomponent p Hprow Hpcol)).
        destruct Hpath as [[? ?] [? ?]]. split; lia. }
      assert (Houtpcolor :
          Znth (snd p) (Znth (fst p) output_grid []) 0 =
          Znth (snd q) (Znth (fst q) output_grid []) 0).
      { exact (same_color_path_endpoint_color__solver_final output_grid q p
          Houtpath). }
      exfalso. apply Houtfirst.
      rewrite Hfirst.
      rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
        (fst p) (snd p) Houtrows) by lia.
      rewrite Houtpcolor.
      assert (Hqpath : SameColorPath output_grid q (oi, oj)).
      { apply (proj2 (Houtcomponent (oi, oj) ltac:(simpl; lia)
          ltac:(simpl; lia))). simpl. split; lia. }
      assert (Hqcolor :
          Znth (snd q) (Znth (fst q) output_grid []) 0 = color).
      { transitivity (Znth oj (Znth oi output_grid []) 0).
        - symmetry. exact (same_color_path_endpoint_color__solver_final
            output_grid q (oi, oj) Hqpath).
        - rewrite (rows_of_flat_Znth__solver_final n m output output_grid
            oi oj Houtrows) by lia. exact Houtanchor. }
      exact Hqcolor. }
    assert (Hcandidate_q :
        oi <= fst q < oi + candidate_side /\
        oj <= snd q < oj + candidate_side) by (split; lia).
    assert (Hanchor_q : SameColorPath candidate (oi, oj) q).
    { apply (proj2 (Hcandcomponent q Hqrow Hqcol)). exact Hcandidate_q. }
    assert (Hcandidate_q_color :
        Znth (snd q) (Znth (fst q) candidate []) 0 = color).
    { transitivity (Znth oj (Znth oi candidate []) 0).
      - exact (same_color_path_endpoint_color__solver_final candidate
          (oi, oj) q Hanchor_q).
      - exact Hcandidate_anchor. }
    assert (Hanchor_p : SameColorPath candidate (oi, oj) p).
    { eapply same_color_path_append__solver_final with (x := q) (y := p).
      - exact Hanchor_q.
      - pose proof (square_tiling_rows__solver_final n m candidate Hcandidate)
          as [Hlen [? ?]]. rewrite Hlen. exact Hprow.
      - pose proof (square_tiling_rows__solver_final n m candidate Hcandidate)
          as [Hlen [Hrows ?]]. rewrite Forall_forall in Hrows.
        assert (Hrow0 : Zlength (Znth 0 candidate []) = m).
        { apply Hrows, Znth_In_range__solver_final. rewrite Hlen. lia. }
        rewrite Hrow0. exact Hpcol.
      - transitivity color; [exact Hcandidate_p | symmetry; exact Hcandidate_anchor].
      - unfold AdjCell in Hadj |- *.
        replace (fst q - fst p) with (-(fst p - fst q)) by ring.
        replace (snd q - snd p) with (-(snd p - snd q)) by ring.
        rewrite !Z.abs_opp. exact Hadj. }
    assert (Hp_candidate := proj1 (Hcandcomponent p Hprow Hpcol) Hanchor_p).
    exists candidate_side.
    exact (conj Hcandidate_side (conj Hcandidate_i
      (conj Hcandidate_j (conj Hstrict
        (conj Hcandcomponent Hp_candidate))))).
Qed.
Lemma trace_existing_component_origin_before__solver_final :
  forall n m start prior next output output_grid p,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m start prior ->
    GreedyPlacementTrace n m next output ->
    start <= next ->
    RowsOfFlat n m output output_grid ->
    0 <= fst p < n -> 0 <= snd p < m ->
    Znth (fst p * m + snd p) prior 0 <> 0 ->
    exists anchor before painted i j color side,
      anchor = i * m + j /\
      anchor < start /\
      GreedyPlacementTrace n m anchor before /\
      SettledSquareState before n m i j color side /\
      PaintRectanglePrefix before painted m i j side color (side * side) /\
      0 <= i < n /\ 0 <= j < m /\
      i <= fst p < i + side /\ j <= snd p < j + side /\
      Znth (snd p) (Znth (fst p) output_grid []) 0 = color /\
      (forall q,
        0 <= fst q < n -> 0 <= snd q < m ->
        (SameColorPath output_grid p q <->
         i <= fst q < i + side /\ j <= snd q < j + side)).
Proof.
  intros n m start prior next output output_grid p Hn Hm Hprior Houtput
    Hstart Hrows Hprow Hpcol Hprior_nonzero.
  assert (Hindex : 0 <= fst p * m + snd p < n * m) by nia.
  assert (Houtput_nonzero : Znth (fst p * m + snd p) output 0 <> 0).
  { rewrite (greedy_trace_prefix_persistence__solver_final n m start next
      prior output Hn Hm Hstart Hprior Houtput (fst p * m + snd p) Hindex
      Hprior_nonzero). exact Hprior_nonzero. }
  assert (Hgrid_nonzero :
      Znth (snd p) (Znth (fst p) output_grid []) 0 <> 0).
  { rewrite (rows_of_flat_Znth__solver_final n m output output_grid
      (fst p) (snd p) Hrows Hprow Hpcol). exact Houtput_nonzero. }
  destruct (trace_colored_component_origin__solver_final n m next output
    output_grid p Hn Hm Houtput Hrows Hprow Hpcol Hgrid_nonzero) as
    [anchor [before [painted [i [j [color [side Horigin]]]]]]].
  destruct Horigin as [Hanchor [Hanchor_next [Htrace [Hsettled [Hpaint
    [Hi [Hj [Hpi [Hpj [Hpcolor [Hcomponent Hpersist]]]]]]]]]]].
  assert (Hanchor_start : anchor < start).
  { destruct (Z_lt_ge_dec anchor start); [lia | exfalso].
    assert (Hstart_anchor : start <= anchor) by lia.
    assert (Hbefore_nonzero :
        Znth (fst p * m + snd p) before 0 <> 0).
    { rewrite (greedy_trace_prefix_persistence__solver_final n m start anchor
        prior before Hn Hm Hstart_anchor Hprior Htrace
        (fst p * m + snd p) Hindex Hprior_nonzero).
      exact Hprior_nonzero. }
    destruct Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
    destruct Hplace as [Hside [Hibound [Hjbound [Hempty Hboundaries]]]].
    specialize (Hempty (fst p) (snd p) Hpi Hpj).
    apply Hbefore_nonzero. exact Hempty. }
  exists anchor, before, painted, i, j, color, side.
  tauto.
Qed.
Lemma conflict_zero_has_painted_neighbour__solver_final :
  forall flat n m i j color,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    65 <= color ->
    NeighborConflict flat n m i j color 0 ->
    exists q,
      0 <= fst q < n /\ 0 <= snd q < m /\
      AdjCell (i, j) q /\
      Znth (fst q * m + snd q) flat 0 = color.
Proof.
  intros flat n m i j color Hn Hm Hi Hj Hcolor Hconflict.
  unfold NeighborConflict in Hconflict.
  destruct Hconflict as
      [[Hitop Htop] |
       [[Hibottom Hbottom] |
        [[Hjright Hright] |
         [[Hjleft Hleft] | [Hjzero Hbad]]]]].
  - exists (i - 1, j). simpl. repeat split; try lia.
    unfold AdjCell. simpl.
    replace (i - (i - 1)) with 1 by lia.
    replace (j - j) with 0 by lia. reflexivity.
  - exists (i + 1, j). simpl. repeat split; try lia.
    unfold AdjCell. simpl.
    replace (i - (i + 1)) with (-1) by lia.
    replace (j - j) with 0 by lia. reflexivity.
  - exists (i, j + 1). simpl. repeat split; try lia.
    + unfold AdjCell. simpl.
      replace (i - i) with 0 by lia.
      replace (j - (j + 1)) with (-1) by lia. reflexivity.
    + replace (i * m + (j + 1)) with (i * m + j + 1) by lia.
      exact Hright.
  - destruct (Z.eq_dec 0 0) as [_ | Habsurd]; [|contradiction].
    exists (i, j - 1). simpl. repeat split; try lia.
    + unfold AdjCell. simpl.
      replace (i - i) with 0 by lia.
      replace (j - (j - 1)) with 1 by lia. reflexivity.
    + replace (i * m + (j - 1)) with (i * m + j - 1) by lia.
      exact Hleft.
  - lia.
Qed.
Lemma lower_conflict_has_crossing_component__solver_final :
  forall n m start prior next output output_grid candidate first p lower,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m start prior ->
    GreedyPlacementTrace n m next output ->
    start <= next ->
    start <= first ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= fst p < n -> 0 <= snd p < m ->
    first = fst p * m + snd p ->
    65 <= lower ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    Znth first (Flatten candidate) 0 = lower ->
    Znth first output 0 <> lower ->
    (NeighborConflict prior n m (fst p) (snd p) lower 0 \/
     exists override,
       lower < override /\
       NeighborConflict prior n m (fst p) (snd p) lower override) ->
    exists q earlier before painted oi oj side candidate_side,
      earlier = oi * m + oj /\
      earlier < start /\
      GreedyPlacementTrace n m earlier before /\
      SettledSquareState before n m oi oj lower side /\
      PaintRectanglePrefix before painted m oi oj side lower (side * side) /\
      0 <= oi < n /\ 0 <= oj < m /\
      oi <= fst q < oi + side /\ oj <= snd q < oj + side /\
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower /\
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         oi <= fst x < oi + side /\ oj <= snd x < oj + side)) /\
      1 <= candidate_side /\
      oi + candidate_side <= n /\ oj + candidate_side <= m /\
      side < candidate_side /\
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (oi, oj) x <->
         oi <= fst x < oi + candidate_side /\
         oj <= snd x < oj + candidate_side)) /\
      oi <= fst p < oi + candidate_side /\
      oj <= snd p < oj + candidate_side.
Proof.
  intros n m start prior next output output_grid candidate first p lower
    Hn Hm Hprior Houtput Hstart Hstart_first Hrows Hcandidate Hprow Hpcol Hfirst
    Hlower Hprefix Hcandfirst Houtfirst Hconflict.
  assert (Hneighbor : exists q,
      0 <= fst q < n /\ 0 <= snd q < m /\
      AdjCell (fst p, snd p) q /\
      Znth (fst q * m + snd q) prior 0 = lower).
  { destruct Hconflict as [Hzero | [override [Hlower_override Hoverride]]].
    - exact (conflict_zero_has_painted_neighbour__solver_final prior n m
        (fst p) (snd p) lower Hn Hm Hprow Hpcol Hlower Hzero).
    - destruct (smaller_conflict_has_painted_neighbour__solver_final prior n m
        (fst p) (snd p) lower override Hn Hm Hprow Hpcol ltac:(lia)
        Hlower_override Hoverride) as
        [q [Hqrow [Hqcol [Hadj [Hnotleft Hqprior]]]]].
      exists q. tauto. }
  destruct Hneighbor as [q [Hqrow [Hqcol [Hadj Hqprior]]]].
  assert (Hqindex : 0 <= fst q * m + snd q < n * m) by nia.
  assert (Hqprior_nonzero : Znth (fst q * m + snd q) prior 0 <> 0) by lia.
  destruct (trace_existing_component_origin_before__solver_final n m start
    prior next output output_grid q Hn Hm Hprior Houtput Hstart Hrows
    Hqrow Hqcol Hqprior_nonzero) as
    [earlier [before [painted [oi [oj [found [side Horigin]]]]]]].
  destruct Horigin as [Hearlier [Hearlier_start [Htrace [Hsettled [Hpaint
    [Hoi [Hoj [Hqoi [Hqoj [Hqfound Hcomponent]]]]]]]]]].
  assert (Hfound : found = lower).
  { assert (Hqoutput : Znth (fst q * m + snd q) output 0 = lower).
    { rewrite (greedy_trace_prefix_persistence__solver_final n m start next
        prior output Hn Hm Hstart Hprior Houtput (fst q * m + snd q)
        Hqindex Hqprior_nonzero). exact Hqprior. }
    rewrite (rows_of_flat_Znth__solver_final n m output output_grid
      (fst q) (snd q) Hrows) in Hqfound by lia.
    congruence. }
  assert (Hqcolor :
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower) by congruence.
  subst found.
  assert (Houtanchor : Znth (oi * m + oj) output 0 = lower).
  { rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid oi oj
      Hrows) by lia.
    assert (Hqpath : SameColorPath output_grid q (oi, oj)).
    { apply (proj2 (Hcomponent (oi, oj) ltac:(simpl; lia)
        ltac:(simpl; lia))). simpl. split; lia. }
    transitivity (Znth (snd q) (Znth (fst q) output_grid []) 0).
    - exact (same_color_path_endpoint_color__solver_final output_grid q
        (oi, oj) Hqpath).
    - exact Hqcolor. }
  destruct (conflict_component_crosses_candidate__solver_final n m output
    output_grid candidate first p q oi oj lower side Hn Hm Hrows Hcandidate
    Hprow Hpcol Hqrow Hqcol Hfirst Hoi Hoj
    ltac:(destruct Hsettled as [[? [Hplace ?]] ?]; destruct Hplace; lia)
    ltac:(destruct Hsettled as [[? [Hplace ?]] ?]; destruct Hplace; lia)
    ltac:(destruct Hsettled as [[? [Hplace ?]] ?]; destruct Hplace; lia)
    Hqoi Hqoj ltac:(lia) Hprefix Houtanchor Hcandfirst Houtfirst Hadj
    Hcomponent) as
    [candidate_side [Hcandidate_side [Hcandidate_i [Hcandidate_j
      [Hcross Hcandidate_rest]]]]].
  destruct Hcandidate_rest as
    [Hcandcomponent [Hp_candidate_row Hp_candidate_col]].
  rewrite Hqcolor in Hsettled, Hpaint.
  exists q, earlier, before, painted, oi, oj, side, candidate_side.
  repeat match goal with
  | |- _ /\ _ => split
  end; try assumption; try exact Hqcolor; try lia.
Qed.
Lemma base_exchange_from_extend_ih__solver_final :
  forall n m next output output_grid candidate first before i j color side,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= first < next ->
    first = i * m + j ->
    0 <= i < n -> 0 <= j < m ->
    GreedyPlacementTrace n m first before ->
    SettledSquareState before n m i j color side ->
    Znth first output 0 = color ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall lower target q earlier origin_before painted oi oj side candidate_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      earlier = oi * m + oj ->
      earlier < first ->
      GreedyPlacementTrace n m earlier origin_before ->
      SettledSquareState origin_before n m oi oj lower side ->
      PaintRectanglePrefix origin_before painted m oi oj side lower
        (side * side) ->
      0 <= oi < n -> 0 <= oj < m ->
      oi <= fst q < oi + side -> oj <= snd q < oj + side ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         oi <= fst x < oi + side /\ oj <= snd x < oj + side)) ->
      1 <= candidate_side ->
      oi + candidate_side <= n -> oj + candidate_side <= m ->
      side < candidate_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (oi, oj) x <->
         oi <= fst x < oi + candidate_side /\
         oj <= snd x < oj + candidate_side)) ->
      oi <= fst target < oi + candidate_side ->
      oj <= snd target < oj + candidate_side ->
      Znth first output 0 <= lower) ->
    Znth first output 0 <= Znth first (Flatten candidate) 0.
Proof.
  intros n m next output output_grid candidate first before i j color side
    Hn Hm Houtput Hrows Hcandidate Hfirst_range Hfirst Hi Hj Hbefore
    Hsettled Houtfirst Hprefix Hextend.
  set (lower := Znth first (Flatten candidate) 0).
  assert (Hlower_range : 65 <= lower <= 90).
  { unfold lower. apply square_tiling_flat_color__solver_final with
      (n := n) (m := m); [exact Hcandidate | nia]. }
  destruct (Z_le_gt_dec color lower) as [Hle | Hlt].
  - rewrite Houtfirst. exact Hle.
  - assert (Hout_ne : Znth first output 0 <> lower) by
      (rewrite Houtfirst; lia).
    destruct Hsettled as [[Hleast Hgreedy] Hstop].
    destruct Hleast as [[Hcolor_range Hcolor_legal] Hminimal].
    assert (Hconflict : NeighborConflict before n m i j lower 0).
    { specialize (Hminimal lower ltac:(lia)).
      unfold LegalColor in Hminimal. tauto. }
    destruct (lower_conflict_has_crossing_component__solver_final n m first
      before next output output_grid candidate first (i, j) lower Hn Hm
      Hbefore Houtput ltac:(lia) ltac:(lia) Hrows Hcandidate
      ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; exact Hfirst)
      (proj1 Hlower_range) Hprefix eq_refl Hout_ne
      ltac:(simpl; left; exact Hconflict)) as
      [q [earlier [origin_before [painted [oi [oj [oside
        [candidate_side Hcross]]]]]]]].
    destruct Hcross as [Hearlier [Hearlier_first [Htrace [Hsettled0 [Hpaint
      [Hoi [Hoj [Hqoi [Hqoj [Hqcolor [Hcomponent [Hcandidate_side
        [Hcandidate_i [Hcandidate_j [Hside_lt Hcandidate_rest]]]]]]]]]]]]]]].
    destruct Hcandidate_rest as
      [Hcandcomponent [Hp_candidate_row Hp_candidate_col]].
    eapply (Hextend lower (i, j) q earlier origin_before painted oi oj oside
      candidate_side); try eassumption; try reflexivity; simpl; lia.
Qed.
Lemma shrink_exchange_from_extend_ih__solver_final :
  forall n m anchor next output output_grid candidate first before
      i j color side candidate_side,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    anchor = i * m + j ->
    0 <= anchor < next ->
    0 <= i < n -> 0 <= j < m ->
    GreedyPlacementTrace n m anchor before ->
    SettledSquareState before n m i j color side ->
    1 <= candidate_side < side ->
    first = i * m + (j + candidate_side) ->
    Znth first output 0 = color ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall lower target q earlier origin_before painted oi oj oside other_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      earlier = oi * m + oj ->
      earlier < anchor ->
      GreedyPlacementTrace n m earlier origin_before ->
      SettledSquareState origin_before n m oi oj lower oside ->
      PaintRectanglePrefix origin_before painted m oi oj oside lower
        (oside * oside) ->
      0 <= oi < n -> 0 <= oj < m ->
      oi <= fst q < oi + oside -> oj <= snd q < oj + oside ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         oi <= fst x < oi + oside /\ oj <= snd x < oj + oside)) ->
      1 <= other_side ->
      oi + other_side <= n -> oj + other_side <= m ->
      oside < other_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (oi, oj) x <->
         oi <= fst x < oi + other_side /\
         oj <= snd x < oj + other_side)) ->
      oi <= fst target < oi + other_side ->
      oj <= snd target < oj + other_side ->
      Znth first output 0 <= lower) ->
    Znth first output 0 <= Znth first (Flatten candidate) 0.
Proof.
  intros n m anchor next output output_grid candidate first before
    i j color side candidate_side Hn Hm Houtput Hrows Hcandidate Hanchor
    Hanchor_range Hi Hj Hbefore Hsettled Hcandidate_short Hfirst Houtfirst
    Hprefix Hextend.
  set (lower := Znth first (Flatten candidate) 0).
  assert (Hfirst_range : 0 <= first < n * m).
  { destruct Hsettled as [[? [Hplace ?]] ?]. destruct Hplace. nia. }
  assert (Hlower_range : 65 <= lower <= 90).
  { unfold lower. apply square_tiling_flat_color__solver_final with
      (n := n) (m := m); assumption. }
  destruct (Z_le_gt_dec color lower) as [Hle | Hlt].
  - rewrite Houtfirst. exact Hle.
  - assert (Hout_ne : Znth first output 0 <> lower) by
      (rewrite Houtfirst; lia).
    destruct Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
    destruct (Hprevious candidate_side Hcandidate_short) as
      [Hextend_place [fallback [Hfallback Hcolor_fallback]]].
    destruct Hfallback as [[Hfallback_range Hfallback_legal] Hminimal].
    assert (Hconflict :
        NeighborConflict before n m i (j + candidate_side) lower color).
    { specialize (Hminimal lower ltac:(lia)).
      unfold LegalColor in Hminimal. tauto. }
    destruct (lower_conflict_has_crossing_component__solver_final n m anchor
      before next output output_grid candidate first
      (i, j + candidate_side) lower Hn Hm Hbefore Houtput ltac:(lia)
      ltac:(rewrite Hanchor, Hfirst; nia) Hrows Hcandidate
      ltac:(simpl; lia) ltac:(simpl; destruct Hplace; nia)
      ltac:(simpl; exact Hfirst) (proj1 Hlower_range) Hprefix eq_refl Hout_ne
      ltac:(simpl; right; exists color; split; [lia | exact Hconflict])) as
      [q [earlier [origin_before [painted [oi [oj [oside
        [other_side Hcross]]]]]]]].
    destruct Hcross as [Hearlier [Hearlier_anchor [Htrace [Hsettled0 [Hpaint
      [Hoi [Hoj [Hqoi [Hqoj [Hqcolor [Hcomponent [Hother_side
        [Hother_i [Hother_j [Hside_lt Hcandidate_rest]]]]]]]]]]]]]]].
    destruct Hcandidate_rest as
      [Hcandcomponent [Hp_candidate_row Hp_candidate_col]].
    eapply (Hextend lower (i, j + candidate_side) q earlier origin_before
      painted oi oj oside other_side); try eassumption; try reflexivity;
      simpl; lia.
Qed.
Lemma extend_first_is_frontier__solver_final :
  forall n m output output_grid candidate first p i j color side candidate_side,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= i < n -> 0 <= j < m ->
    1 <= side -> i + side <= n -> j + side <= m ->
    side < candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    0 <= fst p < n -> 0 <= snd p < m ->
    first = fst p * m + snd p ->
    i <= fst p < i + candidate_side ->
    j <= snd p < j + candidate_side ->
    i * m + j < first ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    Znth (i * m + j) output 0 = color ->
    Znth first (Flatten candidate) 0 = color ->
    Znth first output 0 <> color ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath output_grid (i, j) x <->
       i <= fst x < i + side /\ j <= snd x < j + side)) ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath candidate (i, j) x <->
       i <= fst x < i + candidate_side /\
       j <= snd x < j + candidate_side)) ->
    first = i * m + (j + side).
Proof.
  intros n m output output_grid candidate first p i j color side
    candidate_side Hn Hm Houtrows Hcandidate Hi Hj Hside Hibound Hjbound
    Hside_lt Hcandidate_i Hcandidate_j Hprow Hpcol Hfirst Hp_i Hp_j
    Hanchor Hprefix Houtanchor Hcandfirst Houtfirst Houtcomponent
    Hcandcomponent.
  assert (Hp_not_output :
      ~ (i <= fst p < i + side /\ j <= snd p < j + side)).
  { intros Hpinside.
    assert (Hpath : SameColorPath output_grid (i, j) p).
    { apply (proj2 (Houtcomponent p Hprow Hpcol)). exact Hpinside. }
    apply Houtfirst. rewrite Hfirst.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
      (fst p) (snd p) Houtrows) by lia.
    transitivity (Znth j (Znth i output_grid []) 0).
    - exact (same_color_path_endpoint_color__solver_final output_grid
        (i, j) p Hpath).
    - rewrite (rows_of_flat_Znth__solver_final n m output output_grid i j
        Houtrows) by lia. exact Houtanchor. }
  assert (Hfrontier_le : i * m + (j + side) <= first).
  { rewrite Hfirst. destruct p as [pr pc]; simpl in *.
    destruct (Z.eq_dec pr i) as [-> | Hneq].
    - assert (j + side <= pc).
      { destruct (Z_lt_ge_dec pc (j + side)); [exfalso | lia].
        apply Hp_not_output. split; lia. }
      nia.
    - assert (i < pr) by lia. nia. }
  assert (Hfirst_le : first <= i * m + (j + side)).
  { destruct (Z_le_gt_dec first (i * m + (j + side))); [lia | exfalso].
    assert (Hfrontier_index : 0 <= i * m + (j + side) < first) by nia.
    pose proof (Hprefix (i * m + (j + side)) Hfrontier_index) as Heq.
    assert (Hout_frontier : Znth (i * m + (j + side)) output 0 <> color).
    { rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
        i (j + side) Houtrows) by lia.
      rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid
        i j Houtrows) in Houtanchor by lia.
      rewrite <- Houtanchor.
      set (inside := (i, j + side - 1)).
      pose proof Houtrows as [Houtlen [Houtrow_lengths Houtflat]].
      assert (Houtrow0 : Zlength (Znth 0 output_grid []) = m).
      { rewrite Forall_forall in Houtrow_lengths.
        apply Houtrow_lengths, Znth_In_range__solver_final.
        rewrite Houtlen. lia. }
      eapply (exact_component_boundary_color__solver_final output_grid
        (i, j) inside (i, j + side) i j side n m);
        try (unfold inside; simpl; lia); try eassumption.
      unfold AdjCell, inside. simpl.
      replace (i - i) with 0 by lia.
      replace (j + side - 1 - (j + side)) with (-1) by lia.
      reflexivity. }
    assert (Hcand_frontier :
        Znth (i * m + (j + side)) (Flatten candidate) 0 = color).
    { rewrite <- (rows_of_flat_Znth__solver_final n m (Flatten candidate)
        candidate i (j + side)
        (square_tiling_rows__solver_final n m candidate Hcandidate)) by lia.
      assert (Hpath : SameColorPath candidate (i, j) (i, j + side)).
      { apply (proj2 (Hcandcomponent (i, j + side) ltac:(simpl; lia)
          ltac:(simpl; lia))). simpl. split; lia. }
      transitivity (Znth j (Znth i candidate []) 0).
      - exact (same_color_path_endpoint_color__solver_final candidate
          (i, j) (i, j + side) Hpath).
      - rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
          candidate i j
          (square_tiling_rows__solver_final n m candidate Hcandidate)) by lia.
        rewrite <- (Hprefix (i * m + j) ltac:(nia)). exact Houtanchor. }
    apply Hout_frontier. rewrite Heq. exact Hcand_frontier. }
  lia.
Qed.
Lemma trace_skip_interval__solver_final :
  forall n m start finish flat,
    GreedyPlacementTrace n m start flat ->
    0 <= start -> start <= finish -> finish <= n * m ->
    (forall k, start <= k < finish -> 65 <= Znth k flat 0 <= 90) ->
    GreedyPlacementTrace n m finish flat.
Proof.
  intros n m start finish flat Htrace Hstart Hle Hfinish Hcolored.
  assert (Hstrong : forall distance,
      0 <= distance ->
      forall (left right : Z) (state : list Z),
        distance = right - left ->
        GreedyPlacementTrace n m left state ->
        0 <= left -> left <= right -> right <= n * m ->
        (forall k, left <= k < right ->
          65 <= Znth k state 0 <= 90) ->
        GreedyPlacementTrace n m right state).
  { refine (nonnegative_anchor_strong_induction__solver_final
      (fun distance =>
        forall (left right : Z) (state : list Z),
          distance = right - left ->
          GreedyPlacementTrace n m left state ->
          0 <= left -> left <= right -> right <= n * m ->
          (forall k, left <= k < right ->
            65 <= Znth k state 0 <= 90) ->
          GreedyPlacementTrace n m right state) _).
    intros distance Hdistance IH left right state Hdistance_eq Hleft
      Hleft0 Hleft_right Hright Hrange.
    destruct (Z.eq_dec left right) as [-> | Hneq].
    - exact Hleft.
    - assert (Hlt : left < right) by lia.
      assert (Hstep : GreedyPlacementTrace n m (left + 1) state).
      { refine (@GreedyTrace_skip n m left state Hleft _ _).
        - split; lia.
        - apply Hrange. lia. }
      eapply (IH (distance - 1) ltac:(lia) (left + 1) right state);
        try eassumption; try lia.
      intros k Hk. apply Hrange. lia. }
  eapply (Hstrong (finish - start)); eauto; lia.
Qed.
Lemma placed_trace_at_frontier__solver_final :
  forall n m anchor before painted i j color side,
    1 <= n -> 1 <= m ->
    anchor = i * m + j ->
    GreedyPlacementTrace n m anchor before ->
    0 <= i < n -> 0 <= j < m ->
    Znth anchor before 0 = 0 ->
    SettledSquareState before n m i j color side ->
    PaintRectanglePrefix before painted m i j side color (side * side) ->
    GreedyPlacementTrace n m (i * m + (j + side)) painted.
Proof.
  intros n m anchor before painted i j color side Hn Hm Hanchor Htrace
    Hi Hj Hzero Hsettled Hpaint.
  assert (Hplaced : GreedyPlacementTrace n m (anchor + 1) painted).
  { eapply (@GreedyTrace_place n m anchor before painted i j color side);
      eauto. }
  destruct Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
  destruct Hleast as [[Hcolor Hlegal] Hminimal].
  destruct Hplace as [Hside [Hibound [Hjbound Hrest]]].
  refine (trace_skip_interval__solver_final n m (anchor + 1)
    (i * m + (j + side)) painted Hplaced _ _ _ _).
  - lia.
  - rewrite Hanchor. lia.
  - nia.
  - intros k Hk.
  assert (Hk_before : 0 <= k < Zlength before).
  { pose proof (trace_bounds_and_canonical__solver_final n m anchor before
      Hn Hm Htrace) as [Hbounds [Hlength Hcanonical]].
    rewrite Hlength. nia. }
    destruct Hpaint as [Hpaint_len Hpaint_cells].
    specialize (Hpaint_cells k Hk_before).
    destruct Hpaint_cells as [[Hmember Hpainted] | [Houtside Hsame]].
    + rewrite Hpainted. exact Hcolor.
    + exfalso. apply (Houtside (k - anchor)).
      * split; [lia | nia].
      * rewrite Hanchor.
        assert ((k - (i * m + j)) / side = 0).
        { apply Z.div_small; lia. }
        assert ((k - (i * m + j)) mod side = k - (i * m + j)).
        { apply Z.mod_small; lia. }
        lia.
Qed.
Lemma least_legal_frontier_equiv__solver_final :
  forall before painted n m i j side color chosen,
    1 <= n -> 1 <= m ->
    0 <= i < n -> 0 <= j < m ->
    65 <= color ->
    j + side < m ->
    Zlength before = n * m ->
    CanPlace before n m i j side color ->
    PaintRectanglePrefix before painted m i j side color (side * side) ->
    (LeastLegalColor painted n m i (j + side) 0 chosen <->
     LeastLegalColor before n m i (j + side) color chosen).
Proof.
  intros before painted n m i j side color chosen Hn Hm Hi Hj Hcolor
    Hfrontier Hlen Hplace Hpaint.
  assert (Hconflict : forall tested,
      NeighborConflict painted n m i (j + side) tested 0 <->
      NeighborConflict before n m i (j + side) tested color).
  { intros tested. eapply paint_frontier_conflict_equiv__solver_final; eauto. }
  unfold LeastLegalColor, LegalColor.
  split; intros [[Hrange Hlegal] Hminimal].
  - split.
    + split; [exact Hrange |]. intros Hbad. apply Hlegal.
      apply (proj2 (Hconflict chosen)). exact Hbad.
    + intros d Hd [Hdrange Hdlegal]. apply (Hminimal d Hd).
      split; [exact Hdrange |]. intros Hbad. apply Hdlegal.
      apply (proj1 (Hconflict d)). exact Hbad.
  - split.
    + split; [exact Hrange |]. intros Hbad. apply Hlegal.
      apply (proj1 (Hconflict chosen)). exact Hbad.
    + intros d Hd [Hdrange Hdlegal]. apply (Hminimal d Hd).
      split; [exact Hdrange |]. intros Hbad. apply Hdlegal.
      apply (proj2 (Hconflict d)). exact Hbad.
Qed.
Lemma frontier_zero_is_new_origin__solver_final :
  forall n m anchor next before painted output output_grid i j color side,
    1 <= n -> 1 <= m ->
    anchor = i * m + j ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    i * m + (j + side) < next ->
    RowsOfFlat n m output output_grid ->
    0 <= i < n -> 0 <= j < m ->
    j + side < m ->
    Znth anchor before 0 = 0 ->
    SettledSquareState before n m i j color side ->
    PaintRectanglePrefix before painted m i j side color (side * side) ->
    Znth (i * m + (j + side)) before 0 = 0 ->
    Znth (i * m + (j + side)) output 0 <> 0 ->
    exists found found_side found_after,
      SettledSquareState painted n m i (j + side) found found_side /\
      PaintRectanglePrefix painted found_after m i (j + side)
        found_side found (found_side * found_side) /\
      Znth (i * m + (j + side)) output 0 = found.
Proof.
  intros n m anchor next before painted output output_grid i j color side
    Hn Hm Hanchor Hbefore Houtput Hfrontier_next Hrows Hi Hj Hfrontier
    Hzero Hsettled Hpaint Hbefore_frontier Houtput_frontier.
  destruct Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
  assert (Hsettled_full : SettledSquareState before n m i j color side).
  { unfold SettledSquareState, ChosenSquareState, GreedySideState. tauto. }
  destruct Hplace as [Hside [Hibound [Hjbound Hplace_rest]]].
  assert (Hfrontier_col : 0 <= j + side < m) by nia.
  assert (Hpainted_frontier :
      Znth (i * m + (j + side)) painted 0 = 0).
  { rewrite (proj2 (paint_rectangle_coordinate__solver_final before painted
      n m i j side color i (j + side) Hm Hi Hj Hi Hfrontier_col
      ltac:(unfold CanPlace; tauto)
      ltac:(pose proof (trace_bounds_and_canonical__solver_final n m anchor
        before Hn Hm Hbefore) as [? [Hlen ?]]; exact Hlen) Hpaint)).
    - exact Hbefore_frontier.
    - intros [Hr Hc]. lia. }
  assert (Hfrontier_trace :
      GreedyPlacementTrace n m (i * m + (j + side)) painted).
  { eapply placed_trace_at_frontier__solver_final; eauto. }
  assert (Hgrid_frontier :
      Znth (j + side) (Znth i output_grid []) 0 <> 0).
  { rewrite (rows_of_flat_Znth__solver_final n m output output_grid i
      (j + side) Hrows Hi Hfrontier_col). exact Houtput_frontier. }
  destruct (trace_colored_component_origin__solver_final n m next output
    output_grid (i, j + side) Hn Hm Houtput Hrows Hi Hfrontier_col
    Hgrid_frontier) as
    [found_anchor [found_before [found_after [fi [fj [found
      [found_side Horigin]]]]]]].
  destruct Horigin as [Hfound_anchor [Hfound_next [Hfound_trace
    [Hfound_settled [Hfound_paint [Hfi [Hfj [Hpi [Hpj [Hpcolor
      [Hcomponent Hpersist]]]]]]]]]]].
  assert (Hfound_le : found_anchor <= i * m + (j + side)).
  { pose proof Hfound_settled as
      [[Hfound_least0 [Hfound_place0 Hfound_prev0]] Hfound_stop0].
    destruct Hfound_place0 as
      [Hfound_side0 [Hfound_i0 [Hfound_j0 Hfound_rest0]]].
    rewrite Hfound_anchor.
    eapply square_anchor_le_member__solver_final; eauto; lia. }
  assert (Hfound_ge : i * m + (j + side) <= found_anchor).
  { destruct (Z_le_gt_dec (i * m + (j + side)) found_anchor); [lia |].
    assert (Hfound_lt : found_anchor < i * m + (j + side)) by lia.
    destruct Hfound_settled as [[Hfound_least [Hfound_place Hfound_prev]]
      Hfound_stop].
    assert (Hfound_settled_full :
        SettledSquareState found_before n m fi fj found found_side).
    { unfold SettledSquareState, ChosenSquareState, GreedySideState. tauto. }
    destruct Hfound_place as
      [Hfound_side [Hfound_i [Hfound_j Hfound_rest]]].
    assert (Hfound_len : Zlength found_before = n * m).
    { pose proof (trace_bounds_and_canonical__solver_final n m found_anchor
        found_before Hn Hm Hfound_trace) as [? [Hlen ?]]. exact Hlen. }
    assert (Hfound_after_cell :
        Znth (i * m + (j + side)) found_after 0 = found).
    { apply (proj1 (paint_rectangle_coordinate__solver_final found_before
        found_after n m fi fj found_side found i (j + side) Hm Hfi Hfj Hi
        Hfrontier_col ltac:(unfold CanPlace; tauto) Hfound_len
        Hfound_paint)). split; assumption. }
    assert (Hfound_after_trace :
        GreedyPlacementTrace n m (found_anchor + 1) found_after).
    { assert (Hfound_zero : Znth found_anchor found_before 0 = 0).
      { rewrite Hfound_anchor.
        destruct Hfound_rest as [Hempty Hboundaries].
        apply Hempty; lia. }
      exact (@GreedyTrace_place n m found_anchor found_before found_after fi
        fj found found_side Hfound_trace Hfound_anchor Hfi Hfj Hfound_zero
        Hfound_settled_full Hfound_paint). }
    assert (Hpersist_to_frontier :
        Znth (i * m + (j + side)) painted 0 = found).
    { rewrite (greedy_trace_prefix_persistence__solver_final n m
        (found_anchor + 1) (i * m + (j + side)) found_after painted Hn Hm
        ltac:(lia) Hfound_after_trace Hfrontier_trace
        (i * m + (j + side)) ltac:(nia) ltac:(rewrite Hfound_after_cell;
          destruct Hfound_least as [[Hrange ?] ?]; lia)).
      exact Hfound_after_cell. }
    rewrite Hpainted_frontier in Hpersist_to_frontier.
    destruct Hfound_least as [[Hrange ?] ?]. lia. }
  assert (Hfound_eq : found_anchor = i * m + (j + side)) by lia.
  assert (Hbefore_eq : found_before = painted).
  { assert (Hfound_trace_frontier :
        GreedyPlacementTrace n m (i * m + (j + side)) found_before).
    { rewrite <- Hfound_eq. exact Hfound_trace. }
    exact (greedy_trace_state_unique__solver_final n m
      (i * m + (j + side)) found_before painted Hn Hm
      Hfound_trace_frontier Hfrontier_trace). }
  subst found_before.
  assert (Hfi_eq : fi = i /\ fj = j + side).
  { assert (Hindex_eq : fi * m + fj = i * m + (j + side)) by lia.
    assert (Hrow_eq : fi = i).
    { destruct (Z.lt_trichotomy fi i) as [Hlt | [Heq | Hgt]];
        [exfalso; nia | exact Heq | exfalso; nia]. }
    split; [exact Hrow_eq |]. subst fi. lia. }
  destruct Hfi_eq as [-> ->].
  exists found, found_side, found_after.
  split; [exact Hfound_settled |]. split; [exact Hfound_paint |].
  rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid i
    (j + side) Hrows Hi Hfrontier_col).
  exact Hpcolor.
Qed.
Lemma frontier_zero_fallback_bound__solver_final :
  forall n m anchor next before painted output output_grid i j color side
      fallback,
    1 <= n -> 1 <= m ->
    anchor = i * m + j ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    i * m + (j + side) < next ->
    RowsOfFlat n m output output_grid ->
    0 <= i < n -> 0 <= j < m ->
    j + side < m ->
    Znth anchor before 0 = 0 ->
    SettledSquareState before n m i j color side ->
    PaintRectanglePrefix before painted m i j side color (side * side) ->
    Znth (i * m + (j + side)) before 0 = 0 ->
    Znth (i * m + (j + side)) output 0 <> 0 ->
    LeastLegalColor before n m i (j + side) color fallback ->
    fallback <= color ->
    Znth (i * m + (j + side)) output 0 <= color.
Proof.
  intros n m anchor next before painted output output_grid i j color side
    fallback Hn Hm Hanchor Hbefore Houtput Hfrontier_next Hrows Hi Hj
    Hfrontier Hzero Hsettled Hpaint Hbefore_zero Houtput_nonzero
    Hfallback Hfallback_le.
  destruct (frontier_zero_is_new_origin__solver_final n m anchor next before
    painted output output_grid i j color side Hn Hm Hanchor Hbefore Houtput
    Hfrontier_next Hrows Hi Hj Hfrontier Hzero Hsettled Hpaint Hbefore_zero
    Houtput_nonzero) as [found [found_side [found_after
      [Hfound_settled [Hfound_paint Houtput_found]]]]].
  destruct Hfound_settled as [[Hfound_least Hfound_greedy] Hfound_stop].
  destruct Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
  destruct Hleast as [[Hcolor_range Hcolor_legal] Hcolor_minimal].
  assert (Hlen : Zlength before = n * m).
  { pose proof (trace_bounds_and_canonical__solver_final n m anchor before
      Hn Hm Hbefore) as [? [Hlength ?]]. exact Hlength. }
  assert (Hfound_before :
      LeastLegalColor before n m i (j + side) color found).
  { apply (proj1 (least_legal_frontier_equiv__solver_final before painted n m
      i j side color found Hn Hm Hi Hj (proj1 Hcolor_range) Hfrontier Hlen
      Hplace Hpaint)). exact Hfound_least. }
  assert (Hfound_eq : found = fallback).
  { eapply least_legal_color_unique__solver_final; eauto. }
  rewrite Houtput_found, Hfound_eq. exact Hfallback_le.
Qed.
Lemma existing_frontier_exchange_from_extend_ih__solver_final :
  forall n m anchor next before output output_grid candidate first i j color
      side,
    1 <= n -> 1 <= m ->
    anchor = i * m + j ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    anchor < first < next ->
    first = i * m + (j + side) ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= i < n -> 0 <= j < m ->
    j + side < m ->
    SettledSquareState before n m i j color side ->
    Znth first before 0 <> 0 ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    Znth first (Flatten candidate) 0 = color ->
    Znth first output 0 <> color ->
    (forall lower target q earlier origin_before painted oi oj oside other_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      earlier = oi * m + oj ->
      earlier < anchor ->
      GreedyPlacementTrace n m earlier origin_before ->
      SettledSquareState origin_before n m oi oj lower oside ->
      PaintRectanglePrefix origin_before painted m oi oj oside lower
        (oside * oside) ->
      0 <= oi < n -> 0 <= oj < m ->
      oi <= fst q < oi + oside -> oj <= snd q < oj + oside ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         oi <= fst x < oi + oside /\ oj <= snd x < oj + oside)) ->
      1 <= other_side ->
      oi + other_side <= n -> oj + other_side <= m ->
      oside < other_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (oi, oj) x <->
         oi <= fst x < oi + other_side /\
         oj <= snd x < oj + other_side)) ->
      oi <= fst target < oi + other_side ->
      oj <= snd target < oj + other_side ->
      Znth first output 0 <= lower) ->
    Znth first output 0 <= color.
Proof.
  intros n m anchor next before output output_grid candidate first i j color
    side Hn Hm Hanchor Hbefore Houtput Hfirst_range Hfirst Hrows Hcandidate
    Hi Hj Hfrontier Hsettled Hbefore_nonzero Hprefix Hcandfirst Houtdiff
    Hextend.
  set (p := (i, j + side)).
  assert (Hprow : 0 <= fst p < n).
  { unfold p; simpl. exact Hi. }
  assert (Hpcol : 0 <= snd p < m).
  { unfold p; simpl. nia. }
  destruct (trace_existing_component_origin_before__solver_final n m anchor
    before next output output_grid p Hn Hm Hbefore Houtput ltac:(lia) Hrows
    Hprow Hpcol ltac:(unfold p; simpl; rewrite <- Hfirst;
      exact Hbefore_nonzero)) as
    [earlier [origin_before [painted [oi [oj [found [oside Horigin]]]]]]].
  destruct Horigin as [Hearlier [Hearlier_anchor [Htrace [Hfound_settled
    [Hpaint [Hoi [Hoj [Hpoi [Hpoj [Hpcolor Hcomponent]]]]]]]]]].
  assert (Hfound_output : Znth first output 0 = found).
  { rewrite Hfirst.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid i
      (j + side) Hrows Hi Hpcol). unfold p in Hpcolor. exact Hpcolor. }
  assert (Hfound_bounds : 1 <= oside /\ oi + oside <= n /\ oj + oside <= m).
  { destruct Hfound_settled as [[? [Hplace ?]] ?]. destruct Hplace. tauto. }
  destruct Hfound_bounds as [Hoside [Hoibound Hojbound]].
  assert (Houtput_diff :
      Znth first output 0 <> Znth first (Flatten candidate) 0).
  { intros Heq. apply Houtdiff. rewrite Heq. exact Hcandfirst. }
  destruct (first_cell_component_dichotomy__solver_final n m output candidate
    output_grid first p earlier oi oj found oside Hn Hm Hrows Hcandidate
    Hprow Hpcol ltac:(unfold p; simpl; exact Hfirst) Hearlier Hoi Hoj Hoside
    Hoibound Hojbound Hpoi Hpoj Hfound_output Hcomponent ltac:(lia) Hprefix
    Houtput_diff) as
    [Himpossible | [candidate_side [Hcandidate_side [Hcandidate_i
      [Hcandidate_j [Hshort [Hpi [Hpj Hcandcomponent]]]]]]]].
  - lia.
  - rewrite <- Hcandfirst.
    refine (shrink_exchange_from_extend_ih__solver_final n m earlier next
      output output_grid candidate first origin_before oi oj found oside
      candidate_side Hn Hm Houtput Hrows Hcandidate Hearlier _ Hoi Hoj Htrace
      Hfound_settled _ _ Hfound_output Hprefix _).
    + split; lia.
    + split; lia.
    + unfold p in Hpi, Hpj. simpl in Hpi, Hpj. rewrite Hfirst. lia.
    + intros lower target q earlier0 origin_before0 painted0 oi0 oj0 oside0
        other_side Hlower Hcandlower Htarget Hearlier0 Hearlier_bound Htrace0
        Hsettled0 Hpaint0 Hoi0 Hoj0 Hqoi Hqoj Hqcolor Hcomponent0
        Hother_side Hother_i Hother_j Hcross Hcandidate0 Htarget_i Htarget_j.
      eapply (Hextend lower target q earlier0 origin_before0 painted0 oi0 oj0
        oside0 other_side); try eassumption; lia.
Qed.
Lemma extend_fallback_from_ih__solver_final :
  forall n m anchor next before painted output output_grid candidate first
      target q i j color side candidate_side fallback,
    1 <= n -> 1 <= m ->
    anchor = i * m + j ->
    anchor < first < next ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    first = fst target * m + snd target ->
    0 <= fst target < n -> 0 <= snd target < m ->
    0 <= i < n -> 0 <= j < m ->
    SettledSquareState before n m i j color side ->
    Znth anchor before 0 = 0 ->
    PaintRectanglePrefix before painted m i j side color (side * side) ->
    i <= fst q < i + side -> j <= snd q < j + side ->
    Znth (snd q) (Znth (fst q) output_grid []) 0 = color ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath output_grid q x <->
       i <= fst x < i + side /\ j <= snd x < j + side)) ->
    1 <= candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    side < candidate_side ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath candidate (i, j) x <->
       i <= fst x < i + candidate_side /\
       j <= snd x < j + candidate_side)) ->
    i <= fst target < i + candidate_side ->
    j <= snd target < j + candidate_side ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    Znth first (Flatten candidate) 0 = color ->
    Znth first output 0 <> color ->
    LeastLegalColor before n m i (j + side) color fallback ->
    fallback <= color ->
    (forall lower target0 q0 earlier origin_before painted0 oi oj oside other_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target0 * m + snd target0 ->
      earlier = oi * m + oj ->
      earlier < anchor ->
      GreedyPlacementTrace n m earlier origin_before ->
      SettledSquareState origin_before n m oi oj lower oside ->
      PaintRectanglePrefix origin_before painted0 m oi oj oside lower
        (oside * oside) ->
      0 <= oi < n -> 0 <= oj < m ->
      oi <= fst q0 < oi + oside -> oj <= snd q0 < oj + oside ->
      Znth (snd q0) (Znth (fst q0) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q0 x <->
         oi <= fst x < oi + oside /\ oj <= snd x < oj + oside)) ->
      1 <= other_side ->
      oi + other_side <= n -> oj + other_side <= m ->
      oside < other_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (oi, oj) x <->
         oi <= fst x < oi + other_side /\
         oj <= snd x < oj + other_side)) ->
      oi <= fst target0 < oi + other_side ->
      oj <= snd target0 < oj + other_side ->
      Znth first output 0 <= lower) ->
    Znth first output 0 <= color.
Proof.
  intros n m anchor next before painted output output_grid candidate first
    target q i j color side candidate_side fallback Hn Hm Hanchor
    Hfirst_range Hbefore Houtput Hrows Hcandidate Hfirst Htarget_row
    Htarget_col Hi Hj Hsettled Hzero Hpaint Hqi Hqj Hqcolor Hcomponent
    Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hcandcomponent
    Htarget_i Htarget_j Hprefix Hcandfirst Houtdiff Hfallback Hfallback_le
    Hextend.
  pose proof Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
  destruct Hplace as [Hside [Hibound [Hjbound Hplace_rest]]].
  assert (Hgrid_len : Zlength output_grid = n) by
    (destruct Hrows as [? [? ?]]; assumption).
  assert (Hrow_len : Zlength (Znth 0 output_grid []) = m).
  { destruct Hrows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hcomponent_anchor : forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath output_grid (i, j) x <->
       i <= fst x < i + side /\ j <= snd x < j + side)).
  { intros x Hxrow Hxcol.
    eapply exact_component_reanchor__solver_final with
      (p := q) (r := i) (c := j) (side := side); eauto; simpl; lia. }
  assert (Houtanchor : Znth (i * m + j) output 0 = color).
  { rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid i j
      Hrows Hi Hj).
    assert (Hpath : SameColorPath output_grid q (i, j)).
    { apply (proj2 (Hcomponent (i, j) ltac:(simpl; lia)
        ltac:(simpl; lia))). simpl. split; lia. }
    transitivity (Znth (snd q) (Znth (fst q) output_grid []) 0).
    - exact (same_color_path_endpoint_color__solver_final output_grid q
        (i, j) Hpath).
    - exact Hqcolor. }
  assert (Hfrontier_eq : first = i * m + (j + side)).
  { exact (extend_first_is_frontier__solver_final n m output output_grid
      candidate first target i j color side candidate_side Hn Hm Hrows
      Hcandidate Hi Hj Hside Hibound Hjbound Hside_lt Hcandidate_i
      Hcandidate_j Htarget_row Htarget_col Hfirst Htarget_i Htarget_j
      ltac:(lia) Hprefix Houtanchor Hcandfirst Houtdiff Hcomponent_anchor
      Hcandcomponent). }
  assert (Hfrontier : j + side < m) by lia.
  assert (Hout_nonzero : Znth first output 0 <> 0).
  { pose proof (trace_bounds_and_canonical__solver_final n m next output Hn
      Hm Houtput) as [Hbounds [Hlength [Hcanonical Hcolored]]].
    specialize (Hcolored first ltac:(lia)). lia. }
  destruct (classic (Znth first before 0 = 0)) as [Hbefore_zero | Hbefore_nonzero].
  - rewrite Hfrontier_eq.
    exact (frontier_zero_fallback_bound__solver_final n m anchor next before
      painted output output_grid i j color side fallback Hn Hm Hanchor
      Hbefore Houtput ltac:(rewrite <- Hfrontier_eq; lia) Hrows Hi Hj
      Hfrontier Hzero Hsettled Hpaint
      ltac:(rewrite <- Hfrontier_eq; exact Hbefore_zero)
      ltac:(rewrite <- Hfrontier_eq; exact Hout_nonzero) Hfallback
      Hfallback_le).
  - exact (existing_frontier_exchange_from_extend_ih__solver_final n m anchor
      next before output output_grid candidate first i j color side Hn Hm
      Hanchor Hbefore Houtput Hfirst_range Hfrontier_eq Hrows Hcandidate Hi
      Hj Hfrontier Hsettled Hbefore_nonzero Hprefix Hcandfirst Houtdiff
      Hextend).
Qed.

(* Also deferred until the step theorem below.
Lemma extend_exchange__solver_final :
  forall n m next output output_grid candidate first,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    first < next ->
    forall anchor, 0 <= anchor ->
    forall lower target q before painted i j side candidate_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      anchor = i * m + j ->
      anchor < first ->
      GreedyPlacementTrace n m anchor before ->
      SettledSquareState before n m i j lower side ->
      PaintRectanglePrefix before painted m i j side lower (side * side) ->
      0 <= i < n -> 0 <= j < m ->
      i <= fst q < i + side -> j <= snd q < j + side ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         i <= fst x < i + side /\ j <= snd x < j + side)) ->
      1 <= candidate_side ->
      i + candidate_side <= n -> j + candidate_side <= m ->
      side < candidate_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (i, j) x <->
         i <= fst x < i + candidate_side /\
         j <= snd x < j + candidate_side)) ->
      i <= fst target < i + candidate_side ->
      j <= snd target < j + candidate_side ->
      Znth first output 0 <= lower.
Proof.
  intros n m next output output_grid candidate first Hn Hm Houtput Hrows
    Hcandidate Hprefix Hfirst_next.
+  refine (nonnegative_anchor_strong_induction__solver_final
    (fun anchor => forall lower target q before painted i j side candidate_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      anchor = i * m + j ->
      anchor < first ->
      GreedyPlacementTrace n m anchor before ->
      SettledSquareState before n m i j lower side ->
      PaintRectanglePrefix before painted m i j side lower (side * side) ->
      0 <= i < n -> 0 <= j < m ->
      i <= fst q < i + side -> j <= snd q < j + side ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         i <= fst x < i + side /\ j <= snd x < j + side)) ->
      1 <= candidate_side ->
      i + candidate_side <= n -> j + candidate_side <= m ->
      side < candidate_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (i, j) x <->
         i <= fst x < i + candidate_side /\
         j <= snd x < j + candidate_side)) ->
      i <= fst target < i + candidate_side ->
      j <= snd target < j + candidate_side ->
      Znth first output 0 <= lower) _).
  intros anchor Hanchor_nonneg IH lower target q before painted i j side
    candidate_side Hlower Hcandfirst Hfirst Hanchor Hearlier Hbefore Hsettled
    Hpaint Hi Hj Hqi Hqj Hqcolor Hcomponent Hcandidate_side Hcandidate_i
    Hcandidate_j Hside_lt Hcandcomponent Htarget_i Htarget_j.
  eapply (extend_exchange_from_ih__solver_final n m next output output_grid
    candidate first lower target q anchor before painted i j side candidate_side
    Hn Hm Houtput Hrows Hcandidate Hprefix Hfirst_next Hlower Hcandfirst Hfirst
    Hanchor Hearlier Hbefore Hsettled Hpaint Hi Hj Hqi Hqj Hqcolor Hcomponent
    Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hcandcomponent Htarget_i
    Htarget_j).
  intros lower0 target0 q0 earlier origin_before painted0 oi oj oside other_side
    Hlower0 Hcandlower Htarget0 Hearlier_eq Hearlier_bound Htrace0 Hsettled0
    Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor0 Hcomponent0 Hother_side Hother_i Hother_j
    Hcross Hcandidate0 Htarget0_i Htarget0_j.
  eapply (IH earlier); try eassumption; try lia.
(* inactive mutual copy *)
Qed.

Lemma first_difference_bound__solver_final :
  forall n m next output output_grid candidate first,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= first < next ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    Znth first output 0 <= Znth first (Flatten candidate) 0.
Proof.
  intros n m next output output_grid candidate first Hn Hm Htrace Hrows
    Hcandidate Hfirst_range Hprefix.
  destruct (Z.eq_dec (Znth first output 0)
      (Znth first (Flatten candidate) 0)) as [Heq | Hdiff]; [lia |].
  destruct (trace_bounds_and_canonical__solver_final n m next output Hn Hm
    Htrace) as [Hnext_bound [Houtlen [Hcanonical Hcolored]]].
  assert (Hfirst_flat : 0 <= first < n * m) by lia.
  set (p := (first / m, first mod m)).
  assert (Hp_row : 0 <= fst p < n).
  { unfold p; simpl. split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (Hp_col : 0 <= snd p < m).
  { unfold p; simpl. apply Z.mod_pos_bound. lia. }
  assert (Hfirst : first = fst p * m + snd p).
  { unfold p; simpl. pose proof (Z.div_mod first m ltac:(lia)). nia. }
  assert (Hgrid_nonzero :
      Znth (snd p) (Znth (fst p) output_grid []) 0 <> 0).
  { rewrite (rows_of_flat_Znth__solver_final n m output output_grid (fst p)
      (snd p) Hrows Hp_row Hp_col).
    rewrite <- Hfirst. specialize (Hcolored first Hfirst_range). lia. }
  destruct (trace_colored_component_origin__solver_final n m next output
    output_grid p Hn Hm Htrace Hrows Hp_row Hp_col Hgrid_nonzero) as
    [anchor [before [painted [i [j [color [side Horigin]]]]]]].
  destruct Horigin as [Hanchor [Hanchor_next [Hbefore [Hsettled [Hpaint
    [Hi [Hj [Hpi [Hpj [Hpcolor [Hcomponent Hpersist]]]]]]]]]]].
  pose proof Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
  destruct Hplace as [Hside [Hibound [Hjbound Hplace_rest]]].
  assert (Houtfirst : Znth first output 0 = color).
  { rewrite Hfirst.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid (fst p)
      (snd p) Hrows Hp_row Hp_col). exact Hpcolor. }
  assert (Hanchor_le : anchor <= first).
  { rewrite Hanchor, Hfirst.
    eapply square_anchor_le_member__solver_final; eauto; lia. }
  destruct (first_cell_component_dichotomy__solver_final n m output candidate
    output_grid first p anchor i j color side Hn Hm Hrows Hcandidate Hp_row
    Hp_col Hfirst Hanchor Hi Hj Hside Hibound Hjbound Hpi Hpj Houtfirst
    Hcomponent Hanchor_le Hprefix Hdiff) as
    [Horigin_first | [candidate_side [Hcandidate_side [Hcandidate_i
      [Hcandidate_j [Hcandidate_short [Hp_i [Hp_j Hcandcomponent]]]]]]]].
  - eapply (base_exchange_from_extend_ih__solver_final n m next output
      output_grid candidate first before i j color side Hn Hm Htrace Hrows
      Hcandidate Hfirst_range ltac:(rewrite <- Horigin_first; exact Hanchor)
      Hi Hj ltac:(rewrite <- Horigin_first; exact Hbefore) Hsettled Houtfirst
      Hprefix).
    intros lower target q earlier origin_before painted0 oi oj oside other_side
      Hlower Hcandlower Htarget Hearlier Hearlier_bound Htrace0 Hsettled0
      Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor Hcomponent0 Hother_side Hother_i
      Hother_j Hcross Hcandidate0 Htarget_i Htarget_j.
    exact (extend_exchange__solver_final n m next output output_grid candidate
      first Hn Hm Htrace Hrows Hcandidate Hprefix (proj2 Hfirst_range) earlier
      ltac:(rewrite Hearlier; nia) lower target q origin_before painted0 oi oj
      oside other_side Hlower Hcandlower Htarget Hearlier ltac:(lia) Htrace0
      Hsettled0 Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor Hcomponent0 Hother_side
      Hother_i Hother_j Hcross Hcandidate0 Htarget_i Htarget_j).
  - eapply (shrink_exchange_from_extend_ih__solver_final n m anchor next output
      output_grid candidate first before i j color side candidate_side Hn Hm
      Htrace Hrows Hcandidate Hanchor ltac:(split; [rewrite Hanchor; nia | lia])
      Hi Hj Hbefore Hsettled ltac:(lia)
      ltac:(rewrite Hfirst, Hp_i, Hp_j; reflexivity) Houtfirst Hprefix).
    intros lower target q earlier origin_before painted0 oi oj oside other_side
      Hlower Hcandlower Htarget Hearlier Hearlier_bound Htrace0 Hsettled0
      Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor Hcomponent0 Hother_side Hother_i
      Hother_j Hcross Hcandidate0 Htarget_i Htarget_j.
    exact (extend_exchange__solver_final n m next output output_grid candidate
      first Hn Hm Htrace Hrows Hcandidate Hprefix (proj2 Hfirst_range) earlier
      ltac:(rewrite Hearlier; nia) lower target q origin_before painted0 oi oj
      oside other_side Hlower Hcandlower Htarget Hearlier ltac:(lia) Htrace0
      Hsettled0 Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor Hcomponent0 Hother_side
      Hother_i Hother_j Hcross Hcandidate0 Htarget_i Htarget_j).
(* inactive first-difference copy *)
Qed.

Lemma greedy_trace_lex__solver_final :
  forall n m next output candidate,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    SquareTiling n m candidate ->
    LexPrefixLe next output (Flatten candidate).
Proof.
  intros n m next output candidate Hn Hm Htrace Hcandidate.
  destruct (trace_bounds_and_canonical__solver_final n m next output Hn Hm
    Htrace) as [Hnext [Hlen Hrest]].
  destruct (rows_of_flat_from_length__solver_final n m output Hn Hm Hlen) as
    [output_grid Hrows].
  apply local_first_difference_implies_lex__solver_final; [lia |].
  intros first Hfirst Hprefix.
  exact (first_difference_bound__solver_final n m next output output_grid
    candidate first Hn Hm Htrace Hrows Hcandidate Hfirst Hprefix).
Qed.

Lemma greedy_trace_implies_partial_tiling__solver_final :
  forall n m next flat,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next flat ->
    PartialTilingState n m next flat.
Proof.
  intros n m next flat Hn Hm Htrace.
  apply (greedy_trace_partial_from_lex__solver_final n m next flat Hn Hm
    Htrace).
  intros candidate Hcandidate.
  exact (greedy_trace_lex__solver_final n m next flat candidate Hn Hm Htrace
    Hcandidate).
Qed.
(* close inactive augmented copy *)
*)

(* Deferred until extend_exchange_from_ih__solver_final is declared.
Lemma extend_exchange__solver_final :
  forall n m next output output_grid candidate first,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    first < next ->
    forall lower target q anchor before painted i j side candidate_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      anchor = i * m + j ->
      anchor < first ->
      GreedyPlacementTrace n m anchor before ->
      SettledSquareState before n m i j lower side ->
      PaintRectanglePrefix before painted m i j side lower (side * side) ->
      0 <= i < n -> 0 <= j < m ->
      i <= fst q < i + side -> j <= snd q < j + side ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         i <= fst x < i + side /\ j <= snd x < j + side)) ->
      1 <= candidate_side ->
      i + candidate_side <= n -> j + candidate_side <= m ->
      side < candidate_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (i, j) x <->
         i <= fst x < i + candidate_side /\
         j <= snd x < j + candidate_side)) ->
      i <= fst target < i + candidate_side ->
      j <= snd target < j + candidate_side ->
      Znth first output 0 <= lower.
Proof.
  intros n m next output output_grid candidate first Hn Hm Houtput Hrows
    Hcandidate Hprefix Hfirst_next.
  assert (Hstrong : forall anchor, 0 <= anchor ->
    forall lower target q before painted i j side candidate_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      anchor = i * m + j ->
      anchor < first ->
      GreedyPlacementTrace n m anchor before ->
      SettledSquareState before n m i j lower side ->
      PaintRectanglePrefix before painted m i j side lower (side * side) ->
      0 <= i < n -> 0 <= j < m ->
      i <= fst q < i + side -> j <= snd q < j + side ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         i <= fst x < i + side /\ j <= snd x < j + side)) ->
      1 <= candidate_side ->
      i + candidate_side <= n -> j + candidate_side <= m ->
      side < candidate_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (i, j) x <->
         i <= fst x < i + candidate_side /\
         j <= snd x < j + candidate_side)) ->
      i <= fst target < i + candidate_side ->
      j <= snd target < j + candidate_side ->
      Znth first output 0 <= lower).
  { apply (nonnegative_anchor_strong_induction__solver_final
      (fun anchor => forall lower target q before painted i j side candidate_side,
        65 <= lower ->
        Znth first (Flatten candidate) 0 = lower ->
        first = fst target * m + snd target ->
        anchor = i * m + j ->
        anchor < first ->
        GreedyPlacementTrace n m anchor before ->
        SettledSquareState before n m i j lower side ->
        PaintRectanglePrefix before painted m i j side lower (side * side) ->
        0 <= i < n -> 0 <= j < m ->
        i <= fst q < i + side -> j <= snd q < j + side ->
        Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
        (forall x,
          0 <= fst x < n -> 0 <= snd x < m ->
          (SameColorPath output_grid q x <->
           i <= fst x < i + side /\ j <= snd x < j + side)) ->
        1 <= candidate_side ->
        i + candidate_side <= n -> j + candidate_side <= m ->
        side < candidate_side ->
        (forall x,
          0 <= fst x < n -> 0 <= snd x < m ->
          (SameColorPath candidate (i, j) x <->
           i <= fst x < i + candidate_side /\
           j <= snd x < j + candidate_side)) ->
        i <= fst target < i + candidate_side ->
        j <= snd target < j + candidate_side ->
        Znth first output 0 <= lower)).
    intros anchor Hanchor_nonneg IH lower target q before painted i j side
      candidate_side Hlower Hcandfirst Hfirst Hanchor Hearlier Hbefore
      Hsettled Hpaint Hi Hj Hqi Hqj Hqcolor Hcomponent Hcandidate_side
      Hcandidate_i Hcandidate_j Hside_lt Hcandcomponent Htarget_i Htarget_j.
    eapply (extend_exchange_from_ih__solver_final n m next output output_grid
      candidate first lower target q anchor before painted i j side
      candidate_side Hn Hm Houtput Hrows Hcandidate Hprefix Hfirst_next Hlower
      Hcandfirst Hfirst Hanchor Hearlier Hbefore Hsettled Hpaint Hi Hj Hqi Hqj
      Hqcolor Hcomponent Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt
      Hcandcomponent Htarget_i Htarget_j).
    intros lower0 target0 q0 earlier origin_before painted0 oi oj oside
      other_side Hlower0 Hcandlower Htarget0 Hearlier_eq Hearlier_bound Htrace0
      Hsettled0 Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor0 Hcomponent0 Hother_side
      Hother_i Hother_j Hcross Hcandidate0 Htarget0_i Htarget0_j.
    eapply (IH earlier); try eassumption; try lia.
(* inactive old mutual copy *)
    rewrite Hearlier_eq. nia. }
  intros lower target q anchor before painted i j side candidate_side Hlower
    Hcandfirst Hfirst Hanchor Hearlier Hbefore Hsettled Hpaint Hi Hj Hqi Hqj
    Hqcolor Hcomponent Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt
    Hcandcomponent Htarget_i Htarget_j.
  eapply (Hstrong anchor); try eassumption.
  rewrite Hanchor. nia.
Qed.
*)
Lemma Znth_rev_inrange__solver_final :
  forall (A : Type) (l : list A) (d : A) k,
    0 <= k < Zlength l ->
    Znth k (rev l) d = Znth (Zlength l - 1 - k) l d.
Proof.
  intros A l d k Hk. unfold Znth.
  rewrite rev_nth.
  - f_equal. rewrite Zlength_correct in *. lia.
  - rewrite Zlength_correct in Hk. lia.
Qed.
Lemma adjcell_sym__solver_final :
  forall p q, AdjCell p q -> AdjCell q p.
Proof.
  intros [pr pc] [qr qc] Hadj. unfold AdjCell in *. simpl in *.
  replace (qr - pr) with (-(pr - qr)) by ring.
  replace (qc - pc) with (-(pc - qc)) by ring.
  rewrite !Z.abs_opp. exact Hadj.
Qed.
Lemma same_color_path_sym__solver_final :
  forall grid p q,
    SameColorPath grid p q -> SameColorPath grid q p.
Proof.
  intros grid p q Hpath.
  unfold SameColorPath in Hpath |- *.
  destruct Hpath as [path [Hnonempty [Hfirst [Hlast [Hforall Hsteps]]]]].
  assert (Hlen_pos : 0 < Zlength path).
  { destruct path; [contradiction |].
    rewrite Zlength_cons. pose proof (Zlength_nonneg path). lia. }
  assert (Hqcolor :
      Znth (snd q) (Znth (fst q) grid []) 0 =
      Znth (snd p) (Znth (fst p) grid []) 0).
  { rewrite Forall_forall in Hforall.
    specialize (Hforall (Znth (Zlength path - 1) path (0, 0))).
    assert (Hin : In (Znth (Zlength path - 1) path (0, 0)) path).
    { apply Znth_In_range__solver_final. lia. }
    specialize (Hforall Hin). destruct Hforall as [_ [_ Hcolor]].
    rewrite Hlast in Hcolor. exact Hcolor. }
  exists (rev path).
  split.
  - intros Hnil. apply (f_equal (@rev Cell)) in Hnil.
    rewrite rev_involutive in Hnil. simpl in Hnil. contradiction.
  - split.
    + rewrite (Znth_rev_inrange__solver_final Cell path (0, 0) 0) by lia.
      replace (Zlength path - 1 - 0) with (Zlength path - 1) by lia.
      exact Hlast.
    + split.
      * assert (Hlenrev : Zlength (rev path) = Zlength path).
        { rewrite !Zlength_correct, length_rev. reflexivity. }
        rewrite Hlenrev.
        rewrite (Znth_rev_inrange__solver_final Cell path (0, 0)
          (Zlength path - 1)) by lia.
        replace (Zlength path - 1 - (Zlength path - 1)) with 0 by lia.
        exact Hfirst.
      * split.
        -- rewrite Forall_forall in Hforall |- *.
           intros x Hxin. apply in_rev in Hxin. specialize (Hforall x Hxin).
           destruct Hforall as [Hxrow [Hxcol Hxcolor]].
           refine (conj Hxrow (conj Hxcol _)).
           transitivity (Znth (snd p) (Znth (fst p) grid []) 0).
           ++ exact Hxcolor.
           ++ symmetry. exact Hqcolor.
        -- intros k Hk.
           assert (Hlenrev : Zlength (rev path) = Zlength path).
           { rewrite !Zlength_correct, length_rev. reflexivity. }
           rewrite Hlenrev in Hk.
           rewrite (Znth_rev_inrange__solver_final Cell path (0, 0) k) by lia.
           rewrite (Znth_rev_inrange__solver_final Cell path (0, 0) (k + 1))
             by lia.
           apply adjcell_sym__solver_final.
           pose proof (Hsteps (Zlength path - 2 - k) ltac:(lia)) as Hstep.
           replace (Zlength path - 1 - (k + 1)) with
             (Zlength path - 2 - k) by lia.
           replace (Zlength path - 1 - k) with
             (Zlength path - 2 - k + 1) by lia.
           exact Hstep.
Qed.
Lemma same_color_path_trans__solver_final :
  forall grid p x q,
    SameColorPath grid p x ->
    SameColorPath grid x q ->
    SameColorPath grid p q.
Proof.
  intros grid p x q Hpx Hxq.
  unfold SameColorPath in Hxq.
  destruct Hxq as [path [Hnonempty [Hfirst [Hlast [Hforall Hsteps]]]]].
  destruct path as [|head tail]; [contradiction |].
  change (head = x) in Hfirst. subst head.
  clear Hnonempty.
  revert x Hpx Hlast Hforall Hsteps.
  induction tail as [|y tail IH]; intros x Hpx Hlast Hforall Hsteps.
  - change (x = q) in Hlast. subst q. exact Hpx.
  - assert (Hydata :
        0 <= fst y < Zlength grid /\
        0 <= snd y < Zlength (Znth 0 grid []) /\
        Znth (snd y) (Znth (fst y) grid []) 0 =
        Znth (snd x) (Znth (fst x) grid []) 0).
    { inversion Hforall as [|? ? Hxdata Htail]; subst.
      inversion Htail as [|? ? Hydata Hrest]; subst. exact Hydata. }
    destruct Hydata as [Hyrow [Hycol Hycolor_x]].
    assert (Hxcolor_p :
        Znth (snd x) (Znth (fst x) grid []) 0 =
        Znth (snd p) (Znth (fst p) grid []) 0).
    { exact (same_color_path_endpoint_color__solver_final grid p x Hpx). }
    assert (Hadj : AdjCell x y).
    { specialize (Hsteps 0 ltac:(rewrite !Zlength_cons;
        pose proof (Zlength_nonneg tail); lia)).
      simpl in Hsteps. exact Hsteps. }
    assert (Hpy : SameColorPath grid p y).
    { eapply same_color_path_append__solver_final; eauto.
      transitivity (Znth (snd x) (Znth (fst x) grid []) 0); assumption. }
    apply (IH y Hpy).
    + rewrite Znth_cons in Hlast by
        (rewrite !Zlength_cons; pose proof (Zlength_nonneg tail); lia).
      replace (Zlength (x :: y :: tail) - 1 - 1) with
        (Zlength tail) in Hlast by
        (rewrite !Zlength_cons; pose proof (Zlength_nonneg tail); lia).
      replace (Zlength (y :: tail) - 1) with (Zlength tail) by
        (rewrite Zlength_cons; lia).
      exact Hlast.
    + inversion Hforall as [|? ? Hxdata Htail]; subst.
      eapply Forall_impl; [|exact Htail].
      intros z [Hzrow [Hzcol Hzcolor]].
      refine (conj Hzrow (conj Hzcol _)).
      transitivity (Znth (snd x) (Znth (fst x) grid []) 0).
      * exact Hzcolor.
      * symmetry. exact Hycolor_x.
    + intros k Hk.
      specialize (Hsteps (k + 1) ltac:(rewrite !Zlength_cons in *;
        pose proof (Zlength_nonneg tail); lia)).
      simpl in Hsteps |- *.
      replace (k + 1 + 1) with (k + 2) in Hsteps by lia.
      rewrite !Znth_cons in Hsteps by lia.
      rewrite (@Znth_cons Cell (0, 0) (k + 2) x (y :: tail)) in Hsteps
        by lia.
      replace (k + 1 - 1) with k in Hsteps by lia.
      replace (k + 2 - 1) with (k + 1) in Hsteps by lia.
      exact Hsteps.
Qed.
Lemma exact_components_rectangles_disjoint__solver_final :
  forall grid n m ai aj aside bi bj bside,
    0 <= ai < n -> 0 <= aj < m ->
    0 <= bi < n -> 0 <= bj < m ->
    1 <= aside -> ai + aside <= n -> aj + aside <= m ->
    1 <= bside -> bi + bside <= n -> bj + bside <= m ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath grid (ai, aj) x <->
       ai <= fst x < ai + aside /\ aj <= snd x < aj + aside)) ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath grid (bi, bj) x <->
       bi <= fst x < bi + bside /\ bj <= snd x < bj + bside)) ->
    ai * m + aj <> bi * m + bj ->
    forall x,
      ai <= fst x < ai + aside -> aj <= snd x < aj + aside ->
      ~ (bi <= fst x < bi + bside /\ bj <= snd x < bj + bside).
Proof.
  intros grid n m ai aj aside bi bj bside Hai Haj Hbi Hbj Haside
    Haibound Hajbound Hbside Hbibound Hbjbound Hacomp Hbcomp Hanchor x
    Hxai Hxaj [Hxbi Hxbj].
  assert (Hxrow : 0 <= fst x < n) by lia.
  assert (Hxcol : 0 <= snd x < m) by lia.
  assert (Hax : SameColorPath grid (ai, aj) x).
  { apply (proj2 (Hacomp x Hxrow Hxcol)). tauto. }
  assert (Hbx : SameColorPath grid (bi, bj) x).
  { apply (proj2 (Hbcomp x Hxrow Hxcol)). tauto. }
  assert (Hab : SameColorPath grid (ai, aj) (bi, bj)).
  { eapply same_color_path_trans__solver_final.
    - exact Hax.
    - apply same_color_path_sym__solver_final. exact Hbx. }
  assert (Hba : SameColorPath grid (bi, bj) (ai, aj)).
  { apply same_color_path_sym__solver_final. exact Hab. }
  apply (proj1 (Hacomp (bi, bj) ltac:(simpl; lia) ltac:(simpl; lia))) in Hab.
  apply (proj1 (Hbcomp (ai, aj) ltac:(simpl; lia) ltac:(simpl; lia))) in Hba.
  simpl in Hab, Hba. apply Hanchor. nia.
Qed.
Lemma disjoint_rectangles_separate__solver_final :
  forall ar ac aside br bc bside,
    1 <= aside -> 1 <= bside ->
    (forall x,
      ar <= fst x < ar + aside -> ac <= snd x < ac + aside ->
      ~ (br <= fst x < br + bside /\ bc <= snd x < bc + bside)) ->
    ar + aside <= br \/ br + bside <= ar \/
    ac + aside <= bc \/ bc + bside <= ac.
Proof.
  intros ar ac aside br bc bside Haside Hbside Hdisjoint.
  destruct (Z_le_gt_dec (ar + aside) br); [tauto |].
  destruct (Z_le_gt_dec (br + bside) ar); [tauto |].
  destruct (Z_le_gt_dec (ac + aside) bc); [tauto |].
  destruct (Z_le_gt_dec (bc + bside) ac); [tauto |].
  exfalso.
  set (r := Z.max ar br). set (c := Z.max ac bc).
  assert (HrA : ar <= r < ar + aside).
  { unfold r. destruct (Z.max_spec ar br); lia. }
  assert (HrB : br <= r < br + bside).
  { unfold r. destruct (Z.max_spec ar br); lia. }
  assert (HcA : ac <= c < ac + aside).
  { unfold c. destruct (Z.max_spec ac bc); lia. }
  assert (HcB : bc <= c < bc + bside).
  { unfold c. destruct (Z.max_spec ac bc); lia. }
  apply (Hdisjoint (r, c)); simpl; tauto.
Qed.
Lemma earlier_component_excluded_from_candidate_square__solver_final :
  forall n m output output_grid candidate first current_i current_j
      current_side candidate_side q oi oj oside x,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= current_i < n -> 0 <= current_j < m ->
    1 <= current_side ->
    current_i + current_side <= n -> current_j + current_side <= m ->
    1 <= candidate_side ->
    current_i + candidate_side <= n -> current_j + candidate_side <= m ->
    current_side < candidate_side ->
    first = current_i * m + (current_j + current_side) ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath candidate (current_i, current_j) z <->
       current_i <= fst z < current_i + candidate_side /\
       current_j <= snd z < current_j + candidate_side)) ->
    0 <= oi < n -> 0 <= oj < m ->
    1 <= oside -> oi + oside <= n -> oj + oside <= m ->
    oi <= fst q < oi + oside -> oj <= snd q < oj + oside ->
    oi * m + oj < current_i * m + current_j ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath output_grid q z <->
       oi <= fst z < oi + oside /\ oj <= snd z < oj + oside)) ->
    oi <= fst x < oi + oside -> oj <= snd x < oj + oside ->
    current_i <= fst x < current_i + candidate_side ->
    current_j <= snd x < current_j + candidate_side ->
    False.
Proof.
  intros n m output output_grid candidate first current_i current_j
    current_side candidate_side q oi oj oside x Hn Hm Hrows Hcandidate Hci
    Hcj Hcurrent_side Hcurrent_i Hcurrent_j Hcandidate_side Hcandidate_i
    Hcandidate_j Hside_lt Hfirst Hprefix Hcurrent_component Hoi Hoj Hoside
    Hoibound Hojbound Hqoi Hqoj Hearlier Houtcomponent Hxoi Hxoj Hxci Hxcj.
  assert (Hqrow : 0 <= fst q < n) by lia.
  assert (Hqcol : 0 <= snd q < m) by lia.
  destruct (candidate_component_at_output_member__solver_final n m output
    candidate output_grid q oi oj oside first Hn Hm Hrows Hcandidate Hqrow
    Hqcol Hoi Hoj Hoside Hoibound Hojbound Hqoi Hqoj ltac:(rewrite Hfirst;
      lia) Hprefix Houtcomponent) as
    [other_side [Hother_side [Hother_i [Hother_j Hother_component]]]].
  assert (Hanchors_ne :
      oi * m + oj <> current_i * m + current_j) by lia.
  assert (Hdisjoint : forall z,
      oi <= fst z < oi + other_side ->
      oj <= snd z < oj + other_side ->
      ~ (current_i <= fst z < current_i + candidate_side /\
         current_j <= snd z < current_j + candidate_side)).
  { intros z Hzoi Hzoj.
    eapply exact_components_rectangles_disjoint__solver_final with
      (grid := candidate) (n := n) (m := m) (ai := oi) (aj := oj)
      (aside := other_side) (bi := current_i) (bj := current_j)
      (bside := candidate_side); eauto. }
  destruct (disjoint_rectangles_separate__solver_final oi oj other_side
    current_i current_j candidate_side Hother_side Hcandidate_side Hdisjoint)
    as [Habove | [Hbelow | [Hleft | Hright]]].
  - assert (Hboundary : oi * m + (oj + other_side) < first).
    { rewrite Hfirst. nia. }
    pose proof (candidate_component_not_short_before_member__solver_final n m
      output candidate output_grid q oi oj oside other_side first Hn Hm Hrows
      Hcandidate Hqrow Hqcol Hoi Hoj Hoside Hoibound Hojbound Hqoi Hqoj
      Hother_side Hother_i Hother_j Hboundary Hprefix Houtcomponent
      Hother_component) as Hnotshort.
    apply (Hdisjoint x); try lia.
  - lia.
  - assert (Hoi_current : oi <= current_i).
    { destruct (Z.le_gt_cases oi current_i); [lia | exfalso]. nia. }
    assert (Hboundary : oi * m + (oj + other_side) < first).
    { rewrite Hfirst. nia. }
    pose proof (candidate_component_not_short_before_member__solver_final n m
      output candidate output_grid q oi oj oside other_side first Hn Hm Hrows
      Hcandidate Hqrow Hqcol Hoi Hoj Hoside Hoibound Hojbound Hqoi Hqoj
      Hother_side Hother_i Hother_j Hboundary Hprefix Houtcomponent
      Hother_component) as Hnotshort.
    apply (Hdisjoint x); try lia.
  - lia.
Qed.
Lemma extension_candidate_square_empty__solver_final :
  forall n m anchor next before output output_grid candidate first i j color
      side candidate_side,
    1 <= n -> 1 <= m ->
    anchor = i * m + j ->
    anchor < first < next ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= i < n -> 0 <= j < m ->
    CanPlace before n m i j side color ->
    1 <= candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    side < candidate_side ->
    first = i * m + (j + side) ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath candidate (i, j) z <->
       i <= fst z < i + candidate_side /\
       j <= snd z < j + candidate_side)) ->
    forall r c,
      i <= r < i + side + 1 -> j <= c < j + side + 1 ->
      Znth (r * m + c) before 0 = 0.
Proof.
  intros n m anchor next before output output_grid candidate first i j color
    side candidate_side Hn Hm Hanchor Hfirst_range Hbefore Houtput Hrows
    Hcandidate Hi Hj Hplace Hcandidate_side Hcandidate_i Hcandidate_j
    Hside_lt Hfirst Hprefix Hcandcomponent r c Hr Hc.
  destruct Hplace as [Hside [Hibound [Hjbound Hplace_rest]]].
  destruct (Z.eq_dec (Znth (r * m + c) before 0) 0) as [Hzero | Hnonzero];
    [exact Hzero | exfalso].
  assert (Hrbound : 0 <= r < n) by lia.
  assert (Hcbound : 0 <= c < m) by lia.
  set (x := (r, c)).
  destruct (trace_existing_component_origin_before__solver_final n m anchor
    before next output output_grid x Hn Hm Hbefore Houtput ltac:(lia) Hrows
    ltac:(unfold x; simpl; exact Hrbound)
    ltac:(unfold x; simpl; exact Hcbound)
    ltac:(unfold x; simpl; exact Hnonzero)) as
    [earlier [origin_before [painted [oi [oj [found [oside Horigin]]]]]]].
  destruct Horigin as [Hearlier [Hearlier_anchor [Htrace [Hsettled [Hpaint
    [Hoi [Hoj [Hxoi [Hxoj [Hxcolor Hcomponent]]]]]]]]]].
  assert (Hoside : 1 <= oside /\ oi + oside <= n /\ oj + oside <= m).
  { destruct Hsettled as [[? [Hfound_place ?]] ?].
    destruct Hfound_place. tauto. }
  destruct Hoside as [Hoside [Hoibound Hojbound]].
  exact (earlier_component_excluded_from_candidate_square__solver_final n m
    output output_grid candidate first i j side candidate_side x oi oj oside x
    Hn Hm Hrows Hcandidate Hi Hj Hside Hibound Hjbound Hcandidate_side
    Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix Hcandcomponent Hoi Hoj
    Hoside Hoibound Hojbound Hxoi Hxoj ltac:(lia) Hcomponent Hxoi Hxoj
    ltac:(unfold x; simpl; lia) ltac:(unfold x; simpl; lia)).
Qed.
Lemma earlier_candidate_component_not_short__solver_final :
  forall n m output output_grid candidate first current_i current_j
      current_side candidate_side q oi oj oside,
    1 <= n -> 1 <= m ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= current_i < n -> 0 <= current_j < m ->
    1 <= current_side ->
    current_i + current_side <= n -> current_j + current_side <= m ->
    1 <= candidate_side ->
    current_i + candidate_side <= n -> current_j + candidate_side <= m ->
    current_side < candidate_side ->
    first = current_i * m + (current_j + current_side) ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath candidate (current_i, current_j) z <->
       current_i <= fst z < current_i + candidate_side /\
       current_j <= snd z < current_j + candidate_side)) ->
    0 <= oi < n -> 0 <= oj < m ->
    1 <= oside -> oi + oside <= n -> oj + oside <= m ->
    oi <= fst q < oi + oside -> oj <= snd q < oj + oside ->
    oi * m + oj < current_i * m + current_j ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath output_grid q z <->
       oi <= fst z < oi + oside /\ oj <= snd z < oj + oside)) ->
    exists other_side,
      1 <= other_side /\
      oi + other_side <= n /\ oj + other_side <= m /\
      oside <= other_side /\
      (forall z,
        0 <= fst z < n -> 0 <= snd z < m ->
        (SameColorPath candidate (oi, oj) z <->
         oi <= fst z < oi + other_side /\
         oj <= snd z < oj + other_side)).
Proof.
  intros n m output output_grid candidate first current_i current_j
    current_side candidate_side q oi oj oside Hn Hm Hrows Hcandidate Hci
    Hcj Hcurrent_side Hcurrent_i Hcurrent_j Hcandidate_side Hcandidate_i
    Hcandidate_j Hside_lt Hfirst Hprefix Hcurrent_component Hoi Hoj Hoside
    Hoibound Hojbound Hqoi Hqoj Hearlier Houtcomponent.
  assert (Hqrow : 0 <= fst q < n) by lia.
  assert (Hqcol : 0 <= snd q < m) by lia.
  destruct (candidate_component_at_output_member__solver_final n m output
    candidate output_grid q oi oj oside first Hn Hm Hrows Hcandidate Hqrow
    Hqcol Hoi Hoj Hoside Hoibound Hojbound Hqoi Hqoj ltac:(rewrite Hfirst;
      lia) Hprefix Houtcomponent) as
    [other_side [Hother_side [Hother_i [Hother_j Hother_component]]]].
  assert (Hanchors_ne :
      oi * m + oj <> current_i * m + current_j) by lia.
  assert (Hdisjoint : forall z,
      oi <= fst z < oi + other_side ->
      oj <= snd z < oj + other_side ->
      ~ (current_i <= fst z < current_i + candidate_side /\
         current_j <= snd z < current_j + candidate_side)).
  { intros z Hzoi Hzoj.
    eapply exact_components_rectangles_disjoint__solver_final with
      (grid := candidate) (n := n) (m := m) (ai := oi) (aj := oj)
      (aside := other_side) (bi := current_i) (bj := current_j)
      (bside := candidate_side); eauto. }
  destruct (disjoint_rectangles_separate__solver_final oi oj other_side
    current_i current_j candidate_side Hother_side Hcandidate_side Hdisjoint)
    as [Habove | [Hbelow | [Hleft | Hright]]].
  - assert (Hboundary : oi * m + (oj + other_side) < first).
    { rewrite Hfirst. nia. }
    pose proof (candidate_component_not_short_before_member__solver_final n m
      output candidate output_grid q oi oj oside other_side first Hn Hm Hrows
      Hcandidate Hqrow Hqcol Hoi Hoj Hoside Hoibound Hojbound Hqoi Hqoj
      Hother_side Hother_i Hother_j Hboundary Hprefix Houtcomponent
      Hother_component) as Hshort.
    exists other_side. split; [exact Hother_side |].
    split; [exact Hother_i |]. split; [exact Hother_j |].
    split; [exact Hshort | exact Hother_component].
  - exfalso. nia.
  - assert (Hoi_current : oi <= current_i).
    { destruct (Z.le_gt_cases oi current_i); [lia | exfalso]. nia. }
    assert (Hboundary : oi * m + (oj + other_side) < first).
    { rewrite Hfirst. nia. }
    pose proof (candidate_component_not_short_before_member__solver_final n m
      output candidate output_grid q oi oj oside other_side first Hn Hm Hrows
      Hcandidate Hqrow Hqcol Hoi Hoj Hoside Hoibound Hojbound Hqoi Hqoj
      Hother_side Hother_i Hother_j Hboundary Hprefix Houtcomponent
      Hother_component) as Hshort.
    exists other_side. split; [exact Hother_side |].
    split; [exact Hother_i |]. split; [exact Hother_j |].
    split; [exact Hshort | exact Hother_component].
  - assert (Hoi_before : oi < current_i).
    { destruct (Z.lt_ge_cases oi current_i); [lia | exfalso]. nia. }
    assert (Hboundary : oi * m + (oj + other_side) < first).
    { rewrite Hfirst. nia. }
    pose proof (candidate_component_not_short_before_member__solver_final n m
      output candidate output_grid q oi oj oside other_side first Hn Hm Hrows
      Hcandidate Hqrow Hqcol Hoi Hoj Hoside Hoibound Hojbound Hqoi Hqoj
      Hother_side Hother_i Hother_j Hboundary Hprefix Houtcomponent
      Hother_component) as Hshort.
    exists other_side. split; [exact Hother_side |].
    split; [exact Hother_i |]. split; [exact Hother_j |].
    split; [exact Hshort | exact Hother_component].
Qed.
Lemma candidate_boundary_cell_cannot_match__solver_final :
  forall n m anchor next before output output_grid candidate first
      current_i current_j color current_side candidate_side x y,
    1 <= n -> 1 <= m ->
    anchor = current_i * m + current_j ->
    anchor < first < next ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= current_i < n -> 0 <= current_j < m ->
    1 <= current_side ->
    current_i + current_side <= n -> current_j + current_side <= m ->
    1 <= candidate_side ->
    current_i + candidate_side <= n -> current_j + candidate_side <= m ->
    current_side < candidate_side ->
    first = current_i * m + (current_j + current_side) ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath candidate (current_i, current_j) z <->
       current_i <= fst z < current_i + candidate_side /\
       current_j <= snd z < current_j + candidate_side)) ->
    65 <= color ->
    Znth (current_i * m + current_j) output 0 = color ->
    Znth (fst x * m + snd x) before 0 = color ->
    0 <= fst x < n -> 0 <= snd x < m ->
    0 <= fst y < n -> 0 <= snd y < m ->
    current_i <= fst y < current_i + candidate_side ->
    current_j <= snd y < current_j + candidate_side ->
    AdjCell y x -> False.
Proof.
  intros n m anchor next before output output_grid candidate first current_i
    current_j color current_side candidate_side x y Hn Hm Hanchor Hrange
    Hbefore Houtput Hrows Hcandidate Hci Hcj Hcurrent_side Hcurrent_i
    Hcurrent_j Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst
    Hprefix Hcurrent_component Hcolor Houtanchor Hbefore_x Hxrow Hxcol Hyrow Hycol
    Hyinside_r Hyinside_c Hadj.
  assert (Hbefore_x_nonzero : Znth (fst x * m + snd x) before 0 <> 0).
  { rewrite Hbefore_x. lia. }
  destruct (trace_existing_component_origin_before__solver_final n m anchor
    before next output output_grid x Hn Hm Hbefore Houtput ltac:(lia) Hrows
    Hxrow Hxcol Hbefore_x_nonzero) as
    [earlier [origin_before [painted [oi [oj [found [oside Horigin]]]]]]].
  destruct Horigin as [Hearlier [Hearlier_anchor [Hearlier_trace
    [Hearlier_settled [Hearlier_paint [Hoi [Hoj [Hxoi [Hxoj
      [Hx_found Hout_component]]]]]]]]]].
  destruct Hearlier_settled as [[Hearlier_least [Hearlier_place Hearlier_prev]]
    Hearlier_stop].
  destruct Hearlier_place as [Hoside [Hoi_bound [Hoj_bound Hearlier_rest]]].
  assert (Hfound_color : found = color).
  { assert (Houtput_x : Znth (fst x * m + snd x) output 0 = color).
    { rewrite (greedy_trace_prefix_persistence__solver_final n m anchor next
        before output Hn Hm ltac:(lia) Hbefore Houtput
        (fst x * m + snd x) ltac:(nia) Hbefore_x_nonzero).
      exact Hbefore_x. }
    rewrite <- Hx_found.
    rewrite (rows_of_flat_Znth__solver_final n m output output_grid
      (fst x) (snd x) Hrows Hxrow Hxcol).
    exact Houtput_x. }
  destruct (earlier_candidate_component_not_short__solver_final n m output
    output_grid candidate first current_i current_j current_side candidate_side
    x oi oj oside Hn Hm Hrows Hcandidate Hci Hcj Hcurrent_side Hcurrent_i
    Hcurrent_j Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst
    Hprefix Hcurrent_component Hoi Hoj Hoside Hoi_bound Hoj_bound Hxoi Hxoj
    ltac:(rewrite <- Hanchor, <- Hearlier; exact Hearlier_anchor)
    Hout_component) as
    [other_side [Hother_side [Hother_i [Hother_j
      [Hoside_le Hother_component]]]]].
  assert (Hcandidate_earlier_x : SameColorPath candidate (oi, oj) x).
  { apply (proj2 (Hother_component x Hxrow Hxcol)). split; lia. }
  assert (Houtput_origin_color :
      Znth (oi * m + oj) output 0 = found).
  { assert (Hpath_x_origin : SameColorPath output_grid x (oi, oj)).
    { apply (proj2 (Hout_component (oi, oj) ltac:(simpl; lia)
        ltac:(simpl; lia))). simpl. split; lia. }
    pose proof (same_color_path_endpoint_color__solver_final output_grid x
      (oi, oj) Hpath_x_origin) as Hcolors.
    simpl in Hcolors.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid oi oj Hrows
      Hoi Hoj).
    rewrite Hcolors. exact Hx_found. }
  assert (Hcandidate_origin_color :
      Znth oj (Znth oi candidate []) 0 = found).
  { rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate oi oj (square_tiling_rows__solver_final n m candidate
        Hcandidate) Hoi Hoj).
    rewrite <- Hprefix by (rewrite <- Hearlier; nia).
    exact Houtput_origin_color. }
  assert (Hcandidate_x_color :
      Znth (snd x) (Znth (fst x) candidate []) 0 = found).
  { rewrite (same_color_path_endpoint_color__solver_final candidate (oi, oj) x
      Hcandidate_earlier_x). exact Hcandidate_origin_color. }
  assert (Hcandidate_current_color :
      Znth current_j (Znth current_i candidate []) 0 = color).
  { rewrite (rows_of_flat_Znth__solver_final n m (Flatten candidate)
      candidate current_i current_j (square_tiling_rows__solver_final n m
        candidate Hcandidate) Hci Hcj).
    rewrite <- Hprefix by (rewrite <- Hanchor; lia).
    exact Houtanchor. }
  assert (Hcandidate_current_y :
      SameColorPath candidate (current_i, current_j) y).
  { apply (proj2 (Hcurrent_component y Hyrow Hycol)). tauto. }
  assert (Hcandidate_x_current_color :
      Znth (snd x) (Znth (fst x) candidate []) 0 =
      Znth current_j (Znth current_i candidate []) 0).
  { rewrite Hcandidate_x_color, Hcandidate_current_color, Hfound_color.
    reflexivity. }
  pose proof (square_tiling_rows__solver_final n m candidate Hcandidate)
    as Hcandidate_rows.
  destruct Hcandidate_rows as [Hcandidate_len [Hcandidate_row_len Hflat]].
  assert (Hrow0_len : Zlength (Znth 0 candidate []) = m).
  { rewrite Forall_forall in Hcandidate_row_len.
    apply Hcandidate_row_len, Znth_In_range__solver_final.
    rewrite Hcandidate_len. lia. }
  destruct (classic (current_i <= fst x < current_i + candidate_side /\
      current_j <= snd x < current_j + candidate_side)) as [Hxinside | Hxoutside].
  - eapply exact_components_rectangles_disjoint__solver_final with
      (grid := candidate) (n := n) (m := m) (ai := oi) (aj := oj)
      (aside := other_side) (bi := current_i) (bj := current_j)
      (bside := candidate_side) (x := x); eauto; lia.
  - assert (Hcurrent_x : SameColorPath candidate (current_i, current_j) x).
    { exact (same_color_path_append__solver_final candidate (current_i, current_j)
        y x Hcandidate_current_y ltac:(rewrite Hcandidate_len; exact Hxrow)
        ltac:(rewrite Hrow0_len; exact Hxcol) Hcandidate_x_current_color Hadj). }
    apply Hxoutside.
    exact (proj1 (Hcurrent_component x Hxrow Hxcol) Hcurrent_x).
Qed.
Lemma extension_candidate_can_place__solver_final :
  forall n m anchor next before output output_grid candidate first i j color
      side candidate_side,
    1 <= n -> 1 <= m ->
    anchor = i * m + j -> anchor < first < next ->
    GreedyPlacementTrace n m anchor before ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= i < n -> 0 <= j < m ->
    65 <= color ->
    CanPlace before n m i j side color ->
    1 <= candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    side < candidate_side ->
    first = i * m + (j + side) ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    (forall z,
      0 <= fst z < n -> 0 <= snd z < m ->
      (SameColorPath candidate (i, j) z <->
       i <= fst z < i + candidate_side /\
       j <= snd z < j + candidate_side)) ->
    Znth (i * m + j) output 0 = color ->
    CanPlace before n m i j (side + 1) color.
Proof.
  intros n m anchor next before output output_grid candidate first i j color
    side candidate_side Hn Hm Hanchor Hrange Hbefore Houtput Hrows Hcandidate
    Hi Hj Hcolor Hplace Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt
    Hfirst Hprefix Hcomponent Houtanchor.
  pose proof Hplace as Hplace_full.
  destruct Hplace as [Hside [Hibound [Hjbound
    [Hempty [Hhorizontal Hvertical]]]]].
  unfold CanPlace.
  split; [lia |]. split; [lia |]. split; [lia |].
  split.
  - intros r q Hr Hq.
    exact (extension_candidate_square_empty__solver_final n m anchor next
      before output output_grid candidate first i j color side candidate_side
      Hn Hm Hanchor Hrange Hbefore Houtput Hrows Hcandidate Hi Hj Hplace_full
      Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
      Hcomponent r q ltac:(lia) ltac:(lia)).
  - split.
    + intros q Hq. split.
      * intro Hitop.
        destruct (Z.lt_ge_cases q (j + side)) as [Hqold | Hqnew].
        -- exact (proj1 (Hhorizontal q ltac:(lia)) Hitop).
        -- assert (Hqeq : q = j + side) by lia. subst q.
           intro Hmatch. exfalso.
           exact (candidate_boundary_cell_cannot_match__solver_final n m anchor
             next before output output_grid candidate first i j color side
             candidate_side (i - 1, j + side) (i, j + side) Hn Hm Hanchor
             Hrange Hbefore Houtput Hrows Hcandidate Hi Hj Hside Hibound Hjbound
             Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
             Hcomponent Hcolor Houtanchor Hmatch ltac:(simpl; lia)
             ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; lia)
             ltac:(simpl; lia) ltac:(simpl; lia)
             ltac:(unfold AdjCell; simpl; lia)).
      * intros Hibottom Hmatch. exfalso.
        exact (candidate_boundary_cell_cannot_match__solver_final n m anchor
          next before output output_grid candidate first i j color side
          candidate_side (i + side + 1, q) (i + side, q) Hn Hm Hanchor Hrange
          Hbefore Houtput Hrows Hcandidate Hi Hj Hside Hibound Hjbound
          Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
          Hcomponent Hcolor Houtanchor
          ltac:(simpl; replace ((i + side + 1) * m + q) with
            ((i + (side + 1)) * m + q) by ring; exact Hmatch)
          ltac:(simpl; lia)
          ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; lia)
          ltac:(simpl; lia) ltac:(simpl; lia)
          ltac:(unfold AdjCell; simpl; lia)).
    + intros r Hr. split.
      * intro Hileft.
        destruct (Z.lt_ge_cases r (i + side)) as [Hrold | Hrnew].
        -- exact (proj1 (Hvertical r ltac:(lia)) Hileft).
        -- assert (Hreq : r = i + side) by lia. subst r.
           intro Hmatch. exfalso.
           exact (candidate_boundary_cell_cannot_match__solver_final n m anchor
             next before output output_grid candidate first i j color side
             candidate_side (i + side, j - 1) (i + side, j) Hn Hm Hanchor
             Hrange Hbefore Houtput Hrows Hcandidate Hi Hj Hside Hibound Hjbound
             Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
             Hcomponent Hcolor Houtanchor
             ltac:(simpl; replace ((i + side) * m + (j - 1)) with
               ((i + side) * m + j - 1) by ring; exact Hmatch)
             ltac:(simpl; lia)
             ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; lia)
             ltac:(simpl; lia) ltac:(simpl; lia)
             ltac:(unfold AdjCell; simpl; lia)).
      * intros Hiright Hmatch. exfalso.
        exact (candidate_boundary_cell_cannot_match__solver_final n m anchor
          next before output output_grid candidate first i j color side
          candidate_side (r, j + side + 1) (r, j + side) Hn Hm Hanchor Hrange
          Hbefore Houtput Hrows Hcandidate Hi Hj Hside Hibound Hjbound
          Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hfirst Hprefix
          Hcomponent Hcolor Houtanchor
          ltac:(simpl; replace (r * m + (j + side + 1)) with
            (r * m + j + (side + 1)) by ring; exact Hmatch)
          ltac:(simpl; lia)
          ltac:(simpl; lia) ltac:(simpl; lia) ltac:(simpl; lia)
          ltac:(simpl; lia) ltac:(simpl; lia)
          ltac:(unfold AdjCell; simpl; lia)).
Qed.
Lemma extend_exchange_from_ih__solver_final :
  forall n m next output output_grid candidate first lower target q anchor
      before painted i j side candidate_side,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    first < next ->
    65 <= lower ->
    Znth first (Flatten candidate) 0 = lower ->
    first = fst target * m + snd target ->
    anchor = i * m + j ->
    anchor < first ->
    GreedyPlacementTrace n m anchor before ->
    SettledSquareState before n m i j lower side ->
    PaintRectanglePrefix before painted m i j side lower (side * side) ->
    0 <= i < n -> 0 <= j < m ->
    i <= fst q < i + side -> j <= snd q < j + side ->
    Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath output_grid q x <->
       i <= fst x < i + side /\ j <= snd x < j + side)) ->
    1 <= candidate_side ->
    i + candidate_side <= n -> j + candidate_side <= m ->
    side < candidate_side ->
    (forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath candidate (i, j) x <->
       i <= fst x < i + candidate_side /\
       j <= snd x < j + candidate_side)) ->
    i <= fst target < i + candidate_side ->
    j <= snd target < j + candidate_side ->
    (forall lower0 target0 q0 earlier origin_before painted0 oi oj oside
        other_side,
      65 <= lower0 ->
      Znth first (Flatten candidate) 0 = lower0 ->
      first = fst target0 * m + snd target0 ->
      earlier = oi * m + oj ->
      earlier < anchor ->
      GreedyPlacementTrace n m earlier origin_before ->
      SettledSquareState origin_before n m oi oj lower0 oside ->
      PaintRectanglePrefix origin_before painted0 m oi oj oside lower0
        (oside * oside) ->
      0 <= oi < n -> 0 <= oj < m ->
      oi <= fst q0 < oi + oside -> oj <= snd q0 < oj + oside ->
      Znth (snd q0) (Znth (fst q0) output_grid []) 0 = lower0 ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q0 x <->
         oi <= fst x < oi + oside /\ oj <= snd x < oj + oside)) ->
      1 <= other_side ->
      oi + other_side <= n -> oj + other_side <= m ->
      oside < other_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (oi, oj) x <->
         oi <= fst x < oi + other_side /\
         oj <= snd x < oj + other_side)) ->
      oi <= fst target0 < oi + other_side ->
      oj <= snd target0 < oj + other_side ->
      Znth first output 0 <= lower0) ->
    Znth first output 0 <= lower.
Proof.
  intros n m next output output_grid candidate first lower target q anchor
    before painted i j side candidate_side Hn Hm Houtput Hrows Hcandidate
    Hprefix Hfirst_next Hlower Hcandfirst Hfirst Hanchor Hearlier Hbefore Hsettled Hpaint
    Hi Hj Hqi Hqj Hqcolor Hcomponent Hcandidate_side Hcandidate_i
    Hcandidate_j Hside_lt Hcandcomponent Htarget_i Htarget_j Hextend.
  destruct (Z_le_gt_dec (Znth first output 0) lower) as [Hdone | Hgreater];
    [exact Hdone |].
  assert (Houtdiff : Znth first output 0 <> lower) by lia.
  pose proof Hsettled as Hsettled_full.
  destruct Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
  destruct Hplace as [Hside [Hibound [Hjbound Hplace_rest]]].
  assert (Htarget_row : 0 <= fst target < n) by lia.
  assert (Htarget_col : 0 <= snd target < m) by lia.
  assert (Hgrid_len : Zlength output_grid = n) by
    (destruct Hrows as [? [? ?]]; assumption).
  assert (Hrow_len : Zlength (Znth 0 output_grid []) = m).
  { destruct Hrows as [Hgl [Hrl Hfl]]. rewrite Forall_forall in Hrl.
    apply Hrl, Znth_In_range__solver_final. rewrite Hgl. lia. }
  assert (Hcomponent_anchor : forall x,
      0 <= fst x < n -> 0 <= snd x < m ->
      (SameColorPath output_grid (i, j) x <->
       i <= fst x < i + side /\ j <= snd x < j + side)).
  { intros x Hxrow Hxcol.
    eapply exact_component_reanchor__solver_final with
      (p := q) (r := i) (c := j) (side := side); eauto; simpl; lia. }
  assert (Houtanchor : Znth (i * m + j) output 0 = lower).
  { rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid i j
      Hrows Hi Hj).
    assert (Hpath : SameColorPath output_grid q (i, j)).
    { apply (proj2 (Hcomponent (i, j) ltac:(simpl; lia)
        ltac:(simpl; lia))). simpl. split; lia. }
    transitivity (Znth (snd q) (Znth (fst q) output_grid []) 0).
    - exact (same_color_path_endpoint_color__solver_final output_grid q
        (i, j) Hpath).
    - exact Hqcolor. }
  assert (Hfrontier_eq : first = i * m + (j + side)).
  { exact (extend_first_is_frontier__solver_final n m output output_grid
      candidate first target i j lower side candidate_side Hn Hm Hrows
      Hcandidate Hi Hj Hside Hibound Hjbound Hside_lt Hcandidate_i
      Hcandidate_j Htarget_row Htarget_col Hfirst Htarget_i Htarget_j
      ltac:(lia) Hprefix Houtanchor Hcandfirst Houtdiff Hcomponent_anchor
      Hcandcomponent). }
  assert (Hanchor_zero : Znth anchor before 0 = 0).
  { rewrite Hanchor. destruct Hplace_rest as [Hempty Hboundaries].
    apply Hempty; lia. }
  destruct Hstop as [Hboundary | [Hcannot | [fallback [Hfallback Hfallback_le]]]].
  - exfalso. lia.
  - exfalso. apply Hcannot.
    exact (extension_candidate_can_place__solver_final n m anchor next before
      output output_grid candidate first i j lower side candidate_side Hn Hm
      Hanchor ltac:(split; [exact Hearlier | exact Hfirst_next]) Hbefore Houtput Hrows
      Hcandidate Hi Hj Hlower ltac:(unfold CanPlace; tauto) Hcandidate_side
      Hcandidate_i Hcandidate_j Hside_lt Hfrontier_eq Hprefix Hcandcomponent
      Houtanchor).
  - exact (extend_fallback_from_ih__solver_final n m anchor next before painted
      output output_grid candidate first target q i j lower side candidate_side
      fallback Hn Hm Hanchor
      ltac:(split; [exact Hearlier | exact Hfirst_next]) Hbefore
      Houtput Hrows Hcandidate Hfirst Htarget_row Htarget_col Hi Hj
      Hsettled_full Hanchor_zero Hpaint Hqi Hqj Hqcolor Hcomponent
      Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hcandcomponent
      Htarget_i Htarget_j Hprefix Hcandfirst Houtdiff Hfallback Hfallback_le
      Hextend).
(* end of fallback helper *)
Qed.
Lemma extend_exchange__solver_final :
  forall n m next output output_grid candidate first,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    first < next ->
    forall anchor, 0 <= anchor ->
    forall lower target q before painted i j side candidate_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      anchor = i * m + j ->
      anchor < first ->
      GreedyPlacementTrace n m anchor before ->
      SettledSquareState before n m i j lower side ->
      PaintRectanglePrefix before painted m i j side lower (side * side) ->
      0 <= i < n -> 0 <= j < m ->
      i <= fst q < i + side -> j <= snd q < j + side ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         i <= fst x < i + side /\ j <= snd x < j + side)) ->
      1 <= candidate_side ->
      i + candidate_side <= n -> j + candidate_side <= m ->
      side < candidate_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (i, j) x <->
         i <= fst x < i + candidate_side /\
         j <= snd x < j + candidate_side)) ->
      i <= fst target < i + candidate_side ->
      j <= snd target < j + candidate_side ->
      Znth first output 0 <= lower.
Proof.
  intros n m next output output_grid candidate first Hn Hm Houtput Hrows
    Hcandidate Hprefix Hfirst_next.
+  refine (nonnegative_anchor_strong_induction__solver_final
    (fun anchor => forall lower target q before painted i j side candidate_side,
      65 <= lower ->
      Znth first (Flatten candidate) 0 = lower ->
      first = fst target * m + snd target ->
      anchor = i * m + j ->
      anchor < first ->
      GreedyPlacementTrace n m anchor before ->
      SettledSquareState before n m i j lower side ->
      PaintRectanglePrefix before painted m i j side lower (side * side) ->
      0 <= i < n -> 0 <= j < m ->
      i <= fst q < i + side -> j <= snd q < j + side ->
      Znth (snd q) (Znth (fst q) output_grid []) 0 = lower ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath output_grid q x <->
         i <= fst x < i + side /\ j <= snd x < j + side)) ->
      1 <= candidate_side ->
      i + candidate_side <= n -> j + candidate_side <= m ->
      side < candidate_side ->
      (forall x,
        0 <= fst x < n -> 0 <= snd x < m ->
        (SameColorPath candidate (i, j) x <->
         i <= fst x < i + candidate_side /\
         j <= snd x < j + candidate_side)) ->
      i <= fst target < i + candidate_side ->
      j <= snd target < j + candidate_side ->
      Znth first output 0 <= lower) _).
  intros anchor Hanchor_nonneg IH lower target q before painted i j side
    candidate_side Hlower Hcandfirst Hfirst Hanchor Hearlier Hbefore Hsettled
    Hpaint Hi Hj Hqi Hqj Hqcolor Hcomponent Hcandidate_side Hcandidate_i
    Hcandidate_j Hside_lt Hcandcomponent Htarget_i Htarget_j.
  eapply (extend_exchange_from_ih__solver_final n m next output output_grid
    candidate first lower target q anchor before painted i j side candidate_side
    Hn Hm Houtput Hrows Hcandidate Hprefix Hfirst_next Hlower Hcandfirst Hfirst
    Hanchor Hearlier Hbefore Hsettled Hpaint Hi Hj Hqi Hqj Hqcolor Hcomponent
    Hcandidate_side Hcandidate_i Hcandidate_j Hside_lt Hcandcomponent Htarget_i
    Htarget_j).
  intros lower0 target0 q0 earlier origin_before painted0 oi oj oside other_side
    Hlower0 Hcandlower Htarget0 Hearlier_eq Hearlier_bound Htrace0 Hsettled0
    Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor0 Hcomponent0 Hother_side Hother_i Hother_j
    Hcross Hcandidate0 Htarget0_i Htarget0_j.
  eapply (IH earlier); try eassumption; try lia.
Qed.
Lemma first_difference_bound__solver_final :
  forall n m next output output_grid candidate first,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    RowsOfFlat n m output output_grid ->
    SquareTiling n m candidate ->
    0 <= first < next ->
    (forall k, 0 <= k < first ->
      Znth k output 0 = Znth k (Flatten candidate) 0) ->
    Znth first output 0 <= Znth first (Flatten candidate) 0.
Proof.
  intros n m next output output_grid candidate first Hn Hm Htrace Hrows
    Hcandidate Hfirst_range Hprefix.
  destruct (Z.eq_dec (Znth first output 0)
      (Znth first (Flatten candidate) 0)) as [Heq | Hdiff]; [lia |].
  destruct (trace_bounds_and_canonical__solver_final n m next output Hn Hm
    Htrace) as [Hnext_bound [Houtlen [Hcanonical Hcolored]]].
  assert (Hfirst_flat : 0 <= first < n * m) by lia.
  set (p := (first / m, first mod m)).
  assert (Hp_row : 0 <= fst p < n).
  { unfold p; simpl. split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (Hp_col : 0 <= snd p < m).
  { unfold p; simpl. apply Z.mod_pos_bound. lia. }
  assert (Hfirst : first = fst p * m + snd p).
  { unfold p; simpl. pose proof (Z.div_mod first m ltac:(lia)). nia. }
  assert (Hgrid_nonzero :
      Znth (snd p) (Znth (fst p) output_grid []) 0 <> 0).
  { rewrite (rows_of_flat_Znth__solver_final n m output output_grid (fst p)
      (snd p) Hrows Hp_row Hp_col).
    rewrite <- Hfirst. specialize (Hcolored first Hfirst_range). lia. }
  destruct (trace_colored_component_origin__solver_final n m next output
    output_grid p Hn Hm Htrace Hrows Hp_row Hp_col Hgrid_nonzero) as
    [anchor [before [painted [i [j [color [side Horigin]]]]]]].
  destruct Horigin as [Hanchor [Hanchor_next [Hbefore [Hsettled [Hpaint
    [Hi [Hj [Hpi [Hpj [Hpcolor [Hcomponent Hpersist]]]]]]]]]]].
  pose proof Hsettled as [[Hleast [Hplace Hprevious]] Hstop].
  destruct Hplace as [Hside [Hibound [Hjbound Hplace_rest]]].
  assert (Houtfirst : Znth first output 0 = color).
  { rewrite Hfirst.
    rewrite <- (rows_of_flat_Znth__solver_final n m output output_grid (fst p)
      (snd p) Hrows Hp_row Hp_col). exact Hpcolor. }
  assert (Hanchor_le : anchor <= first).
  { rewrite Hanchor, Hfirst.
    eapply square_anchor_le_member__solver_final; eauto; lia. }
  destruct (first_cell_component_dichotomy__solver_final n m output candidate
    output_grid first p anchor i j color side Hn Hm Hrows Hcandidate Hp_row
    Hp_col Hfirst Hanchor Hi Hj Hside Hibound Hjbound Hpi Hpj Houtfirst
    Hcomponent Hanchor_le Hprefix Hdiff) as
    [Horigin_first | [candidate_side [Hcandidate_side [Hcandidate_i
      [Hcandidate_j [Hcandidate_short [Hp_i [Hp_j Hcandcomponent]]]]]]]].
  - eapply (base_exchange_from_extend_ih__solver_final n m next output
      output_grid candidate first before i j color side Hn Hm Htrace Hrows
      Hcandidate Hfirst_range ltac:(rewrite <- Horigin_first; exact Hanchor)
      Hi Hj ltac:(rewrite <- Horigin_first; exact Hbefore) Hsettled Houtfirst
      Hprefix).
    intros lower target q earlier origin_before painted0 oi oj oside other_side
      Hlower Hcandlower Htarget Hearlier Hearlier_bound Htrace0 Hsettled0
      Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor Hcomponent0 Hother_side Hother_i
      Hother_j Hcross Hcandidate0 Htarget_i Htarget_j.
    exact (extend_exchange__solver_final n m next output output_grid candidate
      first Hn Hm Htrace Hrows Hcandidate Hprefix (proj2 Hfirst_range) earlier
      ltac:(rewrite Hearlier; nia) lower target q origin_before painted0 oi oj
      oside other_side Hlower Hcandlower Htarget Hearlier ltac:(lia) Htrace0
      Hsettled0 Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor Hcomponent0 Hother_side
      Hother_i Hother_j Hcross Hcandidate0 Htarget_i Htarget_j).
  - eapply (shrink_exchange_from_extend_ih__solver_final n m anchor next output
      output_grid candidate first before i j color side candidate_side Hn Hm
      Htrace Hrows Hcandidate Hanchor ltac:(split; [rewrite Hanchor; nia | lia])
      Hi Hj Hbefore Hsettled ltac:(lia)
      ltac:(rewrite Hfirst, Hp_i, Hp_j; reflexivity) Houtfirst Hprefix).
    intros lower target q earlier origin_before painted0 oi oj oside other_side
      Hlower Hcandlower Htarget Hearlier Hearlier_bound Htrace0 Hsettled0
      Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor Hcomponent0 Hother_side Hother_i
      Hother_j Hcross Hcandidate0 Htarget_i Htarget_j.
    exact (extend_exchange__solver_final n m next output output_grid candidate
      first Hn Hm Htrace Hrows Hcandidate Hprefix (proj2 Hfirst_range) earlier
      ltac:(rewrite Hearlier; nia) lower target q origin_before painted0 oi oj
      oside other_side Hlower Hcandlower Htarget Hearlier ltac:(lia) Htrace0
      Hsettled0 Hpaint0 Hoi Hoj Hqoi Hqoj Hqcolor Hcomponent0 Hother_side
      Hother_i Hother_j Hcross Hcandidate0 Htarget_i Htarget_j).
Qed.
Lemma greedy_trace_lex__solver_final :
  forall n m next output candidate,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next output ->
    SquareTiling n m candidate ->
    LexPrefixLe next output (Flatten candidate).
Proof.
  intros n m next output candidate Hn Hm Htrace Hcandidate.
  destruct (trace_bounds_and_canonical__solver_final n m next output Hn Hm
    Htrace) as [Hnext [Hlen Hrest]].
  destruct (rows_of_flat_from_length__solver_final n m output Hn Hm Hlen) as
    [output_grid Hrows].
  apply local_first_difference_implies_lex__solver_final; [lia |].
  intros first Hfirst Hprefix.
  exact (first_difference_bound__solver_final n m next output output_grid
    candidate first Hn Hm Htrace Hrows Hcandidate Hfirst Hprefix).
Qed.
Lemma greedy_trace_implies_partial_tiling__solver_final :
  forall n m next flat,
    1 <= n -> 1 <= m ->
    GreedyPlacementTrace n m next flat ->
    PartialTilingState n m next flat.
Proof.
  intros n m next flat Hn Hm Htrace.
  apply (greedy_trace_partial_from_lex__solver_final n m next flat Hn Hm
    Htrace).
  intros candidate Hcandidate.
  exact (greedy_trace_lex__solver_final n m next flat candidate Hn Hm Htrace
    Hcandidate).
Qed.
