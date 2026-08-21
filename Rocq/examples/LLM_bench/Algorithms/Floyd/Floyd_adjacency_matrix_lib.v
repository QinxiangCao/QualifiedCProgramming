Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
From SimpleC.EE.LLM_bench.Algorithms.Floyd Require Export concrete_graphs.
From MonadLib Require Import MonadLib.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelMonad.
From RecordUpdate Require Import RecordUpdate.
From MaxMinLib Require Import Interface.
Require Import Algorithms.MapLib.
Require Import Algorithms.Floyd.Floyd.
From GraphLib Require Import graph_basic path path_basic epath Zweight.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope map_scope.
Import naive_C_Rules.
Local Open Scope sac.

Module FloydAdjacencyMatrix2Darray.

Definition state : Type := @St Z.

Definition floyd_update_dist (i j k : Z) : program state unit :=
  @update_dist Z FloydGraph.edge_eqdec i j k.

Definition floyd_j_from
    (g : FloydGraph.G) (n k i j : Z) : program state unit :=
  range_iter j n
    (fun j _ => floyd_update_dist i j k)
    tt.

Definition floyd_i_from
    (g : FloydGraph.G) (n k i : Z) : program state unit :=
  range_iter i n
    (fun i _ => floyd_j_from g n k i 0)
    tt.

Definition floyd_k_from
    (g : FloydGraph.G) (n k : Z) : program state unit :=
  range_iter k n
    (fun k _ => floyd_i_from g n k 0)
    tt.

Definition floyd_k_after
    (g : FloydGraph.G) (n k : Z) : unit -> program state unit :=
  fun _ => floyd_k_from g n (k + 1).

Definition floyd_i_k_from
    (g : FloydGraph.G) (n k i : Z) : program state unit :=
  bind (floyd_i_from g n k i) (floyd_k_after g n k).

Definition floyd_i_k_after
    (g : FloydGraph.G) (n k i : Z) : unit -> program state unit :=
  fun _ => floyd_i_k_from g n k (i + 1).

Definition floyd_j_i_k_from
    (g : FloydGraph.G) (n k i j : Z) : program state unit :=
  bind (floyd_j_from g n k i j) (floyd_i_k_after g n k i).

Definition floyd_indexed_program
    (g : FloydGraph.G) (n : Z) : program state unit :=
  floyd_k_from g n 0.

Definition matrix_distance (rows : list (list Z)) (u v : Z) : option Z :=
  FloydGraph.matrix_distance rows u v.
 
(* function *)
Definition state_of_matrix (rows : list (list Z)) : state :=
  @mkSt Z (fun uv => matrix_distance rows (fst uv) (snd uv)).

Definition storage_index (i : Z) : Prop :=
  0 <= i < FloydGraph.max_vertices.

Definition physical_cell (rows : list (list Z)) (u v : Z) : Z :=
  Znth v (Znth u rows nil) FloydGraph.infinity.

(** Abstract Floyd distances are nonnegative.  [None] is infinity; a finite
    abstract value at or above the physical sentinel is observed as the same
    infinity cell. *)
Definition abstract_distance_nonnegative (d : option Z) : Prop :=
  match d with
  | Some z => 0 <= z
  | None => True
  end.

Definition distance_as_observed_cell (d : option Z) : Z :=
  match d with
  | Some z =>
      if Z_lt_dec z FloydGraph.infinity
      then z
      else FloydGraph.infinity
  | None => FloydGraph.infinity
  end.

(** Only valid physical matrix coordinates are observable.  This guard keeps
    [Znth]'s default/negative-index behavior outside the representation
    boundary, while exact finite values and saturated infinity remain related
    inside the fixed-capacity matrix. *)
Definition state_model (rows : list (list Z)) (s : state) : Prop :=
  forall u v,
    storage_index u ->
    storage_index v ->
    abstract_distance_nonnegative (@dist Z s (u, v)) /\
    physical_cell rows u v =
      distance_as_observed_cell (@dist Z s (u, v)).

Definition matrix_model (g : FloydGraph.G) (rows : list (list Z)) : Prop :=
  FloydGraph.matrix_graph_model g rows.

Definition matrix_shape (rows : list (list Z)) : Prop :=
  FloydGraph.matrix_shape FloydGraph.max_vertices rows.

Definition matrix_values_safe (rows : list (list Z)) : Prop :=
  forall i j,
    storage_index i ->
    storage_index j ->
    0 <= physical_cell rows i j <= FloydGraph.infinity.

Definition graph_storage_size (_ : FloydGraph.G) : Z :=
  FloydGraph.max_vertices.

Definition graph_matrix_model
    (g : FloydGraph.G) (rows : list (list Z)) : Prop :=
  matrix_model g rows /\
  matrix_shape rows /\
  matrix_values_safe rows.

Definition matrix_storage_size : Z :=
  FloydGraph.max_vertices.

Definition matrix_rows_model (rows : list (list Z)) : Prop :=
  matrix_shape rows /\ matrix_values_safe rows.

Lemma matrix_values_safe_Znth_default :
  forall rows default_row r c,
    matrix_shape rows ->
    matrix_values_safe rows ->
    (0 <= r < FloydGraph.max_vertices /\ 0 <= c) /\
      c < FloydGraph.max_vertices ->
    0 <= Znth c (Znth r rows default_row) 0 <= FloydGraph.infinity.
Proof.
  intros rows default_row r c Hshape Hsafe [[Hr Hc0] Hcmax].
  pose proof Hshape as Hshape_bounds.
  unfold matrix_shape, FloydGraph.matrix_shape in Hshape_bounds.
  destruct Hshape_bounds as [Hrows_length Hrow_length].
  pose proof
    (Hsafe r c ltac:(unfold storage_index; lia)
      ltac:(unfold storage_index; lia)) as Hcell.
  unfold matrix_values_safe, physical_cell in Hsafe.
  unfold physical_cell in Hcell.
  rewrite (Znth_indep rows r default_row nil) by
    (rewrite Hrows_length; lia).
  rewrite (Znth_indep (Znth r rows nil) c 0 FloydGraph.infinity) by
    (rewrite Hrow_length; lia).
  exact Hcell.
Qed.

Definition valid_size (n : Z) : Prop :=
  0 <= n <= FloydGraph.max_vertices.

Definition graph_has_size (g : FloydGraph.G) (n : Z) : Prop :=
  FloydGraph.vertex_count g = n /\ valid_size n.

Definition floyd_no_negative_cycle
    (g : FloydGraph.G) : Prop :=
  forall u p,
    @valid_epath FloydGraph.G FloydGraph.V FloydGraph.E
      FloydGraph.graph_instance FloydGraph.gvalid_instance
      FloydGraph.PathData FloydGraph.path_instance g u p u ->
    Z_op_le (Some 0)
      (@epath_weight FloydGraph.G FloydGraph.E
        FloydGraph.weight_instance g p).

Definition floyd_nonnegative_edges
    (g : FloydGraph.G) : Prop :=
  forall e,
    FloydGraph.edge_valid g e ->
    Z_op_le (Some 0)
      (@weight FloydGraph.G FloydGraph.E
        FloydGraph.weight_instance g e).

Definition floyd_initial_state
    (g : FloydGraph.G) (s : state) : Prop :=
  @initialized_state FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance FloydGraph.gvalid_instance
    g FloydGraph.PathData FloydGraph.path_instance
    FloydGraph.weight_instance s.

Definition floyd_shortest_state
    (g : FloydGraph.G) (s : state) : Prop :=
  @distance_correct FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance FloydGraph.gvalid_instance
    g FloydGraph.PathData FloydGraph.path_instance
    FloydGraph.weight_instance s.

Definition floyd_init_matrix
    (g : FloydGraph.G) (rows : list (list Z)) : Prop :=
  floyd_initial_state g (state_of_matrix rows).

Definition floyd_shortest_matrix
    (g : FloydGraph.G) (rows : list (list Z)) : Prop :=
  matrix_shape rows /\
  matrix_values_safe rows /\
  exists s : state,
    state_model rows s /\
    floyd_shortest_state g s.

Lemma matrix_model_nonnegative_edges :
  forall g rows,
    matrix_model g rows ->
    matrix_values_safe rows ->
    floyd_nonnegative_edges g.
Proof.
  intros g rows Hmodel Hsafe [u v] Hedge_valid.
  destruct Hmodel as [Hwf [_ [_ Hedge_weight]]].
  simpl.
  unfold FloydGraph.edge_valid, FloydGraph.graph_step in Hedge_valid.
  simpl in Hedge_valid.
  destruct Hedge_valid as [Hu [Hv _]].
  rewrite (Hedge_weight u v Hu Hv).
  unfold matrix_distance, FloydGraph.matrix_distance,
    FloydGraph.cell_as_distance.
  assert (Hu_storage : storage_index u).
  {
    unfold storage_index, FloydGraph.vertex_valid,
      FloydGraph.graph_wf in *.
    lia.
  }
  assert (Hv_storage : storage_index v).
  {
    unfold storage_index, FloydGraph.vertex_valid,
      FloydGraph.graph_wf in *.
    lia.
  }
  pose proof Hsafe u v Hu_storage Hv_storage as Hcell.
  unfold physical_cell in Hcell.
  destruct (Z.eq_dec (Znth v (Znth u rows nil) FloydGraph.infinity)
              FloydGraph.infinity); simpl; lia.
Qed.

Lemma floyd_nonnegative_edges_no_negative_cycle :
  forall g,
    floyd_nonnegative_edges g ->
    floyd_no_negative_cycle g.
Proof.
  unfold floyd_no_negative_cycle.
  intros g Hedges.
  assert (Hnonnegative_path:
    forall u p v,
      @valid_epath FloydGraph.G FloydGraph.V FloydGraph.E
        FloydGraph.graph_instance FloydGraph.gvalid_instance
        FloydGraph.PathData FloydGraph.path_instance g u p v ->
      Z_op_le (Some 0)
        (@epath_weight FloydGraph.G FloydGraph.E
          FloydGraph.weight_instance g p)).
  {
    intros u p.
    revert u.
    induction p as [| e p IHp]; intros u v Hpath.
    - unfold epath_weight. simpl. lia.
    - apply (@valid_epath_cons_inv
        FloydGraph.G FloydGraph.V FloydGraph.E
        FloydGraph.graph_instance FloydGraph.gvalid_instance
        FloydGraph.PathData FloydGraph.path_instance
        FloydGraph.empty_path_instance FloydGraph.single_path_instance
        FloydGraph.concat_path_instance FloydGraph.destruct1n_path_instance
        g u e p v) in Hpath as [w [Hstep Htail]].
      rewrite epath_weight_cons.
      pose proof (IHp w v Htail) as Htail_nonneg.
      pose proof
        (@step_evalid FloydGraph.G FloydGraph.V FloydGraph.E
          FloydGraph.graph_instance FloydGraph.gvalid_instance
          FloydGraph.stepvalid_instance g e u w Hstep)
        as Hedge_valid.
      pose proof Hedges e Hedge_valid as Hedge_nonneg.
      destruct (@epath_weight FloydGraph.G FloydGraph.E
        FloydGraph.weight_instance g p);
        destruct (@weight FloydGraph.G FloydGraph.E
          FloydGraph.weight_instance g e);
        simpl in *; lia.
  }
  intros u p Hpath.
  exact (Hnonnegative_path u p u Hpath).
Qed.

Lemma floyd_update_matrix_bridge :
  forall (rows : list (list Z)) (i j k n : Z)
         (default_row : list Z) (g : FloydGraph.G)
         (X : unit -> state -> Prop),
    0 <= n ->
    n <= FloydGraph.max_vertices ->
    0 <= k -> k < n ->
    0 <= i -> i < n ->
    0 <= j -> j < n ->
    Znth k (Znth i rows default_row) 0 +
      Znth j (Znth k rows default_row) 0 <
      Znth j (Znth i rows default_row) 0 ->
    Znth j (Znth k rows default_row) 0 < FloydGraph.infinity ->
    Znth k (Znth i rows default_row) 0 < FloydGraph.infinity ->
    matrix_shape rows ->
    matrix_values_safe rows ->
    safeExec (state_model rows)
      (x <- floyd_update_dist i j k ;;
       x0 <- range_iter (j + 1) n
               (fun (j : Z) (_ : unit) => floyd_update_dist i j k) x ;;
       floyd_i_k_after g n k i x0) X ->
    let updated_rows :=
      replace_Znth i
        (replace_Znth j
          (Znth k (Znth i rows default_row) 0 +
           Znth j (Znth k rows default_row) 0)
          (Znth i rows default_row))
        rows in
    matrix_values_safe updated_rows /\
    matrix_shape updated_rows /\
    safeExec (state_model updated_rows)
      (floyd_j_i_k_from g n k i (j + 1)) X.
Proof.
  intros rows i j k n default_row g X Hn0 Hnmax Hk0 Hkn Hi0 Hin
    Hj0 Hjn Himprove Hkj_lt Hik_lt Hshape Hvalues Hexec.
  unfold FloydGraph.max_vertices in Hnmax.
  set (ik := Znth k (Znth i rows default_row) 0).
  set (kj := Znth j (Znth k rows default_row) 0).
  set (ij := Znth j (Znth i rows default_row) 0).
  set (updated_rows :=
    replace_Znth i (replace_Znth j (ik + kj) (Znth i rows default_row))
      rows).
  assert (Hi : storage_index i) by
    (unfold storage_index, FloydGraph.max_vertices; lia).
  assert (Hj : storage_index j) by
    (unfold storage_index, FloydGraph.max_vertices; lia).
  assert (Hk : storage_index k) by
    (unfold storage_index, FloydGraph.max_vertices; lia).
  pose proof Hshape as Hshape_bounds.
  unfold matrix_shape, FloydGraph.matrix_shape, FloydGraph.max_vertices in
    Hshape_bounds.
  destruct Hshape_bounds as [Hrows_length Hrow_length].
  assert (Hdefault_cell:
    forall r c d,
      storage_index r ->
      storage_index c ->
      Znth c (Znth r rows d) 0 = physical_cell rows r c).
  {
    intros r c d Hr Hc.
    unfold physical_cell.
    rewrite (Znth_indep rows r d nil) by
      (rewrite Hrows_length; unfold storage_index, FloydGraph.max_vertices in *; lia).
    rewrite (Znth_indep (Znth r rows nil) c 0 FloydGraph.infinity) by
      (rewrite Hrow_length; unfold storage_index, FloydGraph.max_vertices in *; lia).
    reflexivity.
  }
  assert (Hik_cell : physical_cell rows i k = ik) by
    (symmetry; subst ik; apply Hdefault_cell; auto).
  assert (Hkj_cell : physical_cell rows k j = kj) by
    (symmetry; subst kj; apply Hdefault_cell; auto).
  assert (Hij_cell : physical_cell rows i j = ij) by
    (symmetry; subst ij; apply Hdefault_cell; auto).
  pose proof (Hvalues i k Hi Hk) as Hik_bounds.
  pose proof (Hvalues k j Hk Hj) as Hkj_bounds.
  pose proof (Hvalues i j Hi Hj) as Hij_bounds.
  rewrite Hik_cell in Hik_bounds.
  rewrite Hkj_cell in Hkj_bounds.
  rewrite Hij_cell in Hij_bounds.
  assert (Hsum_bounds : 0 <= ik + kj < FloydGraph.infinity) by lia.
  assert (Hupdated_shape : matrix_shape updated_rows).
  {
    subst updated_rows.
    unfold matrix_shape, FloydGraph.matrix_shape, FloydGraph.max_vertices.
    split.
    - rewrite Zlength_replace_Znth. exact Hrows_length.
    - intros r Hr.
      destruct (Z.eq_dec r i) as [-> | Hri].
      + rewrite Znth_replace_Znth_Same by (rewrite Hrows_length; lia).
        rewrite (Znth_indep rows i default_row nil) by
          (rewrite Hrows_length; lia).
        rewrite Zlength_replace_Znth.
        apply Hrow_length. lia.
      + rewrite Znth_replace_Znth_Diff by (try rewrite Hrows_length; lia).
        apply Hrow_length. lia.
  }
  assert (Hupdated_cell_same :
    physical_cell updated_rows i j = ik + kj).
  {
    subst updated_rows.
    unfold physical_cell.
    rewrite Znth_replace_Znth_Same by (rewrite Hrows_length; lia).
    rewrite Znth_replace_Znth_Same by
      (rewrite (Znth_indep rows i default_row nil) by
        (rewrite Hrows_length; unfold storage_index, FloydGraph.max_vertices in *; lia);
       rewrite Hrow_length; unfold storage_index, FloydGraph.max_vertices in *; lia).
    reflexivity.
  }
  assert (Hupdated_cell_diff :
    forall r c,
      storage_index r ->
      storage_index c ->
      (r <> i \/ c <> j) ->
      physical_cell updated_rows r c = physical_cell rows r c).
  {
    intros r c Hr Hc Hdiff.
    subst updated_rows.
    unfold physical_cell.
    destruct (Z.eq_dec r i) as [Hr_eq | Hr_ne].
    - subst r.
      rewrite Znth_replace_Znth_Same by (rewrite Hrows_length; lia).
      rewrite Znth_replace_Znth_Diff by
        (try rewrite (Znth_indep rows i default_row nil) by
          (rewrite Hrows_length; unfold storage_index, FloydGraph.max_vertices in *; lia);
         try rewrite Hrow_length; unfold storage_index, FloydGraph.max_vertices in *; lia).
      rewrite (Znth_indep rows i default_row nil) by
        (rewrite Hrows_length; unfold storage_index, FloydGraph.max_vertices in *; lia).
      reflexivity.
    - rewrite Znth_replace_Znth_Diff by
        (unfold storage_index, FloydGraph.max_vertices in *;
         try rewrite Hrows_length; lia).
      reflexivity.
  }
  assert (Hupdated_values : matrix_values_safe updated_rows).
  {
    unfold matrix_values_safe.
    intros r c Hr Hc.
    destruct (Z.eq_dec r i) as [Hr_eq | Hr_ne];
      destruct (Z.eq_dec c j) as [Hc_eq | Hc_ne].
    - subst r c. rewrite Hupdated_cell_same. lia.
    - rewrite Hupdated_cell_diff by (auto; right; auto).
      apply Hvalues; auto.
    - rewrite Hupdated_cell_diff by (auto; left; auto).
      apply Hvalues; auto.
    - rewrite Hupdated_cell_diff by (auto; left; auto).
      apply Hvalues; auto.
  }
  assert (Hstate_after_update :
    forall s0,
      state_model rows s0 ->
      state_model updated_rows
        (s0 <| dist ::= (fun dist0 =>
          @t_set FloydGraph.E (option Z) _ FloydGraph.edge_eqdec dist0 (i, j)
            (Z_op_min (dist0 (i, j))
              (Z_op_plus (dist0 (i, k)) (dist0 (k, j))))) |>)).
  {
    intros s0 Hmodel u v Hu Hv.
    pose proof (Hmodel u v Hu Hv) as [Huv_nonneg Huv_cell].
    simpl.
    unfold t_set.
    destruct (@equiv_dec FloydGraph.E eq _ FloydGraph.edge_eqdec
      (i, j) (u, v)) as [Huv_eq | Huv_neq].
    - inversion Huv_eq; subst u v; clear Huv_eq.
      pose proof (Hmodel i k Hi Hk) as [Hik_nonneg Hik_obs].
      pose proof (Hmodel k j Hk Hj) as [Hkj_nonneg Hkj_obs].
      pose proof (Hmodel i j Hi Hj) as [Hij_nonneg Hij_obs].
      rewrite Hik_cell in Hik_obs.
      rewrite Hkj_cell in Hkj_obs.
      rewrite Hij_cell in Hij_obs.
      assert (Hik_some : dist s0 (i, k) = Some ik).
      {
        destruct (dist s0 (i, k)) as [dik |] eqn:Hdik;
          unfold distance_as_observed_cell in Hik_obs; simpl in Hik_obs.
        - destruct (Z_lt_dec dik FloydGraph.infinity) as [Hdik_lt | Hdik_ge].
          + assert (dik = ik) by lia. subst dik. reflexivity.
          + lia.
        - lia.
      }
      assert (Hkj_some : dist s0 (k, j) = Some kj).
      {
        destruct (dist s0 (k, j)) as [dkj |] eqn:Hdkj;
          unfold distance_as_observed_cell in Hkj_obs; simpl in Hkj_obs.
        - destruct (Z_lt_dec dkj FloydGraph.infinity) as [Hdkj_lt | Hdkj_ge].
          + assert (dkj = kj) by lia. subst dkj. reflexivity.
          + lia.
        - lia.
      }
      split.
      + rewrite Hik_some, Hkj_some.
        unfold Z_op_plus, Z_op_min, abstract_distance_nonnegative.
        destruct (dist s0 (i, j)) as [dij |]; simpl in *; lia.
      + rewrite Hupdated_cell_same.
        rewrite Hik_some, Hkj_some.
        unfold Z_op_plus, Z_op_min.
        destruct (dist s0 (i, j)) as [dij |] eqn:Hdij.
        * unfold distance_as_observed_cell in Hij_obs.
          destruct (Z_lt_dec dij FloydGraph.infinity) as [Hdij_lt | Hdij_ge].
          -- assert (dij = ij) by lia. subst dij.
             replace (Z.min ij (ik + kj)) with (ik + kj) by lia.
             unfold distance_as_observed_cell.
             destruct (Z_lt_dec (ik + kj) FloydGraph.infinity); lia.
          -- replace (Z.min dij (ik + kj)) with (ik + kj) by lia.
             unfold distance_as_observed_cell.
             destruct (Z_lt_dec (ik + kj) FloydGraph.infinity); lia.
        * unfold distance_as_observed_cell.
          destruct (Z_lt_dec (ik + kj) FloydGraph.infinity); lia.
    - assert (Hdiff : u <> i \/ v <> j).
      {
        destruct (Z.eq_dec u i) as [Hu_eq | Hu_ne];
          destruct (Z.eq_dec v j) as [Hv_eq | Hv_ne]; auto.
        subst u v. exfalso. apply Huv_neq. reflexivity.
      }
      split.
      + exact Huv_nonneg.
      + rewrite Hupdated_cell_diff by auto.
        exact Huv_cell.
  }
  assert (Hsafe_after_update :
    safeExec
      (fun s =>
        exists s0,
          s =
            (s0 <| dist ::= (fun dist0 =>
              @t_set FloydGraph.E (option Z) _ FloydGraph.edge_eqdec dist0 (i, j)
                (Z_op_min (dist0 (i, j))
                  (Z_op_plus (dist0 (i, k)) (dist0 (k, j))))) |>) /\
          state_model rows s0)
      (x0 <- range_iter (j + 1) n
              (fun (j : Z) (_ : unit) => floyd_update_dist i j k) tt ;;
       floyd_i_k_after g n k i x0) X).
  {
    eapply safeExec_bind_reta with
      (c1 := floyd_update_dist i j k)
      (c2 := fun x =>
        x0 <- range_iter (j + 1) n
                (fun (j : Z) (_ : unit) => floyd_update_dist i j k) x ;;
        floyd_i_k_after g n k i x0)
      (a := tt)
      in Hexec.
    - exact Hexec.
    - intros X' Hupd.
      unfold floyd_update_dist in Hupd.
      apply safeExec_update' in Hupd.
      exact Hupd.
  }
  assert (Hsafe_updated :
    safeExec (state_model updated_rows)
      (x0 <- range_iter (j + 1) n
              (fun (j : Z) (_ : unit) => floyd_update_dist i j k) tt ;;
       floyd_i_k_after g n k i x0) X).
  {
    unfold safeExec in Hsafe_after_update |- *.
    destruct Hsafe_after_update as [st [[s0 [Hst Hs0]] Hsafe]].
    exists st.
    split.
    - subst st. apply Hstate_after_update. exact Hs0.
    - exact Hsafe.
  }
  split.
  - exact Hupdated_values.
  - split.
    + exact Hupdated_shape.
    + unfold floyd_j_i_k_from, floyd_j_from.
      exact Hsafe_updated.
Qed.

Lemma floyd_no_update_matrix_bridge :
  forall (rows : list (list Z)) (i j k n : Z)
         (default_row : list Z) (g : FloydGraph.G)
         (X : unit -> state -> Prop),
    0 <= n ->
    n <= FloydGraph.max_vertices ->
    0 <= k -> k < n ->
    0 <= i -> i < n ->
    0 <= j -> j < n ->
    (Znth j (Znth k rows default_row) 0 >= FloydGraph.infinity \/
     Znth k (Znth i rows default_row) 0 >= FloydGraph.infinity \/
     Znth k (Znth i rows default_row) 0 +
       Znth j (Znth k rows default_row) 0 >=
       Znth j (Znth i rows default_row) 0) ->
    matrix_shape rows ->
    matrix_values_safe rows ->
    safeExec (state_model rows)
      (x <- floyd_update_dist i j k ;;
       x0 <- range_iter (j + 1) n
               (fun (j : Z) (_ : unit) => floyd_update_dist i j k) x ;;
       floyd_i_k_after g n k i x0) X ->
    safeExec (state_model rows)
      (floyd_j_i_k_from g n k i (j + 1)) X.
Proof.
  intros rows i j k n default_row g X Hn0 Hnmax Hk0 Hkn Hi0 Hin
    Hj0 Hjn Hno_update Hshape Hvalues Hexec.
  unfold FloydGraph.max_vertices in Hnmax.
  set (ik := Znth k (Znth i rows default_row) 0).
  set (kj := Znth j (Znth k rows default_row) 0).
  set (ij := Znth j (Znth i rows default_row) 0).
  assert (Hi : storage_index i) by
    (unfold storage_index, FloydGraph.max_vertices; lia).
  assert (Hj : storage_index j) by
    (unfold storage_index, FloydGraph.max_vertices; lia).
  assert (Hk : storage_index k) by
    (unfold storage_index, FloydGraph.max_vertices; lia).
  pose proof Hshape as Hshape_bounds.
  unfold matrix_shape, FloydGraph.matrix_shape, FloydGraph.max_vertices in
    Hshape_bounds.
  destruct Hshape_bounds as [Hrows_length Hrow_length].
  assert (Hdefault_cell:
    forall r c d,
      storage_index r ->
      storage_index c ->
      Znth c (Znth r rows d) 0 = physical_cell rows r c).
  {
    intros r c d Hr Hc.
    unfold physical_cell.
    rewrite (Znth_indep rows r d nil) by
      (rewrite Hrows_length; unfold storage_index, FloydGraph.max_vertices in *; lia).
    rewrite (Znth_indep (Znth r rows nil) c 0 FloydGraph.infinity) by
      (rewrite Hrow_length; unfold storage_index, FloydGraph.max_vertices in *; lia).
    reflexivity.
  }
  assert (Hik_cell : physical_cell rows i k = ik) by
    (symmetry; subst ik; apply Hdefault_cell; auto).
  assert (Hkj_cell : physical_cell rows k j = kj) by
    (symmetry; subst kj; apply Hdefault_cell; auto).
  assert (Hij_cell : physical_cell rows i j = ij) by
    (symmetry; subst ij; apply Hdefault_cell; auto).
  pose proof (Hvalues i k Hi Hk) as Hik_bounds.
  pose proof (Hvalues k j Hk Hj) as Hkj_bounds.
  pose proof (Hvalues i j Hi Hj) as Hij_bounds.
  rewrite Hik_cell in Hik_bounds.
  rewrite Hkj_cell in Hkj_bounds.
  rewrite Hij_cell in Hij_bounds.
  assert (Hstate_after_no_update :
    forall s0,
      state_model rows s0 ->
      state_model rows
        (s0 <| dist ::= (fun dist0 =>
          @t_set FloydGraph.E (option Z) _ FloydGraph.edge_eqdec dist0 (i, j)
            (Z_op_min (dist0 (i, j))
              (Z_op_plus (dist0 (i, k)) (dist0 (k, j))))) |>)).
  {
    intros s0 Hmodel u v Hu Hv.
    pose proof (Hmodel u v Hu Hv) as [Huv_nonneg Huv_cell].
    simpl.
    unfold t_set.
    destruct (@equiv_dec FloydGraph.E eq _ FloydGraph.edge_eqdec
      (i, j) (u, v)) as [Huv_eq | Huv_neq].
    - inversion Huv_eq; subst u v; clear Huv_eq.
      pose proof (Hmodel i k Hi Hk) as [Hik_nonneg Hik_obs].
      pose proof (Hmodel k j Hk Hj) as [Hkj_nonneg Hkj_obs].
      pose proof (Hmodel i j Hi Hj) as [Hij_nonneg Hij_obs].
      rewrite Hik_cell in Hik_obs.
      rewrite Hkj_cell in Hkj_obs.
      rewrite Hij_cell in Hij_obs.
      split.
      + destruct Hno_update as [Hkj_ge | [Hik_ge | Hsum_ge]];
          destruct (dist s0 (i, k)) as [dik |] eqn:Hdik;
          destruct (dist s0 (k, j)) as [dkj |] eqn:Hdkj;
          destruct (dist s0 (i, j)) as [dij |] eqn:Hdij;
          unfold Z_op_plus, Z_op_min, abstract_distance_nonnegative,
            distance_as_observed_cell in *;
          simpl in *;
          repeat match goal with
          | H : context [Z_lt_dec ?a ?b] |- _ =>
              destruct (Z_lt_dec a b)
          | |- context [Z_lt_dec ?a ?b] =>
              destruct (Z_lt_dec a b)
          end;
          simpl in *; auto; lia.
      + destruct Hno_update as [Hkj_ge | [Hik_ge | Hsum_ge]];
          destruct (dist s0 (i, k)) as [dik |] eqn:Hdik;
          destruct (dist s0 (k, j)) as [dkj |] eqn:Hdkj;
          destruct (dist s0 (i, j)) as [dij |] eqn:Hdij;
          unfold Z_op_plus, Z_op_min, distance_as_observed_cell in *;
          simpl in *;
          repeat match goal with
          | H : context [Z_lt_dec ?a ?b] |- _ =>
              destruct (Z_lt_dec a b)
          | |- context [Z_lt_dec ?a ?b] =>
              destruct (Z_lt_dec a b)
          end;
          simpl in *; auto; lia.
    - clear Huv_neq.
      split.
      + exact Huv_nonneg.
      + exact Huv_cell.
  }
  assert (Hsafe_after_no_update :
    safeExec
      (fun s =>
        exists s0,
          s =
            (s0 <| dist ::= (fun dist0 =>
              @t_set FloydGraph.E (option Z) _ FloydGraph.edge_eqdec dist0 (i, j)
                (Z_op_min (dist0 (i, j))
                  (Z_op_plus (dist0 (i, k)) (dist0 (k, j))))) |>) /\
          state_model rows s0)
      (x0 <- range_iter (j + 1) n
              (fun (j : Z) (_ : unit) => floyd_update_dist i j k) tt ;;
       floyd_i_k_after g n k i x0) X).
  {
    eapply safeExec_bind_reta with
      (c1 := floyd_update_dist i j k)
      (c2 := fun x =>
        x0 <- range_iter (j + 1) n
                (fun (j : Z) (_ : unit) => floyd_update_dist i j k) x ;;
        floyd_i_k_after g n k i x0)
      (a := tt)
      in Hexec.
    - exact Hexec.
    - intros X' Hupd.
      unfold floyd_update_dist in Hupd.
      apply safeExec_update' in Hupd.
      exact Hupd.
  }
  assert (Hsafe_rows :
    safeExec (state_model rows)
      (x0 <- range_iter (j + 1) n
              (fun (j : Z) (_ : unit) => floyd_update_dist i j k) tt ;;
       floyd_i_k_after g n k i x0) X).
  {
    unfold safeExec in Hsafe_after_no_update |- *.
    destruct Hsafe_after_no_update as [st [[s0 [Hst Hs0]] Hsafe]].
    exists st.
    split.
    - subst st. apply Hstate_after_no_update. exact Hs0.
    - exact Hsafe.
  }
  unfold floyd_j_i_k_from, floyd_j_from.
  exact Hsafe_rows.
Qed.

End FloydAdjacencyMatrix2Darray.

Section ForsetRangeIterRefinement.

Lemma range_iter_interval_included_forset :
  forall {Σ : Type} (body : Z -> program Σ unit)
         (lo hi : Z) (universe : Z -> Prop),
    (forall x, universe x <-> lo <= x < hi) ->
    Sets.included
      (range_iter lo hi (fun i _ => body i) tt)
      (forset universe body).
Proof.
  intros Σ body.
  assert (Hmain :
    forall fuel lo hi universe,
      (Z.to_nat (hi - lo) <= fuel)%nat ->
      (forall x, universe x <-> lo <= x < hi) ->
      Sets.included
        (range_iter lo hi (fun i _ => body i) tt)
        (forset universe body)).
  {
    induction fuel as [| fuel IH]; intros lo hi universe Hfuel Huniv.
    - intros s r s' Hrun.
      destruct (Z_lt_dec lo hi) as [Hlt | Hge].
      + assert (0 < Z.to_nat (hi - lo))%nat.
        {
          change 0%nat with (Z.to_nat 0).
          apply Z2Nat.inj_lt; lia.
        }
        lia.
      + pose proof (@range_iter_unfold Σ unit hi (fun i _ => body i) lo tt)
          as Hrange_unfold.
        sets_unfold in Hrange_unfold.
        specialize (Hrange_unfold s r s').
        apply Hrange_unfold in Hrun.
        pose proof (@forset_unfold Σ Z universe body) as Hforset_unfold.
        sets_unfold in Hforset_unfold.
        specialize (Hforset_unfold s r s').
        apply Hforset_unfold.
        unfold choice in Hrun.
        unfold choice.
        sets_unfold in Hrun.
        sets_unfold.
        destruct Hrun as [Hrun | Hrun].
        * unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          destruct Hrun as [[] [s1 [[Hlt Hs1] _]]].
          lia.
        * right.
          unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          unfold StateRelMonad.bind, test', StateRelMonad.ret.
          destruct Hrun as [[] [s1 [[_ Hs1] Hret]]].
          subst s1.
          exists tt, s.
          split.
          -- split; [| reflexivity].
             sets_unfold.
             intros x.
             rewrite Huniv.
             split; intros; [lia | contradiction].
          -- exact Hret.
    - intros s r s' Hrun.
      destruct (Z_lt_dec lo hi) as [Hlt | Hge].
      + pose proof (@range_iter_unfold Σ unit hi (fun i _ => body i) lo tt)
          as Hrange_unfold.
        sets_unfold in Hrange_unfold.
        specialize (Hrange_unfold s r s').
        apply Hrange_unfold in Hrun.
        pose proof (@forset_unfold Σ Z universe body) as Hforset_unfold.
        sets_unfold in Hforset_unfold.
        specialize (Hforset_unfold s r s').
        apply Hforset_unfold.
        unfold choice in Hrun.
        unfold choice.
        sets_unfold in Hrun.
        sets_unfold.
        destruct Hrun as [Hrun | Hrun].
        * left.
          unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          unfold StateRelMonad.bind, test', StateRelMonad.ret.
          destruct Hrun as [[] [s1 [[_ Hs1] Hrun]]].
          subst s1.
          destruct Hrun as [[] [s2 [Hbody Hrec]]].
          exists lo, s.
          split.
          -- unfold get.
             split; [apply Huniv; lia | reflexivity].
          -- exists tt, s2.
             split; [exact Hbody |].
             eapply IH.
             ++ apply Nat.lt_succ_r.
                eapply Nat.lt_le_trans; [| exact Hfuel].
                replace (hi - (lo + 1)) with ((hi - lo) - 1) by lia.
                change
                  (Z.to_nat ((hi - lo) - 1) < Z.to_nat (hi - lo))%nat.
                apply Z2Nat.inj_lt; lia.
             ++ intros x.
                rewrite Huniv.
                split; intros Hx.
                ** destruct Hx as [[Hlo Hhi] Hneq].
                   lia.
                ** split; [lia | lia].
             ++ exact Hrec.
        * unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          destruct Hrun as [[] [s1 [[Hge _] _]]].
          lia.
      + pose proof (@range_iter_unfold Σ unit hi (fun i _ => body i) lo tt)
          as Hrange_unfold.
        sets_unfold in Hrange_unfold.
        specialize (Hrange_unfold s r s').
        apply Hrange_unfold in Hrun.
        pose proof (@forset_unfold Σ Z universe body) as Hforset_unfold.
        sets_unfold in Hforset_unfold.
        specialize (Hforset_unfold s r s').
        apply Hforset_unfold.
        unfold choice in Hrun.
        unfold choice.
        sets_unfold in Hrun.
        sets_unfold.
        destruct Hrun as [Hrun | Hrun].
        * unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          destruct Hrun as [[] [s1 [[Hlt _] _]]].
          lia.
        * right.
          unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          unfold StateRelMonad.bind, test', StateRelMonad.ret.
          destruct Hrun as [[] [s1 [[_ Hs1] Hret]]].
          subst s1.
          exists tt, s.
          split.
          -- split; [| reflexivity].
             sets_unfold.
             intros x.
             rewrite Huniv.
             split; intros; [lia | contradiction].
          -- exact Hret.
  }
  intros lo hi universe Huniv.
  eapply Hmain; [reflexivity | exact Huniv].
Qed.

Lemma range_iter_unit_body_included :
  forall {Σ : Type} (body1 body2 : Z -> program Σ unit) lo hi,
    (forall i, lo <= i < hi -> Sets.included (body1 i) (body2 i)) ->
    Sets.included
      (range_iter lo hi (fun i _ => body1 i) tt)
      (range_iter lo hi (fun i _ => body2 i) tt).
Proof.
  intros Σ body1 body2.
  assert (Hmain :
    forall fuel lo hi,
      (Z.to_nat (hi - lo) <= fuel)%nat ->
      (forall i, lo <= i < hi -> Sets.included (body1 i) (body2 i)) ->
      Sets.included
        (range_iter lo hi (fun i _ => body1 i) tt)
        (range_iter lo hi (fun i _ => body2 i) tt)).
  {
    induction fuel as [| fuel IH]; intros lo hi Hfuel Hbody.
    - intros s r s' Hrun.
      destruct (Z_lt_dec lo hi) as [Hlt | Hge].
      + assert (0 < Z.to_nat (hi - lo))%nat.
        {
          change 0%nat with (Z.to_nat 0).
          apply Z2Nat.inj_lt; lia.
        }
        lia.
      + pose proof (@range_iter_unfold Σ unit hi (fun i _ => body1 i) lo tt)
          as Hrange_unfold1.
        sets_unfold in Hrange_unfold1.
        specialize (Hrange_unfold1 s r s').
        apply Hrange_unfold1 in Hrun.
        pose proof (@range_iter_unfold Σ unit hi (fun i _ => body2 i) lo tt)
          as Hrange_unfold2.
        sets_unfold in Hrange_unfold2.
        specialize (Hrange_unfold2 s r s').
        apply Hrange_unfold2.
        unfold choice in Hrun.
        unfold choice.
        sets_unfold in Hrun.
        sets_unfold.
        destruct Hrun as [Hrun | Hrun].
        * unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          destruct Hrun as [[] [s1 [[Hlt Hs1] _]]].
          lia.
        * right.
          unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          unfold StateRelMonad.bind, test', StateRelMonad.ret.
          exact Hrun.
    - intros s r s' Hrun.
      destruct (Z_lt_dec lo hi) as [Hlt | Hge].
      + pose proof (@range_iter_unfold Σ unit hi (fun i _ => body1 i) lo tt)
          as Hrange_unfold1.
        sets_unfold in Hrange_unfold1.
        specialize (Hrange_unfold1 s r s').
        apply Hrange_unfold1 in Hrun.
        pose proof (@range_iter_unfold Σ unit hi (fun i _ => body2 i) lo tt)
          as Hrange_unfold2.
        sets_unfold in Hrange_unfold2.
        specialize (Hrange_unfold2 s r s').
        apply Hrange_unfold2.
        unfold choice in Hrun.
        unfold choice.
        sets_unfold in Hrun.
        sets_unfold.
        destruct Hrun as [Hrun | Hrun].
        * left.
          unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          unfold StateRelMonad.bind, test', StateRelMonad.ret.
          destruct Hrun as [[] [s1 [[_ Hs1] Hrun]]].
          subst s1.
          destruct Hrun as [[] [s2 [Hbody1 Hrec]]].
          exists tt, s.
          split.
          -- split; [exact Hlt | reflexivity].
          -- exists tt, s2.
             split.
             ++ apply Hbody; [lia | exact Hbody1].
             ++ eapply IH.
                ** apply Nat.lt_succ_r.
                   eapply Nat.lt_le_trans; [| exact Hfuel].
                   replace (hi - (lo + 1)) with ((hi - lo) - 1) by lia.
                   change
                     (Z.to_nat ((hi - lo) - 1) < Z.to_nat (hi - lo))%nat.
                   apply Z2Nat.inj_lt; lia.
                ** intros i Hi.
                   apply Hbody; lia.
                ** exact Hrec.
        * unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          destruct Hrun as [[] [s1 [[Hge _] _]]].
          lia.
      + pose proof (@range_iter_unfold Σ unit hi (fun i _ => body1 i) lo tt)
          as Hrange_unfold1.
        sets_unfold in Hrange_unfold1.
        specialize (Hrange_unfold1 s r s').
        apply Hrange_unfold1 in Hrun.
        pose proof (@range_iter_unfold Σ unit hi (fun i _ => body2 i) lo tt)
          as Hrange_unfold2.
        sets_unfold in Hrange_unfold2.
        specialize (Hrange_unfold2 s r s').
        apply Hrange_unfold2.
        unfold choice in Hrun.
        unfold choice.
        sets_unfold in Hrun.
        sets_unfold.
        destruct Hrun as [Hrun | Hrun].
        * unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          destruct Hrun as [[] [s1 [[Hlt _] _]]].
          lia.
        * right.
          unfold StateRelMonad.bind, test', StateRelMonad.ret in Hrun.
          unfold StateRelMonad.bind, test', StateRelMonad.ret.
          exact Hrun.
  }
  intros lo hi Hbody.
  eapply Hmain; [reflexivity | exact Hbody].
Qed.

Definition floyd_program
    (g : FloydGraph.G) : program FloydAdjacencyMatrix2Darray.state unit :=
  @Floyd FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance g FloydGraph.edge_eqdec.

Definition floyd_i_program
    (g : FloydGraph.G) (k i : Z)
    : program FloydAdjacencyMatrix2Darray.state unit :=
  @Floyd_i FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance g FloydGraph.edge_eqdec k i.

Definition floyd_k_program
    (g : FloydGraph.G) (k : Z)
    : program FloydAdjacencyMatrix2Darray.state unit :=
  @Floyd_k FloydGraph.G FloydGraph.V FloydGraph.E
    FloydGraph.graph_instance g FloydGraph.edge_eqdec k.

Lemma graph_has_size_vvalid_interval :
  forall (g : FloydGraph.G) (n x : Z),
    FloydAdjacencyMatrix2Darray.graph_has_size g n ->
    FloydGraph.vertex_valid g x <-> 0 <= x < n.
Proof.
  intros g n x [Hn _].
  unfold FloydGraph.vertex_valid.
  rewrite Hn.
  reflexivity.
Qed.

Lemma floyd_j_from_included_Floyd_i :
  forall (g : FloydGraph.G) (n k i : Z),
    FloydAdjacencyMatrix2Darray.graph_has_size g n ->
    Sets.included
      (FloydAdjacencyMatrix2Darray.floyd_j_from g n k i 0)
      (floyd_i_program g k i).
Proof.
  intros g n k i Hsize.
  unfold FloydAdjacencyMatrix2Darray.floyd_j_from, floyd_i_program, Floyd_i.
  unfold FloydAdjacencyMatrix2Darray.floyd_update_dist.
  apply range_iter_interval_included_forset.
  intros x.
  change (FloydGraph.vertex_valid g x <-> 0 <= x < n).
  apply graph_has_size_vvalid_interval.
  exact Hsize.
Qed.

Lemma floyd_i_from_included_Floyd_k :
  forall (g : FloydGraph.G) (n k : Z),
    FloydAdjacencyMatrix2Darray.graph_has_size g n ->
    Sets.included
      (FloydAdjacencyMatrix2Darray.floyd_i_from g n k 0)
      (floyd_k_program g k).
Proof.
  intros g n k Hsize.
  unfold FloydAdjacencyMatrix2Darray.floyd_i_from, floyd_k_program, Floyd_k.
  eapply Sets_included_trans with
    (y := range_iter 0 n (fun i _ => floyd_i_program g k i) tt).
  - apply range_iter_unit_body_included.
    intros i _.
    apply floyd_j_from_included_Floyd_i.
    exact Hsize.
  - apply range_iter_interval_included_forset.
    intros x.
    change (FloydGraph.vertex_valid g x <-> 0 <= x < n).
    apply graph_has_size_vvalid_interval.
    exact Hsize.
Qed.

Lemma floyd_k_from_included_Floyd :
  forall (g : FloydGraph.G) (n : Z),
    FloydAdjacencyMatrix2Darray.graph_has_size g n ->
    Sets.included
      (FloydAdjacencyMatrix2Darray.floyd_k_from g n 0)
      (floyd_program g).
Proof.
  intros g n Hsize.
  unfold FloydAdjacencyMatrix2Darray.floyd_k_from, floyd_program, Floyd.
  eapply Sets_included_trans with
    (y := range_iter 0 n (fun k _ => floyd_k_program g k) tt).
  - apply range_iter_unit_body_included.
    intros k _.
    apply floyd_i_from_included_Floyd_k.
    exact Hsize.
  - apply range_iter_interval_included_forset.
    intros x.
    change (FloydGraph.vertex_valid g x <-> 0 <= x < n).
    apply graph_has_size_vvalid_interval.
    exact Hsize.
Qed.

Lemma floyd_indexed_program_included_floyd_program :
  forall (g : FloydGraph.G) (n : Z),
    FloydAdjacencyMatrix2Darray.graph_has_size g n ->
    Sets.included
      (FloydAdjacencyMatrix2Darray.floyd_indexed_program g n)
      (floyd_program g).
Proof.
  intros g n Hsize.
  unfold FloydAdjacencyMatrix2Darray.floyd_indexed_program, floyd_program.
  apply floyd_k_from_included_Floyd.
  exact Hsize.
Qed.

Lemma floyd_indexed_program_Hoare_correct :
  forall (g : FloydGraph.G) (n : Z),
    FloydGraph.graph_wf g ->
    FloydAdjacencyMatrix2Darray.floyd_no_negative_cycle g ->
    FloydAdjacencyMatrix2Darray.graph_has_size g n ->
    Hoare
      (FloydAdjacencyMatrix2Darray.floyd_initial_state g)
      (FloydAdjacencyMatrix2Darray.floyd_indexed_program g n)
      (fun _ s => FloydAdjacencyMatrix2Darray.floyd_shortest_state g s).
Proof.
  intros g n Hg Hnon_neg_loop Hsize.
  pose proof
    (@Floyd_correct
       FloydGraph.G FloydGraph.V FloydGraph.E
       FloydGraph.graph_instance FloydGraph.gvalid_instance
       FloydGraph.stepvalid_instance FloydGraph.stepunique_instance
       g Hg FloydGraph.edge_eqdec
       FloydGraph.PathData FloydGraph.path_instance
       FloydGraph.empty_path_instance FloydGraph.single_path_instance
       FloydGraph.concat_path_instance FloydGraph.destruct1n_path_instance
       FloydGraph.weight_instance Hnon_neg_loop)
    as Hcorrect.
  unfold FloydAdjacencyMatrix2Darray.floyd_initial_state,
    FloydAdjacencyMatrix2Darray.floyd_shortest_state in *.
  unfold Hoare in Hcorrect |- *.
  intros s1 a s2 Hinit Hrun.
  eapply Hcorrect; [exact Hinit |].
  pose proof (floyd_indexed_program_included_floyd_program g n Hsize)
    as Hrefine.
  unfold floyd_program in Hrefine.
  apply Hrefine.
  exact Hrun.
Qed.

End ForsetRangeIterRefinement.
