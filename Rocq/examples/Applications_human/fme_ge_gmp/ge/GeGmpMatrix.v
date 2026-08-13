Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import int_auto ListLib.
From SimpleC.SL Require Import Mem SeparationLogic IntLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

(* ====================================================== *)
(* 1. Mathematical matrices                               *)
(* ====================================================== *)

Definition matrix : Type := Z -> Z -> Z.

Definition matrix_shape (rows cols : Z) : Prop :=
  0 <= rows /\ 0 <= cols.

Definition matrix_eq_on
  (rows cols : Z) (A B : matrix) : Prop :=
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    A i j = B i j.

Lemma matrix_eq_on_refl :
  forall rows cols A,
    matrix_eq_on rows cols A A.
Proof.
  unfold matrix_eq_on. auto.
Qed.

Lemma matrix_eq_on_sym :
  forall rows cols A B,
    matrix_eq_on rows cols A B ->
    matrix_eq_on rows cols B A.
Proof.
  unfold matrix_eq_on. intros.
  symmetry. apply H; assumption.
Qed.

Lemma matrix_eq_on_trans :
  forall rows cols A B C,
    matrix_eq_on rows cols A B ->
    matrix_eq_on rows cols B C ->
    matrix_eq_on rows cols A C.
Proof.
  unfold matrix_eq_on. intros.
  rewrite H by assumption.
  apply H0; assumption.
Qed.

(* ====================================================== *)
(* 2. Basic matrix operations                             *)
(* ====================================================== *)

Definition matrix_zero : matrix :=
  fun _ _ => 0.

Definition matrix_const (v : Z) : matrix :=
  fun _ _ => v.

Definition matrix_id : matrix :=
  fun i j => if Z.eq_dec i j then 1 else 0.

Definition matrix_update
  (A : matrix) (r c v : Z) : matrix :=
  fun i j =>
    if Z.eq_dec i r then
      if Z.eq_dec j c then v else A i j
    else A i j.

Definition matrix_add (A B : matrix) : matrix :=
  fun i j => A i j + B i j.

Definition matrix_sub (A B : matrix) : matrix :=
  fun i j => A i j - B i j.

Definition matrix_scalar_mul (k : Z) (A : matrix) : matrix :=
  fun i j => k * A i j.

Definition matrix_transpose (A : matrix) : matrix :=
  fun i j => A j i.

Lemma matrix_update_eq :
  forall A r c v,
    matrix_update A r c v r c = v.
Proof.
  intros. unfold matrix_update.
  repeat destruct Z.eq_dec; lia.
Qed.

Lemma matrix_update_neq :
  forall A r c v i j,
    i <> r \/ j <> c ->
    matrix_update A r c v i j = A i j.
Proof.
  intros A r c v i j Hneq.
  unfold matrix_update.
  repeat destruct Z.eq_dec; subst; try lia; reflexivity.
Qed.

Lemma matrix_add_comm :
  forall rows cols A B,
    matrix_eq_on rows cols
      (matrix_add A B) (matrix_add B A).
Proof.
  unfold matrix_eq_on, matrix_add. intros. lia.
Qed.

Lemma matrix_add_assoc :
  forall rows cols A B C,
    matrix_eq_on rows cols
      (matrix_add (matrix_add A B) C)
      (matrix_add A (matrix_add B C)).
Proof.
  unfold matrix_eq_on, matrix_add. intros. lia.
Qed.

Lemma matrix_add_zero_l :
  forall rows cols A,
    matrix_eq_on rows cols (matrix_add matrix_zero A) A.
Proof.
  unfold matrix_eq_on, matrix_add, matrix_zero. intros. lia.
Qed.

Lemma matrix_add_zero_r :
  forall rows cols A,
    matrix_eq_on rows cols (matrix_add A matrix_zero) A.
Proof.
  unfold matrix_eq_on, matrix_add, matrix_zero. intros. lia.
Qed.

Lemma matrix_transpose_involutive :
  forall rows cols A,
    matrix_eq_on rows cols
      (matrix_transpose (matrix_transpose A)) A.
Proof.
  unfold matrix_eq_on, matrix_transpose. auto.
Qed.

Lemma matrix_transpose_add :
  forall rows cols A B,
    matrix_eq_on rows cols
      (matrix_transpose (matrix_add A B))
      (matrix_add (matrix_transpose A) (matrix_transpose B)).
Proof.
  unfold matrix_eq_on, matrix_transpose, matrix_add. auto.
Qed.

(* ====================================================== *)
(* 3. Dot product and matrix multiplication                *)
(* ====================================================== *)

Fixpoint dot_prod_nat
  (A B : matrix)
  (row col : Z)
  (cnt : nat) : Z :=
  match cnt with
  | O => 0
  | S cnt' =>
      dot_prod_nat A B row col cnt' +
      A row (Z.of_nat cnt') * B (Z.of_nat cnt') col
  end.

Definition dot_prod
  (A B : matrix)
  (row col len : Z) : Z :=
  dot_prod_nat A B row col (Z.to_nat len).

Definition matrix_mul
  (A B : matrix)
  (mid : Z) : matrix :=
  fun i j => dot_prod A B i j mid.

Lemma dot_prod_0 :
  forall A B row col,
    dot_prod A B row col 0 = 0.
Proof.
  intros. unfold dot_prod. reflexivity.
Qed.

Lemma dot_prod_step :
  forall A B row col t,
    0 <= t ->
    dot_prod A B row col (t + 1) =
    dot_prod A B row col t + A row t * B t col.
Proof.
  intros A B row col t Ht.
  unfold dot_prod.
  assert (Hnat : Z.to_nat (t + 1) = S (Z.to_nat t)).
  {
    replace (t + 1) with (Z.succ t) by lia.
    apply Z2Nat.inj_succ; lia.
  }
  rewrite Hnat.
  simpl.
  replace (Z.of_nat (Z.to_nat t)) with t by lia.
  reflexivity.
Qed.

Lemma matrix_mul_entry :
  forall A B mid i j,
    matrix_mul A B mid i j = dot_prod A B i j mid.
Proof.
  intros. unfold matrix_mul. reflexivity.
Qed.

(* Backward-compatible short name for specifications. *)
Definition mat_mul := matrix_mul.

(* ====================================================== *)
(* 4. Row-major array representation                       *)
(* ====================================================== *)

Definition row_major_index (cols i j : Z) : Z :=
  i * cols + j.

Definition rep_matrix
  (l : list Z) (rows cols : Z) (A : matrix) : Prop :=
  matrix_shape rows cols /\
  Zlength l = rows * cols /\
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    Znth (row_major_index cols i j) l 0 = A i j.

Lemma rep_matrix_nth :
  forall l rows cols A i j,
    rep_matrix l rows cols A ->
    0 <= i < rows ->
    0 <= j < cols ->
    Znth (row_major_index cols i j) l 0 = A i j.
Proof.
  intros l rows cols A i j Hrep Hi Hj.
  unfold rep_matrix in Hrep.
  destruct Hrep as [_ [_ Hentry]].
  apply Hentry; assumption.
Qed.

Lemma rep_matrix_length :
  forall l rows cols A,
    rep_matrix l rows cols A ->
    Zlength l = rows * cols.
Proof.
  intros l rows cols A Hrep.
  unfold rep_matrix in Hrep. tauto.
Qed.

Lemma rep_matrix_shape :
  forall l rows cols A,
    rep_matrix l rows cols A ->
    matrix_shape rows cols.
Proof.
  intros l rows cols A Hrep.
  unfold rep_matrix in Hrep. tauto.
Qed.

Lemma rep_matrix_rows_nonneg :
  forall l rows cols A,
    rep_matrix l rows cols A -> 0 <= rows.
Proof.
  intros l rows cols A Hrep.
  pose proof (rep_matrix_shape l rows cols A Hrep) as Hshape.
  unfold matrix_shape in Hshape. tauto.
Qed.

Lemma rep_matrix_cols_nonneg :
  forall l rows cols A,
    rep_matrix l rows cols A -> 0 <= cols.
Proof.
  intros l rows cols A Hrep.
  pose proof (rep_matrix_shape l rows cols A Hrep) as Hshape.
  unfold matrix_shape in Hshape. tauto.
Qed.

Lemma rep_matrix_functional_on :
  forall l rows cols A B,
    rep_matrix l rows cols A ->
    rep_matrix l rows cols B ->
    matrix_eq_on rows cols A B.
Proof.
  intros l rows cols A B HA HB i j Hi Hj.
  pose proof (rep_matrix_nth l rows cols A i j HA Hi Hj) as HAn.
  pose proof (rep_matrix_nth l rows cols B i j HB Hi Hj) as HBn.
  rewrite <- HAn. rewrite <- HBn. reflexivity.
Qed.

Lemma rep_matrix_congr_on :
  forall l rows cols A B,
    rep_matrix l rows cols A ->
    matrix_eq_on rows cols A B ->
    rep_matrix l rows cols B.
Proof.
  intros l rows cols A B Hrep Heq.
  unfold rep_matrix in *.
  destruct Hrep as [Hshape [Hlen Hentry]].
  split.
  - exact Hshape.
  - split.
    + exact Hlen.
    + intros i j Hi Hj.
      rewrite Hentry by assumption.
      apply Heq; assumption.
Qed.

Lemma row_major_index_bound :
  forall rows cols i j,
    0 <= rows ->
    0 <= cols ->
    0 <= i < rows ->
    0 <= j < cols ->
    0 <= row_major_index cols i j < rows * cols.
Proof.
  intros rows cols i j Hrows Hcols Hi Hj.
  unfold row_major_index. nia.
Qed.

Lemma row_major_index_eq :
  forall cols i j,
    row_major_index cols i j = i * cols + j.
Proof.
  intros. unfold row_major_index. reflexivity.
Qed.

Lemma row_major_index_inj :
  forall cols i j i' j',
    0 <= j < cols ->
    0 <= j' < cols ->
    row_major_index cols i j = row_major_index cols i' j' ->
    i = i' /\ j = j'.
Proof.
  intros cols i j i' j' Hj Hj' Heq.
  assert (Hcols : cols > 0) by lia.
  unfold row_major_index in Heq.
  assert (Hmodj : (i * cols + j) mod cols = j).
  {
    replace (i * cols + j) with (j + i * cols) by lia.
    rewrite Z_mod_plus_full.
    apply Z.mod_small. lia.
  }
  assert (Hmodj' : (i' * cols + j') mod cols = j').
  {
    replace (i' * cols + j') with (j' + i' * cols) by lia.
    rewrite Z_mod_plus_full.
    apply Z.mod_small. lia.
  }
  rewrite Heq in Hmodj.
  rewrite Hmodj' in Hmodj.
  subst j'.
  split.
  - assert ((i - i') * cols = 0) by lia.
    apply Zmult_integral in H.
    destruct H; lia.
  - reflexivity.
Qed.

(* ====================================================== *)
(* 5. Public matrix memory predicates                      *)
(* ====================================================== *)

Definition store_matrix
  (p : addr)
  (rows cols : Z)
  (A : matrix) : Assertion :=
  EX l : list Z,
    “ rep_matrix l rows cols A ” &&
    IntArray.full p (rows * cols) l.

Definition matrix_array_view
  (p : addr) (rows cols : Z) (A : matrix) (l : list Z) : Assertion :=
  “ rep_matrix l rows cols A ” &&
  IntArray.full p (rows * cols) l.

(* ====================================================== *)
(* 6. Program-facing specifications                        *)
(* ====================================================== *)

Definition matrix_add_spec
  (rows cols : Z)
  (A B C : matrix) : Prop :=
  matrix_shape rows cols /\
  matrix_eq_on rows cols C (matrix_add A B).

Definition matrix_transpose_spec
  (rows cols : Z)
  (A T : matrix) : Prop :=
  matrix_shape rows cols /\
  matrix_eq_on cols rows T (matrix_transpose A).

Definition matrix_mul_spec
  (n mid k : Z)
  (A B C : matrix) : Prop :=
  matrix_shape n mid /\
  matrix_shape mid k /\
  matrix_eq_on n k C (matrix_mul A B mid).

Definition matrix_array_add_spec
  (la lb lc : list Z)
  (rows cols : Z)
  (A B : matrix) : Prop :=
  rep_matrix la rows cols A /\
  rep_matrix lb rows cols B /\
  rep_matrix lc rows cols (matrix_add A B).

Definition matrix_array_transpose_spec
  (la lt : list Z)
  (rows cols : Z)
  (A : matrix) : Prop :=
  rep_matrix la rows cols A /\
  rep_matrix lt cols rows (matrix_transpose A).

Definition matrix_array_mul_spec
  (la lb lc : list Z)
  (n mid k : Z)
  (A B : matrix) : Prop :=
  rep_matrix la n mid A /\
  rep_matrix lb mid k B /\
  rep_matrix lc n k (matrix_mul A B mid).

Lemma matrix_array_mul_spec_entry :
  forall la lb lc n mid k A B i j,
    matrix_array_mul_spec la lb lc n mid k A B ->
    0 <= i < n ->
    0 <= j < k ->
    Znth (row_major_index k i j) lc 0 = dot_prod A B i j mid.
Proof.
  intros la lb lc n mid k A B i j Hspec Hi Hj.
  unfold matrix_array_mul_spec in Hspec.
  destruct Hspec as [_ [_ HrepC]].
  rewrite (rep_matrix_nth lc n k (matrix_mul A B mid) i j HrepC Hi Hj).
  unfold matrix_mul. reflexivity.
Qed.

(* ====================================================== *)
(* 7. Partial matrix representation for loops              *)
(* ====================================================== *)

Definition partial_rep_matrix
  (l : list Z) (rows cols done : Z) (C : matrix) : Prop :=
  matrix_shape rows cols /\
  Zlength l = rows * cols /\
  0 <= done <= rows * cols /\
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    row_major_index cols i j < done ->
    Znth (row_major_index cols i j) l 0 = C i j.

Definition matrix_partial_array_add_spec
  (la lb lc : list Z)
  (rows cols done : Z)
  (A B : matrix) : Prop :=
  rep_matrix la rows cols A /\
  rep_matrix lb rows cols B /\
  partial_rep_matrix lc rows cols done (matrix_add A B).

Definition matrix_partial_array_mul_spec
  (la lb lc : list Z)
  (n mid k done : Z)
  (A B : matrix) : Prop :=
  rep_matrix la n mid A /\
  rep_matrix lb mid k B /\
  partial_rep_matrix lc n k done (matrix_mul A B mid).

Lemma partial_rep_matrix_entry :
  forall l rows cols done C i j,
    partial_rep_matrix l rows cols done C ->
    0 <= i < rows ->
    0 <= j < cols ->
    row_major_index cols i j < done ->
    Znth (row_major_index cols i j) l 0 = C i j.
Proof.
  intros l rows cols done C i j Hpart Hi Hj Hdone.
  unfold partial_rep_matrix in Hpart.
  destruct Hpart as [_ [_ [_ Hentry]]].
  apply Hentry; assumption.
Qed.

Lemma rep_matrix_implies_partial_full :
  forall l rows cols C,
    rep_matrix l rows cols C ->
    partial_rep_matrix l rows cols (rows * cols) C.
Proof.
  intros l rows cols C Hrep.
  unfold rep_matrix in Hrep.
  destruct Hrep as [Hshape [Hlen Hentry]].
  unfold partial_rep_matrix.
  split.
  - exact Hshape.
  - split.
    + exact Hlen.
    + split.
      * unfold matrix_shape in Hshape. nia.
      * intros i j Hi Hj _.
        apply Hentry; assumption.
Qed.

Lemma rep_matrix_implies_partial_0 :
  forall l rows cols C,
    rep_matrix l rows cols C ->
    partial_rep_matrix l rows cols 0 C.
Proof.
  intros l rows cols C Hrep.
  unfold rep_matrix in Hrep.
  destruct Hrep as [Hshape [Hlen _]].
  unfold partial_rep_matrix.
  split.
  - exact Hshape.
  - split.
    + exact Hlen.
    + split.
      * unfold matrix_shape in Hshape. nia.
      * intros i j Hi Hj Hidx.
        unfold row_major_index in Hidx.
        unfold matrix_shape in Hshape.
        nia.
Qed.

Lemma partial_rep_matrix_0_from_length :
  forall l rows cols C,
    matrix_shape rows cols ->
    Zlength l = rows * cols ->
    partial_rep_matrix l rows cols 0 C.
Proof.
  intros l rows cols C Hshape Hlen.
  unfold partial_rep_matrix.
  split.
  - exact Hshape.
  - split.
    + exact Hlen.
    + split.
      * unfold matrix_shape in Hshape. nia.
      * intros i j Hi Hj Hidx.
        unfold row_major_index in Hidx.
        unfold matrix_shape in Hshape.
        nia.
Qed.

Lemma length_replace_nth :
  forall {A : Type} n (a : A) l,
    length (replace_nth n l a) = length l.
Proof.
  intros A n a l.
  revert l.
  induction n; destruct l; simpl; auto.
Qed.

Lemma Zlength_replace_Znth :
  forall {A : Type} n (a : A) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros A n a l.
  unfold replace_Znth.
  repeat rewrite Zlength_correct.
  rewrite length_replace_nth.
  reflexivity.
Qed.

Lemma nth_replace_nth_same :
  forall {A : Type} n (a d : A) l,
    (n < length l)%nat ->
    nth n (replace_nth n l a) d = a.
Proof.
  intros A n a d l.
  revert n.
  induction l; intros n Hn; simpl in Hn; try lia.
  destruct n; simpl.
  - reflexivity.
  - apply IHl. lia.
Qed.

Lemma nth_replace_nth_diff :
  forall {A : Type} i j (a d : A) l,
    i <> j ->
    nth i (replace_nth j l a) d = nth i l d.
Proof.
  intros A i j a d l.
  revert i j.
  induction l; intros i j Hneq; simpl.
  - destruct i, j; simpl; reflexivity.
  - destruct i, j; simpl; try reflexivity; try congruence.
    apply IHl. congruence.
Qed.

Lemma Znth_replace_Znth_same :
  forall {A : Type} n (a d : A) l,
    0 <= n < Zlength l ->
    Znth n (replace_Znth n a l) d = a.
Proof.
  intros A n a d l Hn.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_same.
  rewrite Zlength_correct in Hn.
  lia.
Qed.

Lemma Znth_replace_Znth_diff :
  forall {A : Type} i j (a d : A) l,
    0 <= i ->
    0 <= j ->
    i <> j ->
    Znth i (replace_Znth j a l) d = Znth i l d.
Proof.
  intros A i j a d l Hi Hj Hneq.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_diff.
  intro Hnat.
  apply Hneq.
  lia.
Qed.

Lemma partial_rep_matrix_update_next :
  forall l rows cols done C i j v,
    partial_rep_matrix l rows cols done C ->
    0 <= i < rows ->
    0 <= j < cols ->
    done = row_major_index cols i j ->
    v = C i j ->
    partial_rep_matrix (replace_Znth done v l) rows cols (done + 1) C.
Proof.
  intros l rows cols done C i j v Hpart Hi Hj Hdone Hv.
  unfold partial_rep_matrix in *.
  destruct Hpart as [Hshape [Hlen [Hrange Hentry]]].
  split.
  - exact Hshape.
  - split.
    + rewrite Zlength_replace_Znth; exact Hlen.
    + split.
      * unfold matrix_shape in Hshape.
        destruct Hshape as [Hrows Hcols].
        pose proof (row_major_index_bound rows cols i j Hrows Hcols Hi Hj).
        subst done. nia.
      * intros i0 j0 Hi0 Hj0 Hidx.
        destruct (Z.eq_dec (row_major_index cols i0 j0) done) as [Heq | Hneq].
        -- rewrite Heq.
           rewrite Znth_replace_Znth_same.
           ++ subst v.
              subst done.
              destruct (row_major_index_inj cols i0 j0 i j Hj0 Hj Heq)
                as [Hi_eq Hj_eq].
              subst i0 j0.
              reflexivity.
           ++ rewrite Hlen.
              subst done.
              unfold matrix_shape in Hshape.
              destruct Hshape as [Hrows Hcols].
              pose proof (row_major_index_bound rows cols i j Hrows Hcols Hi Hj).
              lia.
        -- rewrite Znth_replace_Znth_diff.
           ++ apply Hentry; try assumption. lia.
           ++ unfold row_major_index. nia.
           ++ subst done.
              unfold matrix_shape in Hshape.
              destruct Hshape as [Hrows Hcols].
              pose proof (row_major_index_bound rows cols i j Hrows Hcols Hi Hj).
              lia.
           ++ exact Hneq.
Qed.

Lemma partial_full_implies_rep_matrix :
  forall l rows cols C,
    partial_rep_matrix l rows cols (rows * cols) C ->
    rep_matrix l rows cols C.
Proof.
  intros l rows cols C Hpart.
  unfold partial_rep_matrix in Hpart.
  destruct Hpart as [Hshape [Hlen [_ Hentry]]].
  unfold rep_matrix.
  split.
  - exact Hshape.
  - split.
    + exact Hlen.
    + intros i j Hi Hj.
      apply Hentry; try assumption.
      unfold row_major_index.
      unfold matrix_shape in Hshape.
      nia.
Qed.

Lemma partial_rep_matrix_shape :
  forall l rows cols done C,
    partial_rep_matrix l rows cols done C -> matrix_shape rows cols.
Proof.
  intros l rows cols done C Hpart.
  unfold partial_rep_matrix in Hpart. tauto.
Qed.

Lemma partial_rep_matrix_length :
  forall l rows cols done C,
    partial_rep_matrix l rows cols done C -> Zlength l = rows * cols.
Proof.
  intros l rows cols done C Hpart.
  unfold partial_rep_matrix in Hpart. tauto.
Qed.

Lemma partial_rep_matrix_done_range :
  forall l rows cols done C,
    partial_rep_matrix l rows cols done C -> 0 <= done <= rows * cols.
Proof.
  intros l rows cols done C Hpart.
  unfold partial_rep_matrix in Hpart. tauto.
Qed.

(* ====================================================== *)
(* 8. Integer safety predicates for C programs             *)
(* ====================================================== *)

Definition matrix_entries_int_range
  (rows cols : Z) (A : matrix) : Prop :=
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    INT_MIN <= A i j <= INT_MAX.

Definition matrix_add_int_safe
  (rows cols : Z) (A B : matrix) : Prop :=
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    INT_MIN <= A i j + B i j <= INT_MAX.

Definition matrix_scalar_mul_int_safe
  (rows cols k : Z) (A : matrix) : Prop :=
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    INT_MIN <= k * A i j <= INT_MAX.

Definition matrix_mul_int_safe
  (n mid k : Z) (A B : matrix) : Prop :=
  forall i j t,
    0 <= i < n ->
    0 <= j < k ->
    0 <= t <= mid ->
    INT_MIN <= dot_prod A B i j t <= INT_MAX.

(* ====================================================== *)
(* 9. Fixed 2x2 matrix support for fast power              *)
(* ====================================================== *)

Definition mat2_id : matrix := matrix_id.

Definition mat2_from_entries
  (a00 a01 a10 a11 : Z) : matrix :=
  fun i j =>
    if Z.eq_dec i 0 then
      if Z.eq_dec j 0 then a00 else a01
    else
      if Z.eq_dec j 0 then a10 else a11.

Definition mat2_entries_mod (m : Z) (A : matrix) : Prop :=
  forall i j,
    0 <= i < 2 ->
    0 <= j < 2 ->
    0 <= A i j < m.

Definition mat2_mod (m : Z) (A : matrix) : Prop :=
  0 < m /\ mat2_entries_mod m A.

Definition mat2_mul_mod (m : Z) (A B : matrix) : matrix :=
  fun i j => Z.rem (matrix_mul A B 2 i j) m.

Definition mat2_entry00 (A : matrix) : Z := A 0 0.
Definition mat2_entry01 (A : matrix) : Z := A 0 1.
Definition mat2_entry10 (A : matrix) : Z := A 1 0.
Definition mat2_entry11 (A : matrix) : Z := A 1 1.

Lemma mat2_id_mod :
  forall m,
    2 <= m -> mat2_mod m mat2_id.
Proof.
  intros m Hm.
  unfold mat2_mod, mat2_entries_mod, mat2_id, matrix_id.
  split.
  - lia.
  - intros i j Hi Hj.
    repeat destruct Z.eq_dec; lia.
Qed.

Lemma mat2_mod_entry_nonneg :
  forall m A i j,
    mat2_mod m A ->
    0 <= i < 2 ->
    0 <= j < 2 ->
    0 <= A i j.
Proof.
  intros m A i j [_ Hentries] Hi Hj.
  pose proof (Hentries i j Hi Hj).
  lia.
Qed.

Lemma mat2_mul_nonneg :
  forall m A B i j,
    mat2_mod m A ->
    mat2_mod m B ->
    0 <= i < 2 ->
    0 <= j < 2 ->
    0 <= matrix_mul A B 2 i j.
Proof.
  intros m A B i j HA HB Hi Hj.
  unfold matrix_mul, dot_prod.
  change (Z.to_nat 2) with 2%nat.
  simpl.
  assert (HA0 : 0 <= A i 0) by (eapply mat2_mod_entry_nonneg; eauto; lia).
  assert (HA1 : 0 <= A i 1) by (eapply mat2_mod_entry_nonneg; eauto; lia).
  assert (HB0 : 0 <= B 0 j) by (eapply mat2_mod_entry_nonneg; eauto; lia).
  assert (HB1 : 0 <= B 1 j) by (eapply mat2_mod_entry_nonneg; eauto; lia).
  nia.
Qed.

Lemma mat2_mul_mod_mod_from_mod :
  forall m A B,
    mat2_mod m A ->
    mat2_mod m B ->
    mat2_mod m (mat2_mul_mod m A B).
Proof.
  intros m A B HA HB.
  destruct HA as [Hm HAentries].
  split.
  - exact Hm.
  - unfold mat2_entries_mod.
    intros i j Hi Hj.
    unfold mat2_mul_mod.
    apply Z.rem_bound_pos.
    + apply mat2_mul_nonneg with (m := m); try (split; assumption); auto.
    + exact Hm.
Qed.

Lemma rep_matrix_init_id_list :
  forall l,
    Zlength l = 4 ->
    rep_matrix
      (replace_Znth 3 1 (replace_Znth 2 0 (replace_Znth 1 0 (replace_Znth 0 1 l))))
      2 2 mat2_id.
Proof.
  intros l Hlen.
  rewrite Zlength_correct in Hlen.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  unfold rep_matrix, matrix_shape, mat2_id, matrix_id, row_major_index.
  split.
  - split; lia.
  - split.
    + reflexivity.
    + intros i j Hi Hj.
      assert (Hi01 : i = 0 \/ i = 1) by lia.
      assert (Hj01 : j = 0 \/ j = 1) by lia.
      destruct Hi01 as [-> | ->]; destruct Hj01 as [-> | ->];
        simpl; repeat (rewrite Znth_replace_Znth_same by (repeat rewrite Zlength_replace_Znth; lia) ||
                       rewrite Znth_replace_Znth_diff by lia); simpl;
        repeat destruct Z.eq_dec; reflexivity.
Qed.

Lemma rep_matrix_copy_list :
  forall lbase la A,
    rep_matrix la 2 2 A ->
    Zlength lbase = 4 ->
    rep_matrix
      (replace_Znth 3 (Znth 3 la 0)
        (replace_Znth 2 (Znth 2 la 0)
          (replace_Znth 1 (Znth 1 la 0)
            (replace_Znth 0 (Znth 0 la 0) lbase))))
      2 2 A.
Proof.
  intros lbase la A Hrep Hlen.
  rewrite Zlength_correct in Hlen.
  destruct lbase; simpl in Hlen; try lia.
  destruct lbase; simpl in Hlen; try lia.
  destruct lbase; simpl in Hlen; try lia.
  destruct lbase; simpl in Hlen; try lia.
  destruct lbase; simpl in Hlen; try lia.
  unfold rep_matrix, matrix_shape, row_major_index in *.
  destruct Hrep as [_ [Hla Hentry]].
  split.
  - split; lia.
  - split.
    + reflexivity.
    + intros i j Hi Hj.
      assert (Hi01 : i = 0 \/ i = 1) by lia.
      assert (Hj01 : j = 0 \/ j = 1) by lia.
      destruct Hi01 as [-> | ->]; destruct Hj01 as [-> | ->]; unfold replace_Znth; simpl;
        [ exact (Hentry 0 0 ltac:(lia) ltac:(lia))
        | exact (Hentry 0 1 ltac:(lia) ltac:(lia))
        | exact (Hentry 1 0 ltac:(lia) ltac:(lia))
        | exact (Hentry 1 1 ltac:(lia) ltac:(lia)) ].
Qed.

Lemma rep_matrix_zero_list :
  forall l,
    Zlength l = 4 ->
    rep_matrix
      (replace_Znth 3 0 (replace_Znth 2 0 (replace_Znth 1 0 (replace_Znth 0 0 l))))
      2 2 (mat2_from_entries 0 0 0 0).
Proof.
  intros l Hlen.
  rewrite Zlength_correct in Hlen.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  unfold rep_matrix, matrix_shape, mat2_from_entries, row_major_index.
  split.
  - split; lia.
  - split.
    + reflexivity.
    + intros i j Hi Hj.
      assert (Hi01 : i = 0 \/ i = 1) by lia.
      assert (Hj01 : j = 0 \/ j = 1) by lia.
      destruct Hi01 as [-> | ->]; destruct Hj01 as [-> | ->];
        unfold replace_Znth, Znth; simpl; repeat destruct Z.eq_dec; lia.
Qed.

Lemma rep_matrix_mat2_mul_mod_list :
  forall l m X Y,
    Zlength l = 4 ->
    rep_matrix
      (replace_Znth 3 (mat2_entry11 (mat2_mul_mod m X Y))
        (replace_Znth 2 (mat2_entry10 (mat2_mul_mod m X Y))
          (replace_Znth 1 (mat2_entry01 (mat2_mul_mod m X Y))
            (replace_Znth 0 (mat2_entry00 (mat2_mul_mod m X Y)) l))))
      2 2 (mat2_mul_mod m X Y).
Proof.
  intros l m X Y Hlen.
  rewrite Zlength_correct in Hlen.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  destruct l; simpl in Hlen; try lia.
  unfold rep_matrix, matrix_shape, mat2_entry00, mat2_entry01,
    mat2_entry10, mat2_entry11, row_major_index.
  split.
  - split; lia.
  - split.
    + reflexivity.
    + intros i j Hi Hj.
      assert (Hi01 : i = 0 \/ i = 1) by lia.
      assert (Hj01 : j = 0 \/ j = 1) by lia.
      destruct Hi01 as [-> | ->]; destruct Hj01 as [-> | ->];
        unfold replace_Znth, Znth; simpl; reflexivity.
Qed.

(* ====================================================== *)
(* 10. Fast power semantics                               *)
(* ====================================================== *)

Fixpoint mat2_pow_mod_nat
  (m : Z) (A : matrix) (n : nat) : matrix :=
  match n with
  | O => mat2_id
  | S n' => mat2_mul_mod m (mat2_pow_mod_nat m A n') A
  end.

Definition mat2_pow_mod
  (m : Z) (A : matrix) (n : Z) : matrix :=
  mat2_pow_mod_nat m A (Z.to_nat n).

Definition mat_pow_flat_result
  (A : matrix) (n m : Z) : matrix :=
  mat2_pow_mod m A n.

Definition matrix_congruent_on
  (rows cols m : Z) (A B : matrix) : Prop :=
  forall i j,
    0 <= i < rows ->
    0 <= j < cols ->
    (A i j) mod m = (B i j) mod m.

Lemma matrix_congruent_on_refl :
  forall rows cols m A,
    matrix_congruent_on rows cols m A A.
Proof.
  unfold matrix_congruent_on.
  intros. reflexivity.
Qed.

Lemma matrix_congruent_on_sym :
  forall rows cols m A B,
    matrix_congruent_on rows cols m A B ->
    matrix_congruent_on rows cols m B A.
Proof.
  unfold matrix_congruent_on.
  intros rows cols m A B H i j Hi Hj.
  symmetry. apply H; assumption.
Qed.

Lemma matrix_congruent_on_trans :
  forall rows cols m A B C,
    matrix_congruent_on rows cols m A B ->
    matrix_congruent_on rows cols m B C ->
    matrix_congruent_on rows cols m A C.
Proof.
  unfold matrix_congruent_on.
  intros rows cols m A B C HAB HBC i j Hi Hj.
  rewrite HAB by assumption.
  apply HBC; assumption.
Qed.

Lemma mod_mul2_l :
  forall m x y c d,
    m <> 0 ->
    ((x mod m) * c + (y mod m) * d) mod m =
    (x * c + y * d) mod m.
Proof.
  intros m x y c d Hm.
  rewrite <- Z.add_mod_idemp_l by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  rewrite <- Z.add_mod_idemp_r by lia.
  rewrite Z.mul_mod_idemp_l by lia.
  symmetry. apply Z.add_mod. lia.
Qed.

Lemma mod_mul2_r :
  forall m a b u v,
    m <> 0 ->
    (a * (u mod m) + b * (v mod m)) mod m =
    (a * u + b * v) mod m.
Proof.
  intros m a b u v Hm.
  rewrite <- Z.add_mod_idemp_l by lia.
  rewrite Z.mul_mod_idemp_r by lia.
  rewrite <- Z.add_mod_idemp_r by lia.
  rewrite Z.mul_mod_idemp_r by lia.
  symmetry. apply Z.add_mod. lia.
Qed.

Lemma dot_prod2_congr_l :
  forall m x0 x1 y0 y1 z0 z1,
    0 < m ->
    0 <= x0 -> 0 <= x1 ->
    0 <= y0 -> 0 <= y1 ->
    0 <= z0 -> 0 <= z1 ->
    x0 mod m = y0 mod m ->
    x1 mod m = y1 mod m ->
    (Z.rem (x0 * z0 + x1 * z1) m) mod m =
    (Z.rem (y0 * z0 + y1 * z1) m) mod m.
Proof.
  intros m x0 x1 y0 y1 z0 z1 Hm Hx0 Hx1 Hy0 Hy1 Hz0 Hz1 H0 H1.
  rewrite (Z.rem_mod_nonneg (x0 * z0 + x1 * z1) m) by nia.
  rewrite (Z.rem_mod_nonneg (y0 * z0 + y1 * z1) m) by nia.
  rewrite !Z.mod_mod by lia.
  rewrite (Z.add_mod (x0 * z0) (x1 * z1) m) by lia.
  rewrite (Z.add_mod (y0 * z0) (y1 * z1) m) by lia.
  rewrite (Z.mul_mod x0 z0 m) by lia.
  rewrite (Z.mul_mod x1 z1 m) by lia.
  rewrite (Z.mul_mod y0 z0 m) by lia.
  rewrite (Z.mul_mod y1 z1 m) by lia.
  rewrite H0, H1. reflexivity.
Qed.

Lemma dot_prod2_congr_r :
  forall m x0 x1 z0 z1 w0 w1,
    0 < m ->
    0 <= x0 -> 0 <= x1 ->
    0 <= z0 -> 0 <= z1 ->
    0 <= w0 -> 0 <= w1 ->
    z0 mod m = w0 mod m ->
    z1 mod m = w1 mod m ->
    (Z.rem (x0 * z0 + x1 * z1) m) mod m =
    (Z.rem (x0 * w0 + x1 * w1) m) mod m.
Proof.
  intros m x0 x1 z0 z1 w0 w1 Hm Hx0 Hx1 Hz0 Hz1 Hw0 Hw1 H0 H1.
  rewrite (Z.rem_mod_nonneg (x0 * z0 + x1 * z1) m) by nia.
  rewrite (Z.rem_mod_nonneg (x0 * w0 + x1 * w1) m) by nia.
  rewrite !Z.mod_mod by lia.
  rewrite (Z.add_mod (x0 * z0) (x1 * z1) m) by lia.
  rewrite (Z.add_mod (x0 * w0) (x1 * w1) m) by lia.
  rewrite (Z.mul_mod x0 z0 m) by lia.
  rewrite (Z.mul_mod x1 z1 m) by lia.
  rewrite (Z.mul_mod x0 w0 m) by lia.
  rewrite (Z.mul_mod x1 w1 m) by lia.
  rewrite H0, H1. reflexivity.
Qed.

Lemma mod_mul2_assoc_entry :
  forall m a00 a01 b00 b01 b10 b11 c00 c10,
    0 < m ->
    0 <= a00 -> 0 <= a01 ->
    0 <= b00 -> 0 <= b01 -> 0 <= b10 -> 0 <= b11 ->
    0 <= c00 -> 0 <= c10 ->
    (Z.rem
       (Z.rem (a00 * b00 + a01 * b10) m * c00 +
        Z.rem (a00 * b01 + a01 * b11) m * c10) m) mod m =
    (Z.rem
       (a00 * Z.rem (b00 * c00 + b01 * c10) m +
        a01 * Z.rem (b10 * c00 + b11 * c10) m) m) mod m.
Proof.
  intros m a00 a01 b00 b01 b10 b11 c00 c10 Hm
    Ha00 Ha01 Hb00 Hb01 Hb10 Hb11 Hc00 Hc10.
  rewrite (Z.rem_mod_nonneg (a00 * b00 + a01 * b10) m) by nia.
  rewrite (Z.rem_mod_nonneg (a00 * b01 + a01 * b11) m) by nia.
  rewrite (Z.rem_mod_nonneg (b00 * c00 + b01 * c10) m) by nia.
  rewrite (Z.rem_mod_nonneg (b10 * c00 + b11 * c10) m) by nia.
  rewrite (Z.rem_mod_nonneg
    ((a00 * b00 + a01 * b10) mod m * c00 +
     (a00 * b01 + a01 * b11) mod m * c10) m)
    by (try apply Z.add_nonneg_nonneg; try apply Z.mul_nonneg_nonneg;
        try apply Z.mod_pos_bound; lia).
  rewrite (Z.rem_mod_nonneg
    (a00 * ((b00 * c00 + b01 * c10) mod m) +
     a01 * ((b10 * c00 + b11 * c10) mod m)) m)
    by (try apply Z.add_nonneg_nonneg; try apply Z.mul_nonneg_nonneg;
        try apply Z.mod_pos_bound; lia).
  rewrite mod_mul2_l by lia.
  rewrite mod_mul2_r by lia.
  repeat rewrite Z.mod_mod by lia.
  f_equal. ring.
Qed.

Lemma mat2_mul_mod_congr_l :
  forall m X Y Z,
    mat2_mod m X ->
    mat2_mod m Y ->
    mat2_mod m Z ->
    matrix_congruent_on 2 2 m X Y ->
    matrix_congruent_on 2 2 m
      (mat2_mul_mod m X Z)
      (mat2_mul_mod m Y Z).
Proof.
  intros m X Y Z HX HY HZ HXY i j Hi Hj.
  destruct HX as [Hm HXentries].
  assert (HX' : mat2_mod m X) by (split; assumption).
  unfold mat2_mul_mod, matrix_mul, dot_prod.
  change (Z.to_nat 2) with 2%nat.
  simpl.
  apply dot_prod2_congr_l; try lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - apply HXY; lia.
  - apply HXY; lia.
Qed.

Lemma mat2_mul_mod_congr_r :
  forall m X Y Z,
    mat2_mod m X ->
    mat2_mod m Y ->
    mat2_mod m Z ->
    matrix_congruent_on 2 2 m Y Z ->
    matrix_congruent_on 2 2 m
      (mat2_mul_mod m X Y)
      (mat2_mul_mod m X Z).
Proof.
  intros m X Y Z HX HY HZ HYZ i j Hi Hj.
  destruct HX as [Hm HXentries].
  assert (HX' : mat2_mod m X) by (split; assumption).
  unfold mat2_mul_mod, matrix_mul, dot_prod.
  change (Z.to_nat 2) with 2%nat.
  simpl.
  apply dot_prod2_congr_r; try lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - eapply mat2_mod_entry_nonneg; eauto; lia.
  - apply HYZ; lia.
  - apply HYZ; lia.
Qed.

Lemma mat2_mul_mod_congr :
  forall m A A' B B',
    mat2_mod m A ->
    mat2_mod m A' ->
    mat2_mod m B ->
    mat2_mod m B' ->
    matrix_congruent_on 2 2 m A A' ->
    matrix_congruent_on 2 2 m B B' ->
    matrix_congruent_on 2 2 m
      (mat2_mul_mod m A B)
      (mat2_mul_mod m A' B').
Proof.
  intros m A A' B B' HA HA' HB HB' HAA' HBB'.
  apply matrix_congruent_on_trans with (B := mat2_mul_mod m A' B).
  - apply mat2_mul_mod_congr_l; eauto.
  - apply mat2_mul_mod_congr_r; eauto.
Qed.

Lemma mat2_mul_mod_assoc_entry00 :
  forall m A B C,
    mat2_mod m A ->
    mat2_mod m B ->
    mat2_mod m C ->
    (mat2_mul_mod m (mat2_mul_mod m A B) C 0 0) mod m =
    (mat2_mul_mod m A (mat2_mul_mod m B C) 0 0) mod m.
Proof.
  intros m A B C HA HB HC.
  destruct HA as [Hm HAentries].
  assert (HA' : mat2_mod m A) by (split; assumption).
  assert (HB' : mat2_mod m B) by exact HB.
  assert (HC' : mat2_mod m C) by exact HC.
  unfold mat2_mul_mod, matrix_mul, dot_prod.
  change (Z.to_nat 2) with 2%nat.
  simpl.
  apply mod_mul2_assoc_entry; try lia;
    eapply mat2_mod_entry_nonneg; eauto; lia.
Qed.

Lemma mat2_mul_mod_assoc_entry01 :
  forall m A B C,
    mat2_mod m A ->
    mat2_mod m B ->
    mat2_mod m C ->
    (mat2_mul_mod m (mat2_mul_mod m A B) C 0 1) mod m =
    (mat2_mul_mod m A (mat2_mul_mod m B C) 0 1) mod m.
Proof.
  intros m A B C HA HB HC.
  destruct HA as [Hm HAentries].
  assert (HA' : mat2_mod m A) by (split; assumption).
  unfold mat2_mul_mod, matrix_mul, dot_prod.
  change (Z.to_nat 2) with 2%nat.
  simpl.
  apply mod_mul2_assoc_entry; try lia;
    eapply mat2_mod_entry_nonneg; eauto; lia.
Qed.

Lemma mat2_mul_mod_assoc_entry10 :
  forall m A B C,
    mat2_mod m A ->
    mat2_mod m B ->
    mat2_mod m C ->
    (mat2_mul_mod m (mat2_mul_mod m A B) C 1 0) mod m =
    (mat2_mul_mod m A (mat2_mul_mod m B C) 1 0) mod m.
Proof.
  intros m A B C HA HB HC.
  destruct HA as [Hm HAentries].
  assert (HA' : mat2_mod m A) by (split; assumption).
  unfold mat2_mul_mod, matrix_mul, dot_prod.
  change (Z.to_nat 2) with 2%nat.
  simpl.
  apply mod_mul2_assoc_entry; try lia;
    eapply mat2_mod_entry_nonneg; eauto; lia.
Qed.

Lemma mat2_mul_mod_assoc_entry11 :
  forall m A B C,
    mat2_mod m A ->
    mat2_mod m B ->
    mat2_mod m C ->
    (mat2_mul_mod m (mat2_mul_mod m A B) C 1 1) mod m =
    (mat2_mul_mod m A (mat2_mul_mod m B C) 1 1) mod m.
Proof.
  intros m A B C HA HB HC.
  destruct HA as [Hm HAentries].
  assert (HA' : mat2_mod m A) by (split; assumption).
  unfold mat2_mul_mod, matrix_mul, dot_prod.
  change (Z.to_nat 2) with 2%nat.
  simpl.
  apply mod_mul2_assoc_entry; try lia;
    eapply mat2_mod_entry_nonneg; eauto; lia.
Qed.

Lemma mat2_mul_mod_assoc_congr :
  forall m A B C,
    mat2_mod m A ->
    mat2_mod m B ->
    mat2_mod m C ->
    matrix_congruent_on 2 2 m
      (mat2_mul_mod m (mat2_mul_mod m A B) C)
      (mat2_mul_mod m A (mat2_mul_mod m B C)).
Proof.
  intros m A B C HA HB HC i j Hi Hj.
  assert (Hi01 : i = 0 \/ i = 1) by lia.
  assert (Hj01 : j = 0 \/ j = 1) by lia.
  destruct Hi01 as [-> | ->]; destruct Hj01 as [-> | ->].
  - apply mat2_mul_mod_assoc_entry00; assumption.
  - apply mat2_mul_mod_assoc_entry01; assumption.
  - apply mat2_mul_mod_assoc_entry10; assumption.
  - apply mat2_mul_mod_assoc_entry11; assumption.
Qed.

Lemma mat2_mod_entry_rem_mod :
  forall m X i j,
    mat2_mod m X ->
    0 <= i < 2 ->
    0 <= j < 2 ->
    (Z.rem (X i j) m) mod m = (X i j) mod m.
Proof.
  intros m X i j [_ Hentries] Hi Hj.
  rewrite Z.rem_mod_nonneg by (pose proof (Hentries i j Hi Hj); lia).
  apply Z.mod_mod.
  pose proof (Hentries i j Hi Hj); lia.
Qed.

Lemma mat2_pow_mod_mod :
  forall m A n,
    2 <= m ->
    mat2_mod m A ->
    mat2_mod m (mat2_pow_mod_nat m A n).
Proof.
  intros m A n Hm2 HA.
  induction n.
  - apply mat2_id_mod. lia.
  - simpl.
    apply mat2_mul_mod_mod_from_mod; assumption.
Qed.

Lemma mat2_pow_mod_square_nat :
  forall m Base (k : nat),
    2 <= m ->
    mat2_mod m Base ->
    matrix_congruent_on 2 2 m
      (mat2_pow_mod_nat m Base (k + k)%nat)
      (mat2_pow_mod_nat m (mat2_mul_mod m Base Base) k).
Proof.
  intros m Base k Hm HBase.
  induction k.
  - simpl. apply matrix_congruent_on_refl.
  - replace (S k + S k)%nat with (S (S (k + k)%nat)) by lia.
    simpl.
    set (P := mat2_pow_mod_nat m Base (k + k)%nat).
    set (Q := mat2_pow_mod_nat m (mat2_mul_mod m Base Base) k).
    assert (HBase2 : mat2_mod m (mat2_mul_mod m Base Base)).
    { apply mat2_mul_mod_mod_from_mod; assumption. }
    assert (HP : mat2_mod m P).
    { subst P. apply mat2_pow_mod_mod; assumption. }
    assert (HQ : mat2_mod m Q).
    { subst Q. apply mat2_pow_mod_mod; assumption. }
    assert (HPB : mat2_mod m (mat2_mul_mod m P Base)).
    { apply mat2_mul_mod_mod_from_mod; assumption. }
    assert (HQB : mat2_mod m (mat2_mul_mod m Q Base)).
    { apply mat2_mul_mod_mod_from_mod; assumption. }
    apply matrix_congruent_on_trans with
      (B := mat2_mul_mod m (mat2_mul_mod m Q Base) Base).
    + apply mat2_mul_mod_congr_l; try exact HPB; try exact HQB; try assumption.
      apply mat2_mul_mod_congr_l; try exact HP; try exact HQ; try assumption.
    + apply mat2_mul_mod_assoc_congr; assumption.
Qed.

Lemma Z_to_nat_mul_2 :
  forall z,
    0 <= z ->
    Z.to_nat (z * 2) = (Z.to_nat z + Z.to_nat z)%nat.
Proof.
  intros z Hz.
  replace (z * 2) with (z + z) by ring.
  rewrite Z2Nat.inj_add by lia.
  reflexivity.
Qed.

Lemma Z_to_nat_mul_2_plus_1 :
  forall z,
    0 <= z * 2 ->
    Z.to_nat (z * 2 + 1) = S (Z.to_nat (z * 2)).
Proof.
  intros z Hz2.
  replace (z * 2 + 1) with (Z.succ (z * 2)) by lia.
  rewrite Z2Nat.inj_succ by exact Hz2.
  reflexivity.
Qed.

Lemma mat2_id_left_congr :
  forall m X,
    mat2_mod m X ->
    matrix_congruent_on 2 2 m (mat2_mul_mod m mat2_id X) X.
Proof.
  intros m X HX i j Hi Hj.
  destruct HX as [Hm Hentries].
  assert (Hi01 : i = 0 \/ i = 1) by lia.
  assert (Hj01 : j = 0 \/ j = 1) by lia.
  destruct Hi01 as [-> | ->]; destruct Hj01 as [-> | ->].
  - unfold mat2_mul_mod, matrix_mul, dot_prod, mat2_id, matrix_id.
    change (Z.to_nat 2) with 2%nat. simpl.
    repeat (destruct Z.eq_dec as [? | ?]; subst; try lia).
    replace (0 + 1 * X 0 0 + 0 * X 1 0) with (X 0 0) by ring.
    replace (match X 0 0 with Z0 => 0 | Zpos y => Z.pos y | Zneg y => Z.neg y end + 0)
      with (X 0 0) by (destruct (X 0 0); reflexivity).
    assert (HX00 := Hentries 0 0 ltac:(lia) ltac:(lia)).
    rewrite (Z.rem_mod_nonneg (X 0 0) m) by lia.
    apply Z.mod_mod. lia.
  - unfold mat2_mul_mod, matrix_mul, dot_prod, mat2_id, matrix_id.
    change (Z.to_nat 2) with 2%nat. simpl.
    repeat (destruct Z.eq_dec as [? | ?]; subst; try lia).
    replace (0 + 1 * X 0 1 + 0 * X 1 1) with (X 0 1) by ring.
    replace (match X 0 1 with Z0 => 0 | Zpos y => Z.pos y | Zneg y => Z.neg y end + 0)
      with (X 0 1) by (destruct (X 0 1); reflexivity).
    assert (HX01 := Hentries 0 1 ltac:(lia) ltac:(lia)).
    rewrite (Z.rem_mod_nonneg (X 0 1) m) by lia.
    apply Z.mod_mod. lia.
  - unfold mat2_mul_mod, matrix_mul, dot_prod, mat2_id, matrix_id.
    change (Z.to_nat 2) with 2%nat. simpl.
    repeat (destruct Z.eq_dec as [? | ?]; subst; try lia).
    replace (0 + 0 * X 0 0 + 1 * X 1 0) with (X 1 0) by ring.
    replace (match X 1 0 with Z0 => 0 | Zpos y => Z.pos y | Zneg y => Z.neg y end)
      with (X 1 0) by (destruct (X 1 0); reflexivity).
    assert (HX10 := Hentries 1 0 ltac:(lia) ltac:(lia)).
    rewrite (Z.rem_mod_nonneg (X 1 0) m) by lia.
    apply Z.mod_mod. lia.
  - unfold mat2_mul_mod, matrix_mul, dot_prod, mat2_id, matrix_id.
    change (Z.to_nat 2) with 2%nat. simpl.
    repeat (destruct Z.eq_dec as [? | ?]; subst; try lia).
    replace (0 + 0 * X 0 1 + 1 * X 1 1) with (X 1 1) by ring.
    replace (match X 1 1 with Z0 => 0 | Zpos y => Z.pos y | Zneg y => Z.neg y end)
      with (X 1 1) by (destruct (X 1 1); reflexivity).
    assert (HX11 := Hentries 1 1 ltac:(lia) ltac:(lia)).
    rewrite (Z.rem_mod_nonneg (X 1 1) m) by lia.
    apply Z.mod_mod. lia.
Qed.

Lemma mat2_id_right_congr :
  forall m X,
    mat2_mod m X ->
    matrix_congruent_on 2 2 m (mat2_mul_mod m X mat2_id) X.
Proof.
  intros m X HX i j Hi Hj.
  destruct HX as [Hm Hentries].
  assert (Hi01 : i = 0 \/ i = 1) by lia.
  assert (Hj01 : j = 0 \/ j = 1) by lia.
  destruct Hi01 as [-> | ->]; destruct Hj01 as [-> | ->].
  - unfold mat2_mul_mod, matrix_mul, dot_prod, mat2_id, matrix_id.
    change (Z.to_nat 2) with 2%nat. simpl.
    repeat (destruct Z.eq_dec as [? | ?]; subst; try lia).
    replace (X 0 0 * 1 + X 0 1 * 0) with (X 0 0) by ring.
    replace (match X 0 0 with Z0 => 0 | Zpos y => Z.pos y | Zneg y => Z.neg y end)
      with (X 0 0) by (destruct (X 0 0); reflexivity).
    assert (HX00 := Hentries 0 0 ltac:(lia) ltac:(lia)).
    rewrite (Z.rem_mod_nonneg (X 0 0) m) by lia.
    apply Z.mod_mod. lia.
  - unfold mat2_mul_mod, matrix_mul, dot_prod, mat2_id, matrix_id.
    change (Z.to_nat 2) with 2%nat. simpl.
    repeat (destruct Z.eq_dec as [? | ?]; subst; try lia).
    replace (X 0 0 * 0 + X 0 1 * 1) with (X 0 1) by ring.
    replace (match X 0 1 with Z0 => 0 | Zpos y => Z.pos y | Zneg y => Z.neg y end)
      with (X 0 1) by (destruct (X 0 1); reflexivity).
    assert (HX01 := Hentries 0 1 ltac:(lia) ltac:(lia)).
    rewrite (Z.rem_mod_nonneg (X 0 1) m) by lia.
    apply Z.mod_mod. lia.
  - unfold mat2_mul_mod, matrix_mul, dot_prod, mat2_id, matrix_id.
    change (Z.to_nat 2) with 2%nat. simpl.
    repeat (destruct Z.eq_dec as [? | ?]; subst; try lia).
    replace (X 1 0 * 1 + X 1 1 * 0) with (X 1 0) by ring.
    replace (match X 1 0 with Z0 => 0 | Zpos y => Z.pos y | Zneg y => Z.neg y end)
      with (X 1 0) by (destruct (X 1 0); reflexivity).
    assert (HX10 := Hentries 1 0 ltac:(lia) ltac:(lia)).
    rewrite (Z.rem_mod_nonneg (X 1 0) m) by lia.
    apply Z.mod_mod. lia.
  - unfold mat2_mul_mod, matrix_mul, dot_prod, mat2_id, matrix_id.
    change (Z.to_nat 2) with 2%nat. simpl.
    repeat (destruct Z.eq_dec as [? | ?]; subst; try lia).
    replace (X 1 0 * 0 + X 1 1 * 1) with (X 1 1) by ring.
    replace (match X 1 1 with Z0 => 0 | Zpos y => Z.pos y | Zneg y => Z.neg y end)
      with (X 1 1) by (destruct (X 1 1); reflexivity).
    assert (HX11 := Hentries 1 1 ltac:(lia) ltac:(lia)).
    rewrite (Z.rem_mod_nonneg (X 1 1) m) by lia.
    apply Z.mod_mod. lia.
Qed.

Lemma mat2_base_pow_comm_nat :
  forall m Base (k : nat),
    2 <= m ->
    mat2_mod m Base ->
    matrix_congruent_on 2 2 m
      (mat2_mul_mod m Base (mat2_pow_mod_nat m Base k))
      (mat2_mul_mod m (mat2_pow_mod_nat m Base k) Base).
Proof.
  intros m Base k Hm HBase.
  induction k.
  - simpl.
    apply matrix_congruent_on_trans with (B := Base).
    + apply mat2_id_right_congr. exact HBase.
    + apply matrix_congruent_on_sym.
      apply mat2_id_left_congr. exact HBase.
  - simpl.
    set (P := mat2_pow_mod_nat m Base k).
    assert (HP : mat2_mod m P).
    { subst P. apply mat2_pow_mod_mod; assumption. }
    assert (HBaseP : mat2_mod m (mat2_mul_mod m Base P)).
    { apply mat2_mul_mod_mod_from_mod; assumption. }
    assert (HPBase : mat2_mod m (mat2_mul_mod m P Base)).
    { apply mat2_mul_mod_mod_from_mod; assumption. }
    apply matrix_congruent_on_trans with
      (B := mat2_mul_mod m (mat2_mul_mod m Base P) Base).
    + apply matrix_congruent_on_sym.
      apply mat2_mul_mod_assoc_congr; assumption.
    + apply mat2_mul_mod_congr_l; try exact HBaseP; try exact HPBase; try assumption.
Qed.

Definition mat_pow_flat_sem
  (A : matrix) (n m : Z)
  (R Base : matrix) (e : Z) : Prop :=
  matrix_congruent_on 2 2 m
    (mat2_mul_mod m R (mat2_pow_mod m Base e))
    (mat_pow_flat_result A n m).

Definition mat_pow_flat_inv
  (A : matrix) (n m : Z)
  (R Base : matrix) (e : Z) : Prop :=
  2 <= m /\
  0 <= e /\
  mat2_mod m R /\
  mat2_mod m Base /\
  mat_pow_flat_sem A n m R Base e.

Lemma mat_pow_flat_inv_mod_R :
  forall A n m R Base e,
    mat_pow_flat_inv A n m R Base e ->
    mat2_mod m R.
Proof.
  intros A n m R Base e Hinv.
  destruct Hinv as [_ [_ [HR _]]].
  exact HR.
Qed.

Lemma mat_pow_flat_inv_mod_Base :
  forall A n m R Base e,
    mat_pow_flat_inv A n m R Base e ->
    mat2_mod m Base.
Proof.
  intros A n m R Base e Hinv.
  destruct Hinv as [_ [_ [_ [HBase _]]]].
  exact HBase.
Qed.

Lemma mat_pow_flat_inv_init :
  forall A n m,
    2 <= m ->
    0 <= n ->
    mat2_mod m A ->
    mat_pow_flat_inv A n m mat2_id A n.
Proof.
  intros A n m Hm2 Hn HA.
  unfold mat_pow_flat_inv.
  split.
  - exact Hm2.
  - split.
    + exact Hn.
    + split.
      * apply mat2_id_mod. lia.
      * split.
        -- exact HA.
        -- unfold mat_pow_flat_sem, mat_pow_flat_result, mat2_pow_mod.
           apply mat2_id_left_congr.
           apply mat2_pow_mod_mod; assumption.
Qed.

Lemma mat_pow_flat_inv_take_odd :
  forall A n m R Base e,
    e % 2 = 1 ->
    e > 0 ->
    mat_pow_flat_inv A n m R Base e ->
    mat_pow_flat_inv A n m
      (mat2_mul_mod m R Base) Base ((e ÷ 2) * 2).
Proof.
  intros A n m R Base e Hodd He Hinv.
  destruct Hinv as [Hm2 [He0 [HR [HBase Hsem]]]].
  assert (Heq : e = (e ÷ 2) * 2 + 1).
  {
    pose proof (Z.quot_rem e 2 ltac:(lia)) as Hqr.
    rewrite Hodd in Hqr.
    lia.
  }
  assert (Hz2 : 0 <= (e ÷ 2) * 2) by lia.
  unfold mat_pow_flat_inv.
  split.
  - exact Hm2.
  - split.
    + exact Hz2.
    + split.
      * apply mat2_mul_mod_mod_from_mod; assumption.
      * split.
        -- exact HBase.
        -- unfold mat_pow_flat_sem, mat_pow_flat_result, mat2_pow_mod in *.
           rewrite Heq in Hsem.
           rewrite Z_to_nat_mul_2_plus_1 in Hsem by exact Hz2.
           simpl in Hsem.
           set (P := mat2_pow_mod_nat m Base (Z.to_nat ((e ÷ 2) * 2))).
           assert (HP : mat2_mod m P).
           { subst P. apply mat2_pow_mod_mod; assumption. }
           assert (HRBase : mat2_mod m (mat2_mul_mod m R Base)).
           { apply mat2_mul_mod_mod_from_mod; assumption. }
           assert (HBaseP : mat2_mod m (mat2_mul_mod m Base P)).
           { apply mat2_mul_mod_mod_from_mod; assumption. }
           assert (HPBase : mat2_mod m (mat2_mul_mod m P Base)).
           { apply mat2_mul_mod_mod_from_mod; assumption. }
           apply matrix_congruent_on_trans with
             (B := mat2_mul_mod m R (mat2_mul_mod m Base P)).
           ++ apply mat2_mul_mod_assoc_congr; assumption.
           ++ apply matrix_congruent_on_trans with
                (B := mat2_mul_mod m R (mat2_mul_mod m P Base)).
              ** apply mat2_mul_mod_congr_r; try exact HR; try exact HBaseP;
                   try exact HPBase; try assumption.
                 subst P. apply mat2_base_pow_comm_nat; assumption.
              ** exact Hsem.
Qed.

Lemma mat_pow_flat_inv_take_even :
  forall A n m R Base e,
    e % 2 <> 1 ->
    e > 0 ->
    mat_pow_flat_inv A n m R Base e ->
    mat_pow_flat_inv A n m R Base ((e ÷ 2) * 2).
Proof.
  intros A n m R Base e Hodd He Hinv.
  assert (Heq : (e ÷ 2) * 2 = e).
  {
    pose proof (Z.rem_bound_pos e 2 ltac:(lia) ltac:(lia)) as Hbound.
    assert (e % 2 = 0) by lia.
    pose proof (Z.quot_rem e 2 ltac:(lia)) as Hqr.
    rewrite H in Hqr. lia.
  }
  rewrite Heq.
  exact Hinv.
Qed.

Lemma mat_pow_flat_inv_square :
  forall A n m R Base e,
    mat_pow_flat_inv A n m R Base ((e ÷ 2) * 2) ->
    mat_pow_flat_inv A n m R (mat2_mul_mod m Base Base) (e ÷ 2).
Proof.
  intros A n m R Base e Hinv.
  destruct Hinv as [Hm2 [Hz2 [HR [HBase Hsem]]]].
  assert (Hz : 0 <= e ÷ 2) by lia.
  unfold mat_pow_flat_inv.
  split.
  - exact Hm2.
  - split.
    + exact Hz.
    + split.
      * exact HR.
      * split.
        -- apply mat2_mul_mod_mod_from_mod; assumption.
        -- unfold mat_pow_flat_sem, mat_pow_flat_result, mat2_pow_mod in *.
           rewrite Z_to_nat_mul_2 in Hsem by exact Hz.
           apply matrix_congruent_on_trans with
             (B := mat2_mul_mod m R
                     (mat2_pow_mod_nat m Base
                        (Z.to_nat (e ÷ 2) + Z.to_nat (e ÷ 2))%nat)).
           ++ apply mat2_mul_mod_congr_r.
              ** exact HR.
              ** apply mat2_pow_mod_mod.
                 --- exact Hm2.
                 --- apply mat2_mul_mod_mod_from_mod; assumption.
              ** apply mat2_pow_mod_mod.
                 --- exact Hm2.
                 --- exact HBase.
              ** apply matrix_congruent_on_sym.
                 apply (mat2_pow_mod_square_nat m Base (Z.to_nat (e ÷ 2))); assumption.
           ++ exact Hsem.
Qed.

Lemma mat_pow_flat_inv_zero_result :
  forall A n m R Base,
    mat_pow_flat_inv A n m R Base 0 ->
    matrix_congruent_on 2 2 m R (mat_pow_flat_result A n m).
Proof.
  intros A n m R Base Hinv.
  destruct Hinv as [Hm2 [_ [HR [HBase Hsem]]]].
  unfold mat_pow_flat_sem, mat2_pow_mod in Hsem.
  simpl in Hsem.
  apply matrix_congruent_on_trans with
    (B := mat2_mul_mod m R mat2_id).
  - apply matrix_congruent_on_sym.
    apply mat2_id_right_congr. exact HR.
  - exact Hsem.
Qed.

Definition mat2_mul_mod_result
  (m : Z) (X Y Zm : matrix) : Prop :=
  matrix_eq_on 2 2 Zm (mat2_mul_mod m X Y).

Definition mat2_mul_mod_out_entries
  (m : Z) (X Y : matrix)
  (z0 z1 z2 z3 : Z) : Prop :=
  z0 = mat2_entry00 (mat2_mul_mod m X Y) /\
  z1 = mat2_entry01 (mat2_mul_mod m X Y) /\
  z2 = mat2_entry10 (mat2_mul_mod m X Y) /\
  z3 = mat2_entry11 (mat2_mul_mod m X Y).

Lemma mat2_mul_mod_out_entries_intro :
  forall m X Y,
    mat2_mul_mod_out_entries m X Y
      (mat2_entry00 (mat2_mul_mod m X Y))
      (mat2_entry01 (mat2_mul_mod m X Y))
      (mat2_entry10 (mat2_mul_mod m X Y))
      (mat2_entry11 (mat2_mul_mod m X Y)).
Proof.
  intros. unfold mat2_mul_mod_out_entries. repeat split; reflexivity.
Qed.
