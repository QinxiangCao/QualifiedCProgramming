Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

From MonadLib Require Export MonadLib.
Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.

From MonadLib.Examples Require Export union_find_err.

#[export] Instance uf_state_equiv : Equiv uf_state := eq.

Lemma uf_state_equiv_valid :
  forall s1 s2 x,
    equiv s1 s2 ->
    valid s1 x <-> valid s2 x.
Proof.
  intros s1 s2 x Heq.
  cbv [equiv uf_state_equiv] in Heq.
  subst s2.
  reflexivity.
Qed.

Lemma uf_abstract_equiv :
  forall s1 s2 repr_of,
    equiv s1 s2 ->
    uf_abstract s1 repr_of ->
    uf_abstract s2 repr_of.
Proof.
  intros s1 s2 repr_of Heq Habs.
  cbv [equiv uf_state_equiv] in Heq.
  subst s2.
  exact Habs.
Qed.

Lemma merge_valid_equiv :
  forall s1 s2 repr_of x y repr_of',
    equiv s1 s2 ->
    merge (valid s1) repr_of x y repr_of' ->
    merge (valid s2) repr_of x y repr_of'.
Proof.
  intros s1 s2 repr_of x y repr_of' Heq Hmerge.
  cbv [equiv uf_state_equiv] in Heq.
  subst s2.
  exact Hmerge.
Qed.

Definition applyf {A B : Type} (f : A -> B) (a : A) : B := f a.

Definition uf_state_of (n : Z) (parents ranks : list Z) : uf_state :=
  {|
    uf_size := n;
    uf_parent := fun x =>
      if Z_le_dec 0 x then
        if Z_lt_dec x n then Znth x parents 0 else 0
      else 0;
    uf_rank := fun x =>
      if Z_le_dec 0 x then
        if Z_lt_dec x n then Znth x ranks 0 else 0
      else 0;
  |}.

Lemma uf_state_of_parent_read :
  forall n ps rs x,
    0 <= x < n ->
    uf_parent (uf_state_of n ps rs) x = Znth x ps 0.
Proof.
  intros n ps rs x Hx.
  unfold uf_state_of; simpl.
  destruct (Z_le_dec 0 x) as [_ | Hlt].
  - destruct (Z_lt_dec x n) as [_ | Hge].
    + reflexivity.
    + lia.
  - lia.
Qed.

Lemma uf_state_of_rank_read :
  forall n ps rs x,
    0 <= x < n ->
    uf_rank (uf_state_of n ps rs) x = Znth x rs 0.
Proof.
  intros n ps rs x Hx.
  unfold uf_state_of; simpl.
  destruct (Z_le_dec 0 x) as [_ | Hlt].
  - destruct (Z_lt_dec x n) as [_ | Hge].
    + reflexivity.
    + lia.
  - lia.
Qed.

Lemma uf_state_of_set_parent_replace :
  forall n ps rs x p,
    0 <= x < n ->
    Zlength ps = n ->
    set_parent_state x p (uf_state_of n ps rs) =
      uf_state_of n (replace_Znth x p ps) rs.
Proof.
  intros n ps rs x p Hx Hlen.
  unfold set_parent_state, uf_state_of.
  f_equal.
  apply fun_ext1; intros z.
  simpl.
  destruct (Z_le_dec 0 z) as [Hz0 | Hz0].
  - destruct (Z_lt_dec z n) as [Hzn | Hzn].
    + destruct (Z.eq_dec z x) as [Hzx | Hzx].
      * subst z.
        rewrite Znth_replace_Znth_Same; lia.
      * rewrite Znth_replace_Znth_Diff; try lia.
    + destruct (Z.eq_dec z x).
      * lia.
      * reflexivity.
  - destruct (Z.eq_dec z x).
    + lia.
    + reflexivity.
Qed.

Lemma uf_state_of_set_rank_replace :
  forall n ps rs x k,
    0 <= x < n ->
    Zlength rs = n ->
    set_rank_state x k (uf_state_of n ps rs) =
      uf_state_of n ps (replace_Znth x k rs).
Proof.
  intros n ps rs x k Hx Hlen.
  unfold set_rank_state, uf_state_of.
  f_equal.
  apply fun_ext1; intros z.
  simpl.
  destruct (Z_le_dec 0 z) as [Hz0 | Hz0].
  - destruct (Z_lt_dec z n) as [Hzn | Hzn].
    + destruct (Z.eq_dec z x) as [Hzx | Hzx].
      * subst z.
        rewrite Znth_replace_Znth_Same; lia.
      * rewrite Znth_replace_Znth_Diff; try lia.
    + destruct (Z.eq_dec z x).
      * lia.
      * reflexivity.
  - destruct (Z.eq_dec z x).
    + lia.
    + reflexivity.
Qed.

Lemma uf_state_of_inc_rank_replace :
  forall n ps rs x,
    0 <= x < n ->
    Zlength rs = n ->
    inc_rank_state x (uf_state_of n ps rs) =
      uf_state_of n ps (replace_Znth x (Znth x rs 0 + 1) rs).
Proof.
  intros n ps rs x Hx Hlen.
  unfold inc_rank_state.
  rewrite uf_state_of_rank_read by exact Hx.
  apply uf_state_of_set_rank_replace; auto.
Qed.

Lemma uf_find_unfold : equiv uf_find (uf_find_f uf_find).
Proof.
  intros.
  unfold uf_find.
  apply BW_fixpoint'.
  unfold uf_find_f.
  mono_cont_auto.
Qed.

Definition uf_find_after_read (x p : elem) : program uf_state elem :=
  choice
    (assume!! (p = x);; return x)
    (assume!! (p <> x);;
     y <- uf_find p;;
     write_parent x y;;
     return y).

Definition uf_find_after_rec (x : elem) (y : elem) : program uf_state elem :=
  write_parent x y;; return y.

Definition uf_union_after_find_y (rx ry : elem) : program uf_state unit :=
  choice
    (assume!! (rx = ry);; return tt)
    (assume!! (rx <> ry);;
     rx_rank <- read_rank rx;;
     ry_rank <- read_rank ry;;
     choice
       (assume!! (ry_rank < rx_rank);;
        write_parent ry rx)
       (choice
          (assume!! (rx_rank < ry_rank);;
           write_parent rx ry)
          (assume!! (rx_rank = ry_rank);;
           write_parent rx ry;;
           bump_rank ry))).

Definition uf_union_after_find_x (y rx : elem) : program uf_state unit :=
  ry <- uf_find y;;
  uf_union_after_find_y rx ry.

Definition uf_union_after_rank_rx
  (rx ry rx_rank : elem) : program uf_state unit :=
  ry_rank <- read_rank ry;;
  choice
    (assume!! (ry_rank < rx_rank);;
     write_parent ry rx)
    (choice
       (assume!! (rx_rank < ry_rank);;
        write_parent rx ry)
       (assume!! (rx_rank = ry_rank);;
        write_parent rx ry;;
        bump_rank ry)).

Definition uf_union_after_rank_ry
  (rx ry rx_rank ry_rank : elem) : program uf_state unit :=
  choice
    (assume!! (ry_rank < rx_rank);;
     write_parent ry rx)
    (choice
       (assume!! (rx_rank < ry_rank);;
        write_parent rx ry)
       (assume!! (rx_rank = ry_rank);;
        write_parent rx ry;;
        bump_rank ry)).

Lemma replace_Znth_Zlength :
  forall {A : Type} (n : Z) (a : A) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros A n a l.
  rewrite !Zlength_correct.
  f_equal.
  unfold replace_Znth.
  generalize (Z.to_nat n) as m.
  intro m.
  revert l.
  induction m; intros l; destruct l; simpl; auto.
Qed.
