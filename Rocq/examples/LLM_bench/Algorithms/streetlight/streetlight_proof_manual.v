Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.streetlight Require Import streetlight_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.streetlight.streetlight_lib.
Local Open Scope sac.

Require Import AUXLib.MonotonicList.
Ltac street_shape_term t n :=
  first [assumption |
    apply (proj2 (streetlight_shape_Forall t n)); split; assumption |
    match t with
    | replace_Znth ?r (replace_Znth ?c ?v (Znth ?r ?old ?d)) ?old =>
      apply (streetlight_shape_update old n r c v d); [street_shape_term old n | lia]
    end |
    match goal with
    | H : StreetlightInfRowsFacts t n _ |- _ => exact (proj1 H)
    | H : StreetlightInfProgressFacts t n _ _ |- _ => exact (proj1 (proj1 H))
    | H : StreetlightLengthsDoneFacts _ _ t _ n _ _ |- _ => exact (proj1 H)
    | H : StreetlightLengthsDoneFacts _ _ _ t n _ _ |- _ => exact (proj1 (proj2 H))
    | H : StreetlightLeftProgressFacts _ _ t _ n _ _ _ |- _ => exact (proj1 (proj1 H))
    | H : StreetlightLeftProgressFacts _ _ _ t n _ _ _ |- _ => exact (proj1 (proj2 (proj1 H)))
    | H : StreetlightLeftEndpointReadyFacts _ _ t _ n _ _ _ |- _ => exact (proj1 (proj1 (proj1 H)))
    | H : StreetlightLeftEndpointReadyFacts _ _ _ t n _ _ _ |- _ => exact (proj1 (proj2 (proj1 (proj1 H))))
    end].
Ltac street_pack :=
  repeat match goal with
  | H : StreetlightPrefixProgress ?w ?p ?d |- _ =>
    let F := fresh "HF" in assert (F : StreetlightPrefixProgressFacts w p d) by (split; [lia | exact H]); clear H; rename F into H
  | H : StreetlightInfRows ?t ?n ?r |- _ =>
    let F := fresh "HF" in assert (F : StreetlightInfRowsFacts t n r) by
      (apply (proj2 (streetlight_inf_rows_equiv t n r ltac:(lia) ltac:(street_shape_term t n))); exact H); clear H; rename F into H
  | H : StreetlightInfProgress ?t ?n ?r ?c |- _ =>
    let F := fresh "HF" in assert (F : StreetlightInfProgressFacts t n r c) by
      (apply (proj2 (streetlight_inf_progress_equiv t n r c ltac:(lia) ltac:(lia) ltac:(street_shape_term t n))); exact H); clear H; rename F into H
  | H : StreetlightLengthsDone ?p ?w ?lt ?rt ?n ?s ?k |- _ =>
    let F := fresh "HF" in assert (F : StreetlightLengthsDoneFacts p w lt rt n s k) by
      (apply (proj2 (streetlight_lengths_equiv p w lt rt n s k ltac:(lia) ltac:(street_shape_term lt n) ltac:(street_shape_term rt n))); exact H); clear H; rename F into H
  | H : StreetlightLeftProgress ?p ?w ?lt ?rt ?n ?s ?k ?l |- _ =>
    let F := fresh "HF" in assert (F : StreetlightLeftProgressFacts p w lt rt n s k l) by
      (apply (proj2 (streetlight_left_equiv p w lt rt n s k l ltac:(lia) ltac:(street_shape_term lt n) ltac:(street_shape_term rt n))); exact H); clear H; rename F into H
  | H : StreetlightLeftEndpointReady ?p ?w ?lt ?rt ?n ?s ?k ?l |- _ =>
    let F := fresh "HF" in assert (F : StreetlightLeftEndpointReadyFacts p w lt rt n s k l) by
      (apply (proj2 (streetlight_ready_equiv p w lt rt n s k l ltac:(lia) ltac:(street_shape_term lt n) ltac:(street_shape_term rt n))); exact H); clear H; rename F into H
  | H : StreetlightFinalCandidates ?p ?w ?lt ?rt ?s ?a ?b |- _ =>
    let F := fresh "HF" in assert (F : StreetlightFinalCandidatesFacts p w lt rt s a b) by
      (apply (proj2 (streetlight_final_equiv p w lt rt s a b ltac:(lia))); exact H); clear H; rename F into H
  end.
Ltac street_public_goal :=
  try match goal with
  | |- StreetlightPrefixProgress _ _ _ => apply streetlight_prefix_public
  | |- StreetlightInfRows _ _ _ => apply streetlight_inf_rows_public; [lia |]
  | |- StreetlightInfProgress _ _ _ _ => apply streetlight_inf_progress_public; [lia |lia|]
  | |- StreetlightLengthsDone _ _ _ _ _ _ _ => apply streetlight_lengths_public; [lia |]
  | |- StreetlightLeftProgress _ _ _ _ _ _ _ _ => apply streetlight_left_public; [lia |]
  | |- StreetlightLeftEndpointReady _ _ _ _ _ _ _ _ => apply streetlight_ready_public; [lia |]
  | |- StreetlightFinalCandidates ?p ?w ?lt ?rt ?s ?a ?b => apply (proj1 (streetlight_final_equiv p w lt rt s a b ltac:(lia)))
  | |- StreetlightTourMinimumEnergy ?p ?w ?s ?a =>
      apply (streetlight_interval_minimum_is_global p w s a);
      [lia | lia |
       intros k Hk; match goal with
       | H : forall j : Z, _ -> Znth j p 0 < Znth (j + 1) p 0 |- _ => apply H; lia
       end |
       assumption | assumption |]
  end.
Ltac street_shape_goal :=
  first [assumption |
    match goal with
    | |- Forall (eq ?n) (map StreetlightRowLength ?t) =>
      apply (proj2 (proj1 (streetlight_shape_Forall t n) ltac:(street_shape_term t n)))
    | |- Zlength ?t = ?n =>
      first [apply (proj1 (proj1 (streetlight_shape_Forall t n) ltac:(street_shape_term t n))) |
        rewrite !Zlength_app, !Zlength_cons, ?Zlength_nil, ?Zlength_replace_Znth; lia]
    end].
Ltac street_read_bounds :=
  repeat multimatch goal with
  | H : Forall ?P ?l |- context[Znth ?k ?l 0] =>
      let T := constr:(P (Znth k l 0)) in
      tryif (match goal with _ : T |- _ => idtac end)
      then fail 0
      else let Hval := fresh "Hread" in
        assert (Hval : T) by (apply (proj1 (Forall_Znth P 0 l) H); lia)
  end.

Lemma streetlight_machine_candidate : forall (v x y remaining span : Z),
  0 <= v <= (span - 2) * 40000000 ->
  0 <= x <= 8000 -> 0 <= y <= 8000 ->
  1 <= remaining <= 5000 -> 2 <= span <= 50 ->
  (-2147483648) <= v + (x - y) * remaining <= 2147483647.
Proof. intros v x y remaining span Hv Hx Hy Hr Hspan; split; nia. Qed.
Ltac street_safety_arith :=
  first [lia |
    match goal with
    | |- ?v + (?x - ?y) * ?r <= _ =>
      match goal with span : Z |- _ =>
        let H := fresh "Hmachine" in
        pose proof (streetlight_machine_candidate v x y r span ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H; exact (proj2 H)
      end
    | |- _ <= ?v + (?x - ?y) * ?r =>
      match goal with span : Z |- _ =>
        let H := fresh "Hmachine" in
        pose proof (streetlight_machine_candidate v x y r span ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H; exact (proj1 H)
      end
    | |- (?x - ?y) * ?r <= _ =>
      let H := fresh "Hmachine" in
      pose proof (streetlight_machine_candidate 0 x y r 2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H; cbn in H; exact (proj2 H)
    | |- _ <= (?x - ?y) * ?r =>
      let H := fresh "Hmachine" in
      pose proof (streetlight_machine_candidate 0 x y r 2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H; cbn in H; exact (proj1 H)
    end].

Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg .
Lemma scratch_flat_to_rows_rec : forall (k : nat) x lo m l,
  0 <= m ->
  IntArray.seg x (lo * m) ((lo + Z.of_nat k) * m) l |--
  EX rows, “ Zlength rows = Z.of_nat k /\ Forall (fun row => Zlength row = m) rows ” &&
    store_array_rec (IntArray2.row_store m) x lo (lo + Z.of_nat k) rows.
Proof.
  induction k as [|k IH]; intros x lo m l Hm.
  - simpl. replace (lo + 0) with lo by lia.
    prop_apply (IntArray.seg_Zlength x (lo*m) (lo*m) l). Intros.
    assert (l = nil) by (apply Zlength_nil_inv; lia). subst l.
    rewrite IntArray.seg_empty.
    Exists (@nil (list Z)). simpl. entailer!.
  - rewrite Nat2Z.inj_succ.
    replace (lo + Z.succ (Z.of_nat k)) with ((lo + 1) + Z.of_nat k) by lia.
    sep_apply (IntArray.seg_split_to_seg x (lo*m) ((lo+1)*m)
      (((lo+1)+Z.of_nat k)*m) l); [|nia].
    sep_apply (IH x (lo+1) m (sublist ((lo+1)*m-lo*m)
      (((lo+1)+Z.of_nat k)*m-lo*m) l) Hm).
    Intros rows.
    sep_apply (IntArray.seg_to_full x (lo*m) ((lo+1)*m)
      (sublist 0 ((lo+1)*m-lo*m) l)).
    replace ((lo+1)*m-lo*m) with m by ring.
    prop_apply IntArray.full_Zlength. Intros.
    Exists ((sublist 0 m l) :: rows).
    rewrite Zlength_cons. simpl store_array_rec.
    unfold IntArray2.row_store, IntArray2.row_addr.
    entailer!.
Qed.

Lemma scratch_flat_to_rows : forall x n m l,
  0 <= n -> 0 <= m ->
  IntArray.full x (n*m) l |--
  EX rows, “ Zlength rows = n /\ Forall (fun row => Zlength row = m) rows ” &&
    IntArray2.full x n m rows.
Proof.
  intros x n m l Hn Hm.
  sep_apply IntArray.full_to_seg.
  replace 0 with (0*m) at 1 by ring.
  replace (n*m) with ((0+Z.of_nat (Z.to_nat n))*m) by (rewrite Z2Nat.id by lia; ring).
  sep_apply (scratch_flat_to_rows_rec (Z.to_nat n) x 0 m l Hm).
  Intros rows. Exists rows.
  unfold IntArray2.full, store_array.
  rewrite Z2Nat.id by lia. replace (0+n) with n by lia.
  entailer!.
Qed.

Lemma scratch_row_to_undef_seg : forall x lo m row,
  IntArray2.row_store m x lo row |--
  IntArray.undef_seg x (lo*m) ((lo+1)*m).
Proof.
  intros. unfold IntArray2.row_store, IntArray2.row_addr.
  change (IntArray.full (x+lo*m*sizeof(INT)) m row |-- IntArray.undef_seg x (lo*m) ((lo+1)*m)).
  sep_apply IntArray.full_to_undef_full.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite <- IntArray.undef_seg_shift.
  replace (lo*m+0) with (lo*m) by ring.
  replace (lo*m+m) with ((lo+1)*m) by ring.
  entailer!.
Qed.

Lemma scratch_rows_rec_to_undef_seg : forall rows x lo hi m,
  0 <= m ->
  store_array_rec (IntArray2.row_store m) x lo hi rows |--
  IntArray.undef_seg x (lo*m) (hi*m).
Proof.
  induction rows as [|row rows IH]; intros x lo hi m Hm.
  - simpl. Intros. subst hi. rewrite IntArray.undef_seg_empty. entailer!.
  - simpl store_array_rec.
    prop_apply (store_array_rec_valid (list Z) (IntArray2.row_store m) x (lo+1) hi rows).
    Intros.
    sep_apply (IH x (lo+1) hi m Hm).
    sep_apply (scratch_row_to_undef_seg x lo m row).
    sep_apply (IntArray.undef_seg_merge_to_undef_seg x (lo*m) ((lo+1)*m) (hi*m)); [|nia].
    entailer!.
Qed.

Lemma scratch_rows_to_flat_undef : forall x n m rows,
  0 <= m ->
  IntArray2.full x n m rows |-- IntArray.undef_full x (n*m).
Proof.
  intros x n m rows Hm. unfold IntArray2.full, store_array.
  sep_apply (scratch_rows_rec_to_undef_seg rows x 0 n m Hm).
  replace (0*m) with 0 by ring.
  sep_apply IntArray.undef_seg_to_undef_full.
  replace (x+0*sizeof(INT)) with x by lia.
  replace (n*m-0) with (n*m) by ring.
  entailer!.
Qed.

Ltac street_extrema_bounds :=
  try match goal with H : ?v = Z.max ?a ?b |- _ =>
    let Hl := fresh "Hmaxl" in let Hr := fresh "Hmaxr" in
    pose proof (Z.le_max_l a b) as Hl; pose proof (Z.le_max_r a b) as Hr;
    rewrite <- H in Hl, Hr end;
  try match goal with H : ?v = Z.min ?a ?b |- _ =>
    let Hl := fresh "Hminl" in let Hr := fresh "Hminr" in
    pose proof (Z.le_min_l a b) as Hl; pose proof (Z.le_min_r a b) as Hr;
    rewrite <- H in Hl, Hr end.
Lemma scratch_row_shape : forall n (rows:list(list Z)),
  Forall (fun row => Zlength row = n) rows ->
  Forall (eq n) (map StreetlightRowLength rows).
Proof. intros. unfold StreetlightRowLength. apply Forall_map. eapply Forall_impl; [|eassumption]. intros; simpl in *; lia. Qed.
Ltac scratch_cancel :=
  elim_emp; sepcon_right_assoc;
  repeat match goal with
  | |- ?P ** _ |-- _ => progress (cancel P)
  | |- ?P |-- ?P => apply derivable1_refl
  end; try cancel.
Ltac street_extrema_solve :=
  repeat first [progress (rewrite Z.max_l by lia) | progress (rewrite Z.max_r by lia) |
                progress (rewrite Z.min_l by lia) | progress (rewrite Z.min_r by lia)]; lia.

Lemma scratch_full_tail_undef : forall x k cap l,
  0 <= k <= cap ->
  IntArray.full x k l ** IntArray.undef_seg x k cap |-- IntArray.undef_full x cap.
Proof.
  intros x k cap l Hk.
  sep_apply (IntArray.full_to_undef_full x k l).
  sep_apply (IntArray.undef_full_to_undef_seg x k).
  sep_apply (IntArray.undef_seg_merge_to_undef_full x 0 k cap Hk).
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (cap - 0) with cap by lia. entailer!.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.
Lemma scratch_rows_tail_undef : forall x n cap rows,
  0 <= n -> n*n <= cap ->
  IntArray2.full x n n rows ** IntArray.undef_seg x (n*n) cap |-- IntArray.undef_full x cap.
Proof.
  intros x n cap rows Hn Hcap.
  sep_apply (scratch_rows_to_flat_undef x n n rows Hn).
  sep_apply (IntArray.undef_full_to_undef_seg x (n*n)).
  sep_apply (IntArray.undef_seg_merge_to_undef_full x 0 (n*n) cap ltac:(nia)).
  replace (x+0*sizeof(INT)) with x by lia. rewrite Z.sub_0_r. entailer!.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.
Ltac street_resource_apply H :=
  let h := constr:(H) in
  lazymatch type of h with
  | ?P |-- ?Q =>
    let L := (sepconlistasrts P) in
    sepcon_right_assoc; sep_lift_L L; try rewrite !derivable1_sepcon_assoc1;
    rewrite h; sepcon_right_assoc
  end.




(* Recover the remaining-power bounds from the unchanged prefix invariant. *)
Ltac street_cleanup_remaining :=
  match goal with
  | Hprefix : StreetlightPrefixProgress ?powers ?prefix ?n,
    Htotal : ?total = Znth ?n ?prefix 0,
    Hlo : Forall (Z.le 1) ?powers,
    Hhi : Forall (Z.ge 100) ?powers
    |- context [?total - (Znth ?r ?prefix 0 - Znth ?l ?prefix 0)] =>
    let Hpow := fresh "Hcleanup_powers" in
    assert (Hpow : forall k, 0 <= k < n -> 1 <= Znth k powers 0 <= 100) by
      (intros k Hk;
       pose proof (proj1 (Forall_Znth _ 0 _) Hlo k ltac:(lia));
       pose proof (proj1 (Forall_Znth _ 0 _) Hhi k ltac:(lia)); lia);
    let Hfacts := fresh "Hcleanup_prefix" in
    assert (Hfacts : StreetlightPrefixProgressFacts powers prefix n) by
      (split; [lia | exact Hprefix]);
    first [
      let Hbounds := fresh "Hcleanup_remaining" in
      pose proof (streetlight_remaining_bounds__left_remain powers prefix n total (l - 1) (r - 1)
        ltac:(assumption) Hpow Hfacts Htotal ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds;
      replace (r - 1 + 1) with r in Hbounds by lia;
      replace (l - 1 + 1) with l in Hbounds by lia; lia
    | let Hbounds := fresh "Hcleanup_remaining" in
      pose proof (streetlight_prefix_remaining_bounds__right_first powers prefix n l r total
        ltac:(assumption) Hpow Hfacts Htotal ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbounds;
      lia ]
  end.


Lemma proof_of_solve_safety_wit_14 : solve_safety_wit_14.
Proof. unfold solve_safety_wit_14; first [left | idtac]; intros; street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_40 : solve_safety_wit_40.
Proof. unfold solve_safety_wit_40; first [left | idtac]; intros; street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_41 : solve_safety_wit_41.
Proof. unfold solve_safety_wit_41; first [left | idtac]; intros; street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_43 : solve_safety_wit_43.
Proof. unfold solve_safety_wit_43; first [left | idtac]; intros; street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_44 : solve_safety_wit_44.
Proof. unfold solve_safety_wit_44; first [left | idtac]; intros; street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_53 : solve_safety_wit_53.
Proof. unfold solve_safety_wit_53; first [left | idtac]; intros.
  all: assert (Cleanup_PreH4 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH5 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_54 : solve_safety_wit_54.
Proof. unfold solve_safety_wit_54; first [left | idtac]; intros.
  all: assert (Cleanup_PreH4 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH5 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_55 : solve_safety_wit_55.
Proof. unfold solve_safety_wit_55; first [left | idtac]; intros.
  all: assert (Cleanup_PreH4 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH5 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_66 : solve_safety_wit_66.
Proof. unfold solve_safety_wit_66; first [left | idtac]; intros.
  all: assert (Cleanup_PreH9 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH10 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_67 : solve_safety_wit_67.
Proof. unfold solve_safety_wit_67; first [left | idtac]; intros.
  all: assert (Cleanup_PreH9 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH10 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_68 : solve_safety_wit_68.
Proof. unfold solve_safety_wit_68; first [left | idtac]; intros.
  all: assert (Cleanup_PreH9 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH10 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_69 : solve_safety_wit_69.
Proof. unfold solve_safety_wit_69; first [left | idtac]; intros.
  all: assert (Cleanup_PreH5 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH6 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_70 : solve_safety_wit_70.
Proof. unfold solve_safety_wit_70; first [left | idtac]; intros.
  all: assert (Cleanup_PreH5 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH6 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_71 : solve_safety_wit_71.
Proof. unfold solve_safety_wit_71; first [left | idtac]; intros.
  all: assert (Cleanup_PreH5 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH6 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_83 : solve_safety_wit_83.
Proof. unfold solve_safety_wit_83; first [left | idtac]; intros; street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_84 : solve_safety_wit_84.
Proof. unfold solve_safety_wit_84; first [left | idtac]; intros; street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_89 : solve_safety_wit_89.
Proof. unfold solve_safety_wit_89; first [left | idtac]; intros.
  all: assert (Cleanup_PreH4 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH5 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_90 : solve_safety_wit_90.
Proof. unfold solve_safety_wit_90; first [left | idtac]; intros.
  all: assert (Cleanup_PreH4 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH5 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_91 : solve_safety_wit_91.
Proof. unfold solve_safety_wit_91; first [left | idtac]; intros.
  all: assert (Cleanup_PreH4 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH5 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_100 : solve_safety_wit_100.
Proof. unfold solve_safety_wit_100; first [left | idtac]; intros.
  all: assert (Cleanup_PreH9 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH10 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_101 : solve_safety_wit_101.
Proof. unfold solve_safety_wit_101; first [left | idtac]; intros.
  all: assert (Cleanup_PreH9 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH10 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_102 : solve_safety_wit_102.
Proof. unfold solve_safety_wit_102; first [left | idtac]; intros.
  all: assert (Cleanup_PreH9 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH10 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_105 : solve_safety_wit_105.
Proof. unfold solve_safety_wit_105; first [left | idtac]; intros.
  all: assert (Cleanup_PreH5 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH6 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_106 : solve_safety_wit_106.
Proof. unfold solve_safety_wit_106; first [left | idtac]; intros.
  all: assert (Cleanup_PreH5 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH6 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_safety_wit_107 : solve_safety_wit_107.
Proof. unfold solve_safety_wit_107; first [left | idtac]; intros.
  all: assert (Cleanup_PreH5 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH6 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.
 street_extrema_bounds; street_read_bounds; split_pures; dump_pre_spatial; street_safety_arith. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof. unfold solve_entail_wit_1; right; intros. entailer!. all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  unfold solve_entail_wit_3; left; intros.
  assert (k_2 = n_pre*n_pre) by lia. subst k_2.
  sep_apply (IntArray.seg_to_full (&("dp_l")) 0 (n_pre*n_pre) dp_l_flat).
  sep_apply (IntArray.seg_to_full (&("dp_r")) 0 (n_pre*n_pre) dp_r_flat).
  replace ((&("dp_l")) + 0*sizeof(INT)) with (&("dp_l")) by lia.
  replace ((&("dp_r")) + 0*sizeof(INT)) with (&("dp_r")) by lia.
  rewrite Z.sub_0_r.
  sep_apply (scratch_flat_to_rows (&("dp_l")) n_pre n_pre dp_l_flat ltac:(lia) ltac:(lia)).
  Intros lrows.
  sep_apply (scratch_flat_to_rows (&("dp_r")) n_pre n_pre dp_r_flat ltac:(lia) ltac:(lia)).
  Intros rrows.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hpos_lower : Forall (Z.le 0) pos_l).
  { eapply Forall_impl; [|exact PreH10]. intros v Hv. lia. }
  assert (Hpos_upper : Forall (Z.ge 8000) pos_l).
  { eapply Forall_impl; [|exact PreH11]. intros v Hv. apply Z.ge_le in Hv. apply Z.le_ge. lia. }
  Exists rrows lrows (0 :: nil).
  sep_apply (IntArray.undef_seg_split_to_undef_seg (&("pre")) 1 (n_pre+1) 51 ltac:(lia)).
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    sep_apply (IntArray.seg_single (&("pre")) 0 0).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full pos_pre n_pre pos_l).
    cancel (IntArray.full power_pre n_pre power_l).
    cancel (IntArray.seg (&("pre")) 0 1 (0 :: nil)).
    cancel (IntArray.undef_seg (&("pre")) 1 (n_pre + 1)).
    cancel (IntArray2.full (&("dp_l")) n_pre n_pre lrows).
    cancel (IntArray2.full (&("dp_r")) n_pre n_pre rrows).
  - split_pures.
    all: try (dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try assumption; try lia;
              try (simpl; reflexivity)).
    + constructor; [lia | constructor].
    + constructor; [lia | constructor].
    + apply streetlight_prefix_zero_progress__prefix_setup.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_1 : solve_entail_wit_4_split_goal_1.
Proof.
  unfold solve_entail_wit_4_split_goal_1; intros.
  rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_2 : solve_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH12 as LegacyPreH12.
  all: pose proof PreH13 as LegacyPreH13.
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH17 as LegacyPreH17.
  all: pose proof PreH18 as LegacyPreH18.

  all: street_pack.
  all: assert (Hrange_PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH12 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH13 z ltac:(lia)); lia).
  all: assert (Hrange_PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH15 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH16 z ltac:(lia)); lia).
  all: assert (Hrange_PreH15 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= i)) -> ((0 <= (Znth k_4 prefix_l_2 0)) /\ ((Znth k_4 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH17 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); lia).
  all: street_public_goal.

  replace (i - 0) with i by lia.
  eapply streetlight_prefix_extend__prefix_setup; eauto; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_3 : solve_entail_wit_4_split_goal_3.
Proof.
  unfold solve_entail_wit_4_split_goal_3; intros.
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.

  replace (i - 0) with i by lia.
  pose proof (streetlight_prefix_extend__prefix_setup power_l prefix_l_2 i ltac:(lia) ltac:(lia) (conj LegacyPreH20 LegacyPreH19)) as Hnext.
  pose proof (streetlight_prefix_Forall_bounds power_l
    (prefix_l_2 ++ (Znth i prefix_l_2 0 + Znth i power_l 0) :: nil) (i + 1)
    ltac:(lia) ltac:(lia) LegacyPreH15 LegacyPreH16 (proj1 Hnext) (proj2 Hnext)) as Hb.
  exact (proj2 Hb).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_4 : solve_entail_wit_4_split_goal_4.
Proof.
  unfold solve_entail_wit_4_split_goal_4; intros.
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.

  replace (i - 0) with i by lia.
  pose proof (streetlight_prefix_extend__prefix_setup power_l prefix_l_2 i ltac:(lia) ltac:(lia) (conj LegacyPreH20 LegacyPreH19)) as Hnext.
  pose proof (streetlight_prefix_Forall_bounds power_l
    (prefix_l_2 ++ (Znth i prefix_l_2 0 + Znth i power_l 0) :: nil) (i + 1)
    ltac:(lia) ltac:(lia) LegacyPreH15 LegacyPreH16 (proj1 Hnext) (proj2 Hnext)) as Hb.
  exact (proj1 Hb).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  unfold solve_entail_wit_4; right; intros.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; first [ exact (proof_of_solve_entail_wit_4_split_goal_1 c_pre n_pre power_l pos_l prefix_l_2 i start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) | exact (proof_of_solve_entail_wit_4_split_goal_2 c_pre n_pre power_l pos_l prefix_l_2 i start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) | exact (proof_of_solve_entail_wit_4_split_goal_3 c_pre n_pre power_l pos_l prefix_l_2 i start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) | exact (proof_of_solve_entail_wit_4_split_goal_4 c_pre n_pre power_l pos_l prefix_l_2 i start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) ].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH4 as LegacyPreH4.
  all: pose proof PreH11 as LegacyPreH11.
  all: pose proof PreH12 as LegacyPreH12.
  all: pose proof PreH13 as LegacyPreH13.
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH17 as LegacyPreH17.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH19 as LegacyPreH19.

  all: street_pack.
  all: assert (Hrange_PreH12 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH12 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH13 z ltac:(lia)); lia).
  all: assert (Hrange_PreH14 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH15 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH16 z ltac:(lia)); lia).
  all: assert (Hrange_PreH15 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= i)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH17 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); lia).
  all: street_public_goal.

  assert (i = n_pre) as Hi by lia.
  subst i.
  assert (Htable_shape :
    forall base table,
      IntArray2.full base n_pre n_pre table |--
        “ StreetlightTableShape table n_pre ”).
  {
    intros base table.
    unfold derivable1, coq_prop.
    intros state Hfull.
    apply streetlight_table_shape_from_full__prefix_setup.
    - exact
        (derivable1_imp
          (IntArray2.full base n_pre n_pre table)
          (“ Zlength table = n_pre ”)
          state
          (IntArray2.full_Zlength base n_pre n_pre table)
          Hfull).
    - intros row Hrow.
      pose proof
        (derivable1_imp
          (IntArray2.full base n_pre n_pre table)
          (IntArray2.ElemArray.full
             (IntArray2.row_addr base n_pre row)
             n_pre (Znth row table nil) **
           IntArray2.missing_i base row 0 n_pre n_pre table)
          state
          (IntArray2.full_split_to_missing_i
             base row n_pre n_pre table Hrow)
          Hfull) as Hsplit.
      unfold sepcon in Hsplit.
      destruct Hsplit as
        (row_state & rest_state & Hjoin & Hrowfull & Hrest).
      exact
        (derivable1_imp
          (IntArray2.ElemArray.full
             (IntArray2.row_addr base n_pre row)
             n_pre (Znth row table nil))
          (“ Zlength (Znth row table nil) = n_pre ”)
          row_state
          (IntArray2.ElemArray.full_Zlength
             (IntArray2.row_addr base n_pre row)
             n_pre (Znth row table nil))
          Hrowfull).
  }
  prop_apply (Htable_shape (&("dp_l")) dp_l_init).
  Intros_p Hleft_shape.
  prop_apply (Htable_shape (&("dp_r")) dp_r_init).
  Intros_p Hright_shape.
  assert (Hprefix_positive : 1 <= Znth n_pre prefix_l 0).
  {
    eapply streetlight_prefix_total_positive__prefix_setup.
    - exact LegacyPreH4.
    - exact LegacyPreH11.
    - intros k Hk.
      specialize (Hrange_PreH14 k Hk).
      lia.
    - exact LegacyPreH19.
  }
  assert (Hprefix_bounds : 0 <= Znth n_pre prefix_l 0 <= 5000).
  {
    apply Hrange_PreH15.
    lia.
  }
  replace (n_pre - 0) with n_pre by lia.
  Exists dp_r_init dp_l_init prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    sep_apply_l_atomic
      (IntArray.seg_to_full (&("pre")) 0 (n_pre + 1) prefix_l).
    replace ((&("pre")) + 0 * sizeof (INT)) with (&("pre")) by lia.
    replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
    cancel (IntArray.full pos_pre n_pre pos_l).
    cancel (IntArray.full power_pre n_pre power_l).
    cancel (IntArray.full (&("pre")) (n_pre + 1) prefix_l).
    cancel (IntArray2.full (&("dp_l")) n_pre n_pre dp_l_init).
    cancel (IntArray2.full (&("dp_r")) n_pre n_pre dp_r_init).
  - split_pures.
    all: try (dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try assumption; try lia;
              try (simpl; reflexivity)).
    + apply streetlight_inf_rows_zero__prefix_setup.
      exact Hleft_shape.
    + apply streetlight_inf_rows_zero__prefix_setup.
      exact Hright_shape.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_1 : solve_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH27 as LegacyPreH27.

  all: street_pack.
  all: assert (Hrange_PreH15 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH15 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH16 z ltac:(lia)); lia).
  all: assert (Hrange_PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); lia).
  all: assert (Hrange_PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: street_public_goal.

  unfold StreetlightInfProgressFacts.
  split.
  - exact LegacyPreH27.
  - intros col Hcol.
    lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_2 : solve_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH24 as LegacyPreH24.

  all: street_pack.
  all: assert (Hrange_PreH15 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH15 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH16 z ltac:(lia)); lia).
  all: assert (Hrange_PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); lia).
  all: assert (Hrange_PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: street_public_goal.

  unfold StreetlightInfProgressFacts.
  split.
  - exact LegacyPreH24.
  - intros col Hcol.
    lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_3 : solve_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.

  all: street_pack.
  all: assert (Hrange_PreH15 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH15 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH16 z ltac:(lia)); lia).
  all: assert (Hrange_PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); lia).
  all: assert (Hrange_PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: street_public_goal.

all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  unfold solve_entail_wit_6; right; intros.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; first [ exact (proof_of_solve_entail_wit_6_split_goal_1 c_pre n_pre power_l pos_l right_table_2 left_table_2 row prefix_l_2 total start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29) | exact (proof_of_solve_entail_wit_6_split_goal_2 c_pre n_pre power_l pos_l right_table_2 left_table_2 row prefix_l_2 total start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29) | exact (proof_of_solve_entail_wit_6_split_goal_3 c_pre n_pre power_l pos_l right_table_2 left_table_2 row prefix_l_2 total start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29) ].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH17 as LegacyPreH17.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.

  all: street_pack.
  all: assert (Hrange_PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH17 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); lia).
  all: assert (Hrange_PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: assert (Hrange_PreH20 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l_2 0)) /\ ((Znth k_4 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: street_public_goal.

  subst inf.
  Exists
    (replace_Znth row
      (replace_Znth col 2147483647
        (Znth row right_table_2 __default__List_Z))
      right_table_2)
    (replace_Znth row
      (replace_Znth col 2147483647
        (Znth row left_table_2 __default__List_Z))
      left_table_2)
    prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia].
  all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; assumption].
  all: try solve [
    dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
    eapply streetlight_inf_progress_store__inf_tables;
    eauto;
    lia
  ].
  pose proof (IntArray.missing_i_merge_to_full
    ((&("dp_r")) + row * n_pre * sizeof (INT)) col n_pre 2147483647
    (Znth row right_table_2 __default__List_Z) ltac:(lia))
    as Hright_row_merge.
  simpl in Hright_row_merge.
  assert (Hright_addr :
    (&("dp_r")) + row * n_pre * sizeof (INT) + col * sizeof (INT) =
    (&("dp_r")) + (row * n_pre + col) * sizeof (INT)) by lia.
  rewrite <- Hright_addr.
  sep_apply Hright_row_merge.
  pose proof (IntArray2.missing_i_merge_to_full
    (&("dp_r")) row n_pre n_pre right_table_2
    (replace_Znth col 2147483647
      (Znth row right_table_2 __default__List_Z)) ltac:(lia))
    as Hright_table_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_r")) n_pre row) n_pre
      (replace_Znth col 2147483647
        (Znth row right_table_2 __default__List_Z)))
    with
    (IntArray.full
      ((&("dp_r")) + row * n_pre * 4) n_pre
      (replace_Znth col 2147483647
        (Znth row right_table_2 __default__List_Z)))
    in Hright_table_merge.
  sep_apply Hright_table_merge.
  pose proof (IntArray.missing_i_merge_to_full
    ((&("dp_l")) + row * n_pre * sizeof (INT)) col n_pre 2147483647
    (Znth row left_table_2 __default__List_Z) ltac:(lia))
    as Hleft_row_merge.
  simpl in Hleft_row_merge.
  assert (Hleft_addr :
    (&("dp_l")) + row * n_pre * sizeof (INT) + col * sizeof (INT) =
    (&("dp_l")) + (row * n_pre + col) * sizeof (INT)) by lia.
  rewrite <- Hleft_addr.
  rewrite sizeof_int.
  sep_apply Hleft_row_merge.
  pose proof (IntArray2.missing_i_merge_to_full
    (&("dp_l")) row n_pre n_pre left_table_2
    (replace_Znth col 2147483647
      (Znth row left_table_2 __default__List_Z)) ltac:(lia))
    as Hleft_table_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_l")) n_pre row) n_pre
      (replace_Znth col 2147483647
        (Znth row left_table_2 __default__List_Z)))
    with
    (IntArray.full
      ((&("dp_l")) + row * n_pre * 4) n_pre
      (replace_Znth col 2147483647
        (Znth row left_table_2 __default__List_Z)))
    in Hleft_table_merge.
  sep_apply Hleft_table_merge.
  cancel.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_8_split_goal_1 : solve_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH17 as LegacyPreH17.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH29 as LegacyPreH29.

  all: street_pack.
  all: assert (Hrange_PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH17 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); lia).
  all: assert (Hrange_PreH19 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: assert (Hrange_PreH20 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: street_public_goal.

  apply (streetlight_inf_progress_close_row__inf_tables
    right_table_2 n_pre row col).
  - lia.
  - exact LegacyPreH29.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_8_split_goal_2 : solve_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH17 as LegacyPreH17.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH26 as LegacyPreH26.

  all: street_pack.
  all: assert (Hrange_PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH17 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); lia).
  all: assert (Hrange_PreH19 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: assert (Hrange_PreH20 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: street_public_goal.

  apply (streetlight_inf_progress_close_row__inf_tables
    left_table_2 n_pre row col).
  - lia.
  - exact LegacyPreH26.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_8_split_goal_3 : solve_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH17 as LegacyPreH17.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.

  all: street_pack.
  all: assert (Hrange_PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH17 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); lia).
  all: assert (Hrange_PreH19 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: assert (Hrange_PreH20 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: street_public_goal.

all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Proof.
  unfold solve_entail_wit_8; right; intros.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; first [ exact (proof_of_solve_entail_wit_8_split_goal_1 c_pre n_pre power_l pos_l right_table_2 left_table_2 col row prefix_l_2 total start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31) | exact (proof_of_solve_entail_wit_8_split_goal_2 c_pre n_pre power_l pos_l right_table_2 left_table_2 col row prefix_l_2 total start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31) | exact (proof_of_solve_entail_wit_8_split_goal_3 c_pre n_pre power_l pos_l right_table_2 left_table_2 col row prefix_l_2 total start inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31) ].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH27 as LegacyPreH27.

  all: street_pack.
  all: assert (Hrange_PreH15 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH15 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH16 z ltac:(lia)); lia).
  all: assert (Hrange_PreH17 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); lia).
  all: assert (Hrange_PreH18 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: street_public_goal.

  assert (Hrow : row = n_pre) by lia.
  subst row.
  subst inf.
  pose proof
    (streetlight_diagonal_base__diagonal_base
      pos_l power_l left_table_2 right_table_2 n_pre start
      __default__List_Z ltac:(lia) LegacyPreH24 LegacyPreH27)
    as [Hlengths [Hpending_right Hpending_left]].
  Exists
    (replace_Znth start
      (replace_Znth start 0
        (Znth start right_table_2 __default__List_Z))
      right_table_2)
    (replace_Znth start
      (replace_Znth start 0
        (Znth start left_table_2 __default__List_Z))
      left_table_2)
    prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia].
  all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; assumption].
  all: try solve [
    dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
    intros pending Hpending;
    apply Hpending_right;
    lia
  ].
  all: try solve [
    dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
    intros pending Hpending;
    apply Hpending_left;
    lia
  ].
  pose proof (IntArray.missing_i_merge_to_full
    ((&("dp_r")) + start * n_pre * sizeof (INT)) start n_pre 0
    (Znth start right_table_2 __default__List_Z) ltac:(lia))
    as Hright_row_merge.
  simpl in Hright_row_merge.
  assert (Hright_addr :
    (&("dp_r")) + start * n_pre * sizeof (INT) + start * sizeof (INT) =
    (&("dp_r")) + (start * n_pre + start) * sizeof (INT)) by lia.
  rewrite <- Hright_addr.
  sep_apply Hright_row_merge.
  pose proof (IntArray2.missing_i_merge_to_full
    (&("dp_r")) start n_pre n_pre right_table_2
    (replace_Znth start 0
      (Znth start right_table_2 __default__List_Z)) ltac:(lia))
    as Hright_table_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_r")) n_pre start) n_pre
      (replace_Znth start 0
        (Znth start right_table_2 __default__List_Z)))
    with
    (IntArray.full
      ((&("dp_r")) + start * n_pre * 4) n_pre
      (replace_Znth start 0
        (Znth start right_table_2 __default__List_Z)))
    in Hright_table_merge.
  sep_apply Hright_table_merge.
  pose proof (IntArray.missing_i_merge_to_full
    ((&("dp_l")) + start * n_pre * sizeof (INT)) start n_pre 0
    (Znth start left_table_2 __default__List_Z) ltac:(lia))
    as Hleft_row_merge.
  simpl in Hleft_row_merge.
  assert (Hleft_addr :
    (&("dp_l")) + start * n_pre * sizeof (INT) + start * sizeof (INT) =
    (&("dp_l")) + (start * n_pre + start) * sizeof (INT)) by lia.
  rewrite <- Hleft_addr.
  rewrite sizeof_int.
  sep_apply Hleft_row_merge.
  pose proof (IntArray2.missing_i_merge_to_full
    (&("dp_l")) start n_pre n_pre left_table_2
    (replace_Znth start 0
      (Znth start left_table_2 __default__List_Z)) ltac:(lia))
    as Hleft_table_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_l")) n_pre start) n_pre
      (replace_Znth start 0
        (Znth start left_table_2 __default__List_Z)))
    with
    (IntArray.full
      ((&("dp_l")) + start * n_pre * 4) n_pre
      (replace_Znth start 0
        (Znth start left_table_2 __default__List_Z)))
    in Hleft_table_merge.
  sep_apply Hleft_table_merge.
  cancel.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_1 : solve_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all: 
    first [solve [eauto using streetlight_left_progress_zero__length_entry] |
      replace (c_pre - 1) with start by lia;
      apply streetlight_left_progress_initial__length_entry; assumption].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_2 : solve_entail_wit_10_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH27 as LegacyPreH27.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all:  exact LegacyPreH27.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_3 : solve_entail_wit_10_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH26 as LegacyPreH26.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all:  exact LegacyPreH26.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_4 : solve_entail_wit_10_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.

all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_5 : solve_entail_wit_10_1_split_goal_5.
Proof.
  unfold solve_entail_wit_10_1_split_goal_5; intros.
  try street_extrema_bounds.
  try (LLM_pre_process ltac:(lia || int_auto)).
  all: try street_pack.
  all: try street_public_goal.
  all: try street_shape_goal.
  all: try (split_pures; dump_pre_spatial; lia).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_1_split_goal_6 : solve_entail_wit_10_1_split_goal_6.
Proof.
  unfold solve_entail_wit_10_1_split_goal_6; intros.
  try street_extrema_bounds.
  try (LLM_pre_process ltac:(lia || int_auto)).
  all: try street_pack.
  all: try street_public_goal.
  all: try street_shape_goal.
  all: try (split_pures; dump_pre_spatial; lia).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_1 : solve_entail_wit_10_1.
Proof.
  unfold solve_entail_wit_10_1; right; intros.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; first [ exact (proof_of_solve_entail_wit_10_1_split_goal_1 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_1_split_goal_2 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_1_split_goal_3 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_1_split_goal_4 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_1_split_goal_5 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_1_split_goal_6 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) ].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_1 : solve_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all: 
    first [solve [eauto using streetlight_left_progress_zero__length_entry] |
      replace (c_pre - 1) with start by lia;
      apply streetlight_left_progress_initial__length_entry; assumption].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_2 : solve_entail_wit_10_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH27 as LegacyPreH27.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all:  exact LegacyPreH27.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_3 : solve_entail_wit_10_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH26 as LegacyPreH26.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all:  exact LegacyPreH26.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_4 : solve_entail_wit_10_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.

all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_5 : solve_entail_wit_10_2_split_goal_5.
Proof.
  unfold solve_entail_wit_10_2_split_goal_5; intros.
  try street_extrema_bounds.
  try (LLM_pre_process ltac:(lia || int_auto)).
  all: try street_pack.
  all: try street_public_goal.
  all: try street_shape_goal.
  all: try (split_pures; dump_pre_spatial; lia).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_2_split_goal_6 : solve_entail_wit_10_2_split_goal_6.
Proof.
  unfold solve_entail_wit_10_2_split_goal_6; intros.
  try street_extrema_bounds.
  try (LLM_pre_process ltac:(lia || int_auto)).
  all: try street_pack.
  all: try street_public_goal.
  all: try street_shape_goal.
  all: try (split_pures; dump_pre_spatial; lia).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_2 : solve_entail_wit_10_2.
Proof.
  unfold solve_entail_wit_10_2; right; intros.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; first [ exact (proof_of_solve_entail_wit_10_2_split_goal_1 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_2_split_goal_2 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_2_split_goal_3 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_2_split_goal_4 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_2_split_goal_5 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_2_split_goal_6 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) ].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_1 : solve_entail_wit_10_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all: 
    first [solve [eauto using streetlight_left_progress_zero__length_entry] |
      replace (c_pre - 1) with start by lia;
      apply streetlight_left_progress_initial__length_entry; assumption].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_2 : solve_entail_wit_10_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH27 as LegacyPreH27.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all:  exact LegacyPreH27.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_3 : solve_entail_wit_10_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH26 as LegacyPreH26.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all:  exact LegacyPreH26.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_4 : solve_entail_wit_10_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.

all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_5 : solve_entail_wit_10_3_split_goal_5.
Proof.
  unfold solve_entail_wit_10_3_split_goal_5; intros.
  try street_extrema_bounds.
  try (LLM_pre_process ltac:(lia || int_auto)).
  all: try street_pack.
  all: try street_public_goal.
  all: try street_shape_goal.
  all: try (split_pures; dump_pre_spatial; lia).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_3_split_goal_6 : solve_entail_wit_10_3_split_goal_6.
Proof.
  unfold solve_entail_wit_10_3_split_goal_6; intros.
  try street_extrema_bounds.
  try (LLM_pre_process ltac:(lia || int_auto)).
  all: try street_pack.
  all: try street_public_goal.
  all: try street_shape_goal.
  all: try (split_pures; dump_pre_spatial; lia).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_3 : solve_entail_wit_10_3.
Proof.
  unfold solve_entail_wit_10_3; right; intros.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; first [ exact (proof_of_solve_entail_wit_10_3_split_goal_1 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_3_split_goal_2 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_3_split_goal_3 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_3_split_goal_4 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_3_split_goal_5 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_3_split_goal_6 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) ].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_4_split_goal_1 : solve_entail_wit_10_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all: 
    first [solve [eauto using streetlight_left_progress_zero__length_entry] |
      replace (c_pre - 1) with start by lia;
      apply streetlight_left_progress_initial__length_entry; assumption].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_4_split_goal_2 : solve_entail_wit_10_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH27 as LegacyPreH27.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all:  exact LegacyPreH27.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_4_split_goal_3 : solve_entail_wit_10_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH26 as LegacyPreH26.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.
  all:  exact LegacyPreH26.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_4_split_goal_4 : solve_entail_wit_10_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH25 as LegacyPreH25.

  all: street_pack.
  all: assert (Hrange_PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH19 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); lia).
  all: assert (Hrange_PreH21 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: assert (Hrange_PreH22 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH24 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); lia).
  all: street_public_goal.

all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_4_split_goal_5 : solve_entail_wit_10_4_split_goal_5.
Proof.
  unfold solve_entail_wit_10_4_split_goal_5; intros.
  try street_extrema_bounds.
  try (LLM_pre_process ltac:(lia || int_auto)).
  all: try street_pack.
  all: try street_public_goal.
  all: try street_shape_goal.
  all: try (split_pures; dump_pre_spatial; lia).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_4_split_goal_6 : solve_entail_wit_10_4_split_goal_6.
Proof.
  unfold solve_entail_wit_10_4_split_goal_6; intros.
  try street_extrema_bounds.
  try (LLM_pre_process ltac:(lia || int_auto)).
  all: try street_pack.
  all: try street_public_goal.
  all: try street_shape_goal.
  all: try (split_pures; dump_pre_spatial; lia).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_10_4 : solve_entail_wit_10_4.
Proof.
  unfold solve_entail_wit_10_4; right; intros.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; first [ exact (proof_of_solve_entail_wit_10_4_split_goal_1 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_4_split_goal_2 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_4_split_goal_3 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_4_split_goal_4 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_4_split_goal_5 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) | exact (proof_of_solve_entail_wit_10_4_split_goal_6 c_pre n_pre power_l pos_l right_table_2 left_table_2 len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34) ].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Proof.
  unfold solve_entail_wit_11; right; intros.
  street_extrema_bounds. entailer!.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_12 : solve_entail_wit_12.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH2 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH3 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH2 as LegacyPreH4.
  all: pose proof PreH3 as LegacyPreH5.
  all: pose proof PreH5 as LegacyPreH7.
  all: pose proof PreH6 as LegacyPreH8.
  all: pose proof PreH20 as LegacyPreH22.
  all: pose proof PreH22 as LegacyPreH24.
  all: pose proof PreH29 as LegacyPreH31.
  all: pose proof PreH32 as LegacyPreH34.
  all: pose proof PreH39 as LegacyPreH43.
  all: pose proof PreH40 as LegacyPreH44.
  all: pose proof PreH41 as LegacyPreH45.
  all: pose proof PreH42 as LegacyPreH46.
  all: pose proof PreH43 as LegacyPreH47.
  all: pose proof PreH44 as LegacyPreH48.
  all: pose proof PreH45 as LegacyPreH49.
  all: pose proof PreH46 as LegacyPreH50.
  all: pose proof PreH47 as LegacyPreH51.
  all: pose proof PreH50 as LegacyPreH54.
  all: pose proof PreH52 as LegacyPreH56.

  all: street_pack.
  all: assert (Hrange_PreH45 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH45 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH46 z ltac:(lia)); lia).
  all: assert (Hrange_PreH47 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH48 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH49 z ltac:(lia)); lia).
  all: assert (Hrange_PreH48 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH50 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH51 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (streetlight_previous_left_entry_bounds__left_predecessor
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre total start len left inf
       LegacyPreH43 LegacyPreH44 LegacyPreH24 LegacyPreH34 Hrange_PreH45 LegacyPreH47 Hrange_PreH47
       LegacyPreH5 LegacyPreH4 LegacyPreH7 LegacyPreH8 LegacyPreH31 LegacyPreH22 LegacyPreH54 LegacyPreH56 LegacyPreH1)
    as Hprevious_bounds.
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; auto; try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_13 : solve_entail_wit_13.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH4 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH5 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH43 as LegacyPreH47.
  all: pose proof PreH44 as LegacyPreH48.
  all: pose proof PreH45 as LegacyPreH49.
  all: pose proof PreH46 as LegacyPreH50.
  all: pose proof PreH47 as LegacyPreH51.
  all: pose proof PreH48 as LegacyPreH52.
  all: pose proof PreH49 as LegacyPreH53.

  all: street_pack.
  all: assert (Hrange_PreH47 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH47 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH48 z ltac:(lia)); lia).
  all: assert (Hrange_PreH49 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH50 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH51 z ltac:(lia)); lia).
  all: assert (Hrange_PreH50 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH52 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH53 z ltac:(lia)); lia).
  all: street_public_goal.

  assert (Hpos_left : 0 <= Znth left pos_l 0 <= 8000) by
    (apply Hrange_PreH47; lia).
  assert (Hpos_next : 0 <= Znth (left + 1) pos_l 0 <= 8000) by
    (apply Hrange_PreH47; lia).
  assert (Hpos_step : Znth left pos_l 0 < Znth (left + 1) pos_l 0) by
    (apply LegacyPreH49; lia).
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures;
      dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
      first [assumption | nia].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_14_1 : solve_entail_wit_14_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH7 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH8 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH7 as LegacyPreH9.
  all: pose proof PreH8 as LegacyPreH10.
  all: pose proof PreH10 as LegacyPreH12.
  all: pose proof PreH11 as LegacyPreH13.
  all: pose proof PreH25 as LegacyPreH27.
  all: pose proof PreH27 as LegacyPreH29.
  all: pose proof PreH37 as LegacyPreH39.
  all: pose proof PreH44 as LegacyPreH48.
  all: pose proof PreH45 as LegacyPreH49.
  all: pose proof PreH46 as LegacyPreH50.
  all: pose proof PreH47 as LegacyPreH51.
  all: pose proof PreH48 as LegacyPreH52.
  all: pose proof PreH49 as LegacyPreH53.
  all: pose proof PreH50 as LegacyPreH54.
  all: pose proof PreH51 as LegacyPreH55.
  all: pose proof PreH52 as LegacyPreH56.
  all: pose proof PreH55 as LegacyPreH59.
  all: pose proof PreH57 as LegacyPreH61.

  all: street_pack.
  all: assert (Hrange_PreH50 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH50 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH51 z ltac:(lia)); lia).
  all: assert (Hrange_PreH52 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH53 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH54 z ltac:(lia)); lia).
  all: assert (Hrange_PreH53 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH55 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH56 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (streetlight_right_predecessor_bounds__left_best_a
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start len left total inf
       LegacyPreH48 LegacyPreH49 Hrange_PreH50 LegacyPreH52 Hrange_PreH52
       LegacyPreH29 LegacyPreH39 LegacyPreH59 LegacyPreH61
       LegacyPreH10 LegacyPreH9 LegacyPreH12 LegacyPreH13 LegacyPreH27 LegacyPreH1)
    as Hrightbounds.
  destruct Hrightbounds as [Hrightnonneg Hrightupper].
  
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; auto.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_14_2 : solve_entail_wit_14_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH3 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH4 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH3 as LegacyPreH5.
  all: pose proof PreH4 as LegacyPreH6.
  all: pose proof PreH6 as LegacyPreH8.
  all: pose proof PreH7 as LegacyPreH9.
  all: pose proof PreH25 as LegacyPreH27.
  all: pose proof PreH30 as LegacyPreH32.
  all: pose proof PreH40 as LegacyPreH44.
  all: pose proof PreH41 as LegacyPreH45.
  all: pose proof PreH42 as LegacyPreH46.
  all: pose proof PreH43 as LegacyPreH47.
  all: pose proof PreH44 as LegacyPreH48.
  all: pose proof PreH45 as LegacyPreH49.
  all: pose proof PreH46 as LegacyPreH50.
  all: pose proof PreH47 as LegacyPreH51.
  all: pose proof PreH48 as LegacyPreH52.
  all: pose proof PreH53 as LegacyPreH57.

  all: street_pack.
  all: assert (Hrange_PreH46 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH46 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH47 z ltac:(lia)); lia).
  all: assert (Hrange_PreH48 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH49 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH50 z ltac:(lia)); lia).
  all: assert (Hrange_PreH49 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH51 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH52 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (StreetlightLeftProgress_predecessor_right_bounds__left_best_b
      pos_l power_l left_table right_table n_pre start len left
      __default__List_Z LegacyPreH44 LegacyPreH45 LegacyPreH27 LegacyPreH32 LegacyPreH6 LegacyPreH5
      LegacyPreH8 LegacyPreH9 Hrange_PreH46 LegacyPreH48 Hrange_PreH48 LegacyPreH57 ltac:(lia))
    as Hprev_bounds.
  
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures.
    all: dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: try assumption.
    all: try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_15_1 : solve_entail_wit_15_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH9 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH10 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH2 as LegacyPreH2.
  all: pose proof Cleanup_PreH9 as LegacyPreH9.
  all: pose proof Cleanup_PreH10 as LegacyPreH10.
  all: pose proof PreH10 as LegacyPreH12.
  all: pose proof PreH13 as LegacyPreH15.
  all: pose proof PreH48 as LegacyPreH52.
  all: pose proof PreH49 as LegacyPreH53.
  all: pose proof PreH50 as LegacyPreH54.
  all: pose proof PreH51 as LegacyPreH55.
  all: pose proof PreH52 as LegacyPreH56.
  all: pose proof PreH53 as LegacyPreH57.
  all: pose proof PreH54 as LegacyPreH58.

  all: street_pack.
  all: assert (Hrange_PreH52 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH52 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH53 z ltac:(lia)); lia).
  all: assert (Hrange_PreH54 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH55 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH56 z ltac:(lia)); lia).
  all: assert (Hrange_PreH55 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH57 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH58 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof (Hrange_PreH52 left ltac:(lia)) as Hpos_left.
  pose proof (Hrange_PreH52 (left + len - 1) ltac:(lia)) as Hpos_right.
  pose proof
    (streetlight_adjacent_positions_strict__left_compare_a
       pos_l n_pre LegacyPreH54 left (left + len - 1)
       LegacyPreH12 ltac:(lia) LegacyPreH15) as Hpos_order.
  assert (Hcandidate_bounds :
    0 <=
      Znth (left + len - 1) (Znth (left + 1) right_table __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l 0 - Znth (left + 1) prefix_l 0)) /\
    Znth (left + len - 1) (Znth (left + 1) right_table __default__List_Z) 0 +
      (Znth (left + len - 1) pos_l 0 - Znth left pos_l 0) *
      (total - (Znth (left + len - 1 + 1) prefix_l 0 - Znth (left + 1) prefix_l 0)) <=
      (len - 1) * 40000000).
  {
    eapply streetlight_left_candidate_bounds__left_compare_a.
    - exact LegacyPreH1.
    - exact LegacyPreH2.
    - lia.
    - exact (proj1 Hpos_left).
    - exact (proj2 Hpos_right).
    - exact LegacyPreH9.
    - exact LegacyPreH10.
  }
  destruct Hcandidate_bounds as [Hcandidate_lower Hcandidate_upper].
  
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; auto; try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_15_2 : solve_entail_wit_15_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH5 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH6 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH44 as LegacyPreH48.
  all: pose proof PreH45 as LegacyPreH49.
  all: pose proof PreH47 as LegacyPreH51.
  all: pose proof PreH48 as LegacyPreH52.
  all: pose proof PreH49 as LegacyPreH53.
  all: pose proof PreH50 as LegacyPreH54.

  all: street_pack.
  all: assert (Hrange_PreH48 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH48 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH49 z ltac:(lia)); lia).
  all: assert (Hrange_PreH50 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH51 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH52 z ltac:(lia)); lia).
  all: assert (Hrange_PreH51 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH53 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH54 z ltac:(lia)); lia).
  all: street_public_goal.

  assert (Hposition_order :
    Znth left pos_l 0 < Znth (left + len - 1) pos_l 0).
  { eapply streetlight_strict_positions_between__left_compare_b;
      eauto; lia. }
  pose proof (Hrange_PreH48 left ltac:(lia)) as Hposition_left.
  pose proof (Hrange_PreH48 (left + len - 1) ltac:(lia)) as Hposition_right.
  
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures;
      dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
      try nia;
      assumption.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_16_1 : solve_entail_wit_16_1.
Proof.

  LLM_pre_process ltac:(assumption).
  all: assert (Cleanup_PreH12 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH13 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH51 as LegacyPreH55.
  all: pose proof PreH52 as LegacyPreH56.
  all: pose proof PreH54 as LegacyPreH58.
  all: pose proof PreH55 as LegacyPreH59.
  all: pose proof PreH56 as LegacyPreH60.
  all: pose proof PreH57 as LegacyPreH61.
  all: pose proof PreH62 as LegacyPreH66.

  all: street_pack.
  all: assert (Hrange_PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH55 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH56 z ltac:(lia)); lia).
  all: assert (Hrange_PreH57 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH58 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH59 z ltac:(lia)); lia).
  all: assert (Hrange_PreH58 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH60 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH61 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof LegacyPreH66 as Hshape.
  unfold StreetlightLeftProgressFacts, StreetlightLengthsDoneFacts,
    StreetlightTableShape in Hshape.
  destruct Hshape as
    [[[Hleft_table_len Hleft_row_len]
      [[Hright_table_len Hright_row_len] Hdone]] Hprogress].
  assert (Hrow_bounds : 0 <= left + 1 < n_pre) by lia.
  pose proof (Hleft_row_len (left + 1) Hrow_bounds) as Hleft_len.
  pose proof (Hright_row_len (left + 1) Hrow_bounds) as Hright_len.
  Right. 
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    pose proof (IntArray.missing_i_merge_to_full
      ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hright_row_merge.
    assert (Hright_addr :
      (&("dp_r")) + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      (&("dp_r")) + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hright_addr.
    sep_apply Hright_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      (&("dp_r")) (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z))
      as Hright_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_r")) n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full
        ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) right_table __default__List_Z))
      in Hright_table_merge.
    sep_apply Hright_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_table_len; lia).
    pose proof (IntArray.missing_i_merge_to_full
      ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hleft_row_merge.
    assert (Hleft_addr :
      (&("dp_l")) + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      (&("dp_l")) + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hleft_addr.
    sep_apply Hleft_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      (&("dp_l")) (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z))
      as Hleft_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_l")) n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full
        ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) left_table_2 __default__List_Z))
      in Hleft_table_merge.
    sep_apply Hleft_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_table_len; lia).
    cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try assumption; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_16_2 : solve_entail_wit_16_2.
Proof.

  LLM_pre_process ltac:(assumption).
  all: assert (Cleanup_PreH8 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH9 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH47 as LegacyPreH51.
  all: pose proof PreH48 as LegacyPreH52.
  all: pose proof PreH50 as LegacyPreH54.
  all: pose proof PreH51 as LegacyPreH55.
  all: pose proof PreH52 as LegacyPreH56.
  all: pose proof PreH53 as LegacyPreH57.
  all: pose proof PreH58 as LegacyPreH62.

  all: street_pack.
  all: assert (Hrange_PreH51 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH51 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH52 z ltac:(lia)); lia).
  all: assert (Hrange_PreH53 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH54 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH55 z ltac:(lia)); lia).
  all: assert (Hrange_PreH54 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH56 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH57 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof LegacyPreH62 as Hshape.
  unfold StreetlightLeftProgressFacts, StreetlightLengthsDoneFacts,
    StreetlightTableShape in Hshape.
  destruct Hshape as
    [[[Hleft_table_len Hleft_row_len]
      [[Hright_table_len Hright_row_len] Hdone]] Hprogress].
  assert (Hrow_bounds : 0 <= left + 1 < n_pre) by lia.
  pose proof (Hleft_row_len (left + 1) Hrow_bounds) as Hleft_len.
  pose proof (Hright_row_len (left + 1) Hrow_bounds) as Hright_len.
  Left. Right.   
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    pose proof (IntArray.missing_i_merge_to_full
      ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hright_row_merge.
    assert (Hright_addr :
      (&("dp_r")) + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      (&("dp_r")) + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hright_addr.
    sep_apply Hright_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      (&("dp_r")) (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z))
      as Hright_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_r")) n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full
        ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) right_table __default__List_Z))
      in Hright_table_merge.
    sep_apply Hright_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hright_table_len; lia).
    pose proof (IntArray.missing_i_merge_to_full
      ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT))
      (left + len - 1) n_pre
      (Znth (left + len - 1)
        (Znth (left + 1) left_table_2 __default__List_Z) 0)
      (Znth (left + 1) left_table_2 __default__List_Z)) as Hleft_row_merge.
    assert (Hleft_addr :
      (&("dp_l")) + (left + 1) * n_pre * sizeof (INT) +
        (left + len - 1) * sizeof (INT) =
      (&("dp_l")) + ((left + 1) * n_pre + (left + len - 1)) *
        sizeof (INT)) by lia.
    rewrite <- Hleft_addr.
    sep_apply Hleft_row_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_len; lia).
    pose proof (IntArray2.missing_i_merge_to_full
      (&("dp_l")) (left + 1) n_pre n_pre left_table_2
      (Znth (left + 1) left_table_2 __default__List_Z))
      as Hleft_table_merge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_l")) n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table_2 __default__List_Z)) with
      (IntArray.full
        ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT)) n_pre
        (Znth (left + 1) left_table_2 __default__List_Z))
      in Hleft_table_merge.
    sep_apply Hleft_table_merge; try lia.
    rewrite replace_Znth_Znth by (rewrite Hleft_table_len; lia).
    cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try assumption; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_16_3 : solve_entail_wit_16_3.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH12 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH13 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH51 as LegacyPreH55.
  all: pose proof PreH52 as LegacyPreH56.
  all: pose proof PreH53 as LegacyPreH57.
  all: pose proof PreH54 as LegacyPreH58.
  all: pose proof PreH55 as LegacyPreH59.
  all: pose proof PreH56 as LegacyPreH60.
  all: pose proof PreH57 as LegacyPreH61.

  all: street_pack.
  all: assert (Hrange_PreH55 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH55 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH56 z ltac:(lia)); lia).
  all: assert (Hrange_PreH57 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH58 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH59 z ltac:(lia)); lia).
  all: assert (Hrange_PreH58 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH60 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH61 z ltac:(lia)); lia).
  all: street_public_goal.

  assert (Hposstep :
    Znth left pos_l 0 < Znth (left + 1) pos_l 0).
  { apply LegacyPreH57. lia. }
  Left. Left.
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    pose proof (IntArray2.missing_i_merge_to_full
      (&("dp_r")) (left + 1) n_pre n_pre right_table
      (Znth (left + 1) right_table __default__List_Z)) as Hrtablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_r")) n_pre (left + 1)) n_pre
      (Znth (left + 1) right_table __default__List_Z)) with
      (IntArray.full ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) right_table __default__List_Z))
      in Hrtablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) right_table __default__List_Z) 0)
      (Znth (left + 1) right_table __default__List_Z)) as Hrrowmerge.
    assert (Hraddr :
      (&("dp_r")) + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      (&("dp_r")) + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hraddr.
    sep_apply Hrrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hrtablemerge; try lia.
    rewrite replace_Znth_Znth.
    pose proof (IntArray2.missing_i_merge_to_full
      (&("dp_l")) (left + 1) n_pre n_pre left_table
      (Znth (left + 1) left_table __default__List_Z)) as Hltablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_l")) n_pre (left + 1)) n_pre
      (Znth (left + 1) left_table __default__List_Z)) with
      (IntArray.full ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT))
        n_pre (Znth (left + 1) left_table __default__List_Z))
      in Hltablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT))
      ((left + len) - 1) n_pre
      (Znth ((left + len) - 1)
        (Znth (left + 1) left_table __default__List_Z) 0)
      (Znth (left + 1) left_table __default__List_Z)) as Hlrowmerge.
    assert (Hladdr :
      (&("dp_l")) + (left + 1) * n_pre * sizeof (INT) +
        ((left + len) - 1) * sizeof (INT) =
      (&("dp_l")) + (((left + 1) * n_pre + ((left + len) - 1)) *
        sizeof (INT))) by lia.
    rewrite <- Hladdr.
    sep_apply Hlrowmerge; try lia.
    rewrite replace_Znth_Znth.
    sep_apply Hltablemerge; try lia.
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures.
    all: dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: first [assumption | reflexivity | lia | nia].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_16_4 : solve_entail_wit_16_4.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH7 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH8 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH46 as LegacyPreH50.
  all: pose proof PreH47 as LegacyPreH51.
  all: pose proof PreH49 as LegacyPreH53.
  all: pose proof PreH50 as LegacyPreH54.
  all: pose proof PreH51 as LegacyPreH55.
  all: pose proof PreH52 as LegacyPreH56.

  all: street_pack.
  all: assert (Hrange_PreH50 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH50 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH51 z ltac:(lia)); lia).
  all: assert (Hrange_PreH52 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH53 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH54 z ltac:(lia)); lia).
  all: assert (Hrange_PreH53 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH55 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH56 z ltac:(lia)); lia).
  all: street_public_goal.

  Left.
  
  
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace
      ((&("dp_r")) + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
      with
      (((&("dp_r")) + (left + 1) * n_pre * sizeof (INT)) +
       (left + len - 1) * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT))
        (left + len - 1) n_pre
        (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)
        (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + rewrite replace_Znth_Znth by lia.
      pose proof
        (IntArray2.missing_i_merge_to_full
          (&("dp_r")) (left + 1) n_pre n_pre right_table
          (Znth (left + 1) right_table __default__List_Z))
        as Hmerge_right.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr (&("dp_r")) n_pre (left + 1)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray.full
          ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT)) n_pre
          (Znth (left + 1) right_table __default__List_Z))
        in Hmerge_right.
      sep_apply_l_atomic Hmerge_right.
      * dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          ((&("dp_l")) + (((left + 1) * n_pre + (left + len - 1)) * sizeof (INT)))
          with
          (((&("dp_l")) + (left + 1) * n_pre * sizeof (INT)) +
           (left + len - 1) * sizeof (INT))
          by (rewrite sizeof_int; lia).
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
            ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT))
            (left + len - 1) n_pre
            (Znth (left + len - 1)
              (Znth (left + 1) left_table __default__List_Z) 0)
            (Znth (left + 1) left_table __default__List_Z)).
        -- dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
        -- rewrite replace_Znth_Znth by lia.
           pose proof
             (IntArray2.missing_i_merge_to_full
               (&("dp_l")) (left + 1) n_pre n_pre left_table
               (Znth (left + 1) left_table __default__List_Z))
             as Hmerge_left.
           change
             (IntArray2.ElemArray.full
               (IntArray2.row_addr (&("dp_l")) n_pre (left + 1)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             with
             (IntArray.full
               ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT)) n_pre
               (Znth (left + 1) left_table __default__List_Z))
             in Hmerge_left.
           sep_apply_l_atomic Hmerge_left.
           ++ dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try assumption; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_16_5 : solve_entail_wit_16_5.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH3 : (1 <= (total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH4 : ((total - ((Znth (((left + len ) - 1 ) + 1 ) prefix_l 0) - (Znth (left + 1 ) prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH42 as LegacyPreH46.
  all: pose proof PreH43 as LegacyPreH47.
  all: pose proof PreH45 as LegacyPreH49.
  all: pose proof PreH46 as LegacyPreH50.
  all: pose proof PreH47 as LegacyPreH51.
  all: pose proof PreH48 as LegacyPreH52.
  all: pose proof PreH53 as LegacyPreH57.

  all: street_pack.
  all: assert (Hrange_PreH46 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH46 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH47 z ltac:(lia)); lia).
  all: assert (Hrange_PreH48 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH49 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH50 z ltac:(lia)); lia).
  all: assert (Hrange_PreH49 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH51 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH52 z ltac:(lia)); lia).
  all: street_public_goal.

  prop_apply_p
    (store_int_range
       ((&("dp_r")) + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) right_table __default__List_Z) 0)).
  Intros_p Hright_range.
  prop_apply_p
    (store_int_range
       ((&("dp_l")) + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
       (Znth (left + len - 1)
          (Znth (left + 1) left_table_2 __default__List_Z) 0)).
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  pose proof LegacyPreH57 as Hshape.
  unfold StreetlightLeftProgressFacts, StreetlightLengthsDoneFacts,
    StreetlightTableShape in Hshape.
  destruct Hshape as [Hlengths Hpartial].
  destruct Hlengths as [Hleft_shape Hrest].
  destruct Hrest as [Hright_shape Hdone].
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace
      ((&("dp_r")) + ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
      with
      ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT) +
       (left + len - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT))
         (left + len - 1) n_pre
         (Znth (left + len - 1)
            (Znth (left + 1) right_table __default__List_Z) 0)
         (Znth (left + 1) right_table __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + rewrite replace_Znth_Znth by
        (pose proof (Hright_row_len (left + 1) ltac:(lia)); lia).
      change
        (IntArray.full
           ((&("dp_r")) + (left + 1) * n_pre * sizeof (INT)) n_pre
           (Znth (left + 1) right_table __default__List_Z))
        with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr (&("dp_r")) n_pre (left + 1)) n_pre
           (Znth (left + 1) right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           (&("dp_r")) (left + 1) n_pre n_pre right_table
           (Znth (left + 1) right_table __default__List_Z)).
      * dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          ((&("dp_l")) +
           ((left + 1) * n_pre + (left + len - 1)) * sizeof (INT))
          with
          ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT) +
           (left + len - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT))
             (left + len - 1) n_pre
             (Znth (left + len - 1)
                (Znth (left + 1) left_table_2 __default__List_Z) 0)
             (Znth (left + 1) left_table_2 __default__List_Z)).
        -- dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len (left + 1) ltac:(lia)); lia).
           change
             (IntArray.full
                ((&("dp_l")) + (left + 1) * n_pre * sizeof (INT)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z))
             with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr (&("dp_l")) n_pre (left + 1)) n_pre
                (Znth (left + 1) left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                (&("dp_l")) (left + 1) n_pre n_pre left_table_2
                (Znth (left + 1) left_table_2 __default__List_Z)).
           ++ dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; auto; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_17_1 : solve_entail_wit_17_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH3 as LegacyPreH3.
  all: pose proof PreH5 as LegacyPreH5.
  all: pose proof PreH10 as LegacyPreH10.
  all: pose proof PreH12 as LegacyPreH12.
  all: pose proof PreH13 as LegacyPreH13.
  all: pose proof PreH14 as LegacyPreH14.
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH32 as LegacyPreH34.
  all: pose proof PreH33 as LegacyPreH35.
  all: pose proof PreH34 as LegacyPreH36.
  all: pose proof PreH35 as LegacyPreH37.
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH37 as LegacyPreH39.
  all: pose proof PreH38 as LegacyPreH40.
  all: pose proof PreH39 as LegacyPreH41.
  all: pose proof PreH40 as LegacyPreH42.
  all: pose proof PreH43 as LegacyPreH45.
  all: pose proof PreH45 as LegacyPreH47.

  all: street_pack.
  all: assert (Hrange_PreH36 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: assert (Hrange_PreH38 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (StreetlightPrefixProgress_total_sum__right_remain_a
       power_l prefix_l_2 n_pre total LegacyPreH35 LegacyPreH45 LegacyPreH3)
    as Htotal_sum.
  pose proof
    (StreetlightLeftProgress_predecessor_finite__right_remain_a
       pos_l power_l left_table_2 right_table_2 n_pre start len left right
       __default__List_Z
       LegacyPreH34 LegacyPreH35 Hrange_PreH36 LegacyPreH38 Hrange_PreH38 ltac:(lia) LegacyPreH5 LegacyPreH10
       LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH47)
    as Hfinite.
  destruct Hfinite as [Hfinite | Hfinite].
  - lia.
  - lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_17_2 : solve_entail_wit_17_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH37 as LegacyPreH39.
  all: pose proof PreH39 as LegacyPreH41.
  all: pose proof PreH40 as LegacyPreH42.
  all: pose proof PreH41 as LegacyPreH43.
  all: pose proof PreH42 as LegacyPreH44.
  all: pose proof PreH43 as LegacyPreH45.
  all: pose proof PreH44 as LegacyPreH46.
  all: pose proof PreH47 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); lia).
  all: assert (Hrange_PreH40 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: assert (Hrange_PreH41 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH43 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH44 z ltac:(lia)); lia).
  all: street_public_goal.

  subst inf.
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hremaining :
      remain = sum power_l - sum (sublist (left + 1) (right + 1) power_l)).
  { eapply StreetlightPrefixProgress_remaining__right_remain_b; eauto; lia. }
  assert (Hselected :
      (Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) left_table_2 __default__List_Z) 0 +
         (Znth (left + 1) pos_l 0 - Znth left pos_l 0) * remain) \/
      (Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 <
         2147483647 /\
       best = Znth right (Znth (left + 1) right_table_2 __default__List_Z) 0 +
         (Znth right pos_l 0 - Znth left pos_l 0) * remain)).
  { left. split; assumption. }
  assert (Hready :
      StreetlightLeftEndpointReadyFacts pos_l power_l updated_table right_table_2
        n_pre start len left).
  { unfold updated_table, updated_row.
    eapply StreetlightLeftEndpointReady_after_best__right_remain_b;
      eauto; lia. }
  pose proof LegacyPreH49 as Hprogress_shape.
  unfold StreetlightLeftProgressFacts in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths _].
  unfold StreetlightLengthsDoneFacts in Hlengths.
  destruct Hlengths as [Hshape_left [_ _]].
  assert (Hpending_right :
      forall pending_right,
        start + len - 1 <= pending_right < n_pre ->
        Znth pending_right
          (Znth start updated_table __default__List_Z) 0 = 2147483647).
  { intros pending_right Hpending.
    unfold updated_table.
    rewrite Znth_replace_Znth_Diff.
    - apply LegacyPreH45. exact Hpending.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - unfold StreetlightTableShape in Hshape_left. lia.
    - lia. }
  assert (Hleft_start :
      left = start ->
      Znth right (Znth left updated_table __default__List_Z) 0 = 2147483647).
  { intros Hcontra. lia. }
  assert (Hright_start :
      right = start ->
      Znth right (Znth left right_table_2 __default__List_Z) 0 = 2147483647).
  { intros Hright_start.
    rewrite Hright_start.
    apply LegacyPreH46. lia. }
  
  Exists right_table_2 updated_table prefix_l_2.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    pose proof (IntArray.missing_i_merge_to_full
      ((&("dp_l")) + left * n_pre * sizeof (INT)) right n_pre best
      (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      (&("dp_l")) + left * n_pre * sizeof (INT) + right * sizeof (INT) =
      (&("dp_l")) + (left * n_pre + right) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold updated_row.
    pose proof (IntArray2.missing_i_merge_to_full
      (&("dp_l")) left n_pre n_pre left_table_2 updated_row) as Htable_merge.
    change
      (IntArray2.ElemArray.full
        (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre updated_row)
      with
      (IntArray.full
        ((&("dp_l")) + left * n_pre * sizeof (INT)) n_pre updated_row)
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold updated_table. cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try assumption; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_17_3 : solve_entail_wit_17_3.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH3 as LegacyPreH3.
  all: pose proof PreH5 as LegacyPreH5.
  all: pose proof PreH12 as LegacyPreH12.
  all: pose proof PreH14 as LegacyPreH14.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH26 as LegacyPreH26.
  all: pose proof PreH27 as LegacyPreH27.
  all: pose proof PreH28 as LegacyPreH28.
  all: pose proof PreH29 as LegacyPreH29.
  all: pose proof PreH34 as LegacyPreH36.
  all: pose proof PreH35 as LegacyPreH37.
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH37 as LegacyPreH39.
  all: pose proof PreH38 as LegacyPreH40.
  all: pose proof PreH39 as LegacyPreH41.
  all: pose proof PreH40 as LegacyPreH42.
  all: pose proof PreH41 as LegacyPreH43.
  all: pose proof PreH42 as LegacyPreH44.
  all: pose proof PreH43 as LegacyPreH45.
  all: pose proof PreH44 as LegacyPreH46.
  all: pose proof PreH45 as LegacyPreH47.
  all: pose proof PreH47 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); lia).
  all: assert (Hrange_PreH40 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: assert (Hrange_PreH41 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH43 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH44 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (StreetlightPrefixProgress_remaining__right_remain_c
      power_l prefix_l_2 n_pre total left right remain
      LegacyPreH37 LegacyPreH12 ltac:(lia) LegacyPreH16 LegacyPreH3 LegacyPreH21 LegacyPreH47)
    as Hremain_sum.
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    pose proof LegacyPreH49 as Hshape.
    unfold StreetlightLeftProgressFacts, StreetlightLengthsDoneFacts,
      StreetlightTableShape in Hshape.
    tauto.
  }
  set (updated_row :=
    replace_Znth right best (Znth left left_table_2 __default__List_Z)).
  set (updated_table := replace_Znth left updated_row left_table_2).
  assert (Hready :
    StreetlightLeftEndpointReadyFacts pos_l power_l updated_table right_table_2
      n_pre start len left).
  {
    unfold updated_table, updated_row.
    eapply streetlight_left_endpoint_minimum_extend__right_remain_c;
      [ exact LegacyPreH36 | exact LegacyPreH37 | exact LegacyPreH5 | lia | exact LegacyPreH12
      | lia | exact LegacyPreH14 | exact LegacyPreH16 | exact LegacyPreH19 | exact LegacyPreH40
      | exact Hremain_sum | exact LegacyPreH49 | exact LegacyPreH26
      | intros Hfinite; apply LegacyPreH28; lia
      | intros Hfinite; apply LegacyPreH29; lia
      | left; split; [lia | exact LegacyPreH27] ].
  }
  
  Exists right_table_2 updated_table prefix_l_2.
  repeat (split_pure_spatial || split_pures).
  all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia].
  all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; assumption].
  all: try solve [
    dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
    intros pending_right Hpending;
    unfold updated_table;
    rewrite (Znth_replace_Znth_Diff __default__List_Z left_table_2 left
      start updated_row) by (try rewrite Hleft_table_len; lia);
    apply LegacyPreH45;
    exact Hpending
  ].
  all: try solve [
    dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
    intros Hright_start;
    rewrite Hright_start;
    apply LegacyPreH46;
    lia
  ].
  all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; exact Hready].
  pose proof (IntArray.missing_i_merge_to_full
    ((&("dp_l")) + left * n_pre * sizeof (INT)) right n_pre best
    (Znth left left_table_2 __default__List_Z)) as Hrow_merge.
  simpl in Hrow_merge.
  assert (Haddr :
    (&("dp_l")) + left * n_pre * sizeof (INT) + right * sizeof (INT) =
    (&("dp_l")) + (left * n_pre + right) * sizeof (INT)) by lia.
  rewrite <- Haddr.
  sep_apply Hrow_merge; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    (&("dp_l")) left n_pre n_pre left_table_2 updated_row) as Htable_merge.
  change
    (IntArray2.ElemArray.full
      (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre updated_row)
    with
    (IntArray.full
      ((&("dp_l")) + left * n_pre * 4) n_pre updated_row)
    in Htable_merge.
  fold updated_row.
  sep_apply Htable_merge; try lia.
  cancel (IntArray.full pos_pre n_pre pos_l).
  cancel (IntArray.full power_pre n_pre power_l).
  cancel (IntArray.full (&("pre")) (n_pre + 1) prefix_l_2).
  cancel (IntArray2.full (&("dp_l")) n_pre n_pre updated_table).
  cancel (IntArray2.full (&("dp_r")) n_pre n_pre right_table_2).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_17_4 : solve_entail_wit_17_4.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH3 as LegacyPreH3.
  all: pose proof PreH14 as LegacyPreH14.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH27 as LegacyPreH27.
  all: pose proof PreH34 as LegacyPreH36.
  all: pose proof PreH35 as LegacyPreH37.
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH37 as LegacyPreH39.
  all: pose proof PreH38 as LegacyPreH40.
  all: pose proof PreH39 as LegacyPreH41.
  all: pose proof PreH40 as LegacyPreH42.
  all: pose proof PreH41 as LegacyPreH43.
  all: pose proof PreH42 as LegacyPreH44.
  all: pose proof PreH43 as LegacyPreH45.
  all: pose proof PreH44 as LegacyPreH46.
  all: pose proof PreH45 as LegacyPreH47.
  all: pose proof PreH47 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); lia).
  all: assert (Hrange_PreH40 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: assert (Hrange_PreH41 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH43 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH44 z ltac:(lia)); lia).
  all: street_public_goal.

  set (row' := replace_Znth right best
    (Znth left left_table_2 __default__List_Z)).
  set (left_table := replace_Znth left row' left_table_2).
  assert (Hentry :
    StreetlightLeftEntryCorrectFacts pos_l power_l start left right best).
  {
    eapply (streetlight_right_candidate_left_entry__right_remain_d
      pos_l power_l prefix_l_2 left_table_2 right_table_2
      n_pre start len left right total remain best inf
      __default__List_Z).
    - exact LegacyPreH1.
    - exact LegacyPreH36.
    - exact LegacyPreH37.
    - lia.
    - lia.
    - lia.
    - exact LegacyPreH14.
    - lia.
    - exact LegacyPreH19.
    - exact LegacyPreH3.
    - exact LegacyPreH21.
    - exact LegacyPreH27.
    - exact LegacyPreH23.
    - subst inf. nia.
    - left. exact LegacyPreH24.
    - exact LegacyPreH40.
    - exact LegacyPreH47.
    - exact LegacyPreH49.
  }
  assert (Hready :
    StreetlightLeftEndpointReadyFacts
      pos_l power_l left_table right_table_2 n_pre start len left).
  {
    unfold left_table, row'.
    eapply (streetlight_right_candidate_left_store__right_remain_d
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      best __default__List_Z);
      try eassumption; lia.
  }
  assert (Hleft_table_len : Zlength left_table_2 = n_pre).
  {
    unfold StreetlightLeftProgressFacts, StreetlightLengthsDoneFacts,
      StreetlightTableShape in LegacyPreH49.
    tauto.
  }
  assert (Hpending_right :
    forall pending_right,
      (start + len - 1 <= pending_right /\ pending_right < n_pre) ->
      Znth pending_right
        (Znth start left_table __default__List_Z) 0 = inf).
  {
    intros pending_right Hpending.
    unfold left_table.
    rewrite Znth_replace_Znth_Diff.
    - apply LegacyPreH45. lia.
    - rewrite Hleft_table_len. lia.
    - rewrite Hleft_table_len. lia.
    - lia.
  }
  assert (Hright_sentinel :
    right = start ->
    Znth right (Znth left right_table_2 __default__List_Z) 0 = inf).
  {
    intros Hright_start.
    rewrite Hright_start.
    apply LegacyPreH46. lia.
  }
  
  Exists right_table_2 left_table prefix_l_2.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace ((&("dp_l")) + (left * n_pre + right) * sizeof (INT))
      with ((&("dp_l")) + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        ((&("dp_l")) + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left left_table_2 __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + fold row'.
      change
        (IntArray.full
          ((&("dp_l")) + left * n_pre * sizeof (INT)) n_pre row')
        with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre row').
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
          (&("dp_l")) left n_pre n_pre left_table_2 row').
      * dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
      * fold left_table. cancel.
  - split_pures.
    all: dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: try assumption; try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_17_5 : solve_entail_wit_17_5.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH3 as LegacyPreH3.
  all: pose proof PreH10 as LegacyPreH10.
  all: pose proof PreH14 as LegacyPreH14.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH27 as LegacyPreH27.
  all: pose proof PreH34 as LegacyPreH36.
  all: pose proof PreH35 as LegacyPreH37.
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH37 as LegacyPreH39.
  all: pose proof PreH39 as LegacyPreH41.
  all: pose proof PreH40 as LegacyPreH42.
  all: pose proof PreH41 as LegacyPreH43.
  all: pose proof PreH42 as LegacyPreH44.
  all: pose proof PreH43 as LegacyPreH45.
  all: pose proof PreH44 as LegacyPreH46.
  all: pose proof PreH45 as LegacyPreH47.
  all: pose proof PreH47 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); lia).
  all: assert (Hrange_PreH40 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: assert (Hrange_PreH41 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH43 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH44 z ltac:(lia)); lia).
  all: street_public_goal.

  
  Exists right_table_2
    (replace_Znth left
      (replace_Znth right best
        (Znth left left_table_2 __default__List_Z))
      left_table_2)
    prefix_l_2.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace ((&("dp_l")) + (left * n_pre + right) * sizeof (INT)) with
      ((&("dp_l")) + left * n_pre * sizeof (INT) + right * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        ((&("dp_l")) + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left left_table_2 __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + change (IntArray.full
        ((&("dp_l")) + left * n_pre * sizeof (INT)) n_pre
        (replace_Znth right best
          (Znth left left_table_2 __default__List_Z))) with
        (IntArray2.ElemArray.full
          (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
          (&("dp_l")) left n_pre n_pre left_table_2
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))).
      * dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
      * cancel.
  - split_pures.
    all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; auto].
    all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia].
    all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; intros Hright; rewrite Hright;
                    exact (LegacyPreH46 left ltac:(lia))].
    all: try solve [
      dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
      intros pending_right Hpending;
      pose proof LegacyPreH49 as Hshape_pending;
      unfold StreetlightLeftProgressFacts, StreetlightLengthsDoneFacts,
        StreetlightTableShape in Hshape_pending;
      destruct Hshape_pending as [[[Htable_len_pending _] _] _];
      rewrite Znth_replace_Znth_Diff by lia;
      apply LegacyPreH45; lia
    ].
    all: dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    assert (Hprogress_updated :
      StreetlightLeftProgressFacts pos_l power_l
        (replace_Znth left
          (replace_Znth right best
            (Znth left left_table_2 __default__List_Z))
          left_table_2)
        right_table_2 n_pre start len left).
    { exact (StreetlightLeftProgress_replace_current__right_remain_e
        pos_l power_l left_table_2 right_table_2 n_pre start len left
        right best __default__List_Z ltac:(lia) ltac:(lia) LegacyPreH14 LegacyPreH49). }
    assert (Hentry :
      StreetlightLeftEntryCorrectFacts pos_l power_l start left right best).
    { exact (StreetlightLeftEntryCorrect_right_choice__right_remain_e
        pos_l power_l prefix_l_2 left_table_2 right_table_2 n_pre start
        len left right total remain best __default__List_Z LegacyPreH36 LegacyPreH37
        ltac:(lia) LegacyPreH14 ltac:(lia) LegacyPreH10 LegacyPreH3 LegacyPreH21
        ltac:(rewrite <- LegacyPreH1; exact LegacyPreH23) LegacyPreH24 LegacyPreH27 LegacyPreH47 LegacyPreH49). }
    pose proof LegacyPreH49 as Hshape.
    unfold StreetlightLeftProgressFacts, StreetlightLengthsDoneFacts,
      StreetlightTableShape in Hshape.
    destruct Hshape as [[[Htable_len Hrow_len] _] _].
    unfold StreetlightLeftEndpointReadyFacts.
    split.
    + exact Hprogress_updated.
    + replace (left + len - 1) with right by lia.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same.
      * exact Hentry.
      * rewrite (Znth_indep left_table_2 left __default__List_Z nil) by lia.
        rewrite Hrow_len by lia.
        lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_17_6 : solve_entail_wit_17_6.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH41 as LegacyPreH43.
  all: pose proof PreH42 as LegacyPreH44.
  all: pose proof PreH44 as LegacyPreH46.
  all: pose proof PreH45 as LegacyPreH47.
  all: pose proof PreH46 as LegacyPreH48.
  all: pose proof PreH47 as LegacyPreH49.
  all: pose proof PreH48 as LegacyPreH50.
  all: pose proof PreH52 as LegacyPreH54.

  all: street_pack.
  all: assert (Hrange_PreH43 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH43 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH44 z ltac:(lia)); lia).
  all: assert (Hrange_PreH45 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH46 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH47 z ltac:(lia)); lia).
  all: assert (Hrange_PreH46 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH48 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH49 z ltac:(lia)); lia).
  all: street_public_goal.

  
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    scratch_cancel.
  - split_pures.
    all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; auto].
    all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia].
    all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; intros; apply LegacyPreH50; lia].
    all: try solve [dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; intros Hleft; rewrite Hleft;
                    exact (LegacyPreH50 (start + len - 1) ltac:(lia))].
    all: dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    pose proof LegacyPreH54 as Hshape.
    unfold StreetlightLeftProgressFacts, StreetlightLengthsDoneFacts,
      StreetlightTableShape in Hshape.
    destruct Hshape as [[Hleft_shape _] _].
    destruct Hleft_shape as [Htable_len _].
    unfold StreetlightLeftEndpointReadyFacts.
    split.
    + exact LegacyPreH54.
    + unfold StreetlightLeftEntryCorrectFacts.
      right; right.
      repeat split; try lia.
      replace left with start by lia.
      rewrite (Znth_indep left_table_2 start nil __default__List_Z) by lia.
      rewrite <- LegacyPreH20.
      apply LegacyPreH50; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_18 : solve_entail_wit_18.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH2 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH3 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH2 as LegacyPreH4.
  all: pose proof PreH3 as LegacyPreH5.
  all: pose proof PreH5 as LegacyPreH7.
  all: pose proof PreH12 as LegacyPreH14.
  all: pose proof PreH14 as LegacyPreH16.
  all: pose proof PreH15 as LegacyPreH17.
  all: pose proof PreH16 as LegacyPreH18.
  all: pose proof PreH18 as LegacyPreH20.
  all: pose proof PreH25 as LegacyPreH29.
  all: pose proof PreH26 as LegacyPreH30.
  all: pose proof PreH27 as LegacyPreH31.
  all: pose proof PreH28 as LegacyPreH32.
  all: pose proof PreH29 as LegacyPreH33.
  all: pose proof PreH30 as LegacyPreH34.
  all: pose proof PreH31 as LegacyPreH35.
  all: pose proof PreH32 as LegacyPreH36.
  all: pose proof PreH33 as LegacyPreH37.
  all: pose proof PreH38 as LegacyPreH42.
  all: pose proof PreH40 as LegacyPreH44.

  all: street_pack.
  all: assert (Hrange_PreH31 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH31 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH32 z ltac:(lia)); lia).
  all: assert (Hrange_PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH34 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH35 z ltac:(lia)); lia).
  all: assert (Hrange_PreH34 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (streetlight_right_predecessor_bounds__right_second
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start len left right total inf
       LegacyPreH29 LegacyPreH30 Hrange_PreH31 LegacyPreH33 Hrange_PreH33 LegacyPreH42 LegacyPreH7
       ltac:(lia) LegacyPreH5 LegacyPreH14 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH4 LegacyPreH20
       LegacyPreH44 LegacyPreH1) as Hpredecessor_bounds.
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try assumption; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_19 : solve_entail_wit_19.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH4 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH5 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH29 as LegacyPreH33.
  all: pose proof PreH30 as LegacyPreH34.
  all: pose proof PreH31 as LegacyPreH35.
  all: pose proof PreH32 as LegacyPreH36.
  all: pose proof PreH33 as LegacyPreH37.
  all: pose proof PreH34 as LegacyPreH38.
  all: pose proof PreH35 as LegacyPreH39.

  all: street_pack.
  all: assert (Hrange_PreH33 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH33 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH34 z ltac:(lia)); lia).
  all: assert (Hrange_PreH35 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: assert (Hrange_PreH36 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof (Hrange_PreH33 left ltac:(lia)) as Hleft_bounds.
  pose proof (Hrange_PreH33 right ltac:(lia)) as Hright_bounds.
  pose proof
    (streetlight_strict_positions__right_choose
       pos_l n_pre left right LegacyPreH35 ltac:(lia) ltac:(lia) ltac:(lia))
    as Hpositions_ordered.
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures;
      dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
      try assumption;
      nia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_20_1 : solve_entail_wit_20_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH7 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH8 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH32 as LegacyPreH36.
  all: pose proof PreH33 as LegacyPreH37.
  all: pose proof PreH34 as LegacyPreH38.
  all: pose proof PreH35 as LegacyPreH39.
  all: pose proof PreH36 as LegacyPreH40.
  all: pose proof PreH37 as LegacyPreH41.
  all: pose proof PreH38 as LegacyPreH42.
  all: pose proof PreH43 as LegacyPreH47.
  all: pose proof PreH45 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH36 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: assert (Hrange_PreH38 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof LegacyPreH47 as Hprefix_progress.
  unfold StreetlightPrefixProgressFacts in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_values].
  assert (Hpower_sum : sum power_l = total).
  { specialize (Hprefix_values n_pre ltac:(lia)).
    rewrite (sublist_self power_l n_pre ltac:(lia)) in Hprefix_values.
    lia. }
  assert (Hposition_adjacent :
    forall k, 0 <= k -> k + 1 < Zlength pos_l ->
      Znth k pos_l 0 < Znth (k + 1) pos_l 0).
  { intros k Hk Hnext.
    apply LegacyPreH38.
    lia. }
  assert (Hposition_bounds :
    forall k, 0 <= k < Zlength pos_l ->
      0 <= Znth k pos_l 0 <= 8000).
  { intros k Hk.
    apply Hrange_PreH36.
    lia. }
  assert (Hpower_nonnegative :
    forall k, 0 <= k < Zlength power_l -> 0 <= Znth k power_l 0).
  { intros k Hk.
    specialize (Hrange_PreH38 k ltac:(lia)).
    lia. }
  assert (Hright_bounds :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 <=
      (len - 2) * 40000000).
  { pose proof LegacyPreH49 as Hready.
    unfold StreetlightLeftEndpointReadyFacts in Hready.
    destruct Hready as [Hleft_progress Hleft_entry].
    unfold StreetlightLeftProgressFacts in Hleft_progress.
    destruct Hleft_progress as [Hlengths_done Hfinished_lefts].
    unfold StreetlightLengthsDoneFacts in Hlengths_done.
    destruct Hlengths_done as [Hleft_shape [Hright_shape Hdone]].
    unfold StreetlightTableShape in Hright_shape.
    destruct Hright_shape as [Hright_length Hright_rows].
    assert (Hright_row_default :
      Znth left right_table __default__List_Z =
      Znth left right_table nil).
    { apply Znth_indep.
      lia. }
    pose proof LegacyPreH1 as Hright_finite.
    rewrite Hright_row_default in Hright_finite.
    rewrite Hright_row_default.
    specialize
      (Hdone (len - 1) left (right - 1)
         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold StreetlightIntervalCorrectFacts in Hdone.
    destruct Hdone as [Hleft_previous Hright_previous].
    unfold StreetlightRightEntryCorrectFacts in Hright_previous.
    destruct Hright_previous as [Hbase | [Hminimum | Hsentinel]].
    - destruct Hbase as [Hleft_start [Hright_start Hvalue]].
      lia.
    - destruct Hminimum as [Hstart_before Hminimum].
      unfold StreetlightEndpointMinimumFacts,
        MaxMinLib.MaxMin.min_value_of_subset,
        MaxMinLib.MaxMin.min_object_of_subset in Hminimum.
      destruct Hminimum as [cost [[Hplan Hleast] ->]].
      pose proof
        (StreetlightPlan_cost_bounds__right_bounds_a
           pos_l power_l start left (right - 1) (right - 1)
           (Znth (right - 1) (Znth left right_table nil) 0)
           Hplan
           Hposition_adjacent Hposition_bounds ltac:(lia)
           Hpower_nonnegative ltac:(lia))
        as Hcost_bounds.
      lia.
    - destruct Hsentinel as [Hleft_before [Hright_start Hvalue]].
      lia.
  }
  destruct Hright_bounds as [Hright_nonnegative Hright_upper].
  
  entailer_with ltac:(lia || int_auto).
  all: street_public_goal; assumption.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_20_2 : solve_entail_wit_20_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH3 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH4 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH4 as LegacyPreH6.
  all: pose proof PreH6 as LegacyPreH8.
  all: pose proof PreH13 as LegacyPreH15.
  all: pose proof PreH15 as LegacyPreH17.
  all: pose proof PreH16 as LegacyPreH18.
  all: pose proof PreH17 as LegacyPreH19.
  all: pose proof PreH19 as LegacyPreH21.
  all: pose proof PreH26 as LegacyPreH30.
  all: pose proof PreH27 as LegacyPreH31.
  all: pose proof PreH28 as LegacyPreH32.
  all: pose proof PreH29 as LegacyPreH33.
  all: pose proof PreH30 as LegacyPreH34.
  all: pose proof PreH31 as LegacyPreH35.
  all: pose proof PreH32 as LegacyPreH36.
  all: pose proof PreH33 as LegacyPreH37.
  all: pose proof PreH34 as LegacyPreH38.
  all: pose proof PreH39 as LegacyPreH43.
  all: pose proof PreH41 as LegacyPreH45.

  all: street_pack.
  all: assert (Hrange_PreH32 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH32 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH33 z ltac:(lia)); lia).
  all: assert (Hrange_PreH34 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH35 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); lia).
  all: assert (Hrange_PreH35 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (streetlight_right_predecessor_bounds__right_bounds_b
       pos_l power_l prefix_l left_table right_table __default__List_Z
       n_pre start total len left right inf
       LegacyPreH30 LegacyPreH31 Hrange_PreH32 LegacyPreH34 Hrange_PreH34 LegacyPreH8
       ltac:(lia) LegacyPreH15 LegacyPreH17 LegacyPreH18 LegacyPreH19 ltac:(lia) LegacyPreH21
       LegacyPreH43 LegacyPreH6 LegacyPreH1 LegacyPreH45) as Hprev_bounds.
  
  repeat (split_pure_spatial || split_pures);
    try solve [cancel | dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; auto | dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_21_1 : solve_entail_wit_21_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH9 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH10 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof Cleanup_PreH10 as LegacyPreH10.
  all: pose proof PreH34 as LegacyPreH38.
  all: pose proof PreH35 as LegacyPreH39.
  all: pose proof PreH36 as LegacyPreH40.
  all: pose proof PreH37 as LegacyPreH41.
  all: pose proof PreH38 as LegacyPreH42.
  all: pose proof PreH39 as LegacyPreH43.
  all: pose proof PreH40 as LegacyPreH44.

  all: street_pack.
  all: assert (Hrange_PreH38 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); lia).
  all: assert (Hrange_PreH40 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: assert (Hrange_PreH41 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH43 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH44 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof (Hrange_PreH38 right ltac:(lia)) as Hpos_right.
  pose proof (Hrange_PreH38 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (LegacyPreH40 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  assert (Hdiff_nonneg :
    0 <= Znth right pos_l 0 - Znth (right - 1) pos_l 0) by lia.
  assert (Hdiff_le :
    Znth right pos_l 0 - Znth (right - 1) pos_l 0 <= 8000) by lia.
  assert (Hremain_nonneg :
    0 <= total - (Znth right prefix_l 0 - Znth left prefix_l 0)) by lia.
  pose proof (Z.mul_le_mono_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0) 8000
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) 5000
    Hdiff_nonneg Hdiff_le Hremain_nonneg LegacyPreH10) as Hproduct_le.
  pose proof (Z.mul_nonneg_nonneg
    (Znth right pos_l 0 - Znth (right - 1) pos_l 0)
    (total - (Znth right prefix_l 0 - Znth left prefix_l 0))
    Hdiff_nonneg Hremain_nonneg) as Hproduct_nonneg.
  assert (Hcandidate_nonneg :
    0 <= Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0))) by lia.
  assert (Hcandidate_le :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 +
      (Znth right pos_l 0 - Znth (right - 1) pos_l 0) *
      (total - (Znth right prefix_l 0 - Znth left prefix_l 0)) <=
    (len - 1) * 40000000) by lia.
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures.
    all: dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: assumption.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_21_2 : solve_entail_wit_21_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH5 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH6 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH30 as LegacyPreH34.
  all: pose proof PreH31 as LegacyPreH35.
  all: pose proof PreH32 as LegacyPreH36.
  all: pose proof PreH33 as LegacyPreH37.
  all: pose proof PreH34 as LegacyPreH38.
  all: pose proof PreH35 as LegacyPreH39.
  all: pose proof PreH36 as LegacyPreH40.

  all: street_pack.
  all: assert (Hrange_PreH34 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH34 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH35 z ltac:(lia)); lia).
  all: assert (Hrange_PreH36 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); lia).
  all: assert (Hrange_PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l 0)) /\ ((Znth k_4 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof (Hrange_PreH34 right ltac:(lia)) as Hpos_right.
  pose proof (Hrange_PreH34 (right - 1) ltac:(lia)) as Hpos_prev.
  pose proof (LegacyPreH36 (right - 1) ltac:(lia)) as Hpos_step.
  replace (right - 1 + 1) with right in Hpos_step by lia.
  
  split_pure_spatial.
  - scratch_cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
      try assumption; try reflexivity; try lia; try nia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_22_1 : solve_entail_wit_22_1.
Proof.

  LLM_pre_process ltac:(lia).
  all: assert (Cleanup_PreH12 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH13 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH37 as LegacyPreH36.
  all: pose proof PreH38 as LegacyPreH37.
  all: pose proof PreH40 as LegacyPreH39.
  all: pose proof PreH41 as LegacyPreH40.
  all: pose proof PreH42 as LegacyPreH41.
  all: pose proof PreH43 as LegacyPreH42.
  all: pose proof PreH50 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH36 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: assert (Hrange_PreH38 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: street_public_goal.

  Right.
  pose proof LegacyPreH49 as Hready_shape.
  unfold StreetlightLeftEndpointReadyFacts in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgressFacts in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDoneFacts in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace
      ((&("dp_r")) + (left * n_pre + (right - 1)) * sizeof (INT)) with
      ((&("dp_r")) + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         ((&("dp_r")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full ((&("dp_r")) + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr (&("dp_r")) n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           (&("dp_r")) left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          ((&("dp_l")) + (left * n_pre + (right - 1)) * sizeof (INT)) with
          ((&("dp_l")) + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             ((&("dp_l")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full ((&("dp_l")) + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                (&("dp_l")) left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: try assumption.
    all: try solve [auto].
    all: try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_22_2 : solve_entail_wit_22_2.
Proof.

  LLM_pre_process ltac:(lia).
  all: assert (Cleanup_PreH8 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH9 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH33 as LegacyPreH36.
  all: pose proof PreH34 as LegacyPreH37.
  all: pose proof PreH36 as LegacyPreH39.
  all: pose proof PreH37 as LegacyPreH40.
  all: pose proof PreH38 as LegacyPreH41.
  all: pose proof PreH39 as LegacyPreH42.
  all: pose proof PreH46 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH36 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: assert (Hrange_PreH38 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: street_public_goal.

  Right.
  pose proof LegacyPreH49 as Hready_shape.
  unfold StreetlightLeftEndpointReadyFacts in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgressFacts in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDoneFacts in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace
      ((&("dp_r")) + (left * n_pre + (right - 1)) * sizeof (INT)) with
      ((&("dp_r")) + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         ((&("dp_r")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full ((&("dp_r")) + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr (&("dp_r")) n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           (&("dp_r")) left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          ((&("dp_l")) + (left * n_pre + (right - 1)) * sizeof (INT)) with
          ((&("dp_l")) + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             ((&("dp_l")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)
             (Znth left left_table_2 __default__List_Z)).
        -- dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full ((&("dp_l")) + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table_2 __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre
                (Znth left left_table_2 __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                (&("dp_l")) left n_pre n_pre left_table_2
                (Znth left left_table_2 __default__List_Z)).
           ++ dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: try assumption.
    all: try solve [auto].
    all: try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_22_3 : solve_entail_wit_22_3.
Proof.

  LLM_pre_process ltac:(lia).
  all: assert (Cleanup_PreH12 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH13 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH37 as LegacyPreH36.
  all: pose proof PreH38 as LegacyPreH37.
  all: pose proof PreH40 as LegacyPreH39.
  all: pose proof PreH41 as LegacyPreH40.
  all: pose proof PreH42 as LegacyPreH41.
  all: pose proof PreH43 as LegacyPreH42.
  all: pose proof PreH50 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH36 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: assert (Hrange_PreH38 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: street_public_goal.

  Left.
  pose proof LegacyPreH49 as Hready_shape.
  unfold StreetlightLeftEndpointReadyFacts in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgressFacts in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDoneFacts in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace
      ((&("dp_r")) + (left * n_pre + (right - 1)) * sizeof (INT)) with
      ((&("dp_r")) + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         ((&("dp_r")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full ((&("dp_r")) + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr (&("dp_r")) n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           (&("dp_r")) left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          ((&("dp_l")) + (left * n_pre + (right - 1)) * sizeof (INT)) with
          ((&("dp_l")) + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             ((&("dp_l")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full ((&("dp_l")) + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                (&("dp_l")) left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: try assumption.
    all: try solve [auto].
    all: try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_22_4 : solve_entail_wit_22_4.
Proof.

  LLM_pre_process ltac:(lia).
  all: assert (Cleanup_PreH7 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH8 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH32 as LegacyPreH36.
  all: pose proof PreH33 as LegacyPreH37.
  all: pose proof PreH35 as LegacyPreH39.
  all: pose proof PreH36 as LegacyPreH40.
  all: pose proof PreH37 as LegacyPreH41.
  all: pose proof PreH38 as LegacyPreH42.
  all: pose proof PreH45 as LegacyPreH49.

  all: street_pack.
  all: assert (Hrange_PreH36 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: assert (Hrange_PreH38 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: street_public_goal.

  
  pose proof LegacyPreH49 as Hready_shape.
  unfold StreetlightLeftEndpointReadyFacts in Hready_shape.
  destruct Hready_shape as [Hleft_progress _].
  unfold StreetlightLeftProgressFacts in Hleft_progress.
  destruct Hleft_progress as [Hlengths_done _].
  unfold StreetlightLengthsDoneFacts in Hlengths_done.
  destruct Hlengths_done as [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_len Hleft_row_len].
  destruct Hright_shape as [Hright_table_len Hright_row_len].
  Exists left_table right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace
      ((&("dp_r")) + (left * n_pre + (right - 1)) * sizeof (INT)) with
      ((&("dp_r")) + left * n_pre * sizeof (INT) + (right - 1) * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         ((&("dp_r")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + rewrite replace_Znth_Znth by
          (pose proof (Hright_row_len left ltac:(lia)); lia).
      change
        (IntArray.full ((&("dp_r")) + left * n_pre * sizeof (INT)) n_pre
           (Znth left right_table __default__List_Z)) with
        (IntArray2.ElemArray.full
           (IntArray2.row_addr (&("dp_r")) n_pre left) n_pre
           (Znth left right_table __default__List_Z)).
      sep_apply_l_atomic
        (IntArray2.missing_i_merge_to_full
           (&("dp_r")) left n_pre n_pre right_table
           (Znth left right_table __default__List_Z)).
      * dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
      * rewrite replace_Znth_Znth by lia.
        replace
          ((&("dp_l")) + (left * n_pre + (right - 1)) * sizeof (INT)) with
          ((&("dp_l")) + left * n_pre * sizeof (INT) +
             (right - 1) * sizeof (INT)) by lia.
        sep_apply_l_atomic
          (IntArray.missing_i_merge_to_full
             ((&("dp_l")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
             (Znth (right - 1) (Znth left left_table __default__List_Z) 0)
             (Znth left left_table __default__List_Z)).
        -- dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
        -- rewrite replace_Znth_Znth by
             (pose proof (Hleft_row_len left ltac:(lia)); lia).
           change
             (IntArray.full ((&("dp_l")) + left * n_pre * sizeof (INT)) n_pre
                (Znth left left_table __default__List_Z)) with
             (IntArray2.ElemArray.full
                (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre
                (Znth left left_table __default__List_Z)).
           sep_apply_l_atomic
             (IntArray2.missing_i_merge_to_full
                (&("dp_l")) left n_pre n_pre left_table
                (Znth left left_table __default__List_Z)).
           ++ dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
           ++ rewrite replace_Znth_Znth by lia.
              cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: try assumption.
    all: try solve [auto].
    all: try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_22_5 : solve_entail_wit_22_5.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: assert (Cleanup_PreH3 : (1 <= (total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ))) by street_cleanup_remaining.
  all: assert (Cleanup_PreH4 : ((total - ((Znth right prefix_l 0) - (Znth left prefix_l 0) ) ) <= 5000)) by street_cleanup_remaining.

  all: pose proof PreH28 as LegacyPreH32.
  all: pose proof PreH29 as LegacyPreH33.
  all: pose proof PreH31 as LegacyPreH35.
  all: pose proof PreH32 as LegacyPreH36.
  all: pose proof PreH33 as LegacyPreH37.
  all: pose proof PreH34 as LegacyPreH38.

  all: street_pack.
  all: assert (Hrange_PreH32 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH32 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH33 z ltac:(lia)); lia).
  all: assert (Hrange_PreH34 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH35 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); lia).
  all: assert (Hrange_PreH35 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l 0)) /\ ((Znth k_8 prefix_l 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); lia).
  all: street_public_goal.

  prop_apply_p
    (store_int_range
       ((&("dp_r")) + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left right_table __default__List_Z) 0)).
  prop_apply_p
    (store_int_range
       ((&("dp_l")) + (left * n_pre + (right - 1)) * sizeof (INT))
       (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)).
  Intros_p Hright_range.
  Intros_p Hleft_range.
  change Int.max_signed with 2147483647 in Hright_range, Hleft_range.
  assert (Hright_inf :
    Znth (right - 1) (Znth left right_table __default__List_Z) 0 = inf)
    by lia.
  assert (Hleft_inf :
    Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0 = inf)
    by lia.
  
  Exists left_table_2 right_table prefix_l.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace
      ((&("dp_r")) + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      ((&("dp_r")) + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         ((&("dp_r")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left right_table __default__List_Z) 0)
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         ((&("dp_r")) + left * n_pre * sizeof (INT)) n_pre
         (Znth left right_table __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&("dp_r")) n_pre left) n_pre
         (Znth left right_table __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         (&("dp_r")) left n_pre n_pre right_table
         (Znth left right_table __default__List_Z)).
    { dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia. }
    rewrite replace_Znth_Znth.
    replace
      ((&("dp_l")) + (left * n_pre + (right - 1)) * sizeof (INT))
      with
      ((&("dp_l")) + left * n_pre * sizeof (INT) +
       (right - 1) * sizeof (INT)) by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         ((&("dp_l")) + left * n_pre * sizeof (INT)) (right - 1) n_pre
         (Znth (right - 1) (Znth left left_table_2 __default__List_Z) 0)
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia. }
    rewrite replace_Znth_Znth.
    change
      (IntArray.full
         ((&("dp_l")) + left * n_pre * sizeof (INT)) n_pre
         (Znth left left_table_2 __default__List_Z))
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&("dp_l")) n_pre left) n_pre
         (Znth left left_table_2 __default__List_Z)).
    sep_apply_l_atomic
      (IntArray2.missing_i_merge_to_full
         (&("dp_l")) left n_pre n_pre left_table_2
         (Znth left left_table_2 __default__List_Z)).
    { dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia. }
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; auto; lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_23_1 : solve_entail_wit_23_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH5 as LegacyPreH5.
  all: pose proof PreH10 as LegacyPreH10.
  all: pose proof PreH12 as LegacyPreH12.
  all: pose proof PreH13 as LegacyPreH13.
  all: pose proof PreH14 as LegacyPreH14.
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH24 as LegacyPreH24.
  all: pose proof PreH32 as LegacyPreH34.
  all: pose proof PreH34 as LegacyPreH36.
  all: pose proof PreH35 as LegacyPreH37.
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH37 as LegacyPreH39.
  all: pose proof PreH38 as LegacyPreH40.
  all: pose proof PreH39 as LegacyPreH41.
  all: pose proof PreH40 as LegacyPreH42.
  all: pose proof PreH43 as LegacyPreH45.
  all: pose proof PreH45 as LegacyPreH47.

  all: street_pack.
  all: assert (Hrange_PreH36 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH36 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); lia).
  all: assert (Hrange_PreH38 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH39 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (streetlight_positions_order__right_close_a
      pos_l n_pre LegacyPreH34 LegacyPreH38) as Hmono.
  pose proof LegacyPreH45 as Hprefix.
  unfold StreetlightPrefixProgressFacts in Hprefix.
  destruct Hprefix as [Hprefix_length Hprefix_values].
  pose proof (Hprefix_values n_pre ltac:(lia)) as Htotal_sum.
  rewrite (sublist_self power_l n_pre ltac:(lia)) in Htotal_sum.
  assert (Hsum : sum power_l <= 5000) by lia.
  assert (Hsub : forall lo hi,
    0 <= lo <= hi -> hi <= n_pre ->
    0 <= sum (sublist lo hi power_l)).
  {
    intros lo hi Hlohi Hhi.
    eapply streetlight_sublist_sum_nonnegative__right_close_a; eauto.
  }
  pose proof
    (streetlight_close_interval_right__right_close_a
      pos_l power_l left_table_2 right_table_2 n_pre start len left right
      inf __default__List_Z LegacyPreH34 LegacyPreH5 Hrange_PreH36 Hmono Hsum Hsub LegacyPreH10
      LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH1 LegacyPreH23 LegacyPreH24 LegacyPreH47)
    as Hfalse.
  contradiction.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_23_2 : solve_entail_wit_23_2.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH3 as LegacyPreH3.
  all: pose proof PreH4 as LegacyPreH4.
  all: pose proof PreH5 as LegacyPreH5.
  all: pose proof PreH8 as LegacyPreH8.
  all: pose proof PreH9 as LegacyPreH9.
  all: pose proof PreH10 as LegacyPreH10.
  all: pose proof PreH11 as LegacyPreH11.
  all: pose proof PreH12 as LegacyPreH12.
  all: pose proof PreH13 as LegacyPreH13.
  all: pose proof PreH14 as LegacyPreH14.
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH25 as LegacyPreH25.
  all: pose proof PreH26 as LegacyPreH26.
  all: pose proof PreH27 as LegacyPreH27.
  all: pose proof PreH28 as LegacyPreH28.
  all: pose proof PreH33 as LegacyPreH35.
  all: pose proof PreH34 as LegacyPreH36.
  all: pose proof PreH35 as LegacyPreH37.
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH37 as LegacyPreH39.
  all: pose proof PreH38 as LegacyPreH40.
  all: pose proof PreH39 as LegacyPreH41.
  all: pose proof PreH40 as LegacyPreH42.
  all: pose proof PreH41 as LegacyPreH43.
  all: pose proof PreH43 as LegacyPreH45.
  all: pose proof PreH44 as LegacyPreH46.
  all: pose proof PreH46 as LegacyPreH48.

  all: street_pack.
  all: assert (Hrange_PreH37 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); lia).
  all: assert (Hrange_PreH40 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH43 z ltac:(lia)); lia).
  all: street_public_goal.

  
  set (right_row :=
    replace_Znth right best
      (Znth left right_table_2 __default__List_Z)).
  set (right_table := replace_Znth left right_row right_table_2).
  assert (Hminimum :
    StreetlightEndpointMinimumFacts pos_l power_l start left right right best).
  {
    eapply
      (streetlight_right_endpoint_minimum__right_close_b
        pos_l power_l prefix_l_2 left_table_2 right_table_2
        n_pre start len left right remain best inf __default__List_Z).
    - exact LegacyPreH1.
    - exact LegacyPreH4.
    - exact LegacyPreH5.
    - exact LegacyPreH10.
    - exact LegacyPreH11.
    - exact LegacyPreH8.
    - exact LegacyPreH9.
    - exact LegacyPreH12.
    - exact LegacyPreH13.
    - exact LegacyPreH14.
    - exact LegacyPreH15.
    - exact LegacyPreH16.
    - exact LegacyPreH19.
    - exact LegacyPreH35.
    - exact LegacyPreH36.
    - exact LegacyPreH39.
    - rewrite <- LegacyPreH3. exact LegacyPreH21.
    - exact LegacyPreH46.
    - exact LegacyPreH48.
    - exact LegacyPreH23.
    - exact LegacyPreH25.
    - exact LegacyPreH26.
    - exact LegacyPreH27.
    - exact LegacyPreH28.
  }
  assert (Hnext :
    StreetlightLeftProgressFacts pos_l power_l left_table_2 right_table
      n_pre start len (left + 1)).
  {
    unfold right_table, right_row.
    eapply streetlight_close_interval_and_advance__right_close_b.
    - exact LegacyPreH10.
    - exact LegacyPreH12.
    - exact LegacyPreH14.
    - exact LegacyPreH15.
    - exact LegacyPreH16.
    - exact LegacyPreH48.
    - exact Hminimum.
  }
  pose proof LegacyPreH48 as Hready_shape.
  unfold StreetlightLeftEndpointReadyFacts in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgressFacts in Hprogress_shape.
  destruct Hprogress_shape as [Hdone_shape _].
  unfold StreetlightLengthsDoneFacts in Hdone_shape.
  destruct Hdone_shape as [_ [Hright_shape _]].
  unfold StreetlightTableShape in Hright_shape.
  destruct Hright_shape as [Htable_length Hrow_length].
  assert (Hleft_index : 0 <= left < Zlength right_table_2) by lia.
  assert (Hrow_length_default :
    Zlength (Znth left right_table_2 __default__List_Z) = n_pre).
  {
    rewrite
      (Znth_indep right_table_2 left __default__List_Z (@nil Z)
        Hleft_index).
    apply Hrow_length; lia.
  }
  assert (Hpending :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending_left.
    unfold right_table, right_row.
    destruct (Z.eq_dec pending_left left) as [Heq | Hneq].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hrow_length_default; try lia).
      apply LegacyPreH45; exact Hpending_left.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Htable_length; try lia; exact Hneq).
      apply LegacyPreH45; exact Hpending_left.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace ((&("dp_r")) + (left * n_pre + right) * sizeof (INT))
      with
      ((&("dp_r")) + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by lia.
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
        ((&("dp_r")) + left * n_pre * sizeof (INT)) right n_pre best
        (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + fold right_row.
      pose proof
        (IntArray2.missing_i_merge_to_full
          (&("dp_r")) left n_pre n_pre right_table_2 right_row ltac:(lia))
        as Hmerge.
      change
        (IntArray2.ElemArray.full
          (IntArray2.row_addr (&("dp_r")) n_pre left) n_pre right_row)
        with
        (IntArray.full
          ((&("dp_r")) + left * n_pre * sizeof (INT)) n_pre right_row)
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      fold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial; street_public_goal; try solve [street_shape_goal].
    all: try assumption; try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_23_3 : solve_entail_wit_23_3.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH3 as LegacyPreH3.
  all: pose proof PreH5 as LegacyPreH5.
  all: pose proof PreH10 as LegacyPreH10.
  all: pose proof PreH12 as LegacyPreH12.
  all: pose proof PreH14 as LegacyPreH14.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH26 as LegacyPreH26.
  all: pose proof PreH27 as LegacyPreH27.
  all: pose proof PreH28 as LegacyPreH28.
  all: pose proof PreH33 as LegacyPreH35.
  all: pose proof PreH34 as LegacyPreH36.
  all: pose proof PreH35 as LegacyPreH37.
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH38 as LegacyPreH40.
  all: pose proof PreH39 as LegacyPreH41.
  all: pose proof PreH40 as LegacyPreH42.
  all: pose proof PreH41 as LegacyPreH43.
  all: pose proof PreH43 as LegacyPreH45.
  all: pose proof PreH44 as LegacyPreH46.
  all: pose proof PreH46 as LegacyPreH48.

  all: street_pack.
  all: assert (Hrange_PreH37 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH37 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH38 z ltac:(lia)); lia).
  all: assert (Hrange_PreH39 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH40 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH41 z ltac:(lia)); lia).
  all: assert (Hrange_PreH40 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH42 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH43 z ltac:(lia)); lia).
  all: street_public_goal.

  
  pose proof LegacyPreH48 as Hready_shape.
  unfold StreetlightLeftEndpointReadyFacts in Hready_shape.
  cbn in Hready_shape.
  destruct Hready_shape as [Hprogress_shape _].
  unfold StreetlightLeftProgressFacts in Hprogress_shape.
  destruct Hprogress_shape as [Hlengths_shape _].
  unfold StreetlightLengthsDoneFacts in Hlengths_shape.
  destruct Hlengths_shape as
    [Hleft_shape [Hright_shape _]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_row_length].
  destruct Hright_shape as [Hright_table_length Hright_row_length].
  assert (Hleft_index_left : 0 <= left < Zlength left_table_2) by
    (rewrite Hleft_table_length; lia).
  assert (Hleft_index_right : 0 <= left < Zlength right_table_2) by
    (rewrite Hright_table_length; lia).
  assert (Hright_index :
    0 <= right < Zlength (Znth left right_table_2 __default__List_Z)).
  {
    rewrite (Znth_indep right_table_2 left __default__List_Z (@nil Z)
               Hleft_index_right).
    rewrite Hright_row_length by lia.
    lia.
  }
  pose proof
    (Znth_indep left_table_2 left __default__List_Z (@nil Z)
       Hleft_index_left) as Hleft_default.
  pose proof
    (Znth_indep right_table_2 left __default__List_Z (@nil Z)
       Hleft_index_right) as Hright_default.
  pose proof LegacyPreH46 as Hprefix_progress.
  unfold StreetlightPrefixProgressFacts in Hprefix_progress.
  destruct Hprefix_progress as [Hprefix_length Hprefix_value].
  assert (Htotal_sum : sum power_l = total).
  {
    rewrite LegacyPreH3.
    rewrite Hprefix_value by lia.
    rewrite (sublist_self power_l n_pre) by lia.
    reflexivity.
  }
  assert (Hinterval_sum :
    Znth right prefix_l_2 0 - Znth left prefix_l_2 0 =
      sum (sublist left right power_l)).
  {
    rewrite Hprefix_value by lia.
    rewrite Hprefix_value by lia.
    rewrite (sublist_split 0 right left power_l) by lia.
    rewrite sum_app.
    lia.
  }
  assert (Hremaining :
    remain = sum power_l - sum (sublist left right power_l)) by lia.
  assert (Hminimum :
    StreetlightEndpointMinimumFacts
      pos_l power_l start left right right best).
  {
    eapply
      (streetlight_close_endpoint_right__right_close_c
         pos_l power_l left_table_2 right_table_2 n_pre start len left right
         inf remain best).
    - exact LegacyPreH1.
    - exact LegacyPreH5.
    - exact LegacyPreH35.
    - exact LegacyPreH36.
    - exact Hrange_PreH37.
    - exact Hrange_PreH39.
    - lia.
    - exact LegacyPreH10.
    - exact LegacyPreH12.
    - lia.
    - exact LegacyPreH16.
    - exact LegacyPreH14.
    - exact Hremaining.
    - rewrite <- Hright_default. exact LegacyPreH23.
    - rewrite <- Hright_default. exact LegacyPreH26.
    - rewrite <- Hleft_default. exact LegacyPreH27.
    - rewrite <- Hright_default. exact LegacyPreH28.
    - exact LegacyPreH48.
  }
  set (right_table :=
    replace_Znth left
      (replace_Znth right best
         (Znth left right_table_2 __default__List_Z))
      right_table_2).
  assert (Hnext :
    StreetlightLeftProgressFacts
      pos_l power_l left_table_2 right_table n_pre start len (left + 1)).
  {
    unfold right_table.
    rewrite Hright_default.
    eapply streetlight_close_interval_right__right_close_c;
      eauto; lia.
  }
  assert (Hpending_left :
    forall pending_left,
      0 <= pending_left <= start - len + 1 ->
      Znth start (Znth pending_left right_table __default__List_Z) 0 = inf).
  {
    intros pending_left Hpending.
    unfold right_table.
    destruct (Z.eq_dec pending_left left) as [Hsame | Hdiff].
    - subst pending_left.
      rewrite Znth_replace_Znth_Same by exact Hleft_index_right.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_row_length by lia; lia).
      apply LegacyPreH45. lia.
    - rewrite Znth_replace_Znth_Diff by
        (try rewrite Hright_table_length; try lia; exact Hdiff).
      apply LegacyPreH45. exact Hpending.
  }
  Exists right_table left_table_2 prefix_l_2.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    replace ((&("dp_r")) + (left * n_pre + right) * sizeof (INT))
      with ((&("dp_r")) + left * n_pre * sizeof (INT) + right * sizeof (INT))
      by (rewrite sizeof_int; lia).
    sep_apply_l_atomic
      (IntArray.missing_i_merge_to_full
         ((&("dp_r")) + left * n_pre * sizeof (INT)) right n_pre best
         (Znth left right_table_2 __default__List_Z)).
    + dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; lia.
    + pose proof
        (IntArray2.missing_i_merge_to_full
           (&("dp_r")) left n_pre n_pre right_table_2
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z))
           ltac:(lia)) as Hmerge.
      change
        (IntArray2.ElemArray.full
           (IntArray2.row_addr (&("dp_r")) n_pre left) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        with
        (IntArray.full ((&("dp_r")) + left * n_pre * sizeof (INT)) n_pre
           (replace_Znth right best
              (Znth left right_table_2 __default__List_Z)))
        in Hmerge.
      sep_apply_l_atomic Hmerge.
      unfold right_table.
      cancel.
  - split_pures.
    all: dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try assumption; try lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_23_4 : solve_entail_wit_23_4.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH1 as LegacyPreH1.
  all: pose proof PreH2 as LegacyPreH2.
  all: pose proof PreH11 as LegacyPreH11.
  all: pose proof PreH13 as LegacyPreH13.
  all: pose proof PreH14 as LegacyPreH14.
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH17 as LegacyPreH17.
  all: pose proof PreH26 as LegacyPreH28.
  all: pose proof PreH27 as LegacyPreH29.
  all: pose proof PreH29 as LegacyPreH31.
  all: pose proof PreH30 as LegacyPreH32.
  all: pose proof PreH31 as LegacyPreH33.
  all: pose proof PreH32 as LegacyPreH34.
  all: pose proof PreH36 as LegacyPreH38.
  all: pose proof PreH39 as LegacyPreH41.

  all: street_pack.
  all: assert (Hrange_PreH28 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH28 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH29 z ltac:(lia)); lia).
  all: assert (Hrange_PreH30 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH31 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH32 z ltac:(lia)); lia).
  all: assert (Hrange_PreH31 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH33 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH34 z ltac:(lia)); lia).
  all: street_public_goal.

  pose proof
    (streetlight_close_interval_right__right_close_d
      pos_l power_l left_table_2 right_table_2 __default__List_Z
      n_pre start len left right inf LegacyPreH2 LegacyPreH11 LegacyPreH13 LegacyPreH14 LegacyPreH15
      LegacyPreH16 LegacyPreH1 LegacyPreH17 LegacyPreH38 LegacyPreH41)
    as Hprogress.
  
  Exists right_table_2 left_table_2 prefix_l_2.
  split_pure_spatial.
  - try cancel (IntArray.undef_seg (&("pre")) (n_pre+1) 51); try cancel (IntArray.undef_seg (&("dp_l")) (n_pre*n_pre) 2500); try cancel (IntArray.undef_seg (&("dp_r")) (n_pre*n_pre) 2500).
    scratch_cancel.
  - split_pures; dump_pre_spatial; street_public_goal; try solve [street_shape_goal]; try lia; try assumption.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_24_split_goal_1 : solve_entail_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH3 as LegacyPreH3.
  all: pose proof PreH23 as LegacyPreH25.
  all: pose proof PreH24 as LegacyPreH26.
  all: pose proof PreH26 as LegacyPreH28.
  all: pose proof PreH27 as LegacyPreH29.
  all: pose proof PreH28 as LegacyPreH30.
  all: pose proof PreH29 as LegacyPreH31.
  all: pose proof PreH34 as LegacyPreH36.

  all: street_pack.
  all: assert (Hrange_PreH25 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 pos_l 0)) /\ ((Znth k_5 pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH25 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH26 z ltac:(lia)); lia).
  all: assert (Hrange_PreH27 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < n_pre)) -> ((1 <= (Znth k_7 power_l 0)) /\ ((Znth k_7 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH28 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH29 z ltac:(lia)); lia).
  all: assert (Hrange_PreH28 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 <= n_pre)) -> ((0 <= (Znth k_8 prefix_l_2 0)) /\ ((Znth k_8 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH30 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH31 z ltac:(lia)); lia).
  all: street_public_goal.

  rewrite <- LegacyPreH3.
  eapply streetlight_lengths_done_succ__length_close_b.
  - exact LegacyPreH36.
  - intros query_left Hquery_left Hquery_right Hquery_contains.
    lia.
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_24_split_goal_2 : solve_entail_wit_24_split_goal_2.
Proof. unfold solve_entail_wit_24_split_goal_2; intros. apply PreH31; lia. Qed.

Lemma proof_of_solve_entail_wit_24_split_goal_3 : solve_entail_wit_24_split_goal_3.
Proof. unfold solve_entail_wit_24_split_goal_3; intros. apply PreH30; lia. Qed.

Lemma proof_of_solve_entail_wit_24_split_goal_4 : solve_entail_wit_24_split_goal_4.
Proof. unfold solve_entail_wit_24_split_goal_4; intros. apply PreH25; lia. Qed.

Lemma proof_of_solve_entail_wit_24 : solve_entail_wit_24.
Proof.
  unfold solve_entail_wit_24; right; intros.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; first [ exact (proof_of_solve_entail_wit_24_split_goal_1 c_pre n_pre power_l pos_l right_table_2 left_table_2 left last_left first_left len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38) | exact (proof_of_solve_entail_wit_24_split_goal_2 c_pre n_pre power_l pos_l right_table_2 left_table_2 left last_left first_left len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38) | exact (proof_of_solve_entail_wit_24_split_goal_3 c_pre n_pre power_l pos_l right_table_2 left_table_2 left last_left first_left len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38) | exact (proof_of_solve_entail_wit_24_split_goal_4 c_pre n_pre power_l pos_l right_table_2 left_table_2 left last_left first_left len prefix_l_2 total start inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38) ].
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_25 : solve_entail_wit_25.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  all: pose proof PreH15 as LegacyPreH15.
  all: pose proof PreH16 as LegacyPreH16.
  all: pose proof PreH17 as LegacyPreH17.
  all: pose proof PreH18 as LegacyPreH18.
  all: pose proof PreH19 as LegacyPreH19.
  all: pose proof PreH20 as LegacyPreH20.
  all: pose proof PreH21 as LegacyPreH21.
  all: pose proof PreH22 as LegacyPreH22.
  all: pose proof PreH23 as LegacyPreH23.
  all: pose proof PreH26 as LegacyPreH26.
  all: pose proof PreH28 as LegacyPreH28.

  all: street_pack.
  all: assert (Hrange_PreH17 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k pos_l 0)) /\ ((Znth k pos_l 0) <= 8000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH17 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH18 z ltac:(lia)); lia).
  all: assert (Hrange_PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 power_l 0)) /\ ((Znth k_3 power_l 0) <= 100)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH20 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH21 z ltac:(lia)); lia).
  all: assert (Hrange_PreH20 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 <= n_pre)) -> ((0 <= (Znth k_4 prefix_l_2 0)) /\ ((Znth k_4 prefix_l_2 0) <= 5000)))) by (intros z Hz; pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH22 z ltac:(lia)); pose proof (proj1 (Forall_Znth _ 0 _) LegacyPreH23 z ltac:(lia)); lia).
  all: street_public_goal.

  assert (Hpower_sum : sum power_l <= 5000).
  { unfold StreetlightPrefixProgressFacts in LegacyPreH26.
    destruct LegacyPreH26 as [Hprefix_length Hprefix_values].
    specialize (Hprefix_values n_pre ltac:(lia)).
    rewrite (sublist_self power_l n_pre ltac:(lia)) in Hprefix_values.
    lia. }
  unfold StreetlightLengthsDoneFacts in LegacyPreH28.
  destruct LegacyPreH28 as [Hleft_shape [Hright_shape Hlengths_done]].
  unfold StreetlightTableShape in Hleft_shape, Hright_shape.
  destruct Hleft_shape as [Hleft_table_length Hleft_row_lengths].
  destruct Hright_shape as [Hright_table_length Hright_row_lengths].
  pose proof
    (Hlengths_done n_pre 0 (n_pre - 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as Hfull_interval.
  unfold StreetlightIntervalCorrectFacts in Hfull_interval.
  destruct Hfull_interval as [Hleft_entry Hright_entry].
  assert (Hleft_default :
    Znth 0 left_table __default__List_Z = Znth 0 left_table nil).
  { apply Znth_indep.
    lia. }
  assert (Hright_default :
    Znth 0 right_table __default__List_Z = Znth 0 right_table nil).
  { apply Znth_indep.
    lia. }
  rewrite <- Hleft_default in Hleft_entry.
  rewrite <- Hright_default in Hright_entry.
  pose proof
    (streetlight_final_candidates_cases__final_state
      pos_l power_l left_table right_table n_pre start
      (Znth (n_pre - 1) (Znth 0 left_table __default__List_Z) 0)
      (Znth (n_pre - 1) (Znth 0 right_table __default__List_Z) 0)
      LegacyPreH15 LegacyPreH16 ltac:(lia) ltac:(lia)
      Hrange_PreH17 LegacyPreH19 Hrange_PreH19 Hpower_sum Hleft_entry Hright_entry)
    as [Hfinal_candidates Hfinal_case].
  replace
    ((&("dp_r")) + (0 * n_pre + (n_pre - 1)) * sizeof(INT))
    with
    (((&("dp_r")) + 0 * n_pre * sizeof(INT)) +
      (n_pre - 1) * sizeof(INT)) by ring.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_full
      ((&("dp_r")) + 0 * n_pre * sizeof(INT)) (n_pre - 1) n_pre
      (Znth (n_pre - 1) (Znth 0 right_table __default__List_Z) 0)
      (Znth 0 right_table __default__List_Z) ltac:(lia)).
  rewrite replace_Znth_Znth.
  match goal with
  | |- IntArray.full _ _ _ ** ?R |-- ?Q =>
      change
        (IntArray2.ElemArray.full (IntArray2.row_addr (&("dp_r")) n_pre 0)
          n_pre (Znth 0 right_table __default__List_Z) ** R |-- Q)
  end.
  sep_apply_l_atomic
    (IntArray2.missing_i_merge_to_full
      (&("dp_r")) 0 n_pre n_pre right_table
      (Znth 0 right_table __default__List_Z) ltac:(lia)).
  rewrite replace_Znth_Znth.
  replace
    ((&("dp_l")) + (0 * n_pre + (n_pre - 1)) * sizeof(INT))
    with
    (((&("dp_l")) + 0 * n_pre * sizeof(INT)) +
      (n_pre - 1) * sizeof(INT)) by ring.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_full
      ((&("dp_l")) + 0 * n_pre * sizeof(INT)) (n_pre - 1) n_pre
      (Znth (n_pre - 1) (Znth 0 left_table __default__List_Z) 0)
      (Znth 0 left_table __default__List_Z) ltac:(lia)).
  rewrite replace_Znth_Znth.
  match goal with
  | |- IntArray.full _ _ _ ** ?R |-- ?Q =>
      change
        (IntArray2.ElemArray.full (IntArray2.row_addr (&("dp_l")) n_pre 0)
          n_pre (Znth 0 left_table __default__List_Z) ** R |-- Q)
  end.
  sep_apply_l_atomic
    (IntArray2.missing_i_merge_to_full
      (&("dp_l")) 0 n_pre n_pre left_table
      (Znth 0 left_table __default__List_Z) ltac:(lia)).
  rewrite replace_Znth_Znth.
  Ltac finish_final_case
      right_table_arg left_table_arg prefix_arg
      pos_addr_arg n_arg positions_arg
      power_addr_arg powers_arg prefix_addr_arg
      left_addr_arg right_addr_arg :=
    Exists right_table_arg;
    Exists left_table_arg;
    Exists prefix_arg;
    split_pure_spatial;
    [ cancel (IntArray.full pos_addr_arg n_arg positions_arg);
      cancel (IntArray.full power_addr_arg n_arg powers_arg);
      cancel (IntArray.full prefix_addr_arg (n_arg + 1) prefix_arg);
      cancel (IntArray2.full left_addr_arg n_arg n_arg left_table_arg);
      cancel (IntArray2.full right_addr_arg n_arg n_arg right_table_arg);
      cancel (IntArray.undef_seg prefix_addr_arg (n_arg + 1) 51);
      cancel (IntArray.undef_seg left_addr_arg (n_arg * n_arg) 2500);
      cancel (IntArray.undef_seg right_addr_arg (n_arg * n_arg) 2500)
    | split_pures;
      dump_pre_spatial; street_public_goal; try solve [street_shape_goal];
      first [assumption | lia] ].
  Ltac choose_final_case
      right_table_arg left_table_arg prefix_arg
      pos_addr_arg n_arg positions_arg
      power_addr_arg powers_arg prefix_addr_arg
      left_addr_arg right_addr_arg :=
    let rec choose := first
      [ solve [finish_final_case right_table_arg left_table_arg prefix_arg
          pos_addr_arg n_arg positions_arg power_addr_arg powers_arg prefix_addr_arg
          left_addr_arg right_addr_arg]
      | solve [Left; choose]
      | solve [Right; choose] ] in choose.
  destruct Hfinal_case as
    [Hcase | [Hcase | [Hcase | Hcase]]].
  - destruct Hcase as
      [Hright_inf [Hleft_nonnegative [Hleft_bounded Hleft_finite]]].
    choose_final_case
      right_table left_table prefix_l_2
      pos_pre n_pre pos_l power_pre power_l (&("pre")) (&("dp_l")) (&("dp_r")).
  - destruct Hcase as
      [Hleft_nonnegative
        [Hleft_bounded
          [Hright_nonnegative [Hright_bounded Hright_finite]]]].
    choose_final_case
      right_table left_table prefix_l_2
      pos_pre n_pre pos_l power_pre power_l (&("pre")) (&("dp_l")) (&("dp_r")).
  - destruct Hcase as
      [Hleft_nonnegative
        [Hleft_bounded
          [Hright_nonnegative [Hright_bounded Hleft_finite]]]].
    choose_final_case
      right_table left_table prefix_l_2
      pos_pre n_pre pos_l power_pre power_l (&("pre")) (&("dp_l")) (&("dp_r")).
  - destruct Hcase as
      [Hleft_inf [Hright_nonnegative [Hright_bounded Hright_finite]]].
    choose_final_case
      right_table left_table prefix_l_2
      pos_pre n_pre pos_l power_pre power_l (&("pre")) (&("dp_l")) (&("dp_r")).
all: try (lazymatch goal with |- _ |-- ?R => lazymatch R with context [IntArray.undef_seg _ _ _] => scratch_cancel end end).
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_26_1 : solve_entail_wit_26_1.
Proof.
  unfold solve_entail_wit_26_1; left; intros.
  street_pack.
  assert (Hresult : StreetlightTourMinimumEnergy pos_l power_l (c_pre-1) ans_l).
  { street_public_goal.
    match goal with H : StreetlightFinalCandidatesFacts _ _ _ _ _ _ _ |- _ =>
      destruct H as [_ [_ Hminimum]] end.
    lazymatch type of Hminimum with
    | StreetlightMinimumEnergyFacts ?p ?w ?s (Z.min ?a ?b) =>
      replace (c_pre-1) with s by lia;
      replace ans_l with (Z.min a b) by lia;
      exact Hminimum
    end. }
  street_resource_apply (scratch_full_tail_undef (&("pre")) (n_pre+1) 51 prefix_l ltac:(lia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_l")) n_pre 2500 left_table ltac:(lia) ltac:(nia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_r")) n_pre 2500 right_table ltac:(lia) ltac:(nia)).
  entailer!.
all: try scratch_cancel.
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_26_2 : solve_entail_wit_26_2.
Proof.
  unfold solve_entail_wit_26_2; left; intros.
  street_pack.
  assert (Hresult : StreetlightTourMinimumEnergy pos_l power_l (c_pre-1) ans_l).
  { street_public_goal.
    match goal with H : StreetlightFinalCandidatesFacts _ _ _ _ _ _ _ |- _ =>
      destruct H as [_ [_ Hminimum]] end.
    lazymatch type of Hminimum with
    | StreetlightMinimumEnergyFacts ?p ?w ?s (Z.min ?a ?b) =>
      replace (c_pre-1) with s by lia;
      replace ans_l with (Z.min a b) by lia;
      exact Hminimum
    end. }
  street_resource_apply (scratch_full_tail_undef (&("pre")) (n_pre+1) 51 prefix_l ltac:(lia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_l")) n_pre 2500 left_table ltac:(lia) ltac:(nia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_r")) n_pre 2500 right_table ltac:(lia) ltac:(nia)).
  entailer!.
all: try scratch_cancel.
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_26_3 : solve_entail_wit_26_3.
Proof.
  unfold solve_entail_wit_26_3; left; intros.
  street_pack.
  assert (Hresult : StreetlightTourMinimumEnergy pos_l power_l (c_pre-1) ans_l).
  { street_public_goal.
    match goal with H : StreetlightFinalCandidatesFacts _ _ _ _ _ _ _ |- _ =>
      destruct H as [_ [_ Hminimum]] end.
    lazymatch type of Hminimum with
    | StreetlightMinimumEnergyFacts ?p ?w ?s (Z.min ?a ?b) =>
      replace (c_pre-1) with s by lia;
      replace ans_l with (Z.min a b) by lia;
      exact Hminimum
    end. }
  street_resource_apply (scratch_full_tail_undef (&("pre")) (n_pre+1) 51 prefix_l ltac:(lia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_l")) n_pre 2500 left_table ltac:(lia) ltac:(nia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_r")) n_pre 2500 right_table ltac:(lia) ltac:(nia)).
  entailer!.
all: try scratch_cancel.
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_27_1 : solve_entail_wit_27_1.
Proof.
  unfold solve_entail_wit_27_1; left; intros.
  street_pack.
  assert (Hresult : StreetlightTourMinimumEnergy pos_l power_l (c_pre-1) ans_r).
  { street_public_goal.
    match goal with H : StreetlightFinalCandidatesFacts _ _ _ _ _ _ _ |- _ =>
      destruct H as [_ [_ Hminimum]] end.
    lazymatch type of Hminimum with
    | StreetlightMinimumEnergyFacts ?p ?w ?s (Z.min ?a ?b) =>
      replace (c_pre-1) with s by lia;
      replace ans_r with (Z.min a b) by lia;
      exact Hminimum
    end. }
  street_resource_apply (scratch_full_tail_undef (&("pre")) (n_pre+1) 51 prefix_l ltac:(lia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_l")) n_pre 2500 left_table ltac:(lia) ltac:(nia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_r")) n_pre 2500 right_table ltac:(lia) ltac:(nia)).
  entailer!.
all: try scratch_cancel.
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_27_2 : solve_entail_wit_27_2.
Proof.
  unfold solve_entail_wit_27_2; left; intros.
  street_pack.
  assert (Hresult : StreetlightTourMinimumEnergy pos_l power_l (c_pre-1) ans_r).
  { street_public_goal.
    match goal with H : StreetlightFinalCandidatesFacts _ _ _ _ _ _ _ |- _ =>
      destruct H as [_ [_ Hminimum]] end.
    lazymatch type of Hminimum with
    | StreetlightMinimumEnergyFacts ?p ?w ?s (Z.min ?a ?b) =>
      replace (c_pre-1) with s by lia;
      replace ans_r with (Z.min a b) by lia;
      exact Hminimum
    end. }
  street_resource_apply (scratch_full_tail_undef (&("pre")) (n_pre+1) 51 prefix_l ltac:(lia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_l")) n_pre 2500 left_table ltac:(lia) ltac:(nia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_r")) n_pre 2500 right_table ltac:(lia) ltac:(nia)).
  entailer!.
all: try scratch_cancel.
all: try solve [street_extrema_solve]. Qed.

Lemma proof_of_solve_entail_wit_27_3 : solve_entail_wit_27_3.
Proof.
  unfold solve_entail_wit_27_3; left; intros.
  street_pack.
  assert (Hresult : StreetlightTourMinimumEnergy pos_l power_l (c_pre-1) ans_r).
  { street_public_goal.
    match goal with H : StreetlightFinalCandidatesFacts _ _ _ _ _ _ _ |- _ =>
      destruct H as [_ [_ Hminimum]] end.
    lazymatch type of Hminimum with
    | StreetlightMinimumEnergyFacts ?p ?w ?s (Z.min ?a ?b) =>
      replace (c_pre-1) with s by lia;
      replace ans_r with (Z.min a b) by lia;
      exact Hminimum
    end. }
  street_resource_apply (scratch_full_tail_undef (&("pre")) (n_pre+1) 51 prefix_l ltac:(lia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_l")) n_pre 2500 left_table ltac:(lia) ltac:(nia)).
  street_resource_apply (scratch_rows_tail_undef (&("dp_r")) n_pre 2500 right_table ltac:(lia) ltac:(nia)).
  entailer!.
all: try scratch_cancel.
all: try solve [street_extrema_solve]. Qed.
