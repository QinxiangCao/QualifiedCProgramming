Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap ListLib.
From compcert.lib Require Import Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem CommonAssertion StoreAux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type ArrayLibCoreSig (Arch : CArchSig) (Endian : CEndianSig) (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules) (SLibSig : StoreLibSig Arch Endian CRules DePredSig).

Import CRules.
Import DePredSig.
Import SLibSig.
Local Open Scope sac.  

Module Type ELEMENT_STORE.
  Parameter Inline A : Type.
  Parameter Inline sizeA : Z.
  Parameter Inline storeA : addr -> Z -> A -> Assertion.
  Parameter Inline undefstoreA : addr -> Z -> Assertion.
  Axiom store_to_undefstore : forall x lo a, storeA x lo a |-- undefstoreA x lo.
  Axiom storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Axiom undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Axiom store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Axiom undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Axiom sizeA_valid : 0 < sizeA < Int.max_unsigned.
End ELEMENT_STORE.

Section GeneralArrayLib.
  Variable (A : Type).
  Variable (storeA : addr -> Z -> A -> Assertion).

  Lemma store_array_rec_length: forall x lo hi (l : list A),
  store_array_rec storeA x lo hi l |-- “ Z.of_nat (length l) = hi - lo ”.
  Proof.
    intros.
    revert lo; induction l; simpl store_array_rec ; intros.
    + entailer!. simpl in *; lia.
    + prop_apply IHl.
      entailer!. simpl in * ; lia.
  Qed.

  Lemma store_array_rec_Zlength: forall x lo hi (l : list A),
    store_array_rec storeA x lo hi l |-- “ Zlength l = hi - lo ”.
  Proof.
    intros.
    prop_apply store_array_rec_length.
    Intros.
    rewrite Zlength_correct.
    entailer!.
  Qed.

  Lemma store_array_rec_nil : forall x lo (l : list A),
    store_array_rec storeA x lo lo l |-- “ l = nil ” && emp.
  Proof.
    intros.
    prop_apply (store_array_rec_length x lo lo l).
    Intros.
    destruct l ; simpl in * ; try entailer!.
  Qed.

  Lemma store_array_rec_valid: forall x lo hi (l : list A),
    store_array_rec storeA x lo hi l |-- “ lo <= hi ”.
  Proof.
    intros.
    prop_apply store_array_rec_length.
    entailer!.
  Qed.

  Lemma store_array_length: forall x n (l : list A),
    store_array storeA x n l |-- “ Z.of_nat (length l) = n ”.
  Proof.
    intros.
    unfold store_array.
    prop_apply store_array_rec_length.
    entailer!. 
  Qed.

  Lemma store_array_Zlength: forall x n (l : list A),
    store_array storeA x n l |-- “ Zlength l = n ”.
  Proof.
    intros. rewrite Zlength_correct.
    apply store_array_length.
  Qed.

  Lemma store_array_valid: forall x n (l : list A),
    store_array storeA x n l |-- “ 0 <= n ”.
  Proof.
    intros.
    prop_apply store_array_length.
    entailer!.
  Qed.

  Lemma store_array_missing_i_rec_length: forall x i lo hi (l : list A),
    store_array_missing_i_rec storeA x i lo hi l |-- “ Z.of_nat (length l) = hi - lo ”.
  Proof.
    intros.
    revert i lo hi; induction l; simpl; intros.
    + entailer!.
    + Split; Intros.
      - prop_apply store_array_rec_length.
        Intros. simpl length.
        entailer!.
      - prop_apply IHl. simpl length.
        entailer!.
  Qed.

  Lemma store_array_missing_i_rec_Zlength: forall x i lo hi (l : list A),
    store_array_missing_i_rec storeA x i lo hi l |-- “ Zlength l = hi - lo ”.
  Proof.
    intros.
    prop_apply store_array_missing_i_rec_length.
    Intros.
    rewrite Zlength_correct.
    entailer!.
  Qed.

  Lemma store_array_missing_i_rec_valid: forall x i lo hi (l : list A),
    store_array_missing_i_rec storeA x i lo hi l |-- “ lo <= hi ”.
  Proof.
    intros.
    prop_apply store_array_missing_i_rec_length.
    entailer!.
  Qed.

  Lemma store_array_missing_i_valid: forall x i n (l : list A),
    store_array_missing_i_rec storeA x i 0 n l |-- “ 0 <= n ”.
  Proof.
    intros.
    prop_apply store_array_missing_i_rec_length.
    entailer!.
  Qed.

  Lemma store_array_rec_split_to_missing_i : forall x lo n m (l : list A) a,
    lo <= n < m ->
    store_array_rec storeA x lo m l |-- storeA x n (Znth (n - lo) l a) ** store_array_missing_i_rec storeA x n lo m l.
  Proof.
    intros.
    revert H.
    rename m into hi.
    revert lo; induction l; intros; simpl; intros.
    + entailer!.
    + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
      - Right.
        sep_apply IHl; [ | lia ].
        rewrite Znth_cons by lia.
        replace (n - (lo + 1)) with (n - lo - 1) by lia.
        entailer!.
      - rewrite <- derivable1_orp_intros1.
        subst n.
        replace (lo - lo) with 0 by lia.
        entailer!.
  Qed. 

  Lemma store_array_split_to_missing_i : forall x n m (l : list A) a,
    0 <= n < m ->
    store_array storeA x m l |-- storeA x n (Znth n l a) ** store_array_missing_i_rec storeA x n 0 m l.
  Proof.
    intros.
    revert H.
    unfold store_array.
    replace n with (n - 0) at 4 by lia.
    eapply store_array_rec_split_to_missing_i.
  Qed. 

  Lemma store_array_missing_i_merge_to_rec: forall x lo n m a (l: list A),
    lo <= n < m -> 
    storeA x n a ** store_array_missing_i_rec storeA x n lo m l |-- store_array_rec storeA x lo m (replace_Znth (n - lo) a l).
  Proof.
    intros.
    revert H.
    revert lo; induction l; intros; simpl.
    + entailer!.
    + Split; Intros.
      - subst n.
        replace (lo - lo) with 0 by lia.
        simpl.
        entailer!.
      - sep_apply IHl; [ | lia ].
        entailer!.
        rewrite replace_Znth_cons by lia.
        replace (n - (lo + 1)) with (n - lo - 1) by lia.
        simpl.
        entailer!.
  Qed.

  Lemma store_array_missing_i_merge_to_array: forall x n m a (l: list A),
    0 <= n < m -> 
    storeA x n a ** store_array_missing_i_rec storeA x n 0 m l |-- store_array storeA x m (replace_Znth n a l).
  Proof.
    intros.
    unfold store_array.
    replace n with (n - 0) at 3 by lia.
    eapply store_array_missing_i_merge_to_rec;auto.
  Qed.

End GeneralArrayLib.

Module ArrayLib (ES: ELEMENT_STORE).

Import ES.

Definition mixedstoreA (x : addr) (lo : Z) (a : option A) :=
  match a with 
    | Some v => storeA x lo v
    | None => undefstoreA x lo
  end.

Definition seg x lo hi (l : list A): Assertion :=
  store_array_rec storeA x lo hi l.

Definition missing_i x i lo hi (l : list A): Assertion :=
  store_array_missing_i_rec storeA x i lo hi l.

Definition full x n (l : list A): Assertion :=
  store_array storeA x n l.

Definition undef_seg x lo hi : Assertion :=
  store_undef_array_rec undefstoreA x lo hi (Z.to_nat (hi - lo)).

Definition undef_missing_i x i lo hi : Assertion :=
  store_undef_array_missing_i_rec undefstoreA x i lo hi (Z.to_nat (hi - lo)).

Definition undef_full x n : Assertion :=
  store_undef_array undefstoreA x n.

Definition seg_shape x lo hi : Assertion :=
  store_undef_array_rec (fun x lo => EX a, storeA x lo a) x lo hi (Z.to_nat (hi - lo)).

Definition missing_i_shape x i lo hi : Assertion :=
  store_undef_array_missing_i_rec (fun x lo => EX a, storeA x lo a) x i lo hi (Z.to_nat (hi - lo)).

Definition full_shape x n : Assertion :=
  store_undef_array (fun x lo => EX a, storeA x lo a) x n.

Definition mixed_seg x lo hi (l : list (option A)) : Assertion :=
  store_array_rec mixedstoreA x lo hi l.

Definition mixed_missing_i x i lo hi (l : list (option A)) : Assertion :=
  store_array_missing_i_rec mixedstoreA x i lo hi l.

Definition mixed_full x n (l : list (option A)) : Assertion :=
  store_array mixedstoreA x n l.

Lemma mixedstoreA_to_undefstoreA : forall x lo a,
  mixedstoreA x lo a |-- undefstoreA x lo.
Proof.
  intros.
  destruct a; simpl.
  + apply store_to_undefstore.
  + entailer!.
Qed.

Lemma mixedstoreA_shift : forall x n lo a,
  mixedstoreA (x + n * sizeA) lo a --||-- mixedstoreA x (lo + n) a.
Proof.
  intros.
  destruct a; simpl.
  + apply storeA_shift.
  + apply undefstoreA_shift.
Qed.

(** length Lemmas *)

Lemma seg_length: forall x lo hi (l : list A),
  seg x lo hi l |-- “ Z.of_nat (length l) = hi - lo ”.
Proof.
  intros.
  revert lo; induction l; unfold seg ; simpl ; intros.
  + entailer!.
  + prop_apply IHl.
    entailer!. 
Qed.

Lemma seg_Zlength: forall x lo hi (l : list A),
  seg x lo hi l |-- “ Zlength l = hi - lo ”.
Proof.
  intros.
  prop_apply seg_length.
  Intros.
  rewrite Zlength_correct.
  entailer!.
Qed.

Lemma seg_nil : forall x lo (l : list A),
  seg x lo lo l |-- “ l = nil ” && emp.
Proof.
  intros.
  prop_apply seg_length.
  Intros.
  destruct l ; simpl in * ; try entailer!.
Qed.

Lemma seg_single : forall x lo a, 
  storeA x lo a |-- seg x lo (lo + 1) (a :: nil).
Proof.
  intros.
  unfold seg.
  simpl.
  entailer!.
Qed.

Lemma mixed_seg_single : forall x lo a,
  mixedstoreA x lo a |-- mixed_seg x lo (lo + 1) (a :: nil).
Proof.
  intros.
  unfold mixed_seg.
  simpl.
  entailer!.
Qed.

Lemma undef_seg_single: forall x lo,
  undefstoreA x lo |-- undef_seg x lo (lo + 1).
Proof.
  intros.
  unfold undef_seg.
  replace (Z.to_nat (lo + 1 - lo)) with 1%nat by lia.
  simpl.
  entailer!.
Qed.

Lemma seg_shape_single : forall x lo a,
  storeA x lo a |-- seg_shape x lo (lo + 1).
Proof.
  intros.
  unfold seg_shape.
  replace (Z.to_nat (lo + 1 - lo)) with 1%nat by lia.
  simpl.
  Exists a.
  entailer!.
Qed.

Lemma full_length: forall x n (l : list A),
  full x n l |-- “ Z.of_nat (length l) = n ”.
Proof.
  intros.
  unfold full.
  prop_apply seg_length.
  entailer!. 
Qed.

Lemma full_Zlength: forall x n (l : list A),
  full x n l |-- “ Zlength l = n ”.
Proof.
  intros. rewrite Zlength_correct.
  apply full_length.
Qed.

Lemma mixed_seg_length: forall x lo hi (l : list (option A)),
  mixed_seg x lo hi l |-- “ Z.of_nat (length l) = hi - lo ”.
Proof.
  intros.
  unfold mixed_seg.
  apply store_array_rec_length.
Qed.

Lemma mixed_seg_Zlength: forall x lo hi (l : list (option A)),
  mixed_seg x lo hi l |-- “ Zlength l = hi - lo ”.
Proof.
  intros.
  unfold mixed_seg.
  apply store_array_rec_Zlength.
Qed.

Lemma mixed_seg_nil : forall x lo (l : list (option A)),
  mixed_seg x lo lo l |-- “ l = nil ” && emp.
Proof.
  intros.
  unfold mixed_seg.
  apply store_array_rec_nil.
Qed.

Lemma mixed_full_length: forall x n (l : list (option A)),
  mixed_full x n l |-- “ Z.of_nat (length l) = n ”.
Proof.
  intros.
  unfold mixed_full.
  apply store_array_length.
Qed.

Lemma mixed_full_Zlength: forall x n (l : list (option A)),
  mixed_full x n l |-- “ Zlength l = n ”.
Proof.
  intros. rewrite Zlength_correct.
  apply mixed_full_length.
Qed.

Lemma mixed_missing_i_length: forall x i lo hi (l : list (option A)),
  mixed_missing_i x i lo hi l |-- “ Z.of_nat (length l) = hi - lo ”.
Proof.
  intros.
  unfold mixed_missing_i.
  apply store_array_missing_i_rec_length.
Qed.

Lemma mixed_missing_i_Zlength: forall x i lo hi (l : list (option A)),
  mixed_missing_i x i lo hi l |-- “ Zlength l = hi - lo ”.
Proof.
  intros.
  unfold mixed_missing_i.
  apply store_array_missing_i_rec_Zlength.
Qed.

Lemma missing_i_length: forall x i lo hi (l : list A),
  missing_i x i lo hi l |-- “ Z.of_nat (length l) = hi - lo ”.
Proof.
  intros.
  unfold missing_i.
  apply store_array_missing_i_rec_length.
Qed.

Lemma missing_i_Zlength: forall x i lo hi (l : list A),
  missing_i x i lo hi l |-- “ Zlength l = hi - lo ”.
Proof.
  intros.
  unfold missing_i.
  apply store_array_missing_i_rec_Zlength.
Qed.

(* Basic Properties *)

Lemma seg_valid : forall x lo hi l,
  seg x lo hi l |-- “ lo <= hi ”.
Proof.
  intros.
  unfold seg.
  prop_apply store_array_rec_length.
  entailer!.
Qed.

Lemma mixed_seg_valid : forall x lo hi l,
  mixed_seg x lo hi l |-- “ lo <= hi ”.
Proof.
  intros.
  prop_apply mixed_seg_length.
  entailer!.
Qed.

Lemma undef_seg_valid : forall x lo hi,
  undef_seg x lo hi |-- “ lo <= hi ”.
Proof.
  intros.
  unfold undef_seg.
  destruct (Z_le_gt_dec lo hi) as [H | H].
  - entailer!.
  - replace (Z.to_nat (hi - lo)) with 0%nat by lia.
    simpl.
    entailer!.
Qed.

Lemma seg_shape_valid : forall x lo hi,
  seg_shape x lo hi |-- “ lo <= hi ”.
Proof.
  intros.
  unfold seg_shape.
  destruct (Z_le_gt_dec lo hi) as [H | H].
  - entailer!.
  - replace (Z.to_nat (hi - lo)) with 0%nat by lia.
    simpl.
    entailer!.
Qed.

Lemma seg_empty : forall x lo hi,
  seg x lo hi nil --||-- “ hi = lo ” && emp.
Proof.
  intros.
  unfold seg.
  simpl.
  split ; entailer!.
Qed.

Lemma mixed_seg_empty : forall x lo hi,
  mixed_seg x lo hi nil --||-- “ hi = lo ” && emp.
Proof.
  intros.
  unfold mixed_seg.
  simpl.
  split; entailer!.
Qed.

Lemma undef_seg_empty : forall x lo,
  undef_seg x lo lo --||-- emp.
Proof.
  intros.
  unfold undef_seg.
  replace (Z.to_nat (lo - lo)) with O by lia.
  simpl.
  split ; entailer!.
Qed.

Lemma seg_shape_empty : forall x lo,
  seg_shape x lo lo --||-- emp.
Proof.
  intros.
  unfold seg_shape.
  replace (Z.to_nat (lo - lo)) with O by lia.
  simpl.
  split ; entailer!.
Qed.

Lemma seg_unfold : forall x lo hi (l : list A) a,
  seg x lo hi (a :: l) --||-- storeA x lo a ** seg x (lo + 1) hi l.
Proof.
  intros.
  unfold seg.
  simpl.
  entailer!.
Qed.

Lemma mixed_seg_unfold : forall x lo hi (l : list (option A)) a,
  mixed_seg x lo hi (a :: l) --||-- mixedstoreA x lo a ** mixed_seg x (lo + 1) hi l.
Proof.
  intros.
  unfold mixed_seg.
  simpl.
  entailer!.
Qed.

Lemma undef_seg_unfold : forall x lo hi,
  lo < hi ->
  undef_seg x lo hi --||-- undefstoreA x lo ** undef_seg x (lo + 1) hi.
Proof.
  intros.
  unfold undef_seg.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  entailer!.
Qed.

Lemma seg_shape_unfold : forall x lo hi,
  lo < hi ->
  seg_shape x lo hi --||-- EX a, storeA x lo a ** seg_shape x (lo + 1) hi.
Proof.
  intros.
  unfold seg_shape.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  split ; 
  entailer!.
Qed.

Lemma missing_i_empty : forall x i lo hi,
  missing_i x i lo hi nil --||-- “ False ” .
Proof.
  intros.
  unfold missing_i.
  simpl.
  entailer!.
Qed.

Lemma mixed_missing_i_empty : forall x i lo hi,
  mixed_missing_i x i lo hi nil --||-- “ False ”.
Proof.
  intros.
  unfold mixed_missing_i.
  simpl.
  entailer!.
Qed.

Lemma undef_missing_i_empty : forall x i lo,
  undef_missing_i x i lo lo |-- “ False ” .
Proof.
  intros.
  unfold undef_missing_i.
  replace (Z.to_nat (lo - lo)) with O by lia.
  simpl.
  entailer!.
Qed.

Lemma missing_i_shape_empty : forall x i lo,
  missing_i_shape x i lo lo --||-- “ False ” .
Proof.
  intros.
  unfold missing_i_shape.
  replace (Z.to_nat (lo - lo)) with O by lia.
  simpl.
  entailer!.
Qed.

Lemma missing_i_unfold : forall x i lo hi (l : list A) a,
  missing_i x i lo hi (a :: l) --||--
   “ i = lo ” && seg x (lo + 1) hi l || 
   “ i > lo ” && storeA x lo a ** missing_i x i (lo + 1) hi l.
Proof.
  intros.
  unfold missing_i.
  simpl.
  entailer!.
Qed.

Lemma mixed_missing_i_unfold : forall x i lo hi (l : list (option A)) a,
  mixed_missing_i x i lo hi (a :: l) --||--
   “ i = lo ” && mixed_seg x (lo + 1) hi l ||
   “ i > lo ” && mixedstoreA x lo a ** mixed_missing_i x i (lo + 1) hi l.
Proof.
  intros.
  unfold mixed_missing_i.
  simpl.
  entailer!.
Qed.

Lemma undef_missing_i_unfold : forall x i lo hi,
  lo < hi ->
  undef_missing_i x i lo hi --||--
   “ i = lo ” && undef_seg x (lo + 1) hi || 
   “ i > lo ” && undefstoreA x lo ** undef_missing_i x i (lo + 1) hi.
Proof.
  intros.
  unfold undef_missing_i.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  entailer!.
Qed.

Lemma missing_i_shape_unfold : forall x i lo hi,
  lo < hi ->
  missing_i_shape x i lo hi --||--
   “ i = lo ” && seg_shape x (lo + 1) hi || 
   “ i > lo ” && (EX a, storeA x lo a) ** missing_i_shape x i (lo + 1) hi.
Proof.
  intros.
  unfold missing_i_shape.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  split ; entailer!.
Qed.

Lemma full_empty : forall x n,
  full x n nil --||-- “ n = 0 ” && emp.
Proof.
  intros.
  unfold full, store_array.
  simpl.
  split; entailer!.
Qed.

Lemma mixed_full_empty : forall x n,
  mixed_full x n nil --||-- “ n = 0 ” && emp.
Proof.
  intros.
  unfold mixed_full, store_array.
  simpl.
  split; entailer!.
Qed.

Lemma undef_full_empty : forall x,
  undef_full x 0 --||-- emp.
Proof.
  intros.
  unfold undef_full, store_undef_array.
  simpl.
  split; entailer!.
Qed.

Lemma full_shape_empty : forall x,
  full_shape x 0 --||-- emp.
Proof.
  intros.
  unfold full_shape, store_undef_array.
  simpl.
  split; entailer!.
Qed.

Lemma full_unfold : forall x n (l : list A) a,
  full x n (a :: l) --||-- storeA x 0 a ** seg x 1 n l.
Proof.
  intros.
  unfold full, store_array.
  simpl.
  entailer!.
Qed.

Lemma mixed_full_unfold : forall x n (l : list (option A)) a,
  mixed_full x n (a :: l) --||-- mixedstoreA x 0 a ** mixed_seg x 1 n l.
Proof.
  intros.
  unfold mixed_full, mixed_seg, store_array.
  simpl.
  entailer!.
Qed.

Lemma undef_full_unfold : forall x n (l : list A),
  n >= 0 -> 
  undef_full x (n + 1) --||-- undefstoreA x 0 ** undef_seg x 1 (n + 1).
Proof.
  intros.
  unfold undef_full, store_undef_array, undef_seg.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  simpl.
  replace (Z.to_nat (n + 1 - 1)) with (Z.to_nat n) by lia.
  entailer!.
Qed.

Lemma full_shape_unfold : forall x n (l : list A),
  n >= 0 -> 
  full_shape x (n + 1) --||-- EX a, storeA x 0 a ** seg_shape x 1 (n + 1).
Proof.
  intros.
  unfold full_shape, seg_shape, store_undef_array.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  simpl.
  replace (Z.to_nat (n + 1 - 1)) with (Z.to_nat n) by lia.
  split ; entailer!.
Qed.

Ltac ArraySimplify :=
  repeat progress (
    match goal with
      | |- context [seg ?x ?lo ?hi nil] => rewrite (seg_empty x lo hi)
      | |- context [mixed_seg ?x ?lo ?hi nil] => rewrite (mixed_seg_empty x lo hi)
      | |- context [undef_seg ?x ?lo ?lo] => rewrite (undef_seg_empty x lo)
      | |- context [seg_shape ?x ?lo ?lo] => rewrite (seg_shape_empty x lo)
      | |- context [seg ?x ?lo ?hi (?a :: ?l)] => rewrite (seg_unfold x lo hi l a)
      | |- context [mixed_seg ?x ?lo ?hi (?a :: ?l)] => rewrite (mixed_seg_unfold x lo hi l a)
      | |- context [missing_i ?x ?i ?lo ?hi nil] => rewrite (missing_i_empty x i lo hi)
      | |- context [mixed_missing_i ?x ?i ?lo ?hi nil] => rewrite (mixed_missing_i_empty x i lo hi)
      | |- context [undef_missing_i ?x ?i ?lo ?lo] => rewrite (undef_missing_i_empty x i lo)
      | |- context [missing_i_shape ?x ?i ?lo ?lo] => rewrite (missing_i_shape_empty x i lo)
      | |- context [missing_i ?x ?i ?lo ?hi (?a :: ?l)] => rewrite (missing_i_unfold x i lo hi l a)
      | |- context [mixed_missing_i ?x ?i ?lo ?hi (?a :: ?l)] => rewrite (mixed_missing_i_unfold x i lo hi l a)
      | |- context [full ?x ?n nil] => rewrite (full_empty x n)
      | |- context [mixed_full ?x ?n nil] => rewrite (mixed_full_empty x n)
      | |- context [undef_full ?x 0] => rewrite (undef_full_empty x)
      | |- context [full_shape ?x 0] => rewrite (full_shape_empty x)
      | |- context [full ?x ?n (?a :: ?l)] => rewrite (full_unfold x n l a)
      | |- context [mixed_full ?x ?n (?a :: ?l)] => rewrite (mixed_full_unfold x n l a)
      | |- context [undef_full ?x (?n + 1)] => rewrite (undef_full_unfold x n)
      | |- context [full_shape ?x (?n + 1)] => rewrite (full_shape_unfold x n)
    end).

(* Transition Lemmas *)

(* Transition lemma families, grouped by source prefix.
   mixedstoreA_to_*:
     mixedstoreA_to_undefstoreA

   seg_to_*:
     seg_to_mixed_seg
     seg_to_full
     seg_to_undef_seg
     seg_to_seg_shape

   mixed_seg_to_*:
     mixed_seg_to_seg
     mixed_seg_to_mixed_full
     mixed_seg_to_undef_seg
     mixed_seg_to_undef_full

   full_to_*:
     full_to_seg
     full_to_mixed_seg
     full_to_mixed_full
     full_to_undef_full
     full_to_full_shape

   mixed_full_to_*:
     mixed_full_to_mixed_seg
     mixed_full_to_full
     mixed_full_to_undef_seg
     mixed_full_to_undef_full

   undef_seg_to_*:
     undef_seg_to_mixed_seg
     undef_seg_to_undef_full

   undef_full_to_*:
     undef_full_to_undef_seg
     undef_full_to_mixed_seg
     undef_full_to_mixed_full

   seg_shape_to_*:
     seg_shape_to_full_shape
     seg_shape_to_undef_seg

   full_shape_to_*:
     full_shape_to_seg_shape
     full_shape_to_undef_full

   missing_i_to_*:
     missing_i_to_seg_head
     missing_i_to_seg_tail
     missing_i_to_mixed_missing_i
     missing_i_to_undef_missing_i
     missing_i_to_missing_i_shape

   mixed_missing_i_to_*:
     mixed_missing_i_to_mixed_seg_head
     mixed_missing_i_to_mixed_seg_tail
     mixed_missing_i_to_missing_i
     mixed_missing_i_to_undef_missing_i

   undef_missing_i_to_*:
     undef_missing_i_to_undef_seg_head
     undef_missing_i_to_undef_seg_tail
     undef_missing_i_to_mixed_missing_i

   missing_i_shape_to_*:
     missing_i_shape_to_seg_shape_head
     missing_i_shape_to_seg_shape_tail
*)

Lemma full_to_seg : forall x n (l : list A),
  full x n l |-- seg x 0 n l.
Proof.
  intros.
  unfold full, seg.
  unfold store_array.
  entailer!.
Qed.

Lemma undef_full_to_undef_seg : forall x n,
  undef_full x n |-- undef_seg x 0 n.
Proof.
  intros.
  unfold undef_full, undef_seg.
  unfold store_undef_array.
  replace (Z.to_nat (n - 0)) with (Z.to_nat n) by lia.
  entailer!.
Qed.

Lemma full_shape_to_seg_shape : forall x n,
  full_shape x n |-- seg_shape x 0 n.
Proof.
  intros.
  unfold full_shape, seg_shape.
  unfold store_undef_array.
  replace (Z.to_nat (n - 0)) with (Z.to_nat n) by lia.
  entailer!.
Qed.

Lemma mixed_full_to_mixed_seg : forall x n (l : list (option A)),
  mixed_full x n l |-- mixed_seg x 0 n l.
Proof.
  intros.
  unfold mixed_full, mixed_seg, store_array.
  entailer!.
Qed.

Lemma seg_to_mixed_seg : forall x lo hi (l : list A),
  seg x lo hi l |-- mixed_seg x lo hi (map (@Some A) l).
Proof.
  intros.
  revert lo hi; induction l; intros; simpl.
  - rewrite seg_empty.
    rewrite mixed_seg_empty.
    entailer!.
  - rewrite seg_unfold.
    rewrite mixed_seg_unfold.
    simpl mixedstoreA.
    sep_apply IHl.
    entailer!.
Qed.

Lemma full_to_mixed_seg : forall x n (l : list A),
  full x n l |-- mixed_seg x 0 n (map (@Some A) l).
Proof.
  intros.
  sep_apply full_to_seg.
  sep_apply seg_to_mixed_seg.
  entailer!.
Qed.

Lemma mixed_seg_to_seg : forall x lo hi (l : list A),
  mixed_seg x lo hi (map (@Some A) l) |-- seg x lo hi l.
Proof.
  intros.
  revert lo hi; induction l; intros; simpl.
  - rewrite mixed_seg_empty.
    rewrite seg_empty.
    entailer!.
  - rewrite mixed_seg_unfold.
    rewrite seg_unfold.
    simpl mixedstoreA.
    sep_apply IHl.
    entailer!.
Qed.

Lemma missing_i_to_mixed_missing_i : forall x i lo hi (l : list A),
  missing_i x i lo hi l |-- mixed_missing_i x i lo hi (map (@Some A) l).
Proof.
  intros.
  revert i lo hi; induction l; intros; simpl.
  - rewrite missing_i_empty.
    rewrite mixed_missing_i_empty.
    entailer!.
  - rewrite missing_i_unfold.
    rewrite mixed_missing_i_unfold.
    simpl mixedstoreA.
    Split; Intros; [Left | Right].
    + sep_apply seg_to_mixed_seg.
      entailer!.
    + sep_apply IHl.
      entailer!.
Qed.

Lemma mixed_missing_i_to_missing_i : forall x i lo hi (l : list A),
  mixed_missing_i x i lo hi (map (@Some A) l) |-- missing_i x i lo hi l.
Proof.
  intros.
  revert i lo hi; induction l; intros; simpl.
  - rewrite mixed_missing_i_empty.
    rewrite missing_i_empty.
    entailer!.
  - rewrite mixed_missing_i_unfold.
    rewrite missing_i_unfold.
    simpl mixedstoreA.
    Split; Intros; [Left | Right].
    + sep_apply mixed_seg_to_seg.
      entailer!.
    + sep_apply IHl.
      entailer!.
Qed.

Lemma undef_seg_to_mixed_seg : forall x lo hi,
  undef_seg x lo hi |-- mixed_seg x lo hi (repeat None (Z.to_nat (hi - lo))).
Proof.
  intros.
  prop_apply undef_seg_valid. Intros.
  rename H into Hle.
  set (len := Z.to_nat (hi - lo)).
  assert (Hlen: len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert lo hi Hle Hlen.
  induction len; intros.
  - assert (hi = lo) by lia.
    subst hi.
    rewrite undef_seg_empty.
    rewrite mixed_seg_empty.
    entailer!.
  - assert (lo < hi) by lia.
    rewrite (undef_seg_unfold x lo hi) by lia.
    replace (Z.to_nat (hi - lo)) with (S len) by lia.
    simpl.
    rewrite (mixed_seg_unfold x lo hi (repeat None len) None).
    simpl mixedstoreA.
    sep_apply (IHlen (lo + 1) hi); try lia.
    entailer!.
Qed.

Lemma undef_full_to_mixed_seg : forall x n,
  undef_full x n |-- mixed_seg x 0 n (repeat None (Z.to_nat n)).
Proof.
  intros.
  sep_apply undef_full_to_undef_seg.
  sep_apply undef_seg_to_mixed_seg.
  replace (0 - 0) with 0 by lia.
  replace (x + 0 * sizeA) with x by lia.
  replace (Z.to_nat (n - 0)) with (Z.to_nat n) by lia.
  entailer!.
Qed.

Lemma seg_shift : forall x lo mid hi (l : list A),
  seg x (lo + mid) (lo + hi) l --||-- seg (x + lo * sizeA) mid hi l.
Proof.
  intros.
  revert lo mid hi ; induction l; intros ; ArraySimplify.
  - split ; entailer!.
  - rewrite (storeA_shift x lo mid a).
    replace (mid + lo) with (lo + mid) by lia.
    replace (lo + mid + 1) with (lo + (mid + 1)) by lia.
    rewrite (IHl lo (mid + 1) hi).
    entailer!.
Qed.

Lemma mixed_seg_shift : forall x lo mid hi (l : list (option A)),
  mixed_seg x (lo + mid) (lo + hi) l --||-- mixed_seg (x + lo * sizeA) mid hi l.
Proof.
  intros.
  revert lo mid hi; induction l; intros; ArraySimplify.
  - split; entailer!.
  - rewrite (mixedstoreA_shift x lo mid a).
    replace (mid + lo) with (lo + mid) by lia.
    replace (lo + mid + 1) with (lo + (mid + 1)) by lia.
    rewrite (IHl lo (mid + 1) hi).
    entailer!.
Qed.

Lemma seg_0_shift : forall x lo hi (l : list A),
  seg x lo hi l --||-- seg (x + lo * sizeA) 0 (hi - lo) l.
Proof.
  intros.
  replace lo with (lo + 0) at 1 by lia.
  replace hi with (lo + (hi - lo)) at 1 by lia.
  rewrite seg_shift.
  entailer!.
Qed.

Lemma mixed_seg_0_shift : forall x lo hi (l : list (option A)),
  mixed_seg x lo hi l --||-- mixed_seg (x + lo * sizeA) 0 (hi - lo) l.
Proof.
  intros.
  replace lo with (lo + 0) at 1 by lia.
  replace hi with (lo + (hi - lo)) at 1 by lia.
  rewrite mixed_seg_shift.
  entailer!.
Qed.

Lemma undef_seg_shift : forall x lo mid hi,
  undef_seg x (lo + mid) (lo + hi) --||-- undef_seg (x + lo * sizeA) mid hi.
Proof.
  intros.
  unfold undef_seg.
  replace (lo + hi - (lo + mid)) with (hi - mid) by lia.
  set (len := Z.to_nat (hi - mid)).
  assert (len = Z.to_nat (hi - mid)) by lia.
  clearbody len. 
  revert H. revert lo mid hi ; induction len; intros ; simpl.
  - split ; entailer!.
  - rewrite (undefstoreA_shift x lo mid).
    replace (mid + lo) with (lo + mid) by lia.
    replace (lo + mid + 1) with (lo + (mid + 1)) by lia.
    rewrite (IHlen lo (mid + 1) hi).
    entailer!.
    lia.
Qed.

Lemma undef_seg_0_shift : forall x lo hi,
  undef_seg x lo hi --||-- undef_seg (x + lo * sizeA) 0 (hi - lo).
Proof.
  intros.
  replace lo with (lo + 0) at 1 by lia.
  replace hi with (lo + (hi - lo)) at 1 by lia.
  rewrite undef_seg_shift.
  entailer!.
Qed.

Lemma seg_shape_shift : forall x lo mid hi,
  seg_shape x (lo + mid) (lo + hi) --||-- seg_shape (x + lo * sizeA) mid hi.
Proof.
  intros.
  unfold seg_shape.
  replace (lo + hi - (lo + mid)) with (hi - mid) by lia.
  set (len := Z.to_nat (hi - mid)).
  assert (len = Z.to_nat (hi - mid)) by lia.
  clearbody len. 
  revert H. revert lo mid hi ; induction len; intros ; simpl.
  - split ; entailer!.
  - split ; Intros a ; Exists a ;
    rewrite (storeA_shift x lo mid);
    replace (mid + lo) with (lo + mid) by lia;
    replace (lo + mid + 1) with (lo + (mid + 1)) by lia;
    rewrite (IHlen lo (mid + 1) hi);
    entailer!.
Qed.

Lemma seg_shape_0_shift : forall x lo hi,
  seg_shape x lo hi --||-- seg_shape (x + lo * sizeA) 0 (hi - lo).
Proof.
  intros.
  replace lo with (lo + 0) at 1 by lia.
  replace hi with (lo + (hi - lo)) at 1 by lia.
  rewrite seg_shape_shift.
  entailer!.
Qed.

Lemma seg_to_full : forall x lo hi (l : list A),
  seg x lo hi l |-- full (x + lo * sizeA) (hi - 
  lo) l.
Proof.
  intros.
  rewrite seg_0_shift.
  unfold seg, full, store_array. 
  entailer!.
Qed.

Lemma mixed_seg_to_mixed_full : forall x lo hi (l : list (option A)),
  mixed_seg x lo hi l |-- mixed_full (x + lo * sizeA) (hi - lo) l.
Proof.
  intros.
  rewrite mixed_seg_0_shift.
  unfold mixed_seg, mixed_full, store_array.
  entailer!.
Qed.

Lemma mixed_full_to_full : forall x n (l : list A),
  mixed_full x n (map (@Some A) l) |-- full x n l.
Proof.
  intros.
  sep_apply mixed_full_to_mixed_seg.
  sep_apply mixed_seg_to_seg.
  replace (0 - 0) with 0 by lia.
  replace (x + 0 * sizeA) with x by lia.
  entailer!.
Qed.

Lemma full_to_mixed_full : forall x n (l : list A),
  full x n l |-- mixed_full x n (map (@Some A) l).
Proof.
  intros.
  sep_apply full_to_mixed_seg.
  sep_apply (mixed_seg_to_mixed_full x 0 n (map (@Some A) l)).
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma undef_full_to_mixed_full : forall x n,
  undef_full x n |-- mixed_full x n (repeat None (Z.to_nat n)).
Proof.
  intros.
  sep_apply undef_full_to_mixed_seg.
  sep_apply (mixed_seg_to_mixed_full x 0 n (repeat None (Z.to_nat n))).
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma seg_to_undef_seg : forall x lo hi (l : list A),
  seg x lo hi l |-- undef_seg x lo hi.
Proof.
  intros.
  prop_apply seg_length. Intros.
  revert H ; revert lo; induction l ; intros ; simpl ; ArraySimplify.
  + Intros. subst. ArraySimplify. entailer!.
  + simpl length in H.
    sep_apply IHl ; try lia.
    sep_apply store_to_undefstore.
    rewrite (undef_seg_unfold x lo hi) ; try lia.
    entailer!.
Qed.

Lemma mixed_seg_to_undef_seg : forall x lo hi (l : list (option A)),
  mixed_seg x lo hi l |-- undef_seg x lo hi.
Proof.
  intros.
  prop_apply mixed_seg_length. Intros.
  revert H; revert lo; induction l; intros; simpl; ArraySimplify.
  + Intros. subst. ArraySimplify. entailer!.
  + simpl length in H.
    sep_apply IHl; try lia.
    sep_apply mixedstoreA_to_undefstoreA.
    rewrite (undef_seg_unfold x lo hi); try lia.
    entailer!.
Qed.

Lemma seg_to_seg_shape : forall x lo hi (l : list A),
  seg x lo hi l |-- seg_shape x lo hi.
Proof.
  intros.
  prop_apply seg_length. Intros.
  revert H ; revert lo; induction l ; intros ; simpl ; ArraySimplify.
  + Intros. subst. ArraySimplify. entailer!.
  + simpl length in H.
    sep_apply IHl ; try lia.
    rewrite (seg_shape_unfold x lo hi) ; try lia.
    Exists a. entailer!.
Qed.

Lemma undef_seg_to_undef_full : forall x lo hi,
  undef_seg x lo hi |-- undef_full (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  rewrite undef_seg_0_shift.
  unfold undef_seg, undef_full, store_undef_array.
  replace (Z.to_nat (hi - lo - 0)) with (Z.to_nat (hi - lo)) by lia.
  entailer!.
Qed.

Lemma seg_shape_to_full_shape : forall x lo hi,
  seg_shape x lo hi |-- full_shape (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  rewrite seg_shape_0_shift.
  unfold seg_shape, full_shape, store_undef_array.
  replace (Z.to_nat (hi - lo - 0)) with (Z.to_nat (hi - lo)) by lia.
  entailer!.
Qed.

Lemma missing_i_to_seg_head : forall x lo hi a (l : list A),
  missing_i x lo lo hi (a :: l) |-- seg x (lo + 1) hi l.
Proof.
  intros.
  rewrite missing_i_unfold.
  Split ; try entailer!.
Qed.

Lemma mixed_missing_i_to_mixed_seg_head : forall x lo hi a (l : list (option A)),
  mixed_missing_i x lo lo hi (a :: l) |-- mixed_seg x (lo + 1) hi l.
Proof.
  intros.
  rewrite mixed_missing_i_unfold.
  Split; try entailer!.
Qed.

Lemma undef_missing_i_to_undef_seg_head : forall x lo hi,
  lo < hi ->
  undef_missing_i x lo lo hi |-- undef_seg x (lo + 1) hi.
Proof.
  intros.
  rewrite undef_missing_i_unfold ; try lia.
  Split ; try entailer!.
Qed.

Lemma missing_i_shape_to_seg_shape_head : forall x lo hi,
  lo < hi ->
  missing_i_shape x lo lo hi |-- seg_shape x (lo + 1) hi.
Proof.
  intros.
  rewrite missing_i_shape_unfold ; try lia.
  Split ; try entailer!.
  Intros x0. entailer!.
Qed.

Lemma missing_i_to_seg_tail : forall x lo hi a (l : list A),
  missing_i x hi lo hi (l ++ a :: nil) |-- seg x lo (hi - 1) l.
Proof.
  intros.
  revert lo hi.
  induction l ; simpl ; intros ; ArraySimplify ; Split ; try entailer!.
  prop_apply seg_length. 
  Intros.
  rewrite length_app in H0. simpl in H0. 
  lia.
Qed.

Lemma mixed_missing_i_to_mixed_seg_tail : forall x lo hi a (l : list (option A)),
  mixed_missing_i x hi lo hi (l ++ a :: nil) |-- mixed_seg x lo (hi - 1) l.
Proof.
  intros.
  revert lo hi.
  induction l; simpl; intros; ArraySimplify; Split; try entailer!.
  prop_apply mixed_seg_length.
  Intros.
  rewrite length_app in H0. simpl in H0.
  lia.
Qed.

Lemma undef_missing_i_to_undef_seg_tail : forall x lo hi,
  lo < hi -> 
  undef_missing_i x hi lo hi |-- undef_seg x lo (hi - 1).
Proof.
  intros.
  unfold undef_missing_i, undef_seg.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  replace (hi - 1 - lo) with (hi - (lo + 1)) by lia.
  simpl. 
  Split ; try entailer!.
  set (len := Z.to_nat (hi - (lo + 1))).
  assert (len = Z.to_nat (hi - (lo + 1))) by lia.
  clearbody len.
  generalize dependent lo. revert hi.
  induction len ; simpl ; intros ; ArraySimplify.
  - entailer!. 
  - Split ; try entailer!.
    sep_apply IHlen ; try lia.
    entailer!. 
Qed.

Lemma missing_i_shape_to_seg_shape_tail : forall x lo hi,
  lo < hi -> 
  missing_i_shape x hi lo hi |-- seg_shape x lo (hi - 1).
Proof.
  intros.
  unfold missing_i_shape, seg_shape.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  replace (hi - 1 - lo) with (hi - (lo + 1)) by lia.
  simpl.  
  Split ; try entailer!. Intros x0.
  set (len := Z.to_nat (hi - (lo + 1))).
  assert (len = Z.to_nat (hi - (lo + 1))) by lia.
  clearbody len.
  generalize dependent lo. revert hi x0.
  induction len ; simpl ; intros ; ArraySimplify.
  - entailer!.
  - Split ; try entailer!. Intros x1.
    Exists x0.
    sep_apply IHlen ; try lia.
    entailer!.
Qed.

(* Missing-i transitions: pure, mixed, then shape/undef forgetful variants. *)

Lemma missing_i_to_undef_missing_i : forall x i lo hi (l : list A),
  missing_i x i lo hi l |-- undef_missing_i x i lo hi.
Proof.
  intros.
  prop_apply missing_i_length. Intros.
  revert H.
  revert i lo hi.
  induction l ; simpl ; intros ; ArraySimplify. 
  + entailer!.
  + Split ; Intros ; rewrite undef_missing_i_unfold ; try lia ; [Left | Right].
    * sep_apply seg_to_undef_seg.
      entailer!. 
    * sep_apply IHl.
      sep_apply store_to_undefstore.
      entailer!.
      lia.
Qed.

Lemma mixed_missing_i_to_undef_missing_i : forall x i lo hi (l : list (option A)),
  mixed_missing_i x i lo hi l |-- undef_missing_i x i lo hi.
Proof.
  intros.
  prop_apply mixed_missing_i_length. Intros.
  revert H.
  revert i lo hi.
  induction l; simpl; intros; ArraySimplify.
  + entailer!.
  + Split; Intros; rewrite undef_missing_i_unfold; try lia; [Left | Right].
    * sep_apply mixed_seg_to_undef_seg.
      entailer!.
    * sep_apply IHl.
      sep_apply mixedstoreA_to_undefstoreA.
      entailer!.
      lia.
Qed.

Lemma undef_missing_i_to_mixed_missing_i : forall x i lo hi,
  undef_missing_i x i lo hi |-- mixed_missing_i x i lo hi (repeat None (Z.to_nat (hi - lo))).
Proof.
  intros.
  set (len := Z.to_nat (hi - lo)).
  assert (Hlen: len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert i lo hi Hlen.
  induction len; intros.
  - unfold undef_missing_i, mixed_missing_i.
    rewrite <- Hlen.
    simpl.
    entailer!.
  - assert (lo < hi) by lia.
    rewrite (undef_missing_i_unfold x i lo hi) by lia.
    replace (Z.to_nat (hi - lo)) with (S len) by lia.
    simpl.
     assert (Htail: len = Z.to_nat (hi - (lo + 1))) by lia.
     Split ; Intros.
     1: rewrite (mixed_missing_i_unfold x i lo hi (repeat None len) None);
       simpl mixedstoreA;
       Left;
       rewrite Htail;
       sep_apply undef_seg_to_mixed_seg;
       entailer!.
     rewrite (mixed_missing_i_unfold x i lo hi (repeat None len) None).
     simpl mixedstoreA.
     Right.
     sep_apply (IHlen i (lo + 1) hi Htail).
    entailer!.
Qed.

Lemma missing_i_to_missing_i_shape : forall x i lo hi (l : list A),
  missing_i x i lo hi l |-- missing_i_shape x i lo hi.
Proof.
  intros.
  prop_apply missing_i_length. Intros.
  revert H.
  revert i lo hi.
  induction l ; simpl ; intros ; ArraySimplify.
  + entailer!.
  + Split ; Intros ; rewrite missing_i_shape_unfold ; try lia ; [Left | Right].
    * sep_apply seg_to_seg_shape.
      entailer!.
    * sep_apply IHl.
      Exists a.
      entailer!.
      lia.
Qed.

(* Full/segment transitions: preserve information first, then forget to undef/shape. *)

Lemma full_to_undef_full : forall x n (l : list A),
  full x n l |-- undef_full x n.
Proof.
  intros.
  sep_apply full_to_seg.
  sep_apply seg_to_undef_seg.
  sep_apply undef_seg_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!. 
Qed.

Lemma mixed_seg_to_undef_full : forall x lo hi (l : list (option A)),
  mixed_seg x lo hi l |-- undef_full (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  sep_apply mixed_seg_to_undef_seg.
  sep_apply undef_seg_to_undef_full.
  entailer!.
Qed.

Lemma mixed_full_to_undef_seg : forall x n (l : list (option A)),
  mixed_full x n l |-- undef_seg x 0 n.
Proof.
  intros.
  sep_apply mixed_full_to_mixed_seg.
  sep_apply mixed_seg_to_undef_seg.
  replace (0 - 0) with 0 by lia.
  replace (x + 0 * sizeA) with x by lia.
  entailer!.
Qed.

Lemma mixed_full_to_undef_full : forall x n (l : list (option A)),
  mixed_full x n l |-- undef_full x n.
Proof.
  intros.
  sep_apply mixed_full_to_mixed_seg.
  sep_apply mixed_seg_to_undef_seg.
  sep_apply undef_seg_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma full_to_full_shape : forall x n (l : list A),
  full x n l |-- full_shape x n.
Proof.
  intros.
  sep_apply full_to_seg.
  sep_apply seg_to_seg_shape.
  sep_apply seg_shape_to_full_shape.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.  
Qed.

(* Split & Merge Lemmas  *)

(* Split/merge lemma families, grouped by source prefix.
   seg_split_to_*:
     seg_split_to_missing_i
     seg_split_to_seg

   full_split_to_*:
     full_split_to_missing_i
     full_split_to_seg
     full_split_to_full

   mixed_seg_split_to_*:
     mixed_seg_split_to_mixed_missing_i
     mixed_seg_split_to_undef_missing_i
     mixed_seg_split_to_mixed_seg

   mixed_full_split_to_*:
     mixed_full_split_to_mixed_missing_i
     mixed_full_split_to_undef_missing_i
     mixed_full_split_to_mixed_seg
     mixed_full_split_to_mixed_full

   undef_seg_split_to_*:
     undef_seg_split_to_undef_missing_i
     undef_seg_split_to_undef_seg

   undef_full_split_to_*:
     undef_full_split_to_undef_missing_i
     undef_full_split_to_undef_seg
     undef_full_split_to_undef_full

   seg_shape_split_to_*:
     seg_shape_split_to_missing_i_shape
     seg_shape_split_to_seg_shape

   full_shape_split_to_*:
     full_shape_split_to_missing_i_shape
     full_shape_split_to_seg_shape
     full_shape_split_to_full_shape

   missing_i_merge_to_*:
     missing_i_merge_to_seg
     missing_i_merge_to_full

   mixed_missing_i_merge_to_*:
     mixed_missing_i_merge_to_mixed_seg
     mixed_missing_i_merge_to_mixed_full
     mixed_missing_i_merge_to_undef_seg
     mixed_missing_i_merge_to_undef_full

   undef_missing_i_merge_to_*:
     undef_missing_i_merge_to_undef_seg
     undef_missing_i_merge_to_undef_full

   missing_i_shape_merge_to_*:
     missing_i_shape_merge_to_seg_shape
     missing_i_shape_merge_to_full_shape

   seg_merge_to_*:
     seg_merge_to_seg
     seg_merge_to_full

   mixed_seg_merge_to_*:
     mixed_seg_merge_to_mixed_seg
     mixed_seg_merge_to_mixed_full

   undef_seg_merge_to_*:
     undef_seg_merge_to_undef_seg
     undef_seg_merge_to_undef_full

   seg_shape_merge_to_*:
     seg_shape_merge_to_seg_shape
     seg_shape_merge_to_full_shape

   full_merge_to_*:
     full_merge_to_full

   mixed_full_merge_to_*:
     mixed_full_merge_to_mixed_full

   undef_full_merge_to_*:
     undef_full_merge_to_undef_full

   full_shape_merge_to_*:
     full_shape_merge_to_full_shape
*)

(* Pure and mixed split/merge rules that preserve concrete element information. *)

Lemma seg_split_to_missing_i : forall x lo n m (l : list A) a,
  lo <= n < m ->
  seg x lo m l |-- storeA x n (Znth (n - lo) l a) ** missing_i x n lo m l.
Proof.
  intros.
  revert H.
  rename m into hi.
  revert lo; induction l; intros; simpl; ArraySimplify.
  + entailer!.
  + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - Right.
      sep_apply IHl; [ | lia ].
      rewrite Znth_cons by lia.
      replace (n - (lo + 1)) with (n - lo - 1) by lia.
      entailer!.
    - Left.
      subst n.
      replace (lo - lo) with 0 by lia.
      entailer!.
Qed. 

Lemma full_split_to_missing_i : forall x n m (l : list A) a,
  0 <= n < m ->
  full x m l |-- storeA x n (Znth n l a) ** missing_i x n 0 m l.
Proof.
  intros.
  sep_apply full_to_seg.
  sep_apply (seg_split_to_missing_i x 0 n m l a) ; eauto.
  replace (n - 0) with n by lia.
  entailer!.
Qed. 

Lemma mixed_seg_split_to_mixed_missing_i : forall x lo n m (l : list (option A)) a,
  lo <= n < m ->
  mixed_seg x lo m l |-- mixedstoreA x n (Znth (n - lo) l a) ** mixed_missing_i x n lo m l.
Proof.
  intros.
  unfold mixed_seg, mixed_missing_i.
  eapply store_array_rec_split_to_missing_i.
  eauto.
Qed.

Lemma mixed_full_split_to_mixed_missing_i : forall x n m (l : list (option A)) a,
  0 <= n < m ->
  mixed_full x m l |-- mixedstoreA x n (Znth n l a) ** mixed_missing_i x n 0 m l.
Proof.
  intros.
  sep_apply mixed_full_to_mixed_seg.
  sep_apply (mixed_seg_split_to_mixed_missing_i x 0 n m l a); eauto.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma missing_i_merge_to_seg: forall x lo n m a (l: list A),
  lo <= n < m -> 
  storeA x n a ** missing_i x n lo m l |-- seg x lo m (replace_Znth (n - lo) a l).
Proof.
  intros.
  revert H.
  revert lo n m.
  induction l; intros; simpl ; ArraySimplify ; try entailer!.
  Split ; try entailer!.
  - subst n.
    replace (lo - lo) with 0 by lia.
    simpl.
    entailer!.
  - sep_apply IHl; [ | lia ].
    rewrite replace_Znth_cons by lia.
    replace (n - (lo + 1)) with (n - lo - 1) by lia.
    ArraySimplify.
    entailer!.
Qed.

Lemma missing_i_merge_to_full: forall x n m a (l: list A),
  0 <= n < m -> 
  storeA x n a ** missing_i x n 0 m l |-- full x m (replace_Znth n a l).
Proof.
  intros.
  sep_apply (missing_i_merge_to_seg x 0 n m a l) ; eauto.
  sep_apply seg_to_full.
  replace (n - 0) with n by lia.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma mixed_missing_i_merge_to_mixed_seg: forall x lo n m a (l: list (option A)),
  lo <= n < m -> 
  mixedstoreA x n a ** mixed_missing_i x n lo m l |-- mixed_seg x lo m (replace_Znth (n - lo) a l).
Proof.
  intros.
  unfold mixed_seg, mixed_missing_i.
  eapply store_array_missing_i_merge_to_rec.
  eauto.
Qed.

Lemma mixed_missing_i_merge_to_mixed_full: forall x n m a (l: list (option A)),
  0 <= n < m -> 
  mixedstoreA x n a ** mixed_missing_i x n 0 m l |-- mixed_full x m (replace_Znth n a l).
Proof.
  intros.
  sep_apply (mixed_missing_i_merge_to_mixed_seg x 0 n m a l); eauto.
  sep_apply mixed_seg_to_mixed_full.
  replace (n - 0) with n by lia.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma undef_seg_split_to_undef_missing_i : forall x lo n m,
  lo <= n < m ->
  undef_seg x lo m |-- undefstoreA x n ** undef_missing_i x n lo m.
Proof.
  intros.
  unfold undef_seg, undef_missing_i.
  revert H.
  rename m into hi.
  set (len := Z.to_nat (hi - lo)).
  assert (len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert H.
  revert lo n hi; induction len; intros; simpl.
  + entailer!.
  + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - Right. entailer!.
      sep_apply (IHlen (lo + 1) n hi) ; eauto ; try lia.
      entailer!.
    - Left.
      subst n. entailer!.
Qed.

Lemma undef_full_split_to_undef_missing_i : forall x n m,
  0 <= n < m ->
  undef_full x m |-- undefstoreA x n ** undef_missing_i x n 0 m.
Proof.
  intros.
  sep_apply undef_full_to_undef_seg.
  sep_apply (undef_seg_split_to_undef_missing_i x 0 n m) ; eauto.
  entailer!.
Qed. 

Lemma undef_missing_i_merge_to_undef_seg: forall x lo n m,
  lo <= n < m -> 
  undefstoreA x n ** undef_missing_i x n lo m |-- undef_seg x lo m.
Proof.
  intros.
  unfold undef_seg, undef_missing_i.
  revert H.
  rename m into hi.
  set (len := Z.to_nat (hi - lo)).
  assert (len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert H.
  revert lo n hi.
  induction len; intros; simpl ; try entailer!.
  Split ; try entailer!.
  - subst n.
    replace (lo - lo) with 0 by lia.
    simpl.
    entailer!.
  - sep_apply (IHlen (lo + 1) n hi) ; try lia.
    entailer!.
Qed.

Lemma undef_missing_i_merge_to_undef_full: forall x n m,
  0 <= n < m -> 
  undefstoreA x n ** undef_missing_i x n 0 m |-- undef_full x m.
Proof.
  intros.
  sep_apply (undef_missing_i_merge_to_undef_seg x 0 n m) ; eauto.
  sep_apply undef_seg_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

(* Forgetful mixed split/merge rules that drop element values to undef arrays. *)

Lemma mixed_seg_split_to_undef_missing_i : forall x lo n m (l : list (option A)),
  lo <= n < m ->
  mixed_seg x lo m l |-- undefstoreA x n ** undef_missing_i x n lo m.
Proof.
  intros.
  sep_apply mixed_seg_to_undef_seg.
  sep_apply (undef_seg_split_to_undef_missing_i x lo n m); eauto.
  entailer!.
Qed.

Lemma mixed_full_split_to_undef_missing_i : forall x n m (l : list (option A)),
  0 <= n < m ->
  mixed_full x m l |-- undefstoreA x n ** undef_missing_i x n 0 m.
Proof.
  intros.
  sep_apply mixed_full_to_undef_full.
  sep_apply (undef_full_split_to_undef_missing_i x n m); eauto.
  entailer!.
Qed.

Lemma mixed_missing_i_merge_to_undef_seg: forall x lo n m a (l: list (option A)),
  lo <= n < m ->
  mixedstoreA x n a ** mixed_missing_i x n lo m l |-- undef_seg x lo m.
Proof.
  intros.
  sep_apply mixedstoreA_to_undefstoreA.
  sep_apply mixed_missing_i_to_undef_missing_i.
  sep_apply (undef_missing_i_merge_to_undef_seg x lo n m); eauto.
  entailer!.
Qed.

Lemma mixed_missing_i_merge_to_undef_full: forall x n m a (l: list (option A)),
  0 <= n < m ->
  mixedstoreA x n a ** mixed_missing_i x n 0 m l |-- undef_full x m.
Proof.
  intros.
  sep_apply (mixed_missing_i_merge_to_undef_seg x 0 n m a l); eauto.
  sep_apply undef_seg_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma seg_shape_split_to_missing_i_shape : forall x lo n m,
  lo <= n < m ->
  seg_shape x lo m |-- EX a, storeA x n a ** missing_i_shape x n lo m.
Proof.
  intros.
  unfold seg_shape, missing_i_shape.
  revert H.
  rename m into hi.
  set (len := Z.to_nat (hi - lo)).
  assert (len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert H.
  revert lo n hi; induction len; intros; simpl.
  + entailer!.
  + Intros a.
    pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - sep_apply (IHlen (lo + 1) n hi) ; eauto ; try lia.
      Intros a0. Exists a0.
      Right. entailer!. Exists a.
      entailer!.
    - Exists a. Left.
      subst n.
       entailer!.
Qed.

Lemma full_shape_split_to_missing_i_shape : forall x n m,
  0 <= n < m ->
  full_shape x m |-- EX a, storeA x n a ** missing_i_shape x n 0 m.
Proof.
  intros.
  sep_apply full_shape_to_seg_shape.
  sep_apply (seg_shape_split_to_missing_i_shape x 0 n m) ; eauto.
  entailer!.
Qed. 

Lemma missing_i_shape_merge_to_seg_shape: forall x lo n m a,
  lo <= n < m -> 
  storeA x n a ** missing_i_shape x n lo m |-- seg_shape x lo m.
Proof.
  intros.
  unfold seg_shape, missing_i_shape.
  revert H.
  rename m into hi.
  set (len := Z.to_nat (hi - lo)).
  assert (len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert H.
  revert lo n hi.
  induction len; intros; simpl ; try entailer!.
  Split ; try entailer!.
  - subst n. Exists a. entailer!.
  - Intros x0.
    sep_apply (IHlen (lo + 1) n hi) ; try lia.
    Exists x0.
    entailer!.
Qed.

Lemma missing_i_shape_merge_to_full_shape: forall x n m a,
  0 <= n < m -> 
  storeA x n a ** missing_i_shape x n 0 m |-- full_shape x m.
Proof.
  intros.
  sep_apply (missing_i_shape_merge_to_seg_shape x 0 n m) ; eauto.
  sep_apply seg_shape_to_full_shape.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma seg_split_to_seg : forall x lo mid hi (l : list A),
  lo <= mid <= hi ->
  seg x lo hi l |-- seg x lo mid (sublist 0 (mid - lo) l) ** seg x mid hi (sublist (mid - lo) (hi - lo) l).
Proof.
  intros.
  generalize dependent lo. revert mid hi.
  induction l; intros ; ArraySimplify.
  - do 2 rewrite Zsublist_of_nil. 
    ArraySimplify.
    entailer!. 
  - prop_apply seg_length. Intros.
    destruct (Z_lt_ge_dec mid (lo + 1)).
    + assert (mid = lo) by lia; subst mid.
      rewrite Zsublist_nil by lia. 
      replace (lo - lo) with 0 by lia.
      rewrite sublist_cons1 ; try lia.
      ArraySimplify.
      rewrite sublist_self.
      entailer!.
      rewrite Zlength_correct. lia.
    + rewrite sublist_cons1 by lia.
      rewrite sublist_cons2; try lia.
      2 :{
        rewrite Zlength_correct. simpl. lia. 
      }
      replace (mid - lo - 1) with (mid - (lo + 1)) by lia.
      replace (hi - lo - 1) with (hi - (lo + 1)) by lia.
      sep_apply (IHl mid) ; try lia.
      ArraySimplify.
      entailer!.
Qed.

Lemma undef_seg_split_to_undef_seg : forall x lo mid hi,
  lo <= mid <= hi ->
  undef_seg x lo hi |-- undef_seg x lo mid ** undef_seg x mid hi.
Proof.
  intros.
  unfold undef_seg.
  set (len1 := Z.to_nat (mid - lo)).
  set (len2 := Z.to_nat (hi - mid)).
  replace (Z.to_nat (hi - lo)) with (len1 + len2)%nat by lia.
  assert (len1 = Z.to_nat (mid - lo)) by lia.
  assert (len2 = Z.to_nat (hi - mid)) by lia.
  clearbody len1. clearbody len2.
  generalize dependent mid. revert lo hi len2.
  induction len1; intros ; simpl ; try entailer!.
  - assert (mid = lo) by lia. 
    subst. 
    entailer!.
  - apply IHlen1; lia.
Qed.

Lemma seg_shape_split_to_seg_shape : forall x lo mid hi,
  lo <= mid <= hi ->
  seg_shape x lo hi |-- seg_shape x lo mid ** seg_shape x mid hi.
Proof.
  intros.
  unfold seg_shape.
  set (len1 := Z.to_nat (mid - lo)).
  set (len2 := Z.to_nat (hi - mid)).
  replace (Z.to_nat (hi - lo)) with (len1 + len2)%nat by lia.
  assert (len1 = Z.to_nat (mid - lo)) by lia.
  assert (len2 = Z.to_nat (hi - mid)) by lia.
  clearbody len1. clearbody len2.
  generalize dependent mid. revert lo hi len2.
  induction len1; intros ; simpl ; try entailer!.
  - assert (mid = lo) by lia. 
    subst. 
    entailer!.
  - Intros x0. Exists x0.
    sep_apply IHlen1 ; eauto ; try lia.
    entailer!.
Qed.

Lemma mixed_seg_split_to_mixed_seg : forall x lo mid hi (l : list (option A)),
  lo <= mid <= hi ->
  mixed_seg x lo hi l |--
  mixed_seg x lo mid (sublist 0 (mid - lo) l) ** mixed_seg x mid hi (sublist (mid - lo) (hi - lo) l).
Proof.
  intros.
  generalize dependent lo. revert mid hi.
  induction l; intros; ArraySimplify.
  - do 2 rewrite Zsublist_of_nil.
    ArraySimplify.
    entailer!.
  - prop_apply mixed_seg_length. Intros.
    destruct (Z_lt_ge_dec mid (lo + 1)).
    + assert (mid = lo) by lia; subst mid.
      rewrite Zsublist_nil by lia.
      replace (lo - lo) with 0 by lia.
      rewrite sublist_cons1; try lia.
      ArraySimplify.
      rewrite sublist_self.
      entailer!.
      rewrite Zlength_correct. lia.
    + rewrite sublist_cons1 by lia.
      rewrite sublist_cons2; try lia.
      2 : {
        rewrite Zlength_correct. simpl. lia.
      }
      replace (mid - lo - 1) with (mid - (lo + 1)) by lia.
      replace (hi - lo - 1) with (hi - (lo + 1)) by lia.
      sep_apply (IHl mid); try lia.
      ArraySimplify.
      entailer!.
Qed.

Lemma full_split_to_seg : forall x n m (l : list A),
  0 <= n <= m ->
  full x m l |--  
  seg x 0 n (sublist 0 n l) ** seg x n m (sublist n m l).
Proof.
  intros.
  sep_apply full_to_seg.
  sep_apply (seg_split_to_seg x 0 n m l) ; try lia.
  replace (n - 0) with n by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma mixed_full_split_to_mixed_seg : forall x n m (l : list (option A)),
  0 <= n <= m ->
  mixed_full x m l |--
  mixed_seg x 0 n (sublist 0 n l) ** mixed_seg x n m (sublist n m l).
Proof.
  intros.
  sep_apply mixed_full_to_mixed_seg.
  sep_apply (mixed_seg_split_to_mixed_seg x 0 n m l); try lia.
  replace (n - 0) with n by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma full_split_to_full : forall x n m (l : list A),
  0 <= n <= m ->
  full x m l |--  
  full x n (sublist 0 n l) ** full (x + n * sizeA) (m - n) (sublist n m l).
Proof.
  intros.
  sep_apply full_split_to_seg ; eauto.
  sep_apply seg_to_full. 
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
  apply seg_to_full.
Qed.

Lemma mixed_full_split_to_mixed_full : forall x n m (l : list (option A)),
  0 <= n <= m ->
  mixed_full x m l |--
  mixed_full x n (sublist 0 n l) ** mixed_full (x + n * sizeA) (m - n) (sublist n m l).
Proof.
  intros.
  sep_apply mixed_full_split_to_mixed_seg; eauto.
  sep_apply mixed_seg_to_mixed_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
  apply mixed_seg_to_mixed_full.
Qed.

Lemma undef_full_split_to_undef_seg : forall x n m,
  0 <= n <= m ->
  undef_full x m |--  
  undef_seg x 0 n ** undef_seg x n m.
Proof.
  intros.
  sep_apply undef_full_to_undef_seg.
  sep_apply (undef_seg_split_to_undef_seg x 0 n m) ; try lia.
  replace (n - 0) with n by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma undef_full_split_to_undef_full : forall x n m,
  0 <= n <= m ->
  undef_full x m |--  
  undef_full x n ** undef_full (x + n * sizeA) (m - n).
Proof.
  intros.
  sep_apply undef_full_split_to_undef_seg ; eauto.
  sep_apply undef_seg_to_undef_full. 
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
  apply undef_seg_to_undef_full.
Qed.

Lemma full_shape_split_to_seg_shape : forall x n m,
  0 <= n <= m ->
  full_shape x m |--  
  seg_shape x 0 n ** seg_shape x n m.
Proof.
  intros.
  sep_apply full_shape_to_seg_shape.
  sep_apply (seg_shape_split_to_seg_shape x 0 n m) ; try lia.
  replace (n - 0) with n by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma full_shape_split_to_full_shape : forall x n m,
  0 <= n <= m ->
  full_shape x m |--  
  full_shape x n ** full_shape (x + n * sizeA) (m - n).
Proof.
  intros.
  sep_apply full_shape_split_to_seg_shape ; eauto.
  sep_apply seg_shape_to_full_shape.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
  apply seg_shape_to_full_shape.
Qed.

Lemma seg_merge_to_seg : forall x lo mid hi (l1 l2 : list A),
  lo <= mid <= hi ->
  seg x lo mid l1 ** seg x mid hi l2 |-- seg x lo hi (l1 ++ l2).
Proof.
  intros.
  generalize dependent lo. revert mid hi l2.
  induction l1; intros ; ArraySimplify. 
  - rewrite app_nil_l.
    Intros. subst.
    entailer!.
  - simpl. ArraySimplify.
    entailer!.
    prop_apply seg_length. Intros.
    apply IHl1. lia. 
Qed. 

Lemma mixed_seg_merge_to_mixed_seg : forall x lo mid hi (l1 l2 : list (option A)),
  lo <= mid <= hi ->
  mixed_seg x lo mid l1 ** mixed_seg x mid hi l2 |-- mixed_seg x lo hi (l1 ++ l2).
Proof.
  intros.
  generalize dependent lo. revert mid hi l2.
  induction l1; intros; ArraySimplify.
  - rewrite app_nil_l.
    Intros. subst.
    entailer!.
  - simpl. ArraySimplify.
    entailer!.
    prop_apply mixed_seg_length. Intros.
    apply IHl1. lia.
Qed.

Lemma undef_seg_merge_to_undef_seg : forall x lo mid hi,
  lo <= mid <= hi ->
  undef_seg x lo mid ** undef_seg x mid hi |-- undef_seg x lo hi.
Proof.
  intros.
   unfold undef_seg.
  set (len1 := Z.to_nat (mid - lo)).
  set (len2 := Z.to_nat (hi - mid)).
  replace (Z.to_nat (hi - lo)) with (len1 + len2)%nat by lia.
  assert (len1 = Z.to_nat (mid - lo)) by lia.
  assert (len2 = Z.to_nat (hi - mid)) by lia.
  clearbody len1. clearbody len2.
  generalize dependent mid. revert lo hi len2.
  induction len1; intros ; simpl ; try entailer!. 
  - subst.
    entailer!.
  - apply IHlen1; lia.
Qed.

Lemma seg_shape_merge_to_seg_shape : forall x lo mid hi,
  lo <= mid <= hi ->
  seg_shape x lo mid ** seg_shape x mid hi |-- seg_shape x lo hi.
Proof.
  intros.
  unfold seg_shape.
  set (len1 := Z.to_nat (mid - lo)).
  set (len2 := Z.to_nat (hi - mid)).
  replace (Z.to_nat (hi - lo)) with (len1 + len2)%nat by lia.
  assert (len1 = Z.to_nat (mid - lo)) by lia.
  assert (len2 = Z.to_nat (hi - mid)) by lia.
  clearbody len1. clearbody len2.
  generalize dependent mid. revert lo hi len2.
  induction len1; intros ; simpl ; try entailer!.
  - subst. 
    entailer!.
  - Intros x0. Exists x0.
    sep_apply IHlen1 ; eauto ; try lia.
    entailer!.
Qed.

Lemma seg_merge_to_full : forall x lo mid hi (l1 l2 : list A),
  lo <= mid <= hi ->
  seg x lo mid l1 ** seg x mid hi l2 |-- full (x + lo * sizeA) (hi - lo) (l1 ++ l2).
Proof.
  intros.
  sep_apply seg_merge_to_seg ; eauto.
  sep_apply seg_to_full.
  entailer!.
Qed.

Lemma mixed_seg_merge_to_mixed_full : forall x lo mid hi (l1 l2 : list (option A)),
  lo <= mid <= hi ->
  mixed_seg x lo mid l1 ** mixed_seg x mid hi l2 |-- mixed_full (x + lo * sizeA) (hi - lo) (l1 ++ l2).
Proof.
  intros.
  sep_apply mixed_seg_merge_to_mixed_seg; eauto.
  sep_apply mixed_seg_to_mixed_full.
  entailer!.
Qed.

Lemma full_merge_to_full : forall x n m (l1 l2 : list A),
  0 <= n <= m ->
  full x n l1 ** full (x + n * sizeA) (m - n) l2 |-- full x m (l1 ++ l2).
Proof.
  intros.
  sep_apply full_to_seg.
  sep_apply (full_to_seg (x + n * sizeA)).
  rewrite <- seg_shift.
  replace (n + 0) with n by lia.
  replace (n + (m - n)) with m by lia.
  sep_apply (seg_merge_to_full x 0 n m) ; eauto.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma mixed_full_merge_to_mixed_full : forall x n m (l1 l2 : list (option A)),
  0 <= n <= m ->
  mixed_full x n l1 ** mixed_full (x + n * sizeA) (m - n) l2 |-- mixed_full x m (l1 ++ l2).
Proof.
  intros.
  sep_apply mixed_full_to_mixed_seg.
  sep_apply (mixed_full_to_mixed_seg (x + n * sizeA)).
  rewrite <- mixed_seg_shift.
  replace (n + 0) with n by lia.
  replace (n + (m - n)) with m by lia.
  sep_apply (mixed_seg_merge_to_mixed_full x 0 n m); eauto.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma undef_seg_merge_to_undef_full : forall x lo mid hi,
  lo <= mid <= hi ->
  undef_seg x lo mid ** undef_seg x mid hi |-- undef_full (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  sep_apply undef_seg_merge_to_undef_seg ; eauto.
  sep_apply undef_seg_to_undef_full.
  entailer!.
Qed.

Lemma undef_full_merge_to_undef_full : forall x n m,
  0 <= n <= m ->
  undef_full x n ** undef_full (x + n * sizeA) (m - n) |-- undef_full x m.
Proof.
  intros.
  sep_apply undef_full_to_undef_seg.
  sep_apply (undef_full_to_undef_seg (x + n * sizeA)).
  rewrite <- undef_seg_shift.
  replace (n + 0) with n by lia.
  replace (n + (m - n)) with m by lia.
  sep_apply (undef_seg_merge_to_undef_seg x 0 n m) ; eauto.
  replace (Z.to_nat n + Z.to_nat (m - n))%nat with (Z.to_nat m) by lia.
  sep_apply undef_seg_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma seg_shape_merge_to_full_shape : forall x lo mid hi,
  lo <= mid <= hi ->
  seg_shape x lo mid ** seg_shape x mid hi |-- full_shape (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  sep_apply seg_shape_merge_to_seg_shape ; eauto.
  sep_apply seg_shape_to_full_shape.
  entailer!.
Qed.

Lemma full_shape_merge_to_full_shape : forall x n m,
  0 <= n <= m ->
  full_shape x n ** full_shape (x + n * sizeA) (m - n) |-- full_shape x m.
Proof.
  intros.
  sep_apply full_shape_to_seg_shape.
  sep_apply (full_shape_to_seg_shape (x + n * sizeA)).
  rewrite <- seg_shape_shift.
  replace (n + 0) with n by lia.
  replace (n + (m - n)) with m by lia.
  sep_apply (seg_shape_merge_to_seg_shape x 0 n m) ; eauto.
  replace (Z.to_nat n + Z.to_nat (m - n))%nat with (Z.to_nat m) by lia.
  sep_apply seg_shape_to_full_shape.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma seg_shape_to_undef_seg : forall x lo hi,
  seg_shape x lo hi |-- undef_seg x lo hi.
Proof.
  intros.
  unfold seg_shape , undef_seg.
  set (len := Z.to_nat (hi - lo)).
  clearbody len.
  revert lo hi.
  induction len ; simpl ; intros ; ArraySimplify ; try entailer!.
  Intros x0.
  sep_apply store_to_undefstore.
  entailer!.
Qed.

Lemma full_shape_to_undef_full : forall x n,
  full_shape x n |-- undef_full x n.
Proof.
  intros.
  sep_apply full_shape_to_seg_shape.
  sep_apply seg_shape_to_undef_seg.
  sep_apply undef_seg_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

(** Predicate to align *)

Lemma undef_seg_to_align : forall x lo hi,
  undef_seg x lo hi |-- store_align_n ((hi - lo) * sizeA).
Proof.
  intros.
  unfold undef_seg.
  set (n := Z.to_nat (hi - lo)).
  assert (n = Z.to_nat (hi - lo)) by lia.
  clearbody n.
  generalize dependent lo. revert hi.
  induction n; intros; simpl; try entailer!.
  - replace ((hi - lo) * sizeA) with 0 by lia.
    unfold store_align_n. Exists nil.
    simpl. entailer!. constructor.
  - sep_apply IHn ; try lia.
    sep_apply undefstore_to_align.
    sep_apply (store_align_merge sizeA ((hi - (lo + 1)) * sizeA)).
    replace (sizeA + (hi - (lo + 1)) * sizeA) with ((hi - lo) * sizeA) by lia.
    entailer!.
Qed.

Lemma seg_to_align : forall x lo hi (l : list A),
  seg x lo hi l |-- store_align_n ((hi - lo) * sizeA) .
Proof.
  intros.
  sep_apply seg_to_undef_seg.
  sep_apply undef_seg_to_align.
  entailer!.
Qed.

Lemma mixed_seg_to_align : forall x lo hi (l : list (option A)),
  mixed_seg x lo hi l |-- store_align_n ((hi - lo) * sizeA).
Proof.
  intros.
  sep_apply mixed_seg_to_undef_seg.
  sep_apply undef_seg_to_align.
  entailer!.
Qed.

Lemma seg_shape_to_align : forall x lo hi,
  seg_shape x lo hi |-- store_align_n ((hi - lo) * sizeA).
Proof.
  intros.
  sep_apply seg_shape_to_undef_seg.
  sep_apply undef_seg_to_align.
  entailer!.
Qed.

Lemma full_to_align : forall x n (l : list A),
  full x n l |-- store_align_n (n * sizeA).
Proof.
  intros.
  sep_apply full_to_seg.
  sep_apply seg_to_align.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma mixed_full_to_align : forall x n (l : list (option A)),
  mixed_full x n l |-- store_align_n (n * sizeA).
Proof.
  intros.
  sep_apply mixed_full_to_mixed_seg.
  sep_apply mixed_seg_to_align.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma undef_full_to_align : forall x n,
  undef_full x n |-- store_align_n (n * sizeA).
Proof.
  intros.
  sep_apply undef_full_to_undef_seg.
  sep_apply undef_seg_to_align.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma full_shape_to_align : forall x n,
  full_shape x n |-- store_align_n (n * sizeA).
Proof.
  intros.
  sep_apply full_shape_to_seg_shape.
  sep_apply seg_shape_to_align.
  replace (n - 0) with n by lia.
  entailer!.
Qed.

Lemma undef_full_valid : forall x n,
  undef_full x n |-- “ 0 <= n ”.
Proof.
  intros.
  unfold undef_full, store_undef_array.
  destruct (Z_le_gt_dec 0 n) as [H | H].
  - entailer!.
  - replace (Z.to_nat n) with 0%nat by lia.
    simpl.
    entailer!.
Qed.

Lemma full_shape_valid : forall x n,
  full_shape x n |-- “ 0 <= n ”.
Proof.
  intros.
  unfold full_shape, store_undef_array.
  destruct (Z_le_gt_dec 0 n) as [H | H].
  - entailer!.
  - replace (Z.to_nat n) with 0%nat by lia.
    simpl.
    entailer!.
Qed.

(** Predicate byte-length range with the address-space-sized upper bound *)

Lemma seg_length_range : forall x lo hi (l : list A),
  seg x lo hi l |-- “ 0 <= (hi - lo) * sizeA <= addr_max_unsigned + 1 ”.
Proof.
  intros.
  prop_apply seg_valid. Intros.
  sep_apply seg_to_align.
  prop_apply store_align_n_valid. Intros.
  match goal with
  | Hrange: _ <= addr_max_unsigned / 1 + 1 |- _ =>
      replace (addr_max_unsigned / 1 + 1) with (addr_max_unsigned + 1) in Hrange by (rewrite Z.div_1_r; lia)
  end.
  pose proof sizeA_valid.
  entailer!.
Qed.

Lemma mixed_seg_length_range : forall x lo hi (l : list (option A)),
  mixed_seg x lo hi l |-- “ 0 <= (hi - lo) * sizeA <= addr_max_unsigned + 1 ”.
Proof.
  intros.
  prop_apply mixed_seg_valid. Intros.
  sep_apply mixed_seg_to_align.
  prop_apply store_align_n_valid. Intros.
  match goal with
  | Hrange: _ <= addr_max_unsigned / 1 + 1 |- _ =>
      replace (addr_max_unsigned / 1 + 1) with (addr_max_unsigned + 1) in Hrange by (rewrite Z.div_1_r; lia)
  end.
  pose proof sizeA_valid.
  entailer!.
Qed.

Lemma undef_seg_length_range : forall x lo hi,
  undef_seg x lo hi |-- “ 0 <= (hi - lo) * sizeA <= addr_max_unsigned + 1 ”.
Proof.
  intros.
  prop_apply undef_seg_valid. Intros.
  sep_apply undef_seg_to_align.
  prop_apply store_align_n_valid. Intros.
  match goal with
  | Hrange: _ <= addr_max_unsigned / 1 + 1 |- _ =>
      replace (addr_max_unsigned / 1 + 1) with (addr_max_unsigned + 1) in Hrange by (rewrite Z.div_1_r; lia)
  end.
  pose proof sizeA_valid.
  entailer!.
Qed.

Lemma seg_shape_length_range : forall x lo hi,
  seg_shape x lo hi |-- “ 0 <= (hi - lo) * sizeA <= addr_max_unsigned + 1 ”.
Proof.
  intros.
  prop_apply seg_shape_valid. Intros.
  sep_apply seg_shape_to_align.
  prop_apply store_align_n_valid. Intros.
  match goal with
  | Hrange: _ <= addr_max_unsigned / 1 + 1 |- _ =>
      replace (addr_max_unsigned / 1 + 1) with (addr_max_unsigned + 1) in Hrange by (rewrite Z.div_1_r; lia)
  end.
  pose proof sizeA_valid.
  entailer!.
Qed.

Lemma full_length_range : forall x n (l : list A),
  full x n l |-- “ 0 <= n * sizeA <= addr_max_unsigned + 1 ”.
Proof.
  intros.
  prop_apply full_length. Intros.
  sep_apply full_to_align.
  prop_apply store_align_n_valid. Intros.
  match goal with
  | Hrange: _ <= addr_max_unsigned / 1 + 1 |- _ =>
      replace (addr_max_unsigned / 1 + 1) with (addr_max_unsigned + 1) in Hrange by (rewrite Z.div_1_r; lia)
  end.
  pose proof sizeA_valid.
  entailer!.
Qed.

Lemma mixed_full_length_range : forall x n (l : list (option A)),
  mixed_full x n l |-- “ 0 <= n * sizeA <= addr_max_unsigned + 1 ”.
Proof.
  intros.
  prop_apply mixed_full_length. Intros.
  sep_apply mixed_full_to_align.
  prop_apply store_align_n_valid. Intros.
  match goal with
  | Hrange: _ <= addr_max_unsigned / 1 + 1 |- _ =>
      replace (addr_max_unsigned / 1 + 1) with (addr_max_unsigned + 1) in Hrange by (rewrite Z.div_1_r; lia)
  end.
  pose proof sizeA_valid.
  entailer!.
Qed.

Lemma undef_full_length_range : forall x n,
  undef_full x n |-- “ 0 <= n * sizeA <= addr_max_unsigned + 1 ”.
Proof.
  intros.
  prop_apply undef_full_valid. Intros.
  sep_apply undef_full_to_align.
  prop_apply store_align_n_valid. Intros.
  match goal with
  | Hrange: _ <= addr_max_unsigned / 1 + 1 |- _ =>
      replace (addr_max_unsigned / 1 + 1) with (addr_max_unsigned + 1) in Hrange by (rewrite Z.div_1_r; lia)
  end.
  pose proof sizeA_valid.
  entailer!.
Qed.

Lemma full_shape_length_range : forall x n,
  full_shape x n |-- “ 0 <= n * sizeA <= addr_max_unsigned + 1 ”.
Proof.
  intros.
  prop_apply full_shape_valid. Intros.
  sep_apply full_shape_to_align.
  prop_apply store_align_n_valid. Intros.
  match goal with
  | Hrange: _ <= addr_max_unsigned / 1 + 1 |- _ =>
      replace (addr_max_unsigned / 1 + 1) with (addr_max_unsigned + 1) in Hrange by (rewrite Z.div_1_r; lia)
  end.
  pose proof sizeA_valid.
  entailer!.
Qed.

End ArrayLib. 

Definition repeat_Z {A: Type} (a: A) (n: Z): list A :=
  repeat a (Z.to_nat n).

Lemma repeat_Z_tail : forall {A: Type} (a: A) n,
  n >= 0 ->
  repeat_Z a (n + 1) = repeat_Z a n ++ a :: nil.
Proof.
  intros.
  unfold repeat_Z.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  set (Z.to_nat n) as m.
  clearbody m. clear H n. 
  rename m into n. 
  induction n ; simpl in *; auto. 
  rewrite IHn. auto. 
Qed.

Definition SingleSome {A : Type} (l : list (option A)) (n : Z) (a : A) : Prop :=
  Znth n l None = Some a /\ forall m, (0 <= m < Zlength l -> m <> n -> Znth m l None = None).

End ArrayLibCoreSig.
