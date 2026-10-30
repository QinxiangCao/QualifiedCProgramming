(** * Growable vectors

    A growable vector is a C struct holding a length, a capacity and a buffer
    pointer, as in [struct { int size; int cap; T *ptr; }].  Its elements are
    [ptr[0 .. size)]; the cells [ptr[size .. cap)] are allocated but not
    initialized.  A vector with no capacity has no buffer: its pointer is
    [NULL], so freeing or reallocating it is defined.

    [DynVec E L] describes such a vector for one element array [E] and one
    struct layout [L]:
    - [shell v]: the three fields of the struct at [v], uninitialized;
    - [rep_at v p l cap]: the vector at [v] is open: its buffer is [p], its
      capacity is [cap], and it holds [l];
    - [rep_ptr v p l]: the vector at [v] holds [l] in buffer [p]; the
      capacity is hidden;
    - [rep v l]: the vector at [v] holds [l]; buffer and capacity are hidden;
    - [slot base i]: the [i]-th struct of a C array of such structs.

    [VecArray V] (after [DynVec]) reads a C array of vectors through the
    framework's generic array predicates: [full], [seg], [missing_i],
    [undef_seg], and [missing2] for two vectors out at once.

    [ArrayElems ES AL] turns any framework array library built by
    [ArrayLib ES] (for example [IntArray] or [PtrArray]) into an element
    array; [IntElems] and [PtrElems] are the two instances. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
From SimpleC.EE.Applications_human Require Export list_index_lib.
From SimpleC.SL Require Import SeparationLogic.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** The element array: segments of initialized and uninitialized cells. *)
Module Type VEC_ELEMS.
  Parameter Inline A : Type.
  Parameter Inline seg : Z -> Z -> Z -> list A -> Assertion.
  Parameter Inline undef_seg : Z -> Z -> Z -> Assertion.
  Parameter seg_nil_frame : forall p lo P Q, P |-- Q -> P |-- Q ** seg p lo lo nil.
  Parameter undef_seg_nil_frame : forall p lo P Q, P |-- Q -> P |-- Q ** undef_seg p lo lo.
  Parameter seg_truncate : forall p k n cap l Q,
    0 <= k <= n -> n <= cap -> n = Zlength l ->
    Q ** seg p 0 n l ** undef_seg p n cap
    |-- Q ** seg p 0 k (sublist 0 k l) ** undef_seg p k cap.
End VEC_ELEMS.

(** The C struct: its name and the names of its length, capacity and buffer
    fields.  Inlined, so an instance unfolds to the field-address spelling
    that QCP emits. *)
Module Type VEC_LAYOUT.
  Parameter Inline struct_name size_field cap_field ptr_field : string.
End VEC_LAYOUT.

(** ** Element arrays from the framework's array libraries

    [ARRAY_VIEW ES] lists the members of [ArrayLib ES] that vectors need, with
    the statements of [ArrayLibCore.v].  An array library such as [IntArray]
    matches it structurally, and because [seg] and [undef_seg] are not
    inlined here, an instance unfolds to the library's own [IntArray.seg]. *)
Module Type ARRAY_VIEW (ES : ELEMENT_STORE).
  Parameter seg : addr -> Z -> Z -> list ES.A -> Assertion.
  Parameter undef_seg : addr -> Z -> Z -> Assertion.
  Axiom seg_empty : forall x lo hi, seg x lo hi nil --||-- “ hi = lo ” && emp.
  Axiom undef_seg_empty : forall x lo, undef_seg x lo lo --||-- emp.
  Axiom seg_to_undef_seg : forall x lo hi (l : list ES.A),
    seg x lo hi l |-- undef_seg x lo hi.
  Axiom seg_split_to_seg : forall x lo mid hi (l : list ES.A),
    lo <= mid <= hi ->
    seg x lo hi l |-- seg x lo mid (sublist 0 (mid - lo) l) ** seg x mid hi (sublist (mid - lo) (hi - lo) l).
  Axiom undef_seg_merge_to_undef_seg : forall x lo mid hi,
    lo <= mid <= hi ->
    undef_seg x lo mid ** undef_seg x mid hi |-- undef_seg x lo hi.
End ARRAY_VIEW.

Module ArrayElems (ES : ELEMENT_STORE) (AL : ARRAY_VIEW ES) <: VEC_ELEMS.
  Definition A := ES.A.
  Definition seg := AL.seg.
  Definition undef_seg := AL.undef_seg.

  Lemma seg_nil_frame : forall p lo P Q, P |-- Q -> P |-- Q ** seg p lo lo nil.
  Proof.
    intros p lo P Q H. sep_apply H. unfold seg.
    pose proof (AL.seg_empty p lo lo) as [_ He]. rewrite <- He.
    split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto ..].
  Qed.

  Lemma undef_seg_nil_frame : forall p lo P Q, P |-- Q -> P |-- Q ** undef_seg p lo lo.
  Proof.
    intros p lo P Q H. sep_apply H. unfold undef_seg.
    pose proof (AL.undef_seg_empty p lo) as [_ He]. rewrite <- He.
    apply derivable1_sepcon_emp_r.
  Qed.

  Lemma seg_truncate : forall p k n cap l Q,
    0 <= k <= n -> n <= cap -> n = Zlength l ->
    Q ** seg p 0 n l ** undef_seg p n cap
    |-- Q ** seg p 0 k (sublist 0 k l) ** undef_seg p k cap.
  Proof.
    intros. unfold seg, undef_seg.
    sep_apply (AL.seg_split_to_seg p 0 k n l); [| lia].
    sep_apply (AL.seg_to_undef_seg p k n (sublist (k - 0) (n - 0) l)).
    sep_apply (AL.undef_seg_merge_to_undef_seg p k n cap); [| lia].
    rewrite Z.sub_0_r. cancel.
  Qed.

End ArrayElems.

Module IntElems := ArrayElems StoreIntAsElement IntArray.
Module PtrElems := ArrayElems StorePtrAsElement PtrArray.


(** A buffer pointer is valid for its capacity: a vector without capacity
    owns no buffer and stores [NULL], so [free] and [realloc] of the pointer
    are defined. *)
Definition vec_buf_ok (cap p : Z) : Prop := cap = 0 -> p = 0.

(** Discharges [vec_buf_ok cap p] from a hypothesis, from [0 < cap], or from [p = 0]. *)
Ltac vec_buf_solve := unfold vec_buf_ok in *; first [assumption | intros; lia | tauto].

Module DynVec (E : VEC_ELEMS) (L : VEC_LAYOUT).

Definition A : Type := E.A.

Local Ltac pure_close :=
  unfold vec_buf_ok in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  solve [tauto | lia | intros; lia].

Definition shell (v : Z) : Assertion :=
  &( v # L.struct_name ->ₛ L.size_field) # Int |->_ **
  &( v # L.struct_name ->ₛ L.cap_field) # Int |->_ **
  &( v # L.struct_name ->ₛ L.ptr_field) # Ptr |->_.

(** The struct of an open vector: length [n], capacity [cap], buffer [p].
    Opening a vector to reach its buffer leaves this atom in place of the
    three field cells; only the vector unit's own bodies open it further. *)
Definition header (v p n cap : Z) : Assertion :=
  &( v # L.struct_name ->ₛ L.size_field) # Int |-> n **
  &( v # L.struct_name ->ₛ L.cap_field) # Int |-> cap **
  &( v # L.struct_name ->ₛ L.ptr_field) # Ptr |-> p.

Lemma header_fold : forall v p n cap,
  &( v # L.struct_name ->ₛ L.size_field) # Int |-> n **
  &( v # L.struct_name ->ₛ L.cap_field) # Int |-> cap **
  &( v # L.struct_name ->ₛ L.ptr_field) # Ptr |-> p
  |-- header v p n cap.
Proof. intros. unfold header. cancel. Qed.

Lemma header_open : forall v p n cap,
  header v p n cap
  |-- &( v # L.struct_name ->ₛ L.size_field) # Int |-> n **
      &( v # L.struct_name ->ₛ L.cap_field) # Int |-> cap **
      &( v # L.struct_name ->ₛ L.ptr_field) # Ptr |-> p.
Proof. intros. unfold header. cancel. Qed.

Lemma shell_fold : forall v,
  &( v # L.struct_name ->ₛ L.size_field) # Int |->_ **
  &( v # L.struct_name ->ₛ L.cap_field) # Int |->_ **
  &( v # L.struct_name ->ₛ L.ptr_field) # Ptr |->_
  |-- shell v.
Proof. intros. unfold shell. cancel. Qed.

Lemma shell_open : forall v,
  shell v
  |-- &( v # L.struct_name ->ₛ L.size_field) # Int |->_ **
      &( v # L.struct_name ->ₛ L.cap_field) # Int |->_ **
      &( v # L.struct_name ->ₛ L.ptr_field) # Ptr |->_.
Proof. intros. unfold shell. cancel. Qed.

(** The open vector.  A vector without capacity owns no buffer and stores
    [NULL], which keeps [free] and [realloc] of its pointer defined. *)
Definition rep_at (v p : Z) (l : list E.A) (cap : Z) : Assertion :=
  “ 0 <= Zlength l <= cap /\ cap <= INT_MAX /\ vec_buf_ok cap p ” &&
  (header v p (Zlength l) cap **
   E.seg p 0 (Zlength l) l **
   E.undef_seg p (Zlength l) cap).

(** The vector with its buffer named and its capacity hidden: the view for
    code that walks the buffer but never grows it. *)
Definition rep_ptr (v p : Z) (l : list E.A) : Assertion :=
  EX cap : Z, rep_at v p l cap.

Definition rep (v : Z) (l : list E.A) : Assertion :=
  EX p : Z, EX cap : Z, rep_at v p l cap.

Lemma rep_at_rep : forall v p l cap, rep_at v p l cap |-- rep v l.
Proof. intros. unfold rep. Exists p cap. cancel. Qed.

Lemma rep_at_rep_ptr : forall v p l cap, rep_at v p l cap |-- rep_ptr v p l.
Proof. intros. unfold rep_ptr. Exists cap. cancel. Qed.

Lemma rep_ptr_rep : forall v p l, rep_ptr v p l |-- rep v l.
Proof. intros. unfold rep_ptr, rep. Intros cap. Exists p cap. cancel. Qed.

Lemma rep_rep_ptr : forall v l, rep v l |-- EX p : Z, rep_ptr v p l.
Proof. intros. unfold rep, rep_ptr. Intros p cap. Exists p cap. cancel. Qed.

Lemma rep_at_bounds : forall v p l cap,
  rep_at v p l cap
  |-- “ 0 <= Zlength l <= cap /\ cap <= INT_MAX ” && rep_at v p l cap.
Proof.
  intros. unfold rep_at. Intros.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; pure_close ..].
Qed.

Lemma rep_ptr_bounds : forall v p l,
  rep_ptr v p l |-- “ 0 <= Zlength l <= INT_MAX ” && rep_ptr v p l.
Proof.
  intros. unfold rep_ptr at 1. Intros cap.
  sep_apply (rep_at_bounds v p l cap). Intros.
  sep_apply (rep_at_rep_ptr v p l cap).
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; pure_close ..].
Qed.

(** Opening [rep_ptr] to the capacity-explicit form, for a lemma stated on [rep_at]. *)
Lemma rep_ptr_open : forall v p l, rep_ptr v p l |-- EX cap : Z, rep_at v p l cap.
Proof. intros. unfold rep_ptr. Intros cap. Exists cap. cancel. Qed.

(** Opening [rep] to the form with buffer and capacity named. *)
Lemma rep_open : forall v l, rep v l |-- EX p cap : Z, rep_at v p l cap.
Proof. intros. unfold rep. Intros p cap. Exists p cap. cancel. Qed.

Lemma rep_bounds : forall v l,
  rep v l |-- “ 0 <= Zlength l <= INT_MAX ” && rep v l.
Proof.
  intros. unfold rep at 1. Intros p cap.
  sep_apply (rep_at_bounds v p l cap). Intros.
  sep_apply (rep_at_rep v p l cap).
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; pure_close ..].
Qed.

(** Opening a vector into its header, live segment and spare tail, with the
    facts [rep_at_intro] takes; the converse of [rep_at_intro]. *)
Lemma rep_at_open : forall v p l cap,
  rep_at v p l cap
  |-- “ 0 <= Zlength l <= cap /\ cap <= INT_MAX /\ vec_buf_ok cap p ” &&
      (header v p (Zlength l) cap **
       E.seg p 0 (Zlength l) l **
       E.undef_seg p (Zlength l) cap).
Proof.
  intros. unfold rep_at. Intros.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; pure_close ..].
Qed.

(** Building a vector from its header, live segment and spare tail.  The three
    lengths are separate so that a caller can pass them in whatever form the
    program computed them. *)
Lemma rep_at_intro : forall v p l cap n_size n_seg n_undef,
  n_size = Zlength l -> n_seg = Zlength l -> n_undef = Zlength l ->
  0 <= Zlength l <= cap -> cap <= INT_MAX -> vec_buf_ok cap p ->
  header v p n_size cap **
  E.seg p 0 n_seg l **
  E.undef_seg p n_undef cap
  |-- rep_at v p l cap.
Proof.
  intros. subst. unfold rep_at.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; pure_close ..].
Qed.

(** Fold the header, the live segment and the spare tail straight into [rep_ptr]
    (the predicate the getters speak), hiding the capacity. *)
Lemma rep_ptr_intro : forall v p l cap n_size n_seg n_undef,
  n_size = Zlength l -> n_seg = Zlength l -> n_undef = Zlength l ->
  0 <= Zlength l <= cap -> cap <= INT_MAX -> vec_buf_ok cap p ->
  header v p n_size cap **
  E.seg p 0 n_seg l **
  E.undef_seg p n_undef cap
  |-- rep_ptr v p l.
Proof.
  intros. sep_apply (rep_at_intro v p l cap n_size n_seg n_undef); try assumption.
  apply rep_at_rep_ptr.
Qed.

Lemma rep_intro : forall v p l cap n_size n_seg n_undef,
  n_size = Zlength l -> n_seg = Zlength l -> n_undef = Zlength l ->
  0 <= Zlength l <= cap -> cap <= INT_MAX -> vec_buf_ok cap p ->
  header v p n_size cap **
  E.seg p 0 n_seg l **
  E.undef_seg p n_undef cap
  |-- rep v l.
Proof.
  intros.
  sep_apply (rep_at_intro v p l cap n_size n_seg n_undef); try assumption.
  apply rep_at_rep.
Qed.

(** An empty vector over a buffer of [cap] cells. *)
Lemma rep_nil_intro : forall v p cap,
  0 <= cap <= INT_MAX -> vec_buf_ok cap p ->
  header v p 0 cap **
  E.undef_seg p 0 cap
  |-- rep v nil.
Proof.
  intros. unfold rep, rep_at. Exists p cap.
  rewrite Zlength_nil.
  split_pure_spatial; [| split_pures; dump_pre_spatial; pure_close ..].
  cancel.
  apply E.seg_nil_frame.
  cancel.
Qed.

(** An empty vector with no buffer: its pointer is [NULL]. *)
Lemma rep_empty_intro : forall v,
  header v 0 0 0 |-- rep v nil.
Proof.
  intros. unfold rep, rep_at. Exists 0 0.
  rewrite Zlength_nil.
  split_pure_spatial; [| split_pures; dump_pre_spatial; pure_close ..].
  apply E.undef_seg_nil_frame.
  apply E.seg_nil_frame.
  cancel.
Qed.

(** Dropping all but the first [k] elements keeps the buffer. *)
Lemma rep_at_truncate : forall v p l cap k,
  0 <= k <= Zlength l -> Zlength l <= cap -> cap <= INT_MAX -> vec_buf_ok cap p ->
  header v p k cap **
  E.seg p 0 (Zlength l) l **
  E.undef_seg p (Zlength l) cap
  |-- rep_at v p (sublist 0 k l) cap.
Proof.
  intros. unfold rep_at.
  rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
  split_pure_spatial; [| split_pures; dump_pre_spatial; pure_close ..].
  apply E.seg_truncate; lia.
Qed.

(** Two vectors held at the same time are at different addresses. *)
Lemma rep_distinct : forall v0 l0 v1 l1,
  rep v0 l0 ** rep v1 l1 |-- “ v0 <> v1 ”.
Proof.
  intros v0 l0 v1 l1.
  destruct (Z.eq_dec v0 v1) as [Heq | Hne].
  - subst v1. unfold rep, rep_at, header. Intros p0 c0 p1 c1.
    sep_apply (dup_store_int (&( v0 # L.struct_name ->ₛ L.size_field))
                 (Zlength l0) (Zlength l1)).
    Intros. contradiction.
  - apply dump_spatial_left. exact Hne.
Qed.

(** ** Slot of an array of vectors

    Arrays of vectors themselves are [VecArray] below. *)

(** Slot [i] of a contiguous C array of [L.struct_name] structs at [base].
    [VEC_STORE] below takes [slot] as a parameter and [VecArray] never
    computes with it, so another implementation can place its vectors
    differently (a padded stride, an offset inside a larger record, a
    non-uniform layout).  The framework's [ELEMENT_STORE] instead fixes a
    contiguous affine layout through its shift and alignment axioms. *)
Definition slot (base i : Z) : Z := base + i * sizeof(L.struct_name).

Lemma slot_eq : forall base i, slot base i = base + i * sizeof(L.struct_name).
Proof. reflexivity. Qed.

End DynVec.

(** * Arrays of vectors in the framework's array shape

    An array of vector structs, read through the framework's generic array
    predicates ([store_array_rec], [store_array_missing_i_rec],
    [store_undef_array_rec] of SeparationLogic) with one vector per element,
    as [Array2LibCore] does for rows: [full], [seg], [missing_i], [undef_seg]
    and the split/merge lemmas, plus [missing2] for two vectors taken out at
    once. *)
Module Type VEC_STORE.
  Parameter Inline A : Type.
  Parameter rep : Z -> list A -> Assertion.
  Parameter slot : Z -> Z -> Z.
  Parameter shell : Z -> Assertion.
End VEC_STORE.

Module VecArray (V : VEC_STORE).
Definition vec_store (x : addr) (i : Z) (l : list V.A) : Assertion :=
  V.rep (V.slot x i) l.
Definition seg (x lo hi : Z) (ls : list (list V.A)) : Assertion :=
  store_array_rec vec_store x lo hi ls.
Definition full (x n : Z) (ls : list (list V.A)) : Assertion :=
  store_array vec_store x n ls.
Definition missing_i (x i lo hi : Z) (ls : list (list V.A)) : Assertion :=
  store_array_missing_i_rec vec_store x i lo hi ls.

(** Uninitialized vector structs, the framework's [undefstoreA]. *)
Definition vec_undef_store (x : addr) (i : Z) : Assertion := V.shell (V.slot x i).
Definition undef_seg (x lo hi : Z) : Assertion :=
  store_undef_array_rec vec_undef_store x lo hi (Z.to_nat (hi - lo)).
Definition undef_missing_i (x i lo hi : Z) : Assertion :=
  store_undef_array_missing_i_rec vec_undef_store x i lo hi (Z.to_nat (hi - lo)).
Definition undef_full (x n : Z) : Assertion :=
  store_undef_array vec_undef_store x n.

Lemma seg_split_to_missing_i : forall x lo n m ls a,
  lo <= n < m ->
  seg x lo m ls |-- vec_store x n (Znth (n - lo) ls a) ** missing_i x n lo m ls.
Proof. intros. apply store_array_rec_split_to_missing_i; auto. Qed.

Lemma full_split_to_missing_i : forall x n m ls a,
  0 <= n < m ->
  full x m ls |-- vec_store x n (Znth n ls a) ** missing_i x n 0 m ls.
Proof. intros. apply store_array_split_to_missing_i; auto. Qed.

(** [full_split_to_missing_i] with the vector taken out read as [V.rep] at its slot. *)
Lemma full_split_to_slot : forall x n m ls a,
  0 <= n < m ->
  full x m ls |-- V.rep (V.slot x n) (Znth n ls a) ** missing_i x n 0 m ls.
Proof. intros. apply full_split_to_missing_i; auto. Qed.

Lemma missing_i_merge_to_seg : forall x lo n m a ls,
  lo <= n < m ->
  vec_store x n a ** missing_i x n lo m ls |-- seg x lo m (replace_Znth (n - lo) a ls).
Proof. intros. apply store_array_missing_i_merge_to_rec; auto. Qed.

Lemma missing_i_merge_to_full : forall x n m a ls,
  0 <= n < m ->
  vec_store x n a ** missing_i x n 0 m ls |-- full x m (replace_Znth n a ls).
Proof. intros. apply store_array_missing_i_merge_to_array; auto. Qed.

(** [missing_i_merge_to_full] with the vector put back read as [V.rep] at its slot. *)
Lemma slot_merge_to_full : forall x n m a ls,
  0 <= n < m ->
  V.rep (V.slot x n) a ** missing_i x n 0 m ls |-- full x m (replace_Znth n a ls).
Proof. intros. apply missing_i_merge_to_full; auto. Qed.

Lemma missing_i_Zlength : forall x i lo hi ls,
  missing_i x i lo hi ls |-- “ Zlength ls = hi - lo ”.
Proof. intros. apply store_array_missing_i_rec_Zlength. Qed.

Lemma seg_Zlength : forall x lo hi ls,
  seg x lo hi ls |-- “ Zlength ls = hi - lo ”.
Proof. intros. apply store_array_rec_Zlength. Qed.

Lemma full_Zlength : forall x n ls,
  full x n ls |-- “ Zlength ls = n ”.
Proof. intros. apply store_array_Zlength. Qed.

Lemma seg_single : forall x lo a,
  vec_store x lo a |-- seg x lo (lo + 1) (a :: nil).
Proof.
  intros. unfold seg. cbn [store_array_rec]. cancel.
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; reflexivity ..].
Qed.

Lemma full_to_seg : forall x n ls,
  full x n ls |-- seg x 0 n ls.
Proof. intros. unfold full, seg, store_array. cancel. Qed.

(** Only a segment that starts at slot [0] becomes [full]: ArrayLib's
    [seg_to_full] moves the base to element [lo], which needs the address
    arithmetic that [slot] keeps abstract. *)
Lemma seg_to_full : forall x n ls,
  seg x 0 n ls |-- full x n ls.
Proof. intros. unfold full, seg, store_array. cancel. Qed.

Lemma undef_full_to_undef_seg : forall x n,
  undef_full x n |-- undef_seg x 0 n.
Proof.
  intros. unfold undef_full, undef_seg, store_undef_array.
  rewrite Z.sub_0_r. cancel.
Qed.

Lemma undef_seg_valid : forall x lo hi,
  undef_seg x lo hi |-- “ lo <= hi ”.
Proof.
  intros. unfold undef_seg.
  destruct (Z_le_gt_dec lo hi) as [Hle | Hgt].
  - dump_pre_spatial. lia.
  - replace (Z.to_nat (hi - lo)) with O by lia. simpl. Intros. lia.
Qed.

Lemma undef_seg_empty : forall x lo,
  undef_seg x lo lo --||-- emp.
Proof.
  intros. unfold undef_seg. replace (Z.to_nat (lo - lo)) with O by lia. simpl.
  split.
  - Intros. cancel.
  - split_pure_spatial; [cancel | split_pures; dump_pre_spatial; reflexivity ..].
Qed.

Lemma seg_empty : forall x lo hi,
  seg x lo hi nil --||-- “ hi = lo ” && emp.
Proof.
  intros. unfold seg. simpl.
  split.
  - Intros. split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia ..].
  - Intros. split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [reflexivity | lia] ..].
Qed.

Lemma full_empty : forall x n,
  full x n nil --||-- “ n = 0 ” && emp.
Proof.
  intros. unfold full, store_array. simpl.
  split.
  - Intros. split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia ..].
  - Intros. split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [reflexivity | lia] ..].
Qed.

Lemma undef_full_empty : forall x,
  undef_full x 0 --||-- emp.
Proof.
  intros. unfold undef_full, store_undef_array. simpl.
  split.
  - Intros. cancel.
  - split_pure_spatial; [cancel | split_pures; dump_pre_spatial; reflexivity ..].
Qed.

Lemma undef_missing_i_empty : forall x i lo,
  undef_missing_i x i lo lo |-- “ False ”.
Proof.
  intros. unfold undef_missing_i. replace (Z.to_nat (lo - lo)) with O by lia. simpl.
  apply coq_prop_False_left. tauto.
Qed.

Lemma undef_seg_unfold : forall x lo hi,
  lo < hi ->
  undef_seg x lo hi --||-- vec_undef_store x lo ** undef_seg x (lo + 1) hi.
Proof.
  intros. unfold undef_seg.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl. split; cancel.
Qed.

Lemma missing_i_index_range : forall x i lo hi ls,
  missing_i x i lo hi ls |-- “ lo <= i < hi ”.
Proof.
  intros x i lo hi ls. revert lo.
  induction ls as [|a ls IH]; intros lo; unfold missing_i in *; simpl.
  - apply coq_prop_False_left. tauto.
  - apply derivable1_orp_elim.
    + Intros. subst lo. prop_apply_p (seg_Zlength x (i + 1) hi ls). Intros.
      pose proof (Zlength_nonneg ls). dump_pre_spatial. lia.
    + Intros. prop_apply_p (IH (lo + 1)). Intros. dump_pre_spatial. lia.
Qed.

Lemma seg_split_to_seg : forall x lo mid hi ls,
  lo <= mid <= hi ->
  seg x lo hi ls
  |-- seg x lo mid (sublist 0 (mid - lo) ls) ** seg x mid hi (sublist (mid - lo) (hi - lo) ls).
Proof.
  intros x lo mid hi ls Hm.
  assert (Happ : forall (l1 : list (list V.A)) lo' hi' l2,
      seg x lo' hi' (l1 ++ l2)
      |-- seg x lo' (lo' + Zlength l1) l1 ** seg x (lo' + Zlength l1) hi' l2).
  { induction l1 as [|a l1 IH]; intros lo' hi' l2.
    - unfold seg. simpl. rewrite Zlength_nil. replace (lo' + 0) with lo' by lia.
      split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto ..].
    - unfold seg in *. simpl.
      replace (lo' + Zlength (a :: l1)) with ((lo' + 1) + Zlength l1)
        by (rewrite Zlength_cons; lia).
      sep_apply (IH (lo' + 1) hi' l2). cancel. }
  prop_apply_p (seg_Zlength x lo hi ls). Intros.
  assert (Hls : ls = sublist 0 (mid - lo) ls ++ sublist (mid - lo) (hi - lo) ls).
  { rewrite <- sublist_split by lia. rewrite sublist_self by lia. reflexivity. }
  rewrite Hls at 1.
  sep_apply (Happ (sublist 0 (mid - lo) ls) lo hi (sublist (mid - lo) (hi - lo) ls)).
  rewrite Zlength_sublist by lia. replace (lo + (mid - lo - 0)) with mid by lia.
  cancel.
Qed.

Lemma seg_merge_to_seg : forall x lo mid hi l1 l2,
  lo <= mid <= hi ->
  seg x lo mid l1 ** seg x mid hi l2 |-- seg x lo hi (l1 ++ l2).
Proof.
  intros x lo mid hi l1 l2 _. revert lo.
  induction l1 as [|a l1 IH]; intros lo.
  - unfold seg. simpl. Intros. subst. cancel.
  - unfold seg in *. simpl. sep_apply (IH (lo + 1)). cancel.
Qed.

Lemma missing_i_split_to_seg : forall x i lo hi l1 a l2,
  i = lo + Zlength l1 ->
  missing_i x i lo hi (l1 ++ a :: l2) |-- seg x lo i l1 ** seg x (i + 1) hi l2.
Proof.
  intros x i lo hi l1 a l2. revert lo.
  induction l1 as [|b l1 IH]; intros lo Hi.
  - rewrite Zlength_nil in Hi. subst i. unfold missing_i, seg. simpl.
    apply derivable1_orp_elim.
    + Intros. replace (lo + 0 + 1) with (lo + 1) by lia.
      split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto ..].
    + Intros. lia.
  - rewrite Zlength_cons in Hi. pose proof (Zlength_nonneg l1).
    unfold missing_i, seg in *. simpl.
    apply derivable1_orp_elim.
    + Intros. lia.
    + Intros. sep_apply (IH (lo + 1) ltac:(lia)). cancel.
Qed.

Lemma seg_merge_to_missing_i : forall x i lo hi l1 a l2,
  i = lo + Zlength l1 ->
  seg x lo i l1 ** seg x (i + 1) hi l2 |-- missing_i x i lo hi (l1 ++ a :: l2).
Proof.
  intros x i lo hi l1 a l2. revert lo.
  induction l1 as [|b l1 IH]; intros lo Hi.
  - rewrite Zlength_nil in Hi. subst i. unfold missing_i, seg. simpl.
    Intros. rewrite <- derivable1_orp_intros1.
    replace (lo + 0 + 1) with (lo + 1) by lia.
    split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia ..].
  - rewrite Zlength_cons in Hi. pose proof (Zlength_nonneg l1).
    unfold missing_i, seg in *. simpl.
    rewrite <- derivable1_orp_intros2.
    sep_apply (IH (lo + 1) ltac:(lia)).
    split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia ..].
Qed.

Lemma seg_unfold : forall x lo hi ls a,
  seg x lo hi (a :: ls) --||-- vec_store x lo a ** seg x (lo + 1) hi ls.
Proof. intros. unfold seg. simpl. split; cancel. Qed.

Lemma missing_i_unfold : forall x i lo hi ls a,
  missing_i x i lo hi (a :: ls) --||--
   “ i = lo ” && seg x (lo + 1) hi ls ||
   “ i > lo ” && vec_store x lo a ** missing_i x i (lo + 1) hi ls.
Proof.
  intros. unfold missing_i, seg. simpl.
  split; (apply derivable1_orp_elim;
    [apply derivable1_orp_intros1 | apply derivable1_orp_intros2]).
Qed.

Lemma undef_missing_i_unfold : forall x i lo hi,
  lo < hi ->
  undef_missing_i x i lo hi --||--
   “ i = lo ” && undef_seg x (lo + 1) hi ||
   “ i > lo ” && vec_undef_store x lo ** undef_missing_i x i (lo + 1) hi.
Proof.
  intros. unfold undef_missing_i, undef_seg.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  split; (apply derivable1_orp_elim;
    [apply derivable1_orp_intros1 | apply derivable1_orp_intros2]).
Qed.

(** Two elements [i] and [j] missing from an array of [n]: the three segments
    around them, over the full list [ls]. *)
Definition missing2 (x i j n : Z) (ls : list (list V.A)) : Assertion :=
  “ Zlength ls = n ” &&
  seg x 0 (Z.min i j) (sublist 0 (Z.min i j) ls) **
  seg x (Z.min i j + 1) (Z.max i j) (sublist (Z.min i j + 1) (Z.max i j) ls) **
  seg x (Z.max i j + 1) n (sublist (Z.max i j + 1) n ls).

(** Take element [j] out of an array already missing [i]. *)
Lemma missing_i_split_to_missing2 : forall x i j n ls a,
  0 <= i < n -> 0 <= j < n -> i <> j ->
  missing_i x i 0 n ls |-- vec_store x j (Znth j ls a) ** missing2 x i j n ls.
Proof.
  intros x i j n ls a Hi Hj Hij.
  prop_apply_p (missing_i_Zlength x i 0 n ls). Intros.
  assert (Hlen : Zlength ls = n) by lia.
  unfold missing2.
  destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
  - rewrite Z.min_r, Z.max_l by lia.
    pose proof (sublist_Znth_mid a 0 i n ls ltac:(lia) ltac:(lia)) as Hls.
    pose proof (sublist_Znth_mid a 0 j i ls ltac:(lia) ltac:(lia)) as Hpre.
    rewrite (sublist_self ls n) in Hls by lia.
    pose proof (missing_i_split_to_seg x i 0 n (sublist 0 i ls)
      (Znth i ls a) (sublist (i + 1) n ls)
      ltac:(rewrite Zlength_sublist by lia; lia)) as Hd.
    rewrite <- Hls in Hd. sep_apply Hd.
    sep_apply (seg_split_to_seg x 0 j i (sublist 0 i ls) ltac:(lia)).
    rewrite Hpre.
    rewrite (sublist_split_app_r (j - 0) (i - 0) j) by (try rewrite Zlength_sublist by lia; lia).
    rewrite sublist_split_app_l by (try rewrite Zlength_sublist by lia; lia).
    replace (j - 0 - j) with 0 by lia.
    rewrite (sublist_self (Znth j ls a :: sublist (j + 1) i ls))
      by (rewrite Zlength_cons, Zlength_sublist by lia; lia).
    rewrite (sublist_self (sublist 0 j ls)) by (rewrite Zlength_sublist by lia; lia).
    sep_apply (proj1 (seg_unfold x j i (sublist (j + 1) i ls) (Znth j ls a))).
    split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia ..].
  - rewrite Z.min_l, Z.max_r by lia.
    pose proof (sublist_Znth_mid a 0 i n ls ltac:(lia) ltac:(lia)) as Hls.
    pose proof (sublist_Znth_mid a (i + 1) j n ls ltac:(lia) ltac:(lia)) as Hpost.
    rewrite (sublist_self ls n) in Hls by lia.
    pose proof (missing_i_split_to_seg x i 0 n (sublist 0 i ls)
      (Znth i ls a) (sublist (i + 1) n ls)
      ltac:(rewrite Zlength_sublist by lia; lia)) as Hd.
    rewrite <- Hls in Hd. sep_apply Hd.
    sep_apply (seg_split_to_seg x (i + 1) j n (sublist (i + 1) n ls) ltac:(lia)).
    rewrite Hpost.
    rewrite (sublist_split_app_r (j - (i + 1)) (n - (i + 1)) (j - (i + 1)))
      by (try rewrite Zlength_sublist by lia; lia).
    rewrite sublist_split_app_l by (try rewrite Zlength_sublist by lia; lia).
    replace (j - (i + 1) - (j - (i + 1))) with 0 by lia.
    rewrite (sublist_self (Znth j ls a :: sublist (j + 1) n ls))
      by (rewrite Zlength_cons, Zlength_sublist by lia; lia).
    rewrite (sublist_self (sublist (i + 1) j ls)) by (rewrite Zlength_sublist by lia; lia).
    sep_apply (proj1 (seg_unfold x j n (sublist (j + 1) n ls) (Znth j ls a))).
    split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia ..].
Qed.

(** Put element [j] back with contents [w]; [i] stays missing. *)
Lemma missing2_merge_to_missing_i : forall x i j n ls w,
  0 <= i < n -> 0 <= j < n -> i <> j ->
  vec_store x j w ** missing2 x i j n ls |-- missing_i x i 0 n (replace_Znth j w ls).
Proof.
  intros x i j n ls w Hi Hj Hij.
  unfold missing2. Intros. rename H into Hlen.
  rewrite (replace_Znth_split j w ls) by lia.
  rewrite Hlen.
  destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
  - rewrite Z.min_r, Z.max_l by lia.
    sep_apply (proj2 (seg_unfold x j i (sublist (j + 1) i ls) w)).
    sep_apply (seg_merge_to_seg x 0 j i (sublist 0 j ls) (w :: sublist (j + 1) i ls) ltac:(lia)).
    rewrite (sublist_Znth_mid nil (j + 1) i n ls) by lia.
    replace (sublist 0 j ls ++ w :: sublist (j + 1) i ls ++ Znth i ls nil :: sublist (i + 1) n ls)
      with ((sublist 0 j ls ++ w :: sublist (j + 1) i ls) ++ Znth i ls nil :: sublist (i + 1) n ls)
      by (rewrite <- app_assoc; reflexivity).
    apply seg_merge_to_missing_i.
    rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
  - rewrite Z.min_l, Z.max_r by lia.
    sep_apply (proj2 (seg_unfold x j n (sublist (j + 1) n ls) w)).
    sep_apply (seg_merge_to_seg x (i + 1) j n (sublist (i + 1) j ls) (w :: sublist (j + 1) n ls) ltac:(lia)).
    rewrite (sublist_Znth_mid nil 0 i j ls) by lia.
    replace ((sublist 0 i ls ++ Znth i ls nil :: sublist (i + 1) j ls) ++ w :: sublist (j + 1) n ls)
      with (sublist 0 i ls ++ Znth i ls nil :: (sublist (i + 1) j ls ++ w :: sublist (j + 1) n ls))
      by (rewrite <- app_assoc; reflexivity).
    sep_apply (seg_merge_to_missing_i x i 0 n (sublist 0 i ls) (Znth i ls nil)
      (sublist (i + 1) j ls ++ w :: sublist (j + 1) n ls)
      ltac:(rewrite Zlength_sublist by lia; lia)).
    cancel.
Qed.

(** Two elements out of a full array and back, through [missing_i]. *)
Lemma full_split_to_missing2 : forall x i j n ls a,
  0 <= i < n -> 0 <= j < n -> i <> j ->
  full x n ls |-- vec_store x i (Znth i ls a) ** vec_store x j (Znth j ls a) ** missing2 x i j n ls.
Proof.
  intros x i j n ls a Hi Hj Hij.
  sep_apply (full_split_to_missing_i x i n ls a Hi).
  sep_apply (missing_i_split_to_missing2 x i j n ls a Hi Hj Hij).
  cancel.
Qed.

Lemma missing2_merge_to_full : forall x i j n ls wi wj,
  0 <= i < n -> 0 <= j < n -> i <> j ->
  vec_store x i wi ** vec_store x j wj ** missing2 x i j n ls
  |-- full x n (replace_Znth i wi (replace_Znth j wj ls)).
Proof.
  intros x i j n ls wi wj Hi Hj Hij.
  sep_apply (missing2_merge_to_missing_i x i j n ls wj Hi Hj Hij).
  sep_apply (missing_i_merge_to_full x i n wi (replace_Znth j wj ls) Hi).
  cancel.
Qed.

End VecArray.
