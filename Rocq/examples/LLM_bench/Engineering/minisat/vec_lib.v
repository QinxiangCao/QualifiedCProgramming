Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From compcert.lib Require Import Integers.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Import naive_C_Rules.
Local Open Scope sac.

(**
  Allocation arithmetic used by a live vector.  The array predicates carry
  the concrete allocation span; this pure interface records the corresponding
  UInt32 byte-count side condition used by the current C front end.
 *)
Definition vec_alloc_ok (stride cap : Z) : Prop :=
  0 < stride /\
  0 <= cap /\
  0 <= cap * stride <= Int.max_unsigned.

(**
  The condition needed only when a full vector grows.  It separates signed
  arithmetic for [2 * cap + 1], the UInt32 allocation argument, and the
  address-space span.  In particular, it does not assert that realloc moves.
 *)
Definition vec_growth_ok (stride cap : Z) : Prop :=
  0 < stride /\
  0 <= cap /\
  2 * cap <= Int.max_signed /\
  2 * cap + 1 <= Int.max_signed /\
  0 <= (2 * cap + 1) * stride <= Int.max_unsigned /\
  (2 * cap + 1) * stride <= addr_max_unsigned + 1.

(** The address/capacity relation produced by either branch of push. *)
Definition vec_push_result
    (len oldbuf oldcap newbuf newcap : Z) : Prop :=
  (len < oldcap /\ newbuf = oldbuf /\ newcap = oldcap) \/
  (len = oldcap /\ newcap = 2 * oldcap + 1).

Definition veci_buffer
    (buf : addr) (xs : list Z) (cap : Z) : Assertion :=
  IntArray.full buf (Zlength xs) xs **
  IntArray.undef_seg buf (Zlength xs) cap.

Definition veci_header
    (v : addr) (len cap : Z) (buf : addr) : Assertion :=
  &(v # "veci_t" ->ₛ "size") # Int |-> len **
  &(v # "veci_t" ->ₛ "cap") # Int |-> cap **
  &(v # "veci_t" ->ₛ "ptr") # Ptr |-> buf.

Definition veci_raw
    (v buf : addr) (cap : Z) (xs : list Z) : Assertion :=
  “ v <> 0 /\
    buf <> 0 /\
    0 <= Zlength xs /\ Zlength xs <= cap /\
    4 <= cap /\ cap <= Int.max_signed /\
    vec_alloc_ok (sizeof(INT)) cap ” &&
  (veci_header v (Zlength xs) cap buf **
   veci_buffer buf xs cap).

(** The one public live-vector abstraction for integer vectors. *)
Definition store_veci (v : addr) (xs : list Z) : Assertion :=
  EX buf cap, veci_raw v buf cap xs.

Definition veci_shell (v : addr) : Assertion :=
  “ v <> 0 ” &&
  (&(v # "veci_t" ->ₛ "size") # Int |->_ **
   &(v # "veci_t" ->ₛ "cap") # Int |->_ **
   &(v # "veci_t" ->ₛ "ptr") # Ptr |->_).

Definition vecp_buffer
    (buf : addr) (xs : list Z) (cap : Z) : Assertion :=
  PtrArray.full buf (Zlength xs) xs **
  PtrArray.undef_seg buf (Zlength xs) cap.

Definition vecp_header
    (v : addr) (len cap : Z) (buf : addr) : Assertion :=
  &(v # "vecp_t" ->ₛ "size") # Int |-> len **
  &(v # "vecp_t" ->ₛ "cap") # Int |-> cap **
  &(v # "vecp_t" ->ₛ "ptr") # Ptr |-> buf.

Definition vecp_raw
    (v buf : addr) (cap : Z) (xs : list Z) : Assertion :=
  “ v <> 0 /\
    buf <> 0 /\
    0 <= Zlength xs /\ Zlength xs <= cap /\
    4 <= cap /\ cap <= Int.max_signed /\
    vec_alloc_ok ptr_size_Z cap ” &&
  (vecp_header v (Zlength xs) cap buf **
   vecp_buffer buf xs cap).

(**
  The one public live-vector abstraction for pointer vectors.  [PtrArray]
  owns pointer-valued slots only: no pointee assertion is included, so NULL,
  duplicates, and opaque/tagged pointer values remain admissible.
 *)
Definition store_vecp (v : addr) (xs : list Z) : Assertion :=
  EX buf cap, vecp_raw v buf cap xs.

Definition vecp_shell (v : addr) : Assertion :=
  “ v <> 0 ” &&
  (&(v # "vecp_t" ->ₛ "size") # Int |->_ **
   &(v # "vecp_t" ->ₛ "cap") # Int |->_ **
   &(v # "vecp_t" ->ₛ "ptr") # Ptr |->_).

Require Import Coq.micromega.Lia.
Lemma veci_buffer_truncate__resize_prefix :
  forall (buf : addr) (xs : list Z) (cap k : Z),
    0 <= k <= Zlength xs ->
    Zlength xs <= cap ->
    IntArray.full buf (Zlength xs) xs **
    IntArray.undef_seg buf (Zlength xs) cap |--
    IntArray.full buf k (sublist 0 k xs) **
    IntArray.undef_seg buf k cap.
Proof.
  intros.
  sep_apply (IntArray.full_split_to_seg buf k (Zlength xs) xs); try lia.
  sep_apply (IntArray.seg_to_full buf 0 k (sublist 0 k xs)).
  replace (buf + 0 * sizeof(INT)) with buf by lia.
  replace (k - 0) with k by lia.
  sep_apply (IntArray.seg_to_undef_seg
    buf k (Zlength xs) (sublist k (Zlength xs) xs)).
  sep_apply (IntArray.undef_seg_merge_to_undef_seg
    buf k (Zlength xs) cap); try lia.
  cancel (IntArray.full buf k (sublist 0 k xs)).
  cancel (IntArray.undef_seg buf k cap).
Qed.
Lemma vecp_buffer_truncate__resize_prefix :
  forall (buf : addr) (xs : list Z) (cap k : Z),
    0 <= k <= Zlength xs ->
    Zlength xs <= cap ->
    PtrArray.full buf (Zlength xs) xs **
    PtrArray.undef_seg buf (Zlength xs) cap |--
    PtrArray.full buf k (sublist 0 k xs) **
    PtrArray.undef_seg buf k cap.
Proof.
  intros.
  sep_apply (PtrArray.full_split_to_seg buf k (Zlength xs) xs); try lia.
  sep_apply (PtrArray.seg_to_full buf 0 k (sublist 0 k xs)).
  replace (buf + 0 * ptr_size_Z) with buf by lia.
  replace (k - 0) with k by lia.
  sep_apply (PtrArray.seg_to_undef_seg
    buf k (Zlength xs) (sublist k (Zlength xs) xs)).
  sep_apply (PtrArray.undef_seg_merge_to_undef_seg
    buf k (Zlength xs) cap); try lia.
  cancel (PtrArray.full buf k (sublist 0 k xs)).
  cancel (PtrArray.undef_seg buf k cap).
Qed.
Lemma reassociate_sepcon_7_entail__push_nongrowth
    {P1 P2 P3 P4 P5 P6 P7 Q : Assertion} :
  (P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 |-- Q) ->
  (P1 ** (P2 ** (P3 ** (P4 ** (P5 ** (P6 ** P7)))))) |-- Q.
Proof.
  intros H.
  sep_apply H.
  cancel.
Qed.
Lemma vec_push_result_from_branches__push_final :
  forall len oldbuf oldcap newbuf newcap,
    len <= oldcap ->
    len < newcap ->
    (len < oldcap -> newbuf = oldbuf /\ newcap = oldcap) ->
    (len = oldcap -> newcap = 2 * oldcap + 1) ->
    vec_push_result len oldbuf oldcap newbuf newcap.
Proof.
  intros len oldbuf oldcap newbuf newcap Hle Hnew Hsame Hgrow.
  unfold vec_push_result.
  destruct (Z_lt_ge_dec len oldcap) as [Hlt | Hge].
  - left. split; [exact Hlt | exact (Hsame Hlt)].
  - right. assert (Heq : len = oldcap) by lia.
    split; [exact Heq | exact (Hgrow Heq)].
Qed.
