Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

(* ================================================================
   Part 1: Predicate Definitions
   ================================================================ *)

(* sll: singly linked list
   - x = NULL when l is empty
   - x points to first node when l is non-empty *)
Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
    | nil     => “ x = NULL ” && emp
    | a :: l0 => “ x <> NULL ” && 
                 EX y: addr,
                   &(x # "sll" ->ₛ "data") # UInt |-> a **
                   &(x # "sll" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

(* sllseg: segment of singly linked list from x to y *)
Fixpoint sllseg (x y: addr) (l: list Z): Assertion :=
  match l with
    | nil     => “ x = y ” && emp
    | a :: l0 => “ x <> NULL ” && 
                 EX z: addr,
                   &(x # "sll" ->ₛ "data") # UInt |-> a **
                   &(x # "sll" ->ₛ "next") # Ptr |-> z **
                   sllseg z y l0
  end.

(* sllbseg: segment for list box (stores pointer to node)
   - x: pointer location (not node address)
   - y: tail pointer location *)
Fixpoint sllbseg (x y: addr) (l: list Z): Assertion :=
  match l with
    | nil     => “ x = y ” && emp
    | a :: l0 => EX z: addr,
                   “ z <> NULL ” &&
                   x # Ptr |-> z **
                   &(z # "sll" ->ₛ "data") # UInt |-> a **
                   sllbseg (&(z # "sll" ->ₛ "next")) y l0
  end.

(* sllb: list box containing singly linked list
   Design: split empty/non-empty cases for precise tail tracking
   - Empty: head = NULL, ptail = &head
   - Non-empty: use sllbseg *)
Definition sllb (x: addr) (l: list Z): Assertion :=
  “ x <> NULL ” &&
  match l with
  | nil =>
      &(x # "sllb" ->ₛ "head") # Ptr |-> NULL **
      &(x # "sllb" ->ₛ "ptail") # Ptr |-> (&(x # "sllb" ->ₛ "head"))
  | a :: l0 =>
      EX ptail_val: addr,
        &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
        sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val (a :: l0) **
        ptail_val # Ptr |-> NULL
  end.

(* sllb_sll: alternative sllb based on sll (simpler but no tail tracking)
   Used for functions that don't modify ptail (map_list_box, sllb2array) *)
Definition sllb_sll (x: addr) (l: list Z): Assertion :=
  “ x <> 0 ” &&
  EX h: addr,
    &(x # "sllb" ->ₛ "head") # Ptr |-> h **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> 0 **
    sll h l.

(* sll_pt: sll with explicit tail pointer tracking
   Used in app_list_box to track where l2 should connect *)
Definition sll_pt (h: addr) (pt: addr) (l: list Z): Assertion :=
  match l with
  | nil => “ h = NULL ” && emp
  | a :: l0 =>
      “ h <> NULL ” &&
      &(h # "sll" ->ₛ "data") # UInt |-> a **
      sllbseg (&(h # "sll" ->ₛ "next")) pt l0 **
      pt # Ptr |-> NULL
  end.

(* map_mult: multiply each element by x *)
Definition map_mult (x: Z) (l: list Z): list Z :=
  List.map (fun a => unsigned_last_nbits (x * a) 32) l.

Lemma map_mult_nil: forall x, map_mult x nil = nil.
Proof. reflexivity. Qed.

Lemma map_mult_cons: forall x a l,
  map_mult x (a :: l) = (unsigned_last_nbits (x * a) 32) :: map_mult x l.
Proof. reflexivity. Qed.

(* ================================================================
   Part 2: Lemmas for sll
   ================================================================ *)

Lemma sll_zero: forall x l,
  x = NULL ->
  sll x l |-- “ l = nil ” && emp.
Proof.
  intros. destruct l.
  + entailer!.
  + simpl. Intros. Intros x0. entailer!.
Qed.

Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y a l0,
      “ l = a :: l0 ” &&
      &(x # "sll" ->ₛ "data") # UInt |-> a **
      &(x # "sll" ->ₛ "next") # Ptr |-> y **
      sll y l0.
Proof.
  intros. destruct l.
  + simpl. Intros. tauto.
  + simpl. Intros. Intros y. Exists y z l. entailer!.
Qed.

Lemma sll_not_zero': forall x l,
  x <> NULL ->
  sll x l |-- “ l <> nil ”.
Proof.
  intros. destruct l.
  + simpl. Intros. tauto.
  + simpl. Intros. Intros y. entailer!. congruence.
Qed.

Lemma sll_not_null_length: forall p l,
  p <> NULL ->
  sll p l |-- “ Zlength l >= 1 ”.
Proof.
  intros. destruct l.
  - simpl sll. Intros. contradiction.
  - simpl sll. Intros. entailer!.
    rewrite Zlength_cons. pose proof Zlength_nonneg l. lia.
Qed.

(* ================================================================
   Part 3: Lemmas for sllseg
   ================================================================ *)

Lemma sllseg_len1: forall x a y,
  x <> NULL ->
  &(x # "sll" ->ₛ "data") # UInt |-> a **
  &(x # "sll" ->ₛ "next") # Ptr |-> y |--
  sllseg x y [a].
Proof.
  intros. simpl sllseg. Exists y. entailer!.
Qed.

Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
Proof.
  intros. revert x; induction l1; simpl sllseg; intros.
  + Intros. subst y. entailer!.
  + Intros. Intros z0. Exists z0. sep_apply IHl1. entailer!.
Qed.

Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
Proof.
  intros. revert x; induction l1; simpl sllseg; simpl sll; intros.
  + Intros. subst y. entailer!.
  + Intros. Intros z0. Exists z0. sep_apply IHl1. entailer!.
Qed.

Lemma sllseg_0_sll: forall x l,
  sllseg x 0 l |-- sll x l.
Proof.
  intros. revert x. induction l; try easy.
  simpl. intros. Intros z. Exists z. entailer!.
Qed.

(* ================================================================
   Part 4: Lemmas for sllbseg
   ================================================================ *)

Lemma sllbseg_len1: forall (x y: addr) (a: Z),
  y <> 0 ->
  x # Ptr |-> y **
  &(y # "sll" ->ₛ "data") # UInt |-> a |--
  sllbseg x (&(y # "sll" ->ₛ "next")) [a].
Proof.
  intros. simpl. Exists y. entailer!.
Qed.

Lemma sllbseg_sllbseg: forall x y z l1 l2,
  sllbseg x y l1 ** sllbseg y z l2 |--
  sllbseg x z (l1 ++ l2).
Proof.
  intros. revert x; induction l1; simpl; intros.
  + entailer!. subst x. entailer!.
  + Intros u. Exists u. entailer!.
Qed.

Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.
Proof.
  intros. revert x; induction l; simpl; intros.
  + Intros. subst x. Exists z; entailer!.
  + Intros x_v. Exists x_v. sep_apply IHl. Intros y'. Exists y'. entailer!.
Qed.

Lemma sllbseg_0_sll': forall x y l,
  sllbseg x y l ** y # Ptr |-> NULL |--
  EX head_val: addr, x # Ptr |-> head_val ** sll head_val l.
Proof.
  intros. revert x; induction l; simpl; intros.
  + Intros. subst x. Exists NULL. simpl sll. entailer!.
  + Intros head_val. Exists head_val.
    sep_apply IHl. Intros next_val. simpl sll. Exists next_val. entailer!.
Qed.

Lemma sllbseg_sll': forall x y l1 l2,
  sllbseg x y l1 ** y # Ptr |-> 0 ** sll 0 l2 |--
  EX h: addr, x # Ptr |-> h ** sll h (l1 ++ l2).
Proof.
  intros.
  assert (H0: (0:addr) = NULL) by reflexivity.
  sep_apply (sll_zero 0 l2 H0). Intros. subst l2.
  rewrite app_nil_r. sep_apply sllbseg_0_sll'.
  Intros head_val. Exists head_val. entailer!.
Qed.

Lemma sllbseg_sll: forall x y z l1 l2,
  sllbseg x y l1 ** y # Ptr |-> z ** sll z l2 |--
  EX h: addr, x # Ptr |-> h ** sll h (l1 ++ l2).
Proof.
  intros.
  sep_apply sllbseg_2_sllseg. Intros y'.
  Exists y'. sep_apply sllseg_sll. entailer!.
Qed.

Lemma sllbseg_0_sll_pt: forall x pt l,
  sllbseg x pt l ** pt # Ptr |-> NULL |--
  EX head_val: addr, x # Ptr |-> head_val ** sll_pt head_val pt l.
Proof.
  intros. destruct l; simpl.
  + simpl sllbseg. Intros. subst x.
    Exists NULL. simpl sll_pt. entailer!.
  + simpl sllbseg. Intros head_val.
    Exists head_val. simpl sll_pt. entailer!.
Qed.

(* Append two sllbsegs: used in app_list_box *)
Lemma sllbseg_append_sllbseg: forall x pt1 l1 h2 pt2 a l2,
  h2 <> NULL ->
  sllbseg x pt1 l1 ** 
  pt1 # Ptr |-> h2 ** 
  &(h2 # "sll" ->ₛ "data") # UInt |-> a **
  sllbseg (&(h2 # "sll" ->ₛ "next")) pt2 l2 **
  pt2 # Ptr |-> NULL |--
  sllbseg x pt2 (l1 ++ a :: l2) ** pt2 # Ptr |-> NULL.
Proof.
  intros. revert x. induction l1; simpl; intros.
  + Intros. subst x. Exists h2. entailer!.
  + Intros u. Exists u. sep_apply IHl1. entailer!.
Qed.

(* ================================================================
   Part 5: Lemmas for sllb (conversions between representations)
   ================================================================ *)

(* Unfold sllb to sllbseg form *)
Lemma sllb_2_sllbseg: forall x l,
  sllb x l |--
  EX ptail_val: addr,
    “ x <> NULL ” &&
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    sllbseg (&(x # "sllb" ->ₛ "head")) ptail_val l **
    ptail_val # Ptr |-> NULL.
Proof.
  intros. unfold sllb. destruct l.
  + Exists (&(x # "sllb" ->ₛ "head")).
    simpl sllbseg. entailer!.
  + Intros ptail_val. Exists ptail_val. entailer!.
Qed.

(* Unfold sllb to sll form (loses ptail precision) *)
Lemma sllb_2_sll: forall x l,
  sllb x l |--
  EX head_val ptail_val: addr,
    “ x <> NULL ” &&
    &(x # "sllb" ->ₛ "head") # Ptr |-> head_val **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> ptail_val **
    sll head_val l.
Proof.
  intros. unfold sllb. destruct l.
  + Exists NULL (&(x # "sllb" ->ₛ "head")).
    simpl sll. entailer!.
  + Intros ptail_val. sep_apply sllbseg_0_sll'.
    Intros head_val. Exists head_val ptail_val. entailer!.
Qed.

(* Unfold sllb to sll_pt form (preserves ptail) *)
Lemma sllb_2_sll_pt: forall x l,
  sllb x l |--
  EX h pt: addr,
    “ x <> NULL ” &&
    &(x # "sllb" ->ₛ "head") # Ptr |-> h **
    &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt **
    sll_pt h pt l.
Proof.
  intros. unfold sllb. destruct l; simpl.
  + Exists NULL (&(x # "sllb" ->ₛ "head")).
    simpl sll_pt. entailer!.
  + Intros ptail_val. simpl sllbseg. Intros head_val.
    Exists head_val ptail_val. simpl sll_pt. entailer!.
Qed.

(* Fold sllbseg back to sllb *)
Lemma sllbseg_2_sllb: forall x pt l,
  x <> NULL ->
  &(x # "sllb" ->ₛ "ptail") # Ptr |-> pt **
  sllbseg (&(x # "sllb" ->ₛ "head")) pt l **
  pt # Ptr |-> NULL |--
  sllb x l.
Proof.
  intros. unfold sllb. destruct l.
  + simpl sllbseg. Intros. subst pt. entailer!.
  + Exists pt. entailer!.
Qed.
