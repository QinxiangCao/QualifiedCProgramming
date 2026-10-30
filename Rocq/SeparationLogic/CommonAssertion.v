Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Set Warnings "-warn-library-file-stdlib-vector".
Require Coq.Vectors.Vector.
Require Import String.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap Tactics.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Import Coqlib Integers.

From SimpleC.SL Require Import Mem.
From SimpleC.SL Require Export IntLib.
From SimpleC.SL Require Export FloatLib.
From SimpleC.SL Require Export CArch.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CNotation.

Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope list.
Import ListNotations.

Module Type BasePredSig (Import Names: LanguageSig) (Import DerivedNames: DerivedNamesSig Names).
Parameter mstore: addr -> Z -> expr.
Parameter mstore_noninit: addr -> expr.
Axiom mstore_mstore_noninit:
  forall p v s,
    mstore p v s ->
    mstore_noninit p s.

Axiom mstore_eqm:
  forall p v v',
    Byte.eqm v v' ->
    derivable1 (mstore p v) (mstore p v').

Axiom dup_mstore_noninit: 
  forall x,
    derivable1
      (sepcon (mstore_noninit x) (mstore_noninit x))
      (coq_prop False).
End BasePredSig.

Module Type IterSepconLibSig
  (Import Names: LanguageSig)
  (Import DerivedNames: DerivedNamesSig Names)
  (Import Rules: PrimitiveRuleSig Names DerivedNames)
  (Import Theorems: LogicTheoremSig Names DerivedNames Rules).

Local Notation "x |-- y" := (derivable1 x y) (at level 70, no associativity).
Local Notation "x ** y" := (sepcon x y) (at level 31, left associativity).

Lemma iter_sepcon_remove_nth : forall n (l : list expr) d,
  (n < length l)%nat ->
  logic_equiv (iter_sepcon l) (nth n l d ** iter_sepcon (remove_nth n l)).
Proof.
  intros.
  rewrite remove_nth_decomp by exact H.
  rewrite (firstn_skipSn d n l) at 1 by exact H.
  rewrite !logic_equiv_iter_sepcon_app, logic_equiv_iter_sepcon_cons.
  rewrite !logic_equiv_sepcon_assoc.
  rewrite (logic_equiv_sepcon_comm _ (nth n l d)).
  reflexivity.
Qed.

Lemma iter_sepcon_replace_nth : forall n (l : list expr) v,
  (n < length l)%nat ->
  logic_equiv (iter_sepcon (replace_nth n l v)) (v ** iter_sepcon (remove_nth n l)).
Proof.
  intros.
  rewrite replace_nth_decomp by exact H.
  rewrite remove_nth_decomp by exact H.
  rewrite !logic_equiv_iter_sepcon_app, logic_equiv_iter_sepcon_cons.
  rewrite !logic_equiv_sepcon_assoc.
  rewrite (logic_equiv_sepcon_comm _ v).
  reflexivity.
Qed.

Lemma iter_sepcon_split_remove_nth : forall n (l : list expr) d,
  (n < length l)%nat ->
  iter_sepcon l |--
    nth n l d ** iter_sepcon (remove_nth n l).
Proof. intros. rewrite <- iter_sepcon_remove_nth; auto. reflexivity. Qed.

Lemma iter_sepcon_merge_remove_nth : forall n (l : list expr) v,
  (n < length l)%nat ->
  v ** iter_sepcon (remove_nth n l) |--
    iter_sepcon (replace_nth n l v).
Proof. intros. rewrite iter_sepcon_replace_nth; auto. reflexivity. Qed.

Lemma iter_sepcon_split_remove_Znth : forall i (l : list expr) d,
  0 <= i < Zlength l ->
  iter_sepcon l |--
    Znth i l d ** iter_sepcon (remove_Znth i l).
Proof.
  intros.
  unfold Znth, remove_Znth.
  apply iter_sepcon_split_remove_nth.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma iter_sepcon_merge_remove_Znth : forall i (l : list expr) v,
  0 <= i < Zlength l ->
  v ** iter_sepcon (remove_Znth i l) |--
    iter_sepcon (replace_Znth i v l).
Proof.
  intros.
  unfold Znth, remove_Znth, replace_Znth.
  apply iter_sepcon_merge_remove_nth.
  rewrite Zlength_correct in H.
  lia.
Qed.

End IterSepconLibSig.

Module Type SeparationLogicSig :=
  LanguageSig <+
  DerivedNamesSig <+
  PrimitiveRuleSig <+
  LogicTheoremSig' <+
  BasePredSig <+
  IterSepconLibSig.

Definition aligned_2 (x : Z) : Prop := x mod 2 = 0.

Definition aligned_4 (x : Z) : Prop := x mod 4 = 0.

Definition aligned_8 (x : Z) : Prop := x mod 8 = 0.

Module Type DerivedPredSig (ArchImpl : CArchSig) (Endian : CEndianSig) (CRules: SeparationLogicSig).

Arguments CRules.exp {A}.

Local Set Warnings "-notation-overridden".
Include CNotationSig ArchImpl.
Local Set Warnings "notation-overridden".

Include Arch.
Include CEndian Endian.

Ltac unfold_arch :=
  unfold ptr_width_Z, ptr_align, addr_max_unsigned, aligned in *;
  eval_ptr_size;
  cbn in *.

Ltac fold_arch :=
  fold ptr_width_Z ptr_align addr_max_unsigned aligned in *;
  normalize_ptr_size.

Ltac solve_arch :=
  unfold_arch; try reflexivity; try lia.

(* Byte vectors are ordered by increasing address.  Endianness belongs to
   merge_n_bytes, not to the resource recursion. *)
Definition store_byte : addr -> Z -> CRules.expr := CRules.mstore.

Fixpoint store_bytes (x : addr) (n : nat) : Vector.t Z n -> CRules.expr :=
  match n with
  | O => fun _ => CRules.emp
  | S n' => fun bytes =>
      CRules.sepcon (store_byte x (Vector.hd bytes))
        (store_bytes (x + 1) n' (Vector.tl bytes))
  end.

Arguments store_bytes x {n} _.

Definition store_bytes_Z (x : addr) (n : nat) (v : Z) : CRules.expr :=
  CRules.exp (fun bytes : Vector.t Z n =>
    CRules.andp
      (CRules.coq_prop (merge_n_bytes bytes v))
      (store_bytes x bytes)).

Definition undef_store_byte : addr -> CRules.expr := CRules.mstore_noninit.

Fixpoint undef_store_bytes (x : addr) (n : nat) : CRules.expr :=
  match n with
  | O => CRules.emp
  | S n' => CRules.sepcon (undef_store_byte x) (undef_store_bytes (x + 1) n')
  end.

(* The following are notations *)  
Declare Scope sac_scope.
Delimit Scope sac_scope with sac.
Local Open Scope sac_scope.

Notation "'emp'" := (CRules.emp) : sac_scope.
Notation "x |-- y" := (CRules.derivable1 x y) (at level 70, no associativity) : sac_scope.
Notation "x --||-- y" := (CRules.logic_equiv x y) (at level 60, no associativity) : sac_scope.
Notation "x -* y" := (CRules.wand x y) (at level 45, right associativity) : sac_scope.
Notation "x --> y" := (CRules.impp x y) : sac_scope.
Notation "x || y" := (CRules.orp x y) : sac_scope.
Notation "x && y" := (CRules.andp x y) : sac_scope.
Notation "x ** y" := (CRules.sepcon x y) (at level 31, left associativity) : sac_scope.
Notation " “ P ” " := (CRules.coq_prop P) (at level 29, no associativity) :sac_scope.
Notation " 'TT' " := (CRules.truep) (at level 34, no associativity) : sac_scope.
Notation "'EX' x , p " :=
  (CRules.exp (fun x => p))
    (at level 45, x binder, right associativity) : sac_scope. 
Notation "'EX' x : t , p " :=
  (CRules.exp (fun x : t => p))
    (at level 45, x binder, right associativity) : sac_scope.
Notation "'EX' x .. y , p" :=
  (CRules.exp (fun x => .. (CRules.exp (fun y => p)) ..))
    (at level 45, x binder, right associativity) : sac_scope.
Notation "'ALL' x , p " :=
  (CRules.allp _ (fun x => p))
    (at level 45, x binder, right associativity) : sac_scope. 
Notation "'ALL' x : t , p " :=
  (CRules.allp _ (fun x : t => p))
    (at level 45, x binder, right associativity) : sac_scope.
Notation "'ALL' x .. y , p" :=
  (CRules.allp _ (fun x => .. (CRules.allp _ (fun y => p)) ..))
    (at level 45, x binder, right associativity) : sac_scope.

(* Widths are byte counts.  Positivity belongs to lemmas that need it,
   not to the storage predicates.  At width zero the signed value range
   is empty; the unsigned range contains only zero. *)
Definition valid_signed_value (n : nat) (v : Z) : Prop :=
  - 2 ^ (8 * Z.of_nat n - 1) <= v < 2 ^ (8 * Z.of_nat n - 1).

Definition valid_unsigned_value (n : nat) (v : Z) : Prop :=
  0 <= v < 2 ^ (8 * Z.of_nat n).

Definition store_integer (n : nat) (align : Z) (x : addr) (v : Z) :=
  “ valid_object x (Z.of_nat n) align /\ valid_signed_value n v ” &&
  store_bytes_Z x n v.

Definition store_uinteger (n : nat) (align : Z) (x : addr) (v : Z) :=
  “ valid_object x (Z.of_nat n) align /\ valid_unsigned_value n v ” &&
  store_bytes_Z x n v.

Definition undef_store_integer (n : nat) (align : Z) (x : addr) :=
  “ valid_object x (Z.of_nat n) align ” && undef_store_bytes x n.

(* Readable fixed-width interfaces; all storage proofs use the generic core. *)
Definition store_char := store_integer 1 1.
Definition store_uchar := store_uinteger 1 1.
Definition store_short := store_integer 2 2.
Definition store_ushort := store_uinteger 2 2.
Definition store_int := store_integer 4 4.
Definition store_uint := store_uinteger 4 4.
Definition store_int64 := store_integer 8 4.
Definition store_uint64 := store_uinteger 8 4.
Definition store_int128 := store_integer 16 4.
Definition store_uint128 := store_uinteger 16 4.

Definition undef_store_char := undef_store_integer 1 1.
Definition undef_store_uchar := undef_store_integer 1 1.
Definition undef_store_short := undef_store_integer 2 2.
Definition undef_store_ushort := undef_store_integer 2 2.
Definition undef_store_int := undef_store_integer 4 4.
Definition undef_store_uint := undef_store_integer 4 4.
Definition undef_store_int64 := undef_store_integer 8 4.
Definition undef_store_uint64 := undef_store_integer 8 4.
Definition undef_store_int128 := undef_store_integer 16 4.
Definition undef_store_uint128 := undef_store_integer 16 4.

Definition store_bool (x : addr) (v : Z) :=
  CRules.andp
    (CRules.coq_prop ((valid_object x (sizeof(CHAR)) 1) /\ (v = 0 \/ v = 1)))
    (store_byte x v).

Definition undef_store_bool (x : addr) :=
  CRules.andp (CRules.coq_prop ((valid_object x (sizeof(CHAR)) 1))) (undef_store_byte x).

Definition store_float (x : addr) (v : fp32) :=
  match bits_of_float_value v with
  | Some z =>
      “ (valid_object x (sizeof(FLOAT)) 4) /\ 0 <= z <= Int.max_unsigned ” && store_bytes_Z x 4 z
  | None =>
      “ False ”
  end.

Definition store_double (x : addr) (v : fp64) :=
  match bits_of_double_value v with
  | Some z =>
      “ (valid_object x (sizeof(DOUBLE)) 8) /\ 0 <= z <= Int64.max_unsigned ” && store_bytes_Z x 8 z
  | None =>
      “ False ”
  end.

Definition store_long_double (x : addr) (v : fp128) :=
  match bits_of_long_double_value v with
  | Some z =>
      CRules.andp
        (CRules.coq_prop ((valid_object x (sizeof(LONGDOUBLE)) 8) /\ 0 <= z <= max_unsigned_128))
        (store_bytes_Z x 16 z)
  | None =>
      CRules.coq_prop False
  end.

Definition undef_store_float (x : addr) :=
  “ (valid_object x (sizeof(FLOAT)) 4) ” && undef_store_bytes x 4.

Definition undef_store_double (x : addr) :=
  “ (valid_object x (sizeof(DOUBLE)) 8) ” && undef_store_bytes x 8.

Definition undef_store_long_double (x : addr) :=
  CRules.andp (CRules.coq_prop ((valid_object x (sizeof(LONGDOUBLE)) 8))) (undef_store_bytes x 16).

Definition undef_store_finite_float : addr -> CRules.expr :=
  undef_store_float.

Definition undef_store_finite_double : addr -> CRules.expr :=
  undef_store_double.

Definition undef_store_finite_long_double : addr -> CRules.expr :=
  undef_store_long_double.

Definition store_ptr (x : addr) (v : Z) :=
  “ (valid_object x (sizeof(PTR)) Arch.ptr_align) /\ valid_ptr_value v ” &&
  store_bytes_Z x (Z.to_nat (sizeof(PTR))) v.

Definition undef_store_ptr (x : addr) :=
  “ (valid_object x (sizeof(PTR)) Arch.ptr_align) ” &&
  undef_store_bytes x (Z.to_nat (sizeof(PTR))).

Definition Invalid_store {A : Type} (x : addr) (v : A) :=
  “ False ”.

Definition Invalid_undef_store (x : addr) :=
  “ False ”.

Definition dup_data_at_error (x : addr) := 
  “ False ”.

Definition dup_data_at_error_prop : Prop := True.

Fixpoint store_array_rec {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (lo hi: Z) (l: list A): CRules.expr :=
  match l with
  | nil     => “ lo = hi ” && “ l = nil ” && emp
  | a :: l0 => storeA x lo a ** store_array_rec storeA x (lo + 1) hi l0
  end.

Fixpoint store_array_missing_i_rec {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (i lo hi: Z) (l: list A): CRules.expr :=
  match l with
  | nil     => “ False ”
  | a :: l0 => “ i = lo ” && store_array_rec storeA x (lo + 1) hi l0 ||
               “ i > lo ” && storeA x lo a ** store_array_missing_i_rec storeA x i (lo + 1) hi l0
  end.

Definition store_array {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (n: Z) (l: list A): CRules.expr :=
  store_array_rec storeA x 0 n l.

Fixpoint store_undef_array_rec (storeA : addr -> Z -> CRules.expr) (x: addr) (lo hi: Z) (n: nat): CRules.expr :=
  match n with 
    | O => “ lo = hi ” && emp 
    | S n' => storeA x lo ** store_undef_array_rec storeA x (lo + 1) hi n'
  end.

Fixpoint store_undef_array_missing_i_rec (storeA : addr -> Z -> CRules.expr) (x: addr) (i lo hi: Z) (n: nat): CRules.expr :=
  match n with 
    | O => “ False ”
    | S n' => “ i = lo ” && store_undef_array_rec storeA x (lo + 1) hi n' ||
               “ i > lo ” && storeA x lo ** store_undef_array_missing_i_rec storeA x i (lo + 1) hi n'
  end.

Definition store_undef_array (storeA : addr -> Z -> CRules.expr) (x: addr) (n: Z): CRules.expr :=
  store_undef_array_rec storeA x 0 n (Z.to_nat n).

Fixpoint store_align4_list (l : list Z) := 
  match l with 
    | nil => emp
    | x :: l' => “ (valid_object x (sizeof(INT)) 4) ” && undef_store_bytes x 4 ** store_align4_list l'
  end.

Definition store_align4_n (n : Z) :=
  EX l, “ Zlength l = n /\ interval_list 3 0 addr_max_unsigned l ” && store_align4_list l.

Fixpoint store_align_list (l : list Z) := 
  match l with 
    | nil => emp
    | x :: l' => “ (valid_object x (sizeof(CHAR)) 1) ” && undef_store_byte x ** store_align_list l'
  end.

Definition store_align_n (n : Z) :=
  EX l, “ Zlength l = n /\ interval_list 0 0 addr_max_unsigned l ” && store_align_list l.

Definition front_end_type_value (ty : front_end_type) : Type :=
  match ty with
  | FET_float => fp32
  | FET_double => fp64
  | FET_long_double => fp128
  | _ => Z
  end.

Definition poly_store (ty : front_end_type) :
  addr -> front_end_type_value ty -> CRules.expr :=
  match ty as ty0 return addr -> front_end_type_value ty0 -> CRules.expr with
    | FET_bool => store_bool
    | FET_char => store_char
    | FET_uchar => store_uchar
    | FET_short => store_short
    | FET_ushort => store_ushort
    | FET_int => store_int
    | FET_uint => store_uint
    | FET_int64 => store_int64
    | FET_uint64 => store_uint64
    | FET_int128 => store_int128
    | FET_uint128 => store_uint128
    | FET_float => store_float
    | FET_double => store_double
    | FET_long_double => store_long_double
    | FET_ptr => store_ptr
    | _ => @Invalid_store Z
  end.


Definition store_finite_float (x : addr) (v : fp32) :=
  “ fp32_isFinite v ” && store_float x v.

Definition store_finite_double (x : addr) (v : fp64) :=
  “ fp64_isFinite v ” && store_double x v.

Definition store_finite_long_double (x : addr) (v : fp128) :=
  CRules.andp (CRules.coq_prop (fp128_isFinite v)) (store_long_double x v).

Definition poly_undef_store (ty : front_end_type) := 
  match ty with 
    | FET_bool => undef_store_bool 
    | FET_char => undef_store_char
    | FET_uchar => undef_store_uchar
    | FET_short => undef_store_short
    | FET_ushort => undef_store_ushort
    | FET_int => undef_store_int
    | FET_uint => undef_store_uint
    | FET_int64 => undef_store_int64
    | FET_uint64 => undef_store_uint64
    | FET_int128 => undef_store_int128
    | FET_uint128 => undef_store_uint128
    | FET_float => undef_store_float
    | FET_double => undef_store_double
    | FET_long_double => undef_store_long_double
    | FET_ptr => undef_store_ptr
    | _ => Invalid_undef_store
  end.


Notation "x # 'Char' |-> v" := (store_char x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'Bool' |-> v" := (store_bool x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'UChar' |-> v" := (store_uchar x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'Short' |-> v" := (store_short x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'UShort' |-> v" := (store_ushort x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'Int' |-> v" := (store_int x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'UInt' |-> v" := (store_uint x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'Int64' |-> v" := (store_int64 x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'UInt64' |-> v" := (store_uint64 x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'Int128' |-> v" := (store_int128 x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'UInt128' |-> v" := (store_uint128 x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'Float' |-> v" := (store_float x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'Double' |-> v" := (store_double x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'LongDouble' |-> v" := (store_long_double x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'FiniteFloat' |-> v" := (store_finite_float x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'FiniteDouble' |-> v" := (store_finite_double x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'FiniteLongDouble' |-> v" := (store_finite_long_double x v) (at level 25, no associativity) : sac_scope.
Notation "x # 'Ptr' |-> v" := (store_ptr x v) (at level 25, no associativity) : sac_scope.

Notation " x # 'Char' |->_" := (undef_store_char x) (at level 25, no associativity) : sac_scope.
Notation "x # 'Bool' |->_" := (undef_store_bool x) (at level 25, no associativity) : sac_scope.
Notation "x # 'UChar' |->_" := (undef_store_uchar x) (at level 25, no associativity) : sac_scope.
Notation "x # 'Short' |->_" := (undef_store_short x) (at level 25, no associativity) : sac_scope.
Notation "x # 'UShort' |->_" := (undef_store_ushort x) (at level 25, no associativity) : sac_scope.
Notation "x # 'Int' |->_" := (undef_store_int x) (at level 25, no associativity) : sac_scope.
Notation "x # 'UInt' |->_" := (undef_store_uint x) (at level 25, no associativity) : sac_scope.
Notation "x # 'Int64' |->_" := (undef_store_int64 x) (at level 25, no associativity) : sac_scope.
Notation "x # 'UInt64' |->_" := (undef_store_uint64 x) (at level 25, no associativity) : sac_scope.
Notation "x # 'Int128' |->_" := (undef_store_int128 x) (at level 25, no associativity) : sac_scope.
Notation "x # 'UInt128' |->_" := (undef_store_uint128 x) (at level 25, no associativity) : sac_scope.
Notation "x # 'Float' |->_" := (undef_store_float x) (at level 25, no associativity) : sac_scope.
Notation "x # 'Double' |->_" := (undef_store_double x) (at level 25, no associativity) : sac_scope.
Notation "x # 'LongDouble' |->_" := (undef_store_long_double x) (at level 25, no associativity) : sac_scope.
Notation "x # 'FiniteFloat' |->_" := (undef_store_finite_float x) (at level 25, no associativity) : sac_scope.
Notation "x # 'FiniteDouble' |->_" := (undef_store_finite_double x) (at level 25, no associativity) : sac_scope.
Notation "x # 'FiniteLongDouble' |->_" := (undef_store_finite_long_double x) (at level 25, no associativity) : sac_scope.
Notation "x # 'Ptr' |->_" := (undef_store_ptr x) (at level 25, no associativity) : sac_scope.

Notation "x # ty |-> v" := (poly_store ty x v) (at level 25, no associativity) : sac_scope.
Notation "x # ty |->_" := (poly_undef_store ty x) (at level 25, no associativity) : sac_scope.

(*TODO: to be rewrite *)
Definition struct_padding (x : lvalue_expr) (struct_name : string) : CRules.expr := emp.

Definition union_padding (x : lvalue_expr) (union_name field_name : string) : CRules.expr := emp.

Notation " 'Padding' x struct_name " := (struct_padding x struct_name) (at level 25, no associativity) : sac_scope.

Notation " 'Padding' x union_name . field_name " := (union_padding x union_name field_name) (at level 25, no associativity) : sac_scope.

Import CRules.

(* The following are derived rules *)

Arguments derivable1s_exp_l {A} _ _ _ .
Arguments derivable1s_allp_r {A} _ _ _ .
Arguments derivable1s_exp_r {A} _ _ _ .
Arguments derivable1s_allp_l {A} _ _ _ .

Lemma coq_prop_andp_left : forall (P : Prop) (Q R : expr), (P -> Q |-- R) -> “ P ” && Q |-- R.
Proof.
  unfold andp, coq_prop, derivable1 ; intros. apply H ; tauto.
Qed.

Lemma coq_prop_andp_right : forall (P : Prop) (Q R : expr), R |-- Q -> P -> R |-- “ P ” && Q.
Proof.
  unfold andp, coq_prop, derivable1 ; intros.
  specialize (H m). tauto.
Qed.

Lemma coq_prop_imply : forall (P Q : Prop), (P -> Q) -> “ P ” |-- “ Q ”.
Proof.
  intros.
  unfold coq_prop, derivable1 ; intros ; tauto.
Qed.

Lemma coq_prop_False_left : forall (P : Prop) Q, (P -> False) -> “ P ” |-- Q.
Proof.
  intros.
  unfold coq_prop, derivable1 ; intros ; tauto.
Qed.

Lemma orp_sepcon_left : forall P Q R, (P || Q) ** R |-- (P ** R) || (Q ** R).
Proof.
  intros.
  unfold orp, sepcon, derivable1; intros.
  my_destruct H.
  - left. exists x ,x0. tauto.
  - right. exists x, x0. tauto.
Qed. 

Lemma orp_sepcon_right : forall P Q R, P ** (Q || R) |-- (P ** Q) || (P ** R).
Proof.
  intros.
  unfold orp, sepcon, derivable1; intros.
  my_destruct H.
  - left. exists x ,x0. tauto.
  - right. exists x, x0. tauto.
Qed.

Lemma orp_sepcon_left' : forall P Q R, (P ** R) || (Q ** R) |-- (P || Q) ** R.
Proof.
  intros.
  unfold orp, sepcon, derivable1; intros.
  my_destruct H.
  - exists x ,x0. tauto.
  - exists x, x0. tauto.
Qed. 

Lemma orp_sepcon_right' : forall P Q R, (P ** Q) || (P ** R) |-- P ** (Q || R).
Proof.
  intros.
  unfold orp, sepcon, derivable1; intros.
  my_destruct H.
  - exists x ,x0. tauto.
  - exists x, x0. tauto.
Qed.

Lemma orp_sepcon_left_equiv : forall P Q R, (P || Q) ** R --||-- (P ** R) || (Q ** R).
Proof.
  intros.
  split ; [apply orp_sepcon_left | apply orp_sepcon_left'].
Qed.

Lemma orp_sepcon_right_equiv : forall P Q R, P ** (Q || R) --||-- (P ** Q) || (P ** R).
Proof.
  intros.
  split ; [apply orp_sepcon_right | apply orp_sepcon_right'].
Qed.

Lemma exp_right_exists : forall {A: Type} P (Q: A -> expr),
 (exists x, P |-- Q x) -> P |-- EX x, Q x.
Proof.
  unfold derivable1, exp;intros.
  destruct H.
  eexists. intuition auto. Qed.

Lemma derivable1_imp : forall P Q st, P |-- Q ->  P st -> Q st.
Proof.
  unfold derivable1; intros.
  intuition auto.
Qed.

Lemma derivable1_andp_mono : forall x1 x2 y1 y2 : expr, x1 |-- x2 -> y1 |-- y2 -> x1 && y1 |-- x2 && y2.
Proof.
  unfold derivable1, andp; intros * H H0 * [? ?].
  split;intuition auto.
Qed.

Lemma ex_logic_equiv_andp:
  forall {A : Type} (P : A -> expr) (Q :  expr),
  (EX y, P y) && Q  --||-- EX x : A, P x && Q.
Proof.
  unfold andp, logic_equiv, exp, derivable1;split;intros;my_destruct H ; eauto.
Qed.

Lemma wand_equiv : forall P Q P' Q',
  P --||-- P' ->
  Q --||-- Q' ->
  P -* Q --||-- P' -* Q'.
Proof.
  unfold wand, logic_equiv, derivable1 in *.
  split; intros; destruct H, H0.
  specialize (H1 _ _ H2).
  apply H0, H1, H4, H3.
  specialize (H1 _ _ H2).
  apply H5, H1, H, H3.
Qed.

Lemma ex_logic_equiv_sepcon:
  forall {A : Type} (P : A -> expr) (Q : expr),
  (EX y, P y) ** Q  --||-- EX x : A, P x ** Q.
Proof.
  unfold sepcon, logic_equiv, exp, derivable1;split;intros;my_destruct H.
  - do 3 eexists. split; eauto.
  - do 2 eexists. split;eauto.
Qed.

Lemma prop_add_left : forall P Q, P |-- “ Q ” -> P --||-- “ Q ” && P.
Proof.
  unfold coq_prop, logic_equiv, derivable1, andp ; intros.
  split ; try tauto ; split ; auto.
  eapply H. eauto.
Qed.

Lemma truep_andp_left_equiv : forall P, TT && P --||-- P.
Proof.
  intros.
  unfold logic_equiv, andp, truep, derivable1; split; intros ; tauto.
Qed.

Lemma truep_andp_right_equiv : forall P, P && TT --||-- P.
Proof.
  intros.
  unfold logic_equiv, andp, truep, derivable1; split; intros ; tauto.
Qed.

Lemma sepcon_emp_equiv : 
  forall x, x ** emp --||-- x.
Proof.
  intros. split.
  apply derivable1_sepcon_emp_l.
  apply derivable1_sepcon_emp_r.
Qed.

Lemma sepcon_cancel_res_emp : 
  forall P Q, emp |-- Q -> P |-- P ** Q.
Proof.
  intros.
  rewrite <- sepcon_emp_equiv at 1.
  apply derivable1_sepcon_mono.
  apply derivable1_refl.
  auto.
Qed.

Lemma sepcon_cancel_end : 
  forall P Q R, P |-- R -> emp |-- Q -> P |-- R ** Q.
Proof.
  intros.
  rewrite <- sepcon_emp_equiv at 1.
  apply derivable1_sepcon_mono ; auto.
Qed.

Lemma sepcon_prop_equiv : 
forall P Q,
P ** (“ Q ”) --||-- “ Q ” && P ** TT.
Proof.
  unfold logic_equiv, sepcon, andp, truep, coq_prop, derivable1;
  split;intros.
  - my_destruct H.
    split ; auto.
    do 2 eexists. split;eauto.
  - my_destruct H.
    do 2 eexists. split;eauto.
Qed.

Lemma exp_exp_right: forall {A: Type} P (Q : A -> expr),
  (exists x, P |-- Q x) -> 
  P |-- EX x, Q x.
Proof.
  intros.
  unfold exp, derivable1 in *.
  destruct H. intros.
  exists x. auto.
Qed.

Lemma exp_allp_left: forall {A: Type} (P: A -> expr) Q,
  (exists x, P x |-- Q) -> 
  ALL x, P x|-- Q.
Proof.
  intros.
  unfold exp, allp, derivable1 in *.
  destruct H. intros. auto.
Qed.

Lemma exp_allp_swap: forall {A B : Type} (P : A -> B -> expr), EX x, ALL y, P x y |-- ALL y, EX x, P x y.
Proof.
  intros.
  unfold exp, allp, derivable1; intros.
  destruct H. exists x. auto.
Qed.

Lemma allp_allp_swap: forall {A B : Type} (P : A -> B -> expr), ALL x, ALL y, P x y |-- ALL y, ALL x, P x y.
Proof.
  intros.
  unfold exp, allp, derivable1; intros.
  auto.
Qed.

Definition derivable1_wand_sepcon_adjoint := derivable1s_wand_sepcon_adjoint.

(* The following are ltac to simplify proof *)

Ltac set_String_name :=
  repeat progress match goal with 
    | |- context [FET_alias ?string_name] =>
        match string_name with
          | String _ _ => 
            let name := fresh "s" in
              set (name := string_name) in *
        end
    | |- context [FET_struct ?string_name] =>
        match string_name with
          | String _ _ => 
            let name := fresh "s" in
              set (name := string_name) in *
        end
    | |- context [FET_union ?string_name] =>
        match string_name with
          | String _ _ => 
            let name := fresh "s" in
              set (name := string_name) in *
        end
    | |- context [FET_enum ?string_name] =>
        match string_name with
          | String _ _ => 
            let name := fresh "s" in
              set (name := string_name) in *
        end
    | |- context [LE_var ?string_name] =>
        match string_name with
          | String _ _ => 
            let name := fresh "s" in
              set (name := string_name) in *
        end
    | |- context [LE_arrow_field _ ?string_name] =>
        match string_name with
          | String _ _ => 
            let name := fresh "s" in
              set (name := string_name) in *
        end
    | |- context [LE_dot_field _ ?string_name] =>
        match string_name with
          | String _ _ => 
            let name := fresh "s" in
              set (name := string_name) in *
        end
  end.

Ltac subst_all_strings :=
  repeat progress match goal with
    | x := ?v |- _ =>
        match type of v with
        | string => subst x
        end
  end.

Inductive all_list : Type :=
  | norm_asrt : expr -> all_list
  | dependent_asrt : forall (A : Type), (A -> expr) -> all_list.

Ltac All_listasrts_rec P L :=
  match P with 
  | ?A ** ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in 
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A && ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A -* ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A || ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | @exp ?t ?A => constr:(cons (dependent_asrt t A) L)
  | @allp ?t ?A => constr:(L)
  | TT => constr:(L)
  | emp => constr:(L)
  | ?x => constr:(cons (norm_asrt x) L)
  end.

Ltac All_listasrts P :=
  let l:= (All_listasrts_rec P (@nil all_list)) in 
  constr:(l).

Ltac Rename_rec l Tac :=
  match l with 
  | nil => Tac 
  | ?x :: ?l' => 
    let a := fresh "v" in
    match x with 
      | norm_asrt (“ ?B ”) => pose (a := B) ; change B with a
      | norm_asrt ?v => pose (a := v) ; change v with a
      | dependent_asrt _ ?B => pose (a := B) ; change B with a
    end; Rename_rec l' Tac ; subst a
  end. 

Ltac Rename Tac:= 
  match goal with 
  | |- ?P |-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      Rename_rec l Tac
  | |- ?P --||-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      Rename_rec l Tac
  | _ => idtac 
  end.

Ltac pure_Rename_rec l :=
  match l with 
  | nil => idtac 
  | ?x :: ?l' => 
    let a := fresh "v" in
    match x with 
      | norm_asrt (“ ?B ”) => pose (a := B) ; change B with a
      | norm_asrt ?v => pose (a := v) ; change v with a
      | dependent_asrt _ ?B => pose (a := B) ; change B with a
    end; pure_Rename_rec l'
  end. 

Ltac pure_Rename := 
  match goal with 
  | |- ?P |-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      pure_Rename_rec l
  end.

Ltac sepcon_lift'' p :=
  match goal with 
  | |- ?P |-- ?Q  => match Q with 
                    | context [?x ** p] => rewrite (logic_equiv_sepcon_comm x p) 
                    | context [?x ** (p ** ?y) ] => rewrite (logic_equiv_sepcon_swap x p y) 
                    end
  | |- ?P |-- ?Q  => match P with 
                    | context [?x ** p] => rewrite (logic_equiv_sepcon_comm x p) 
                    | context [?x ** (p ** ?y) ] => rewrite (logic_equiv_sepcon_swap x p y) 
                    end
  end.

Ltac sepcon_lift' p := sepcon_lift'' p ;
  repeat progress (sepcon_lift'' p).

Ltac find_lift x Hp :=
  match Hp with 
  | ?A && ?B => find_lift x A
  | ?A && ?B => find_lift x B
  | ?A ** ?B => find_lift x A
  | ?A ** ?B => find_lift x B
  | ?P => match P with 
          | x => sepcon_lift' P 
          end
  end. 

Ltac sepcon_contains x P :=
  lazymatch P with
  | ?A ** ?B =>
      first
        [ sepcon_contains x A
        | sepcon_contains x B
        ]
  | ?P => constr_eq P x
  end.

Ltac sepcon_lift p :=
  match goal with 
  | |- ?P |-- ?Q => find_lift p P
  | |- _ => idtac end;
  match goal with 
  | |- ?P |-- ?Q => find_lift p Q 
  | |- _ => idtac 
  end.

Ltac derivable1_refl_tac := apply (derivable1_refl _).

Ltac sepcon_cancel' P := 
  match P with 
  | ?x ** ?P' =>
    first [
      (* Try to cancel x *)
      match goal with 
      | |- x ** P' |-- x ** _ =>
        eapply derivable1_sepcon_mono; [derivable1_refl_tac | ];
        sepcon_cancel' P'
      | |- _ |-- ?Q =>
        sepcon_contains x Q;
        sepcon_lift x;
        eapply derivable1_sepcon_mono; [derivable1_refl_tac | ];
        sepcon_cancel' P'
      end
    | (* Search in P' for something to cancel *)
      sepcon_cancel' P'
    ]
  | ?x => match goal with
          | |- _ |-- ?Q => sepcon_contains x Q
          end;
          sepcon_lift x;
          match goal with
            | |- x |-- x => derivable1_refl_tac
            | |- x ** ?P |-- x ** _  => eapply derivable1_sepcon_mono ; [derivable1_refl_tac | ]
            | |- x |-- x ** _ => eapply sepcon_cancel_res_emp 
          end 
  | _ => idtac
   end.

Ltac sepcon_cancel := 
  match goal with 
  | |- ?x |-- ?x => derivable1_refl_tac
  | |- ?x ** _ |-- ?x ** _ => eapply derivable1_sepcon_mono ; [derivable1_refl_tac | ];sepcon_cancel 
  | |- ?P |-- EX _ , _ => idtac 
  | |- ?P |-- _ => sepcon_cancel' P 
  end.

Ltac TT_simpl := repeat rewrite truep_andp_left_equiv; repeat rewrite truep_andp_right_equiv.

Ltac andp_assoc_change := 
  repeat progress match goal with 
  | |- context [ (?P && ?Q) && ?R ] => rewrite (logic_equiv_andp_assoc P Q R)
  end.

Ltac sepcon_assoc_change :=
  repeat progress match goal with 
    | |- context [ ?P ** ?Q ** ?R ] => rewrite <- (logic_equiv_sepcon_assoc P Q R)
  end.

Ltac sepcon_assoc_change_in H :=
  repeat progress match type of H with
    | context [ ?P ** ?Q ** ?R ] => rewrite <- (logic_equiv_sepcon_assoc P Q R) in H
  end.

Ltac coq_prop_lift :=
  repeat progress match goal with 
  | |- context [ (“ ?P ” && ?Q) ** ?R ] => rewrite (logic_equiv_coq_prop_andp_sepcon P Q R)
  | |- context [ ?P ** (“ ?Q ” && ?R) ] => rewrite (logic_equiv_sepcon_coq_prop_andp P Q R)
  | |- context [ ?P ** “ ?Q ” ] => rewrite (sepcon_prop_equiv P Q)
  end.

Ltac asrt_easysimpl := TT_simpl; andp_assoc_change; coq_prop_lift.

Ltac andp_lift'' p :=
  match goal with 
  | |- ?P |-- ?Q  => match Q with 
                    | context [?x && p] => rewrite (logic_equiv_andp_comm x p) 
                    | context [?x && (p && ?y) ] => rewrite (logic_equiv_andp_swap x p y) 
                    | context [?x && p ** ?q ] => rewrite (logic_equiv_andp_comm x (p ** q)) 
                    | context [?x && (p ** ?q  && ?y) ] => rewrite (logic_equiv_andp_swap x (p ** q) y) 
                    end
  | |- ?P |-- ?Q  => match P with 
                    | context [?x && p] => rewrite (logic_equiv_andp_comm x p) 
                    | context [?x && (p && ?y) ] => rewrite (logic_equiv_andp_swap x p y) 
                    | context [?x && p ** ?q ] => rewrite (logic_equiv_andp_comm x (p ** q)) 
                    | context [?x && (p ** ?q  && ?y) ] => rewrite (logic_equiv_andp_swap x (p ** q) y) 
                    end
  end.

Ltac andp_lift' p := andp_lift'' p ;
  repeat progress (andp_lift'' p).
  
Ltac andp_lift p := asrt_easysimpl; try (sepcon_lift p);
match goal with 
  | |- ?P |-- ?Q => andp_lift' p
end.

Ltac asrt_complex_simpl :=
  repeat progress match goal with 
    | |- context [ (_ ** _ ) && ?P ] => andp_lift P
    | |- context [ ?P ** emp ] => rewrite (sepcon_emp_equiv P)
    | |- context [ emp ** ?P ] => rewrite (logic_equiv_sepcon_comm emp P); rewrite (sepcon_emp_equiv P)
    | |- context [( “ ?B ” && ?Q) && ?R] => rewrite (logic_equiv_andp_assoc (“ B ”) Q R )
    | |- context [( “ ?B ” && ?Q) ** ?R] => rewrite (logic_equiv_coq_prop_andp_sepcon B Q R )
    | |- context [( ?P && “ ?B ”) && ?R] => 
      rewrite (logic_equiv_andp_comm P (“ B ”)) ;
      rewrite (logic_equiv_andp_assoc (“ B ”) P R)
    | |- context [( ?P && “ ?B ”) ** ?R] =>
      rewrite (logic_equiv_andp_comm P (“ B ”)) ; 
      rewrite (logic_equiv_coq_prop_andp_sepcon B P R )
    | |- context [?P ** (“ ?B ” && ?R)] => rewrite (logic_equiv_sepcon_coq_prop_andp P B R)
    | |- context [?P ** (“ ?B ”) ] => rewrite (sepcon_prop_equiv P B)
    | |- context [(“ ?B ”) ** ?P ] => rewrite (logic_equiv_sepcon_comm (“ B ”) P)
    | |- context [ (@exp ?t ?P) && ?Q ] => rewrite (ex_logic_equiv_andp _ Q)
    | |- context [ (@exp ?t ?P) ** ?Q ] => rewrite (ex_logic_equiv_sepcon _ Q)
    | |- context [ @exp ?t ?P ] => try andp_lift (@exp t P) ; try sepcon_lift (@exp t P)
    | |- context [ (?P || ?Q) ** ?R ] => rewrite (orp_sepcon_left P Q R)
    | |- context [ ?P ** (?Q || ?R) ] => rewrite (orp_sepcon_right P Q R)
    end.

Ltac asrt_simpl_pure := normalize_ptr_size; asrt_easysimpl; asrt_complex_simpl.

Ltac asrt_simpl := Rename asrt_simpl_pure.

Ltac andp_cancel' P := 
  match P with 
  | ?x && ?P' => andp_lift x;eapply derivable1_andp_mono ; [derivable1_refl_tac | ];
                andp_cancel' P'
  | ?x && ?P' => andp_cancel' P'
  | ?x => apply (derivable1_refl x) ||  eapply (derivable1_andp_elim1 x) ||  (eapply (derivable1_andp_elim2 _ x)) || sepcon_cancel
  end.

Ltac andp_cancel'' :=
  match goal with 
  | |- ?x |-- ?x => derivable1_refl_tac 
  | |- ?x && _ |-- ?x && _ => eapply derivable1_andp_mono ; [derivable1_refl_tac | ];andp_cancel''
  | |- _ |-- ?P => andp_cancel' P
  end.

Ltac solve_auto B := 
  solve [try subst B ; auto] || idtac.

Ltac andp_cancel := asrt_simpl_pure;
    match goal with 
   | |- ?P |-- ?Q || ?R => idtac 
   | |- ?P || ?Q |-- ?R => idtac
   | |- ?P |-- ?Q =>  match P with 
                      | context [ “ ?B ”] => try andp_lift ( “ B ”); eapply coq_prop_andp_left; intros; andp_cancel
                      end
   | |- ?P |-- ?Q  => match Q with 
                      | context [ “ ?B ”] => try andp_lift ( “ B ”); simple eapply (coq_prop_andp_right);[  andp_cancel | solve_auto B ]
                      end
   | |- “ False ” |-- ?Q => apply derivables_false_coq_prop ; auto
   | |- “ ?P ” |-- “ ?Q ” => apply coq_prop_imply ; solve_auto Q
   | |- _ |-- “ ?Q ” => apply (derivable1s_coq_prop_r Q); solve_auto Q
   | |- “ ?P ” |-- ?Q => eapply derivable1s_coq_prop_l; intros; andp_cancel
   | |- _ |-- TT => apply derivable1_truep_intros ; auto
   | |- _ => andp_cancel''
    end.

Ltac pureIntros_without_rename := asrt_simpl_pure;
repeat progress (match goal with 
| |- ?P |-- ?Q => (match P with 
                    | context [ “ ?B ”] => apply (coq_prop_andp_left B); intros
                  end)
end) ; sepcon_assoc_change .

Ltac pureIntros := Rename pureIntros_without_rename.

(* Match the assertion connective before applying its rule.  An unrestricted
   [eapply] can unfold derivable1 and match the whole goal against [Q m]. *)
Ltac apply_exp_left :=
  lazymatch goal with
  | |- @exp ?T ?P |-- ?Q =>
      refine (@derivable1s_exp_l T P Q _)
  end.

Ltac apply_allp_right :=
  lazymatch goal with
  | |- ?P |-- @allp ?T ?Q =>
      refine (@derivable1s_allp_r T P Q _)
  end.

Ltac left_intro v:=
  asrt_simpl;
  apply_exp_left;
  intro v.

Ltac left_intro_any:=
  asrt_simpl;
  apply_exp_left;
  intros .

Ltac right_intro v:=
  asrt_simpl;
  apply_allp_right;
  intro v.

Ltac right_intro_any:=
  asrt_simpl;
  apply_allp_right;
  intros.

Ltac reexists :=
  match goal with 
    | |- ?P |-- (@exp ?T ?Q) => eapply exp_exp_right
    | _ => eapply exp_exp_right
  end.

Ltac rexists v:=
  match goal with 
    | |- ?P |-- (@exp ?T ?Q) => refine (@derivable1s_exp_r T _ _ v _)
    | _ => refine (derivable1s_exp_r _ _ v _)
  end.

Ltac lexists v :=
  match goal with 
  | |- exists _, _ => exists v
  | |- @allp ?T ?P |-- _ => refine (@derivable1s_allp_l T _ _ v _)
  | _ => refine (derivable1s_allp_l _ _ v _) 
  end.
  

Ltac simpl_auto_with tac :=
  solve [auto | tac].

Ltac simpl_auto :=
  simpl_auto_with ltac:(lia || nia || int_auto).

Ltac simpl_entail_with tac := match goal with
  | |- ?Q /\ ?R => split; [simpl_entail_with tac | simpl_entail_with tac]
  | |- _ => simpl_auto_with tac || idtac
  end.

Ltac simpl_entail :=
  simpl_entail_with ltac:(lia || nia || int_auto).

Ltac entailer_pure := asrt_simpl_pure; sepcon_assoc_change; andp_cancel.

Ltac entailer_with tac :=
  set_String_name;
  Rename entailer_pure;
  simpl_entail_with tac;
  subst_all_strings.

Tactic Notation "cancel" := set_String_name ; Rename sepcon_cancel ; subst_all_strings.
Tactic Notation "entailer!" := entailer_with ltac:(lia || nia || int_auto).
Ltac _Intros xs :=
  set_String_name;
  pureIntros;
  ltac1_list_iter ltac:(fun x => left_intro x) xs;
  pureIntros;
  subst_all_strings.

Tactic Notation "Intros" := set_String_name ; pureIntros ; subst_all_strings.
Tactic Notation "Intros" ne_simple_intropattern_list(xs) := _Intros xs.
Tactic Notation "Intro_any" := set_String_name ; pureIntros ; left_intro_any ; pureIntros ; subst_all_strings.
Ltac _Intros_r xs :=
  set_String_name;
  ltac1_list_iter ltac:(fun x => right_intro x) xs;
  pureIntros;
  subst_all_strings.

Tactic Notation "Intros_r" := set_String_name ; pureIntros ; subst_all_strings.
Tactic Notation "Intros_r" ne_simple_intropattern_list(xs) := _Intros_r xs.
Tactic Notation "Intros_r_any" := set_String_name ; right_intro_any; pureIntros; subst_all_strings.

Tactic Notation "eExists" := set_String_name ; asrt_simpl; reexists ; eexists ; subst_all_strings.
Ltac _Exists xs :=
  set_String_name;
  ltac1_list_iter ltac:(fun x => asrt_simpl; rexists x) xs;
  subst_all_strings.

Tactic Notation "Exists" := set_String_name ; asrt_simpl ; subst_all_strings.
Tactic Notation "Exists" ne_uconstr_list(xs) := _Exists xs.
Ltac _Exists_l xs :=
  set_String_name;
  ltac1_list_iter ltac:(fun x => asrt_simpl; lexists x) xs;
  subst_all_strings.

Tactic Notation "Exists_l" := set_String_name ; asrt_simpl ; subst_all_strings.
Tactic Notation "Exists_l" ne_uconstr_list(xs) := _Exists_l xs.
Tactic Notation "normalize"  := set_String_name ; asrt_simpl ; subst_all_strings.

Tactic Notation "Left" := set_String_name ; rewrite <- derivable1_orp_intros1 ; subst_all_strings.
Tactic Notation "Right" := set_String_name ; rewrite <- derivable1_orp_intros2 ; subst_all_strings.
Tactic Notation "Split" := 
  set_String_name ;
  repeat rewrite orp_sepcon_left_equiv;
  repeat rewrite orp_sepcon_right_equiv;
  apply derivable1_orp_elim ; 
  subst_all_strings.

Notation "'Assertion'" := (expr) (at level 1).

Ltac L_sepcon_lift'' p :=
  match goal with 
  | |- ?P |-- ?Q  => match P with 
                    | context [?x ** p] => rewrite (logic_equiv_sepcon_comm x p) 
                    | context [?x ** (p ** ?y) ] => rewrite (logic_equiv_sepcon_swap x p y) 
                    end
  end.

Ltac L_sepcon_lift' p := L_sepcon_lift'' p ;
  repeat progress (L_sepcon_lift'' p).

Ltac sep_lift_L_aux L :=
  match L with 
  | nil => idtac 
  | cons ?p ?l' => try (L_sepcon_lift' p); sep_lift_L_aux l'
  end.

Ltac sep_lift_L L :=
  let revl := eval cbn [List.rev List.app] in (List.rev L) in sep_lift_L_aux revl.

Ltac sep_apply_L L h:=
  let n := eval compute in (List.length L) in 
  match n with 
  | O => fail "nil list"
  | _ => asrt_simpl; sep_lift_L L; try rewrite !derivable1_sepcon_assoc1; rewrite h
  end.

Ltac prop_rewrite h:= rewrite (prop_add_left _ _ h) at 1.

Ltac prop_apply_L L h:=
  let n := eval compute in (List.length L) in 
  match n with 
  | O => fail "nil list"
  | _ => asrt_simpl; sep_lift_L L; try rewrite !derivable1_sepcon_assoc1; prop_rewrite h
  end.

Ltac unify_asrt x Q :=
  match Q with 
  | ?A ** ?B => (unify_asrt x A)
  | ?A ** ?B => unify_asrt x B
  | ?y => unify x y
  end.

Ltac unify_asrts P Q :=
  match P with 
  | ?A ** ?B => (unify_asrts A Q); (unify_asrts B Q)
  | ?x => unify_asrt x Q 
  end.


Ltac unify_prewithgoal  P :=
  match goal with 
  | |- ?Q  |-- _ => unify_asrts P Q 
  end.

Ltac  sepconlistasrts_rec P L :=
  match P with 
  | ?A ** ?B => let L1  :=  (sepconlistasrts_rec A (@nil expr)) in 
                let L2 :=  (sepconlistasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?x => constr:(cons x L)
  end.

Ltac sepconlistasrts P :=
  let l:= (sepconlistasrts_rec P (@nil expr)) in 
  constr:(l).

Ltac sep_apply H :=
  (let h:= fresh "Hlemma" in pose proof H as h;
   set_String_name;
  let rec find_lemmapre_rec h :=
   (lazymatch type of h with
  | forall x:?T, _ => lazymatch type of T with
                      | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                      | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                              find_lemmapre_rec h
                      end
  | ?T -> _ => lazymatch type of T with
                | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                      find_lemmapre_rec h
                end
  | ?P |-- ?Q => unify_prewithgoal P;
                  match type of h with 
                  | ?P |-- _ =>  let L:= (sepconlistasrts P) in sep_apply_L L h;clear  h
                  end
  | ?P --||-- ?Q => find_lemmapre_rec (P |-- Q)
  end) in find_lemmapre_rec h) ; sepcon_assoc_change ; subst_all_strings.

Ltac prop_apply H :=
  (let h:= fresh "Hlemma" in pose proof H as h;
    set_String_name;
  try repeat rewrite <- logic_equiv_coq_prop_and in h;
  let rec find_lemmapre_rec h :=
   (lazymatch type of h with
  | forall x:?T, _ => lazymatch type of T with
                      | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                      | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                              find_lemmapre_rec h
                      end
  | ?T -> _ => lazymatch type of T with
                | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                      find_lemmapre_rec h
                end
  | ?P |-- “ ?Q ” => unify_prewithgoal P;
                  match type of h with 
                  | ?P |-- _ =>  let L:= (sepconlistasrts P) in prop_apply_L L h;clear  h
                  end
  end) in find_lemmapre_rec h) ; sepcon_assoc_change ; subst_all_strings.
    
Ltac Unfold :=
match goal with
  | |- ?P => try unfold P
end.

Ltac Intros_R'' :=
match goal with
  | |- _ |-- ALL p _ , _ => Intros_r p
end.

Ltac Intros_R' :=
match goal with
  | |- _ |-- ALL p , _ => Intros_r p
end.

Ltac Intros_R :=
try (repeat progress Intros_R''); try Intros_R'.

Ltac apply_sepcon_adjoint :=
match goal with
  | |- ?P |-- ?Q -* ?R => destruct (derivable1s_wand_sepcon_adjoint P Q R) as [H_wand_currying H_wand_decurrying];
                          apply H_wand_currying; clear H_wand_currying H_wand_decurrying
end.

Lemma sepcon_emp_logic_equiv' : forall x : Assertion, emp ** x --||-- x.
intros. split ; entailer!.
Qed.

Ltac elim_emp :=
repeat progress (try (rewrite sepcon_emp_equiv || rewrite sepcon_emp_logic_equiv')).

Lemma elim_wand_emp_emp : emp --||-- emp -* emp.
Proof.
  split.
  - apply derivable1s_wand_sepcon_adjoint. elim_emp. apply derivable1_refl.
  - rewrite <- logic_equiv_sepcon_emp.
    apply derivable1_wand_elim1.
Qed.

Ltac wand_elim := 
  repeat progress (
    try rewrite <- elim_wand_emp_emp;
    elim_emp;
    try apply_sepcon_adjoint;
    try Intros_R
  ).

Ltac pre_process_pure :=
  pureIntros_without_rename ;
  wand_elim;
  asrt_simpl_pure.

Ltac LLM_pre_process_tac tac :=
  try Unfold;
  match goal with 
    | |-  _ \/ _ => left 
    | _ => idtac
  end;
  intros;
  cbn [poly_store poly_undef_store];
  Rename pre_process_pure ;
  try (solve [entailer_with tac]).

Tactic Notation "LLM_pre_process" tactic(tac) := LLM_pre_process_tac tac.

Ltac pre_process :=
  LLM_pre_process_tac ltac:(lia || nia || int_auto).

Tactic Notation "pre_process_default" := pre_process.

(* ========== LLM-friendly tactics ========== *)

Notation "a '+::' b" := (a ++ (b :: nil)) (at level 19) : list_scope.

(* ----- Goal decomposition and pure export ----- *)

Lemma dump_spatial_left : forall P Q, Q -> P |-- “ Q ”.
Proof.
  intros. easy.
Qed.

Ltac dump_pre_spatial :=
  apply dump_spatial_left.

Lemma split_pure_and_spatial_goals : forall P pure spatial,
  P |-- spatial -> P |-- pure -> P |-- pure && spatial.
Proof.
  intros. unfold andp, derivable1 in *. intros. split; auto.
Qed.

Ltac _assert_pure t :=
  lazymatch t with
  | “ _ ” => idtac
  | ?A && ?B => _assert_pure A; _assert_pure B
  | _ => fail "not pure: RHS contains non-“ _ ” parts"
  end.

Ltac _assert_no_pure t :=
  lazymatch t with
  | “ _ ” => fail "spatial part contains a pure “ _ ”"
  | ?A ** ?B => _assert_no_pure A; _assert_no_pure B
  | ?A && ?B => _assert_no_pure A; _assert_no_pure B
  | _ => idtac
  end.

Ltac split_pure_spatial :=
  normalize;
  asrt_simpl_pure;
  try repeat rewrite <- logic_equiv_andp_assoc;
  match goal with
  | |- _ |-- (?A && ?B) =>
      first
      [ _assert_pure A; _assert_no_pure B; apply split_pure_and_spatial_goals
      | _assert_pure B; _assert_no_pure A;
        rewrite (logic_equiv_andp_comm A B) at 1;
        apply split_pure_and_spatial_goals
      ]
  | |- _ => fail "split_pure_spatial: RHS must be (pure && spatial) or (spatial && pure)"
  end.

Lemma _derivable1_andp_intros : forall P A B,
  P |-- A -> P |-- B -> P |-- A && B.
Proof.
  unfold derivable1, andp; auto.
Qed.

Ltac split_pures :=
  asrt_simpl_pure;
  repeat progress rewrite <- logic_equiv_andp_assoc;
  repeat match goal with
  | |- _ |-- ?A && ?B =>
      _assert_pure A;
      _assert_pure B;
      apply _derivable1_andp_intros
  end.

Ltac split_pure_and_solve :=
  split_pures;
  try solve [dump_pre_spatial; auto].

Ltac subst_eqs :=
  repeat first
    [ progress subst
    | match goal with
      | H : @eq (list _)   (_ :: _) (_ :: _) |- _ => injection H; clear H; intros
      | H : @eq (list _)   nil      (_ :: _) |- _ => discriminate H
      | H : @eq (list _)   (_ :: _) nil      |- _ => discriminate H
      | H : @eq (prod _ _) (_ , _)  (_ , _)  |- _ => injection H; clear H; intros
      | H : @eq (option _) (Some _) (Some _) |- _ => injection H; clear H; intros
      | H : @eq (option _) None     (Some _) |- _ => discriminate H
      | H : @eq (option _) (Some _) None     |- _ => discriminate H
      end ].

(* ----- Pure facts from the precondition ----- *)

Tactic Notation "Intros_p" simple_intropattern(x) :=
  asrt_simpl_pure;
  lazymatch goal with
  | |- ?P |-- ?Q =>
      lazymatch P with
      | context [ “ ?B ” ] =>
          apply (coq_prop_andp_left B);
          intro x
      | _ => fail 1 "Intros_p: no pure “ _ ” on the left"
      end
  | _ => fail "Intros_p: goal is not an entailment"
  end.

Lemma add_pure_split : forall (P : Prop) (C F : expr) ,
  C |-- “ P ” ->
  (“ P ” && C) |-- F ->
  C |-- F.
Proof.
  unfold derivable1, andp, coq_prop; firstorder.
Qed.

(* Internal helper used by atomic lemma application. *)
Tactic Notation "add_pure" constr(p) "as" ident(H) :=
  apply (add_pure_split p); [ | Intros_p H ].

(* ----- Targeted cancellation on the spatial precondition ----- *)

Ltac same_asrt x p :=
  first
  [ constr_eq x p; idtac
  | tryif unify x p then idtac else fail 1
  ].

Lemma sepcon_cancel_lhs_emp :
  forall P Q, Q |-- emp -> P ** Q |-- P.
Proof.
  intros.
  rewrite <- (sepcon_emp_equiv P) at 2.
  eapply derivable1_sepcon_mono; [derivable1_refl_tac | ].
  exact H.
Qed.

Ltac sepcon_cancel1_p' p P :=
  lazymatch P with
  | ?x ** ?P' =>
      first
      [ same_asrt x p;
        lazymatch goal with
        | |- x ** P' |-- x ** _ =>
            eapply derivable1_sepcon_mono; [derivable1_refl_tac | ];
            idtac
        | |- x ** P' |-- x =>
            eapply sepcon_cancel_lhs_emp;
            idtac
        | |- _ |-- ?Q =>
            sepcon_contains x Q; sepcon_lift x;
            eapply derivable1_sepcon_mono; [derivable1_refl_tac | ];
            idtac
        end
      | sepcon_cancel1_p' p P'
      ]
  | ?x =>
      first
      [ same_asrt x p;
        sepcon_lift x;
        first
        [ lazymatch goal with
          | |- x |-- x => derivable1_refl_tac
          | |- x ** ?P0 |-- x ** _ =>
              eapply derivable1_sepcon_mono; [derivable1_refl_tac | ]
          | |- x ** ?P0 |-- x =>
              eapply sepcon_cancel_lhs_emp
          | |- x |-- x ** _ =>
              eapply sepcon_cancel_res_emp
          end
        | idtac ]
      | idtac ]
  | _ => idtac
  end.

Ltac sepcon_cancel1_p p :=
  lazymatch goal with
  | |- ?x ** _ |-- ?y ** _ =>
      first
      [ same_asrt x p;
        eapply derivable1_sepcon_mono; [derivable1_refl_tac | ]; idtac
      | lazymatch goal with
        | |- ?P |-- _ => sepcon_cancel1_p' p P
        end
      ]
  | |- ?x ** _ |-- ?y =>
      first
      [ same_asrt x p;
        eapply sepcon_cancel_lhs_emp; idtac
      | lazymatch goal with
        | |- ?P |-- _ => sepcon_cancel1_p' p P
        end
      ]
  | |- ?P |-- EX _, _ => idtac
  | |- ?P |-- _ => sepcon_cancel1_p' p P
  end.

Ltac cancel_exactly1_or_fail p :=
  progress (sepcon_cancel1_p p)
  || fail 1 "cancel: failed to find the specified predicate on either side; no cancellation was performed.".

Ltac sepcon_right_assoc :=
  repeat progress sepcon_assoc_change.

Tactic Notation "cancel" uconstr(p) :=
  normalize_ptr_size; sepcon_right_assoc; cancel_exactly1_or_fail p.

(* ----- Lemma application on spatial goals ----- *)

Ltac sep_apply_l_aux H :=
  let t := constr:(H) in
  lazymatch type of t with
  | ?P0 |-- ?Q0 =>
      unify_prewithgoal P0;
      let L := (sepconlistasrts P0) in
      sep_apply_L L t; sepcon_assoc_change
  | ?P0 --||-- ?Q0 =>
      let ent := constr:(proj1 t) in
      unify_prewithgoal P0;
      let L := (sepconlistasrts P0) in
      sep_apply_L L ent; sepcon_assoc_change
  | _ =>
      fail 1 "sep_apply_l: The lemma is not an entailment; please instantiate all non-Prop parameters"
  end.

Ltac R_sepcon_lift'' p :=
  match goal with
  | |- ?P |-- ?Q =>
      lazymatch Q with
      | context [?x ** p]         => rewrite (logic_equiv_sepcon_comm x p)
      | context [?x ** (p ** ?y)] => rewrite (logic_equiv_sepcon_swap x p y)
      | _ => idtac
      end
  end.

Ltac R_sepcon_lift' p := R_sepcon_lift'' p; repeat progress (R_sepcon_lift'' p).

Ltac R_andp_lift'' p :=
  match goal with
  | |- ?P |-- ?Q =>
      lazymatch Q with
      | context [?x && p]               => rewrite (logic_equiv_andp_comm x p)
      | context [?x && (p && ?y)]       => rewrite (logic_equiv_andp_swap x p y)
      | context [?x && p ** ?q]         => rewrite (logic_equiv_andp_comm x (p ** q))
      | context [?x && (p ** ?q && ?y)] => rewrite (logic_equiv_andp_swap x (p ** q) y)
      | _ => idtac
      end
  end.

Ltac R_andp_lift' p := R_andp_lift'' p; repeat progress (R_andp_lift'' p).

Ltac _sep_apply_r_oneway t :=
  lazymatch type of t with
  | ?Q1 |-- ?Q2 =>
      asrt_simpl_pure;
      first
      [ lazymatch goal with
        | |- ?P |-- ?RHS =>
            same_asrt RHS Q2;
            eapply derivable1_trans with (y := Q1); [ idtac | exact t ]
        end
      | R_sepcon_lift' Q2;
        lazymatch goal with
        | |- ?P |-- (?Q2' ** ?R) =>
            tryif unify Q2' Q2 then idtac else fail 1 "sep_apply_r: Internal unification failed";
            eapply derivable1_trans with (y := Q1 ** R);
            [ idtac
            | eapply derivable1_sepcon_mono; [ exact t | derivable1_refl_tac ] ]
        | |- ?P |-- ?RHS' =>
            fail 1 "sep_apply_r: Internal pattern matching failed"
        end
      | R_andp_lift' Q2;
        lazymatch goal with
        | |- ?P |-- (?Q2' && ?R) =>
            tryif unify Q2' Q2 then idtac else fail 1 "sep_apply_r: Internal unification failed";
            eapply derivable1_trans with (y := Q1 && R);
            [ idtac
            | eapply derivable1_andp_mono; [ exact t | derivable1_refl_tac ] ]
        | |- ?P |-- ?RHS' =>
            fail 1 "sep_apply_r: Internal pattern matching failed"
        end
      ]
      || fail 1 "sep_apply_r: The lemma's right-hand side does not appear in the goal's conclusion"
  | _ => fail 1 "sep_apply_r: The lemma is not an entailment; please instantiate all non-Prop parameters"
  end.

Ltac sep_apply_r_aux H :=
  lazymatch type of H with
  | ?Q1 |-- ?Q2 =>
      _sep_apply_r_oneway H
  | ?Q1 --||-- ?Q2 =>
      _sep_apply_r_oneway (proj1 H)
  | _ =>
      fail 1 "sep_apply_r: The lemma is not an entailment; please instantiate all non-Prop parameters"
  end.

Ltac prop_apply_p H :=
  lazymatch type of H with
  | ?P0 |-- “ ?Q0 ” =>
      unify_prewithgoal P0;
      let L := (sepconlistasrts P0) in
      prop_apply_L L H; sepcon_assoc_change
  | ?P0 --||-- “ ?Q0 ” =>
      unify_prewithgoal P0;
      let L := (sepconlistasrts P0) in
      prop_apply_L L (proj1 H); sepcon_assoc_change
  | _ =>
      fail 1 "prop_apply_p: Please instantiate parameters and premises until the lemma has the shape P |-- “ Q ” (or P --||-- “ Q ”)."
  end.

Ltac _try_sep_apply_r t := sep_apply_r_aux t.
Ltac _try_sep_apply_l t := sep_apply_l_aux t.

Ltac _consume_props_with_subgoal t k :=
  lazymatch type of t with
  | forall (x : ?T), ?Rest =>
      lazymatch type of T with
      | Prop =>
          let Hp := fresh "Hp" in
          add_pure T as Hp;
          [
          | lazymatch goal with
            | [ H : T |- _ ] =>
                let t' := constr:(t H) in
                let t'' := eval cbv beta in t' in
                _consume_props_with_subgoal t'' ltac:(fun tf => k tf)
            | _ =>
                fail 1 "_consume_props_with_subgoal: failed to recover the introduced Prop premise"
            end
          ]
      | _ =>
          k t
      end
  | ?T -> ?Rest =>
      lazymatch type of T with
      | Prop =>
          let Hp := fresh "Hp" in
          add_pure T as Hp;
          [
          | lazymatch goal with
            | [ H : T |- _ ] =>
                let t' := constr:(t H) in
                let t'' := eval cbv beta in t' in
                _consume_props_with_subgoal t'' ltac:(fun tf => k tf)
            | _ =>
                fail 1 "_consume_props_with_subgoal: failed to recover the introduced Prop premise"
            end
          ]
      | _ =>
          k t
      end
  | _ => k t
  end.

Tactic Notation "sep_apply_l_atomic" uconstr(t) :=
  _consume_props_with_subgoal t ltac:(fun tfin =>
    _try_sep_apply_l tfin).

Tactic Notation "sep_apply_r_atomic" uconstr(t) :=
  _consume_props_with_subgoal t ltac:(fun tfin =>
    _try_sep_apply_r tfin).

Ltac sep_apply_left H :=
  (let h := fresh "Hlemma" in pose proof H as h;
   set_String_name;
   let rec find_lemmapre_rec h :=
     lazymatch type of h with
     | forall x : ?T, _ =>
         lazymatch type of T with
         | Prop =>
             let H' := fresh "H" in
             cut T; [ intro H'; specialize (h H'); find_lemmapre_rec h | ]
         | _ =>
             let _x := fresh "_x" in
             evar (_x : T); specialize (h _x); subst _x;
             find_lemmapre_rec h
         end
     | ?T -> _ =>
         lazymatch type of T with
         | Prop =>
             let H' := fresh "H" in
             cut T; [ intro H'; specialize (h H'); find_lemmapre_rec h | ]
         | _ =>
             let _x := fresh "_x" in
             evar (_x : T); specialize (h _x); subst _x;
             find_lemmapre_rec h
         end
     | ?P |-- ?Q => sep_apply_l_aux h; clear h
     | ?P --||-- ?Q => find_lemmapre_rec (P |-- Q)
     end in
   find_lemmapre_rec h);
  sepcon_assoc_change;
  subst_all_strings.

Ltac sep_apply_right H :=
  (let h := fresh "Hlemma" in pose proof H as h;
   set_String_name;
   let rec find_lemmapre_rec h :=
     lazymatch type of h with
     | forall x : ?T, _ =>
         lazymatch type of T with
         | Prop =>
             let H' := fresh "H" in
             cut T; [ intro H'; specialize (h H'); find_lemmapre_rec h | ]
         | _ =>
             let _x := fresh "_x" in
             evar (_x : T); specialize (h _x); subst _x;
             find_lemmapre_rec h
         end
     | ?T -> _ =>
         lazymatch type of T with
         | Prop =>
             let H' := fresh "H" in
             cut T; [ intro H'; specialize (h H'); find_lemmapre_rec h | ]
         | _ =>
             let _x := fresh "_x" in
             evar (_x : T); specialize (h _x); subst _x;
             find_lemmapre_rec h
         end
     | ?P |-- ?Q => sep_apply_r_aux h; clear h
     | ?P --||-- ?Q => find_lemmapre_rec (P |-- Q)
     end in
   find_lemmapre_rec h);
  subst_all_strings.

Ltac aggressive_pre_process :=
  try Unfold;
  match goal with 
    | |-  _ \/ _ => right
    | _ => idtac
  end;
  intros;
  Rename pre_process_pure ;
  repeat (split_pure_spatial || split_pures);
  try match goal with
      | |- emp |-- “ _ ” => dump_pre_spatial
      | |- emp |-- emp => cancel
      end;
  try solve [cancel].

(* Normalise sepcon associativity in the instantiated lemma so that split-goal
   conclusions can match the goal with exact, avoiding a full sep_apply. *)
Ltac Goal_apply_finish H :=
  let H_inst := fresh "H_goal_inst" in
  pose proof H as H_inst;
  repeat rewrite truep_andp_left_equiv in H_inst;
  repeat rewrite truep_andp_right_equiv in H_inst;
  sepcon_assoc_change_in H_inst;
  first [ exact H_inst | sep_apply H_inst; entailer! ].

Ltac Goal_apply_used H used :=
  lazymatch type of H with
  | forall x : ?A, _ =>
      first
        [ match reverse goal with
          | h : A |- _ =>
              lazymatch used with
              | context[h] => fail
              | _ => Goal_apply_used (H h) (h, used)
              end
          end
        | Goal_apply_finish H ]
  | _ => Goal_apply_finish H
  end.

Ltac Goal_apply H := 
  pose proof H as H_goal;
  match type of H_goal with
  | ?P => try unfold P in H_goal
  end;
  once (Goal_apply_used H_goal tt);
  match goal with
  | |- _ => fail 1 "Goal_apply: greedy instantiation did not completely solve the goal; use explicit sep_apply/exact with manually supplied parameters"
  end.
  
End DerivedPredSig.
