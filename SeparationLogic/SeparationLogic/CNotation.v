Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import String.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Import Integers.


Definition NULL : Z := 0.
Definition addr: Type := Z.

Inductive front_end_type: Type :=
  | FET_struct (x: string): front_end_type
  | FET_union (x: string): front_end_type
  | FET_enum (x: string): front_end_type
  | FET_alias (x: string): front_end_type
  | FET_int: front_end_type
  | FET_char : front_end_type
  | FET_int64 : front_end_type
  | FET_short : front_end_type
  | FET_uint: front_end_type
  | FET_uchar : front_end_type
  | FET_uint64 : front_end_type
  | FET_ushort : front_end_type
  | FET_float : front_end_type
  | FET_double : front_end_type
  | FET_ptr: front_end_type.

Inductive rvalue_expr: Type :=
  | RE_const (p: addr) (t: front_end_type): rvalue_expr
  | RE_add_pi (p: rvalue_expr) (i: Z): rvalue_expr
  | RE_sub_pi (p: rvalue_expr) (i: Z): rvalue_expr
  | RE_addr_of (p: lvalue_expr): rvalue_expr
with lvalue_expr: Type :=
  | LE_var (x: string): lvalue_expr
  | LE_arrow_field (p: rvalue_expr) (s: string): lvalue_expr
  | LE_array_subst (p: lvalue_expr) (i: Z): lvalue_expr
  | LE_dot_field (p: lvalue_expr) (s: string): lvalue_expr.

Parameter eval_addr_expr: rvalue_expr -> addr.
Parameter sizeof_struct_type: string -> Z.
Parameter sizeof_union_type: string -> Z.
Parameter sizeof_enum_type: string -> Z.
Parameter sizeof_alias_type: string -> Z.

Definition sizeof_front_end_type (ty : front_end_type) : Z :=
  match ty with
  | FET_struct x => sizeof_struct_type x
  | FET_union x => sizeof_union_type x
  | FET_enum x => sizeof_enum_type x
  | FET_alias x => sizeof_alias_type x
  | FET_int => 4
  | FET_char => 1
  | FET_int64 => 8
  | FET_short => 2
  | FET_uint => 4
  | FET_uchar => 1
  | FET_uint64 => 8
  | FET_ushort => 2
  | FET_float => 4
  | FET_double => 8
  | FET_ptr => 4
  end.

Lemma sizeof_int: sizeof_front_end_type FET_int = 4.
Proof. reflexivity. Qed.

Lemma sizeof_char: sizeof_front_end_type FET_char = 1.
Proof. reflexivity. Qed.

Lemma sizeof_int64: sizeof_front_end_type FET_int64 = 8.
Proof. reflexivity. Qed.

Lemma sizeof_short: sizeof_front_end_type FET_short = 2.
Proof. reflexivity. Qed.

Lemma sizeof_uint: sizeof_front_end_type FET_uint = 4.
Proof. reflexivity. Qed.

Lemma sizeof_uchar: sizeof_front_end_type FET_uchar = 1.
Proof. reflexivity. Qed.

Lemma sizeof_uint64: sizeof_front_end_type FET_uint64 = 8.
Proof. reflexivity. Qed.

Lemma sizeof_ushort: sizeof_front_end_type FET_ushort = 2.
Proof. reflexivity. Qed.

Lemma sizeof_float: sizeof_front_end_type FET_float = 4.
Proof. reflexivity. Qed.

Lemma sizeof_double: sizeof_front_end_type FET_double = 8.
Proof. reflexivity. Qed.

Lemma sizeof_ptr: sizeof_front_end_type FET_ptr = 4.
Proof. reflexivity. Qed.

Global Opaque sizeof_front_end_type.
Declare Custom Entry addr_expr_entry.
Declare Custom Entry lvalue_expr_entry.
Declare Custom Entry rvalue_expr_entry.

Inductive struct_or_union : Type := Struct | Union.

Inductive composite_definition : Type :=
  | Composite (name: string) (su: struct_or_union) (fields: list (string * front_end_type)).

(** it is used to parse the term inside a &( ... ) context *)
Ltac get_lvalue_expr x :=
  match type of x with
  | string => constr:(LE_var x)
  | lvalue_expr => constr:(x)
  end.

Notation "( x )" := x
  (in custom lvalue_expr_entry at level 0,
   x custom rvalue_expr_entry at level 99).

Notation "x" := x
  (in custom lvalue_expr_entry at level 0,
   x constr at level 0).

Notation "( x )" := x
  (in custom rvalue_expr_entry at level 0,
   x constr at level 99).

Notation "x" := x
  (in custom rvalue_expr_entry at level 0,
   x constr at level 0).

Coercion LE_var: string >-> lvalue_expr.

Notation "&( x )" := (eval_addr_expr (RE_addr_of x))
  (at level 0,
   x custom lvalue_expr_entry at level 99,
   only printing).

Notation "&( x )" :=
  (ltac:(let x' := get_lvalue_expr x in exact (eval_addr_expr (RE_addr_of x'))))
  (at level 0,
   x custom lvalue_expr_entry at level 99,
   only parsing).

Notation "p '.ₛ' s" := (LE_dot_field p s)
  (in custom lvalue_expr_entry at level 47,
   p custom lvalue_expr_entry,
   left associativity).

Notation "p '[' i ']'" := (LE_array_subst p i)
  (in custom lvalue_expr_entry at level 47,
   p custom lvalue_expr_entry,
   i constr,
   left associativity).

Notation "p '->ₛ' s" := (LE_arrow_field p s)
  (in custom lvalue_expr_entry at level 46,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p + i" := (RE_add_pi p i)
  (in custom rvalue_expr_entry at level 49,
   p custom rvalue_expr_entry,
   i constr,
   left associativity).

Notation "p - i" := (RE_sub_pi p i)
  (in custom rvalue_expr_entry at level 49,
   p custom rvalue_expr_entry,
   i constr,
   left associativity).

Notation "p # 'INT'" := (RE_const p FET_int)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).
  
Notation "p # 'CHAR'" := (RE_const p FET_char)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'INT64'" := (RE_const p FET_int64)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'SHORT'" := (RE_const p FET_short)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'UINT'" := (RE_const p FET_uint)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).
  
Notation "p # 'UCHAR'" := (RE_const p FET_uchar)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'UINT64'" := (RE_const p FET_uint64)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'USHORT'" := (RE_const p FET_ushort)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'FLOAT'" := (RE_const p FET_float)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'DOUBLE'" := (RE_const p FET_double)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'PTR'" := (RE_const p FET_ptr)
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'struct' s" := (RE_const p (FET_struct s))
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # s" := (RE_const p (FET_alias s))
  (in custom rvalue_expr_entry at level 40,
   p custom rvalue_expr_entry,
   no associativity).

Notation "p # 'INT'" := (RE_const p FET_int)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'CHAR'" := (RE_const p FET_char)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'INT64'" := (RE_const p FET_int64)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'SHORT'" := (RE_const p FET_short)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'UINT'" := (RE_const p FET_uint)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).
  
Notation "p # 'UCHAR'" := (RE_const p FET_uchar)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'UINT64'" := (RE_const p FET_uint64)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'USHORT'" := (RE_const p FET_ushort)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'FLOAT'" := (RE_const p FET_float)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'DOUBLE'" := (RE_const p FET_double)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).
   
Notation "p # 'PTR'" := (RE_const p FET_ptr)
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # 'struct' s" := (RE_const p (FET_struct s))
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "p # s" := (RE_const p (FET_alias s))
  (in custom lvalue_expr_entry at level 40,
   p custom lvalue_expr_entry,
   no associativity).

Notation "&( x )" := (RE_addr_of x)
  (in custom rvalue_expr_entry at level 20,
   x custom lvalue_expr_entry at level 99,
   only printing).

Notation "&( x )" :=
  (ltac:(let x' := get_lvalue_expr x in exact (RE_addr_of x')))
  (in custom rvalue_expr_entry at level 20,
   x custom lvalue_expr_entry at level 99,
   only parsing).

Notation "&( x )" := (RE_addr_of x)
  (in custom lvalue_expr_entry at level 20,
   x custom lvalue_expr_entry at level 99,
   only printing).

Notation "&( x )" :=
  (ltac:(let x' := get_lvalue_expr x in exact (RE_addr_of x')))
  (in custom lvalue_expr_entry at level 20,
   x custom lvalue_expr_entry at level 99,
   only parsing).

(*
Notation "&( s )" := (RE_addr_of (LE_var s))
  (in custom rvalue_expr_entry at level 30,
   s constr,
   no associativity).

Notation "&( s )" := (RE_addr_of (LE_var s))
  (in custom lvalue_expr_entry at level 30,
   s constr,
   no associativity).
*)
Notation "'sizeof' ( 'INT' )" := (sizeof_front_end_type FET_int)
  (at level 1).

Notation "'sizeof' ( 'CHAR' )" := (sizeof_front_end_type FET_char)
  (at level 1).

Notation "'sizeof' ( 'INT64' )" := (sizeof_front_end_type FET_int64)
  (at level 1).

Notation "'sizeof' ( 'SHORT' )" := (sizeof_front_end_type FET_short)
  (at level 1).

Notation "'sizeof' ( 'UINT' )" := (sizeof_front_end_type FET_uint)
  (at level 1).

Notation "'sizeof' ( 'UCHAR' )" := (sizeof_front_end_type FET_uchar)
  (at level 1).

Notation "'sizeof' ( 'UINT64' )" := (sizeof_front_end_type FET_uint64)
  (at level 1).

Notation "'sizeof' ( 'USHORT' )" := (sizeof_front_end_type FET_ushort)
  (at level 1).

Notation "'sizeof' ( 'FLOAT' )" := (sizeof_front_end_type FET_float)
  (at level 1).

Notation "'sizeof' ( 'DOUBLE' )" := (sizeof_front_end_type FET_double)
  (at level 1).

Notation "'sizeof' ( 'PTR' )" := (sizeof_front_end_type FET_ptr)
  (at level 1).

Notation "'sizeof' ( 'struct' s )" := (sizeof_front_end_type (FET_struct s))
  (at level 1).

Notation "'sizeof' ( 'union' s )" := (sizeof_front_end_type (FET_union s))
  (at level 1).

Notation "'sizeof' ( s )" := (sizeof_front_end_type (FET_alias s))
  (at level 1).

Parameter rvalue_expr_equiv : rvalue_expr -> rvalue_expr -> Prop.

Parameter lvalue_expr_equiv : lvalue_expr -> lvalue_expr -> Prop.

Theorem rvalue_expr_equiv_refl: forall x : rvalue_expr, rvalue_expr_equiv x x
with lvalue_expr_equiv_refl: forall x : lvalue_expr, lvalue_expr_equiv x x.
Proof. Admitted.

Theorem rvalue_expr_equiv_sym: forall x y : rvalue_expr, rvalue_expr_equiv x y -> rvalue_expr_equiv y x
with lvalue_expr_equiv_sym: forall x y : lvalue_expr, lvalue_expr_equiv x y -> lvalue_expr_equiv y x.
Proof. Admitted.

Theorem rvalue_expr_equiv_trans: forall x y z : rvalue_expr, rvalue_expr_equiv x y -> rvalue_expr_equiv y z -> rvalue_expr_equiv x z
with lvalue_expr_equiv_trans: forall x y z : lvalue_expr, lvalue_expr_equiv x y -> lvalue_expr_equiv y z -> lvalue_expr_equiv x z.
Proof. Admitted.

Theorem rvalue_expr_equiv_equiv: Equivalence rvalue_expr_equiv.
Proof.
  split ; hnf.
  - apply rvalue_expr_equiv_refl.
  - apply rvalue_expr_equiv_sym.
  - apply rvalue_expr_equiv_trans.
Qed.

Theorem lvalue_expr_equiv_equiv: Equivalence lvalue_expr_equiv.
Proof.
  split ; hnf.
  - apply lvalue_expr_equiv_refl.
  - apply lvalue_expr_equiv_sym.
  - apply lvalue_expr_equiv_trans.
Qed.

#[export] Existing Instance rvalue_expr_equiv_equiv.
#[export] Existing Instance lvalue_expr_equiv_equiv.

Axiom LE_arrow_field_congr:
  Proper (rvalue_expr_equiv ==> eq ==> lvalue_expr_equiv) LE_arrow_field.

Axiom LE_array_subst_congr:
  Proper (lvalue_expr_equiv ==> eq ==> lvalue_expr_equiv) LE_array_subst.

Axiom LE_dot_field_congr:
  Proper (lvalue_expr_equiv ==> eq ==> lvalue_expr_equiv) LE_dot_field.

Axiom RE_add_pi_congr:
  Proper (rvalue_expr_equiv ==> eq ==> rvalue_expr_equiv) RE_add_pi.

Axiom RE_sub_pi_congr:
  Proper (rvalue_expr_equiv ==> eq ==> rvalue_expr_equiv) RE_sub_pi.

Axiom RE_addr_of_congr:
  Proper (lvalue_expr_equiv ==> rvalue_expr_equiv) RE_addr_of.

Axiom eval_addr_expr_congr:
  Proper (rvalue_expr_equiv ==> eq) eval_addr_expr.

#[export] Existing Instance LE_arrow_field_congr.
#[export] Existing Instance LE_array_subst_congr.
#[export] Existing Instance LE_dot_field_congr.
#[export] Existing Instance RE_add_pi_congr.
#[export] Existing Instance RE_sub_pi_congr.
#[export] Existing Instance RE_addr_of_congr.
#[export] Existing Instance eval_addr_expr_congr.

Axiom eval_addr: forall R t,
  rvalue_expr_equiv
    (RE_const (eval_addr_expr R) t) R.


Axiom addr_of_array_subst: forall L x t,
  rvalue_expr_equiv
    (RE_const
      (eval_addr_expr (RE_addr_of L) + x * sizeof_front_end_type t) t)
    (RE_addr_of (LE_array_subst L x)).  

Axiom addr_of_array_subst': forall L x t,
  rvalue_expr_equiv
    (RE_const
      (eval_addr_expr (RE_addr_of L) + sizeof_front_end_type t * x) t)
    (RE_addr_of (LE_array_subst L x)). 

Axiom const_array_pi: forall p x t,
  rvalue_expr_equiv
    (RE_const
      (p + x * sizeof_front_end_type t) t)
    (RE_add_pi (RE_const p t) x).

Axiom const_array_pi': forall p x t,
  rvalue_expr_equiv
    (RE_const
      (p + sizeof_front_end_type t * x) t)
    (RE_add_pi (RE_const p t) x).

Axiom addr_of_arrow_field : forall L x, 
  rvalue_expr_equiv
    (RE_addr_of (LE_dot_field L x))
    (RE_addr_of (LE_arrow_field (RE_addr_of L) x)).

Ltac const_array_simpl :=
  match goal with 
    | |- context [eval_addr_expr (RE_addr_of (LE_arrow_field
(RE_const (Z.add ?g_allQueue (Z.mul ?index (sizeof_front_end_type (FET_alias ?name))))
(FET_alias ?name)) ?field_name))] =>
             let ConstArraySimple := fresh "ConstArraySimple" in
             assert (ConstArraySimple: &( ((g_allQueue + index * sizeof (name))) # name ->ₛ field_name) =
&( ((g_allQueue) # (name) + index) ->ₛ field_name)) ; [ rewrite const_array_pi; reflexivity | rewrite ConstArraySimple; clear ConstArraySimple ]
    | |- context [eval_addr_expr (RE_addr_of (LE_arrow_field
(RE_const (Z.add ?g_allQueue (Z.mul (sizeof_front_end_type (FET_alias ?name)) ?index))
(FET_alias ?name)) ?field_name))] =>
              let ConstArraySimple' := fresh "ConstArraySimple'" in
             assert (ConstArraySimple': &( ((g_allQueue + sizeof (name) * index)) # name ->ₛ field_name) =
&( ((g_allQueue) # (name) + index) ->ₛ field_name)) ; [ rewrite const_array_pi'; reflexivity | rewrite ConstArraySimple'; clear ConstArraySimple' ]
  end.

Ltac csimpl :=
  repeat progress
    rewrite ?eval_addr at 1;
    rewrite ?addr_of_array_subst at 1;
    rewrite ?addr_of_array_subst' at 1;
    rewrite ?addr_of_arrow_field at 1;
    try const_array_simpl.
          
Axiom addr_of_arrow_field_inv : forall x y F, 
  eval_addr_expr (RE_addr_of (LE_arrow_field x F)) = eval_addr_expr (RE_addr_of (LE_arrow_field y F)) -> x = y.
    
Axiom addr_of_LE_var_not_zero : forall x, eval_addr_expr (RE_addr_of (LE_var x)) <> 0.

Axiom RE_add_pi_inv_l : forall x y i, 
  RE_add_pi x i = RE_add_pi y i -> x = y.

Axiom RE_add_pi_inv_r : forall x a b,
  RE_add_pi x a = RE_add_pi x b -> a = b.  

Axiom RE_sub_pi_inv_l : forall x y i, 
  RE_sub_pi x i = RE_sub_pi y i -> x = y.

Axiom RE_sub_pi_inv_r : forall x a b,
  RE_sub_pi x a = RE_sub_pi x b -> a = b.

Module TestNotations.

Local Open Scope string.



Goal forall (p: addr) (q: rvalue_expr),
  p = &((q + 1) ->ₛ "pstPrev").
Abort.

Goal forall (p: addr) (q: rvalue_expr),
  p = &(q ->ₛ "pstPrev").
Abort.

Goal forall (p: addr),
  p = &((p # struct "LOS_DL_LIST") ->ₛ "pstPrev").
Abort.

Goal forall (p: addr),
  p = &(p # struct "LOS_DL_LIST" ->ₛ "pstPrev").
Abort.

Goal forall (p: addr),
  p = &(p # "LOS_DL_LIST" ->ₛ "pstPrev").
Abort.

Goal forall (p: addr),
  p = &(p # "LOS_TaskCB" ->ₛ "readWriteCnt" [ 0 + 1 ] ).
Abort.

(** 这个需要双括号不优美 *)
Goal forall (p: addr),
  p = &(((p + 1)) # "LOS_TaskCB" ->ₛ "readWriteCnt" [ 0 + 1 ] ).
Abort.

Goal forall (p: addr),
  p = &("g_TaskCB").
Abort.

(** 这表示整数加法而不是有类型的加法 *)
Goal forall (p: addr),
  p = &("g_TaskCB") + sizeof("TaskCB") * 1.
Abort.

Goal forall (p: addr),
  p = &("g_X") + sizeof(INT) * 1.
Abort.

Goal forall (p: addr) (n: Z),
  p = &((p # "LOS_DL_LIST" + 1) ->ₛ "pstPrev").
Abort.

Goal forall (p: addr) (n: Z),
  p = &((p # "LOS_DL_LIST" + (1)) ->ₛ "pstPrev").
Abort.

Goal forall (p: addr),
  &(&(p # "TaskCB" ->ₛ "pend_list") ->ₛ "pstPrev") = &(p # "TaskCB" ->ₛ "pend_list" .ₛ "pstPrev").
Proof.
  intros. csimpl. reflexivity.
Qed.

Goal forall (q: addr),
  &(q # "TaskCB" ->ₛ "pend_list" .ₛ "pstPrev") =
  &(&(q # "TaskCB" ->ₛ "pend_list") ->ₛ "pstPrev").
Proof.
  intros.
  csimpl.
  reflexivity.
Qed.

Goal forall (p: addr),
  let q := (p + 10 * sizeof ("TaskCB"))%Z in
  &(q # "TaskCB" ->ₛ "pend_list") =
  &((p # "TaskCB" + 10) ->ₛ "pend_list").
Proof.
  intros.
  subst q.
  csimpl.
  reflexivity.
Qed.


Goal forall (p: addr),
  let q := (p + sizeof ("TaskCB") * 10)%Z in
  &(q # "TaskCB" ->ₛ "pend_list") =
  &((p # "TaskCB" + 10) ->ₛ "pend_list").
Proof.
  intros.
  subst q.
  csimpl.
  reflexivity.
Qed.


Goal forall (p q: addr),
  &(q # "TaskCB" ->ₛ "pend_list") =
  &((p # "TaskCB" + 10) ->ₛ "pend_list") -> 
  q = (p + sizeof ("TaskCB") * 10)%Z.
Proof.
  intros.
  revert H. csimpl. intros.
  apply addr_of_arrow_field_inv in H.
  inversion H.
Qed.

Goal
  let q := eval_addr_expr (RE_addr_of ("x")) in
  &(q # "LOS_TaskCB" ->ₛ "pend_list") =
  &(&("x") ->ₛ "pend_list").
Proof.
  intros; subst q.
  csimpl.
  reflexivity.
Qed.

End TestNotations.
