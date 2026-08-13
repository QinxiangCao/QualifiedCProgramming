import AUXLib.SetoidRewrite

namespace SimpleC.SL.CNotation

open AUXLib

def NULL : Int := 0

abbrev addr : Type := Int

inductive front_end_type : Type where
  | FET_struct (x : String)
  | FET_union (x : String)
  | FET_enum (x : String)
  | FET_alias (x : String)
  | FET_int
  | FET_char
  | FET_int64
  | FET_short
  | FET_uint
  | FET_uchar
  | FET_uint64
  | FET_ushort
  | FET_ptr

export front_end_type
  (FET_struct FET_union FET_enum FET_alias FET_int FET_char FET_int64 FET_short
   FET_uint FET_uchar FET_uint64 FET_ushort FET_ptr)

mutual
  inductive rvalue_expr : Type where
    | RE_const (p : addr) (t : front_end_type)
    | RE_add_pi (p : rvalue_expr) (i : Int)
    | RE_sub_pi (p : rvalue_expr) (i : Int)
    | RE_addr_of (p : lvalue_expr)

  inductive lvalue_expr : Type where
    | LE_var (x : String)
    | LE_arrow_field (p : rvalue_expr) (s : String)
    | LE_array_subst (p : lvalue_expr) (i : Int)
    | LE_dot_field (p : lvalue_expr) (s : String)
end

export rvalue_expr (RE_const RE_add_pi RE_sub_pi RE_addr_of)
export lvalue_expr (LE_var LE_arrow_field LE_array_subst LE_dot_field)

axiom eval_addr_expr : rvalue_expr -> addr
axiom sizeof_front_end_type : front_end_type -> Int

axiom sizeof_int : sizeof_front_end_type FET_int = 4
axiom sizeof_char : sizeof_front_end_type FET_char = 1
axiom sizeof_int64 : sizeof_front_end_type FET_int64 = 8
axiom sizeof_short : sizeof_front_end_type FET_short = 2
axiom sizeof_uint : sizeof_front_end_type FET_uint = 4
axiom sizeof_uchar : sizeof_front_end_type FET_uchar = 1
axiom sizeof_uint64 : sizeof_front_end_type FET_uint64 = 8
axiom sizeof_ushort : sizeof_front_end_type FET_ushort = 2
axiom sizeof_ptr : sizeof_front_end_type FET_ptr = 4

inductive struct_or_union : Type where
  | Struct
  | Union

export struct_or_union (Struct Union)

inductive composite_definition : Type where
  | Composite (name : String) (su : struct_or_union)
      (fields : List (String × front_end_type))

export composite_definition (Composite)

instance : Coe String lvalue_expr where
  coe := LE_var

@[reducible] def get_lvalue_expr (x : lvalue_expr) : lvalue_expr := x

class addr_notation_result (A : Type) where
  from_lvalue : lvalue_expr -> A

@[default_instance]
noncomputable instance : addr_notation_result addr where
  from_lvalue x := eval_addr_expr (RE_addr_of x)

instance : addr_notation_result rvalue_expr where
  from_lvalue := RE_addr_of

@[reducible] noncomputable def addr_notation {A : Type} [addr_notation_result A]
    (x : lvalue_expr) : A :=
  addr_notation_result.from_lvalue (get_lvalue_expr x)

end SimpleC.SL.CNotation

namespace SimpleC

open SL.CNotation

scoped notation:max "&(" x ")" => addr_notation x

scoped notation:47 p:47 " .ₛ " s:max => LE_dot_field p s
scoped notation:47 p:47 "[" i "]" => LE_array_subst p i
scoped notation:46 p:47 " ->ₛ " s:max "[" i "]" =>
  LE_array_subst (LE_arrow_field p s) i
scoped notation:46 p:47 " ->ₛ " s:max => LE_arrow_field p s

scoped macro:46 p:term:47 " ->ₛ " s:str "[" i:term "]" : term =>
  `(LE_array_subst (LE_arrow_field $p $s) $i)

scoped macro:46 p:term:47 " ->ₛ " s:str " .ₛ " f:term:max : term =>
  `(LE_dot_field (LE_arrow_field $p $s) $f)

scoped instance : HAdd rvalue_expr Int rvalue_expr where
  hAdd := RE_add_pi

scoped instance : HSub rvalue_expr Int rvalue_expr where
  hSub := RE_sub_pi

scoped instance : HAdd rvalue_expr Nat rvalue_expr where
  hAdd p i := RE_add_pi p (Int.ofNat i)

scoped instance : HSub rvalue_expr Nat rvalue_expr where
  hSub p i := RE_sub_pi p (Int.ofNat i)

scoped notation:70 p:71 " # " "INT" => RE_const p FET_int
scoped notation:70 p:71 " # " "CHAR" => RE_const p FET_char
scoped notation:70 p:71 " # " "INT64" => RE_const p FET_int64
scoped notation:70 p:71 " # " "SHORT" => RE_const p FET_short
scoped notation:70 p:71 " # " "UINT" => RE_const p FET_uint
scoped notation:70 p:71 " # " "UCHAR" => RE_const p FET_uchar
scoped notation:70 p:71 " # " "UINT64" => RE_const p FET_uint64
scoped notation:70 p:71 " # " "USHORT" => RE_const p FET_ushort
scoped notation:70 p:71 " # " "PTR" => RE_const p FET_ptr
scoped notation:70 p:71 " # " "struct" s:71 => RE_const p (FET_struct s)
scoped notation:70 p:71 " # " s:71 => RE_const p (FET_alias s)

scoped notation "sizeof" "(" "INT" ")" => sizeof_front_end_type FET_int
scoped notation "sizeof" "(" "CHAR" ")" => sizeof_front_end_type FET_char
scoped notation "sizeof" "(" "INT64" ")" => sizeof_front_end_type FET_int64
scoped notation "sizeof" "(" "SHORT" ")" => sizeof_front_end_type FET_short
scoped notation "sizeof" "(" "UINT" ")" => sizeof_front_end_type FET_uint
scoped notation "sizeof" "(" "UCHAR" ")" => sizeof_front_end_type FET_uchar
scoped notation "sizeof" "(" "UINT64" ")" => sizeof_front_end_type FET_uint64
scoped notation "sizeof" "(" "USHORT" ")" => sizeof_front_end_type FET_ushort
scoped notation "sizeof" "(" "PTR" ")" => sizeof_front_end_type FET_ptr
scoped notation "sizeof" "(" "struct" s ")" =>
  sizeof_front_end_type (FET_struct s)
scoped notation "sizeof" "(" "union" s ")" =>
  sizeof_front_end_type (FET_union s)
scoped notation "sizeof" "(" s ")" => sizeof_front_end_type (FET_alias s)

end SimpleC

namespace SimpleC.SL.CNotation

open AUXLib

axiom rvalue_expr_equiv : rvalue_expr -> rvalue_expr -> Prop
axiom lvalue_expr_equiv : lvalue_expr -> lvalue_expr -> Prop

axiom rvalue_expr_equiv_refl :
  forall x : rvalue_expr, rvalue_expr_equiv x x

axiom lvalue_expr_equiv_refl :
  forall x : lvalue_expr, lvalue_expr_equiv x x

axiom rvalue_expr_equiv_sym :
  forall x y : rvalue_expr, rvalue_expr_equiv x y -> rvalue_expr_equiv y x

axiom lvalue_expr_equiv_sym :
  forall x y : lvalue_expr, lvalue_expr_equiv x y -> lvalue_expr_equiv y x

axiom rvalue_expr_equiv_trans :
  forall x y z : rvalue_expr,
    rvalue_expr_equiv x y -> rvalue_expr_equiv y z -> rvalue_expr_equiv x z

axiom lvalue_expr_equiv_trans :
  forall x y z : lvalue_expr,
    lvalue_expr_equiv x y -> lvalue_expr_equiv y z -> lvalue_expr_equiv x z

theorem rvalue_expr_equiv_equiv : AUXLib.Equivalence rvalue_expr_equiv where
  refl := rvalue_expr_equiv_refl
  symm := rvalue_expr_equiv_sym
  trans := rvalue_expr_equiv_trans

theorem lvalue_expr_equiv_equiv : AUXLib.Equivalence lvalue_expr_equiv where
  refl := lvalue_expr_equiv_refl
  symm := lvalue_expr_equiv_sym
  trans := lvalue_expr_equiv_trans

attribute [instance] rvalue_expr_equiv_equiv lvalue_expr_equiv_equiv

axiom LE_arrow_field_congr :
  Proper (rvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_arrow_field

axiom LE_array_subst_congr :
  Proper (lvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_array_subst

axiom LE_dot_field_congr :
  Proper (lvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_dot_field

axiom RE_add_pi_congr :
  Proper (rvalue_expr_equiv ==> Eq ==> rvalue_expr_equiv) RE_add_pi

axiom RE_sub_pi_congr :
  Proper (rvalue_expr_equiv ==> Eq ==> rvalue_expr_equiv) RE_sub_pi

axiom RE_addr_of_congr :
  Proper (lvalue_expr_equiv ==> rvalue_expr_equiv) RE_addr_of

axiom eval_addr_expr_congr :
  Proper (rvalue_expr_equiv ==> Eq) eval_addr_expr

attribute [instance] LE_arrow_field_congr LE_array_subst_congr LE_dot_field_congr
  RE_add_pi_congr RE_sub_pi_congr RE_addr_of_congr eval_addr_expr_congr

axiom eval_addr : forall R t,
  rvalue_expr_equiv (RE_const (eval_addr_expr R) t) R

axiom addr_of_array_subst : forall L x t,
  rvalue_expr_equiv
    (RE_const (eval_addr_expr (RE_addr_of L) + x * sizeof_front_end_type t) t)
    (RE_addr_of (LE_array_subst L x))

axiom addr_of_array_subst' : forall L x t,
  rvalue_expr_equiv
    (RE_const (eval_addr_expr (RE_addr_of L) + sizeof_front_end_type t * x) t)
    (RE_addr_of (LE_array_subst L x))

axiom const_array_pi : forall p x t,
  rvalue_expr_equiv
    (RE_const (p + x * sizeof_front_end_type t) t)
    (RE_add_pi (RE_const p t) x)

axiom const_array_pi' : forall p x t,
  rvalue_expr_equiv
    (RE_const (p + sizeof_front_end_type t * x) t)
    (RE_add_pi (RE_const p t) x)

axiom addr_of_arrow_field : forall L x,
  rvalue_expr_equiv
    (RE_addr_of (LE_dot_field L x))
    (RE_addr_of (LE_arrow_field (RE_addr_of L) x))

axiom addr_of_arrow_field_inv : forall x y F,
  eval_addr_expr (RE_addr_of (LE_arrow_field x F)) =
    eval_addr_expr (RE_addr_of (LE_arrow_field y F)) -> x = y

axiom addr_of_LE_var_not_zero : forall x,
  Not (eval_addr_expr (RE_addr_of (LE_var x)) = 0)

axiom RE_add_pi_inv_l : forall x y i,
  RE_add_pi x i = RE_add_pi y i -> x = y

axiom RE_add_pi_inv_r : forall x a b,
  RE_add_pi x a = RE_add_pi x b -> a = b

axiom RE_sub_pi_inv_l : forall x y i,
  RE_sub_pi x i = RE_sub_pi y i -> x = y

axiom RE_sub_pi_inv_r : forall x a b,
  RE_sub_pi x a = RE_sub_pi x b -> a = b

syntax "const_array_simpl" : tactic

macro_rules
  | `(tactic| const_array_simpl) =>
      `(tactic| first | rel_rw [const_array_pi] | rel_rw [const_array_pi'])

syntax "csimpl" : tactic

macro_rules
  | `(tactic| csimpl) =>
      `(tactic|
        repeat
          first
          | rel_rw [eval_addr]
          | rel_rw [addr_of_array_subst]
          | rel_rw [addr_of_array_subst']
          | rel_rw [addr_of_arrow_field]
          | const_array_simpl)

end SimpleC.SL.CNotation
