import AUXLib.SetoidRewrite
import SimpleC.SL.CArch

namespace SimpleC.SL.CNotation

open AUXLib
open SimpleC.SL.CArch

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
  | FET_int128
  | FET_uint128
  | FET_ushort
  | FET_float
  | FET_double
  | FET_long_double
  | FET_ptr

export front_end_type
  (FET_struct FET_union FET_enum FET_alias FET_int FET_char FET_int64 FET_short
   FET_uint FET_uchar FET_uint64 FET_int128 FET_uint128 FET_ushort FET_float
   FET_double FET_long_double FET_ptr)

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
axiom sizeof_struct_type : String -> Int
axiom sizeof_union_type : String -> Int
axiom sizeof_enum_type : String -> Int
axiom sizeof_alias_type : String -> Int

noncomputable def sizeof_front_end_type_of_ptr_size
    (ptr_size : Int) (ty : front_end_type) : Int :=
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
  | FET_int128 => 16
  | FET_uint128 => 16
  | FET_ushort => 2
  | FET_float => 4
  | FET_double => 8
  | FET_long_double => 16
  | FET_ptr => ptr_size

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
scoped notation:70 p:71 " # " "INT128" => RE_const p FET_int128
scoped notation:70 p:71 " # " "UINT128" => RE_const p FET_uint128
scoped notation:70 p:71 " # " "USHORT" => RE_const p FET_ushort
scoped notation:70 p:71 " # " "FLOAT" => RE_const p FET_float
scoped notation:70 p:71 " # " "DOUBLE" => RE_const p FET_double
scoped notation:70 p:71 " # " "LONGDOUBLE" => RE_const p FET_long_double
scoped notation:70 p:71 " # " "PTR" => RE_const p FET_ptr
scoped notation:70 p:71 " # " "struct" s:71 => RE_const p (FET_struct s)
scoped notation:70 p:71 " # " s:71 => RE_const p (FET_alias s)

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

namespace CNotationSig

noncomputable def sizeof_front_end_type
    (Arch : SimpleC.SL.CArch.CArchSig) (ty : front_end_type) : Int :=
  sizeof_front_end_type_of_ptr_size
    (SimpleC.SL.CArch.CArchSig.ptr_size_Z Arch) ty

theorem sizeof_int (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_int = 4 := rfl

theorem sizeof_char (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_char = 1 := rfl

theorem sizeof_int64 (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_int64 = 8 := rfl

theorem sizeof_short (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_short = 2 := rfl

theorem sizeof_uint (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_uint = 4 := rfl

theorem sizeof_uchar (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_uchar = 1 := rfl

theorem sizeof_uint64 (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_uint64 = 8 := rfl

theorem sizeof_int128 (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_int128 = 16 := rfl

theorem sizeof_uint128 (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_uint128 = 16 := rfl

theorem sizeof_ushort (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_ushort = 2 := rfl

theorem sizeof_float (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_float = 4 := rfl

theorem sizeof_double (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_double = 8 := rfl

theorem sizeof_long_double (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_long_double = 16 := rfl

theorem sizeof_ptr (Arch : SimpleC.SL.CArch.CArchSig) :
    sizeof_front_end_type Arch FET_ptr =
      SimpleC.SL.CArch.CArchSig.ptr_size_Z Arch := rfl

axiom eval_addr (Arch : SimpleC.SL.CArch.CArchSig) : forall R t,
  rvalue_expr_equiv (RE_const (eval_addr_expr R) t) R

axiom addr_of_array_subst (Arch : SimpleC.SL.CArch.CArchSig) : forall L x t,
  rvalue_expr_equiv
    (RE_const
      (eval_addr_expr (RE_addr_of L) + x * sizeof_front_end_type Arch t) t)
    (RE_addr_of (LE_array_subst L x))

axiom addr_of_array_subst' (Arch : SimpleC.SL.CArch.CArchSig) : forall L x t,
  rvalue_expr_equiv
    (RE_const
      (eval_addr_expr (RE_addr_of L) + sizeof_front_end_type Arch t * x) t)
    (RE_addr_of (LE_array_subst L x))

axiom const_array_pi (Arch : SimpleC.SL.CArch.CArchSig) : forall p x t,
  rvalue_expr_equiv
    (RE_const (p + x * sizeof_front_end_type Arch t) t)
    (RE_add_pi (RE_const p t) x)

axiom const_array_pi' (Arch : SimpleC.SL.CArch.CArchSig) : forall p x t,
  rvalue_expr_equiv
    (RE_const (p + sizeof_front_end_type Arch t * x) t)
    (RE_add_pi (RE_const p t) x)

axiom addr_of_arrow_field (Arch : SimpleC.SL.CArch.CArchSig) : forall L x,
  rvalue_expr_equiv
    (RE_addr_of (LE_dot_field L x))
    (RE_addr_of (LE_arrow_field (RE_addr_of L) x))

end CNotationSig

class CNotationContext : Type where
  arch : SimpleC.SL.CArch.CArchSig

instance (priority := low) defaultCNotationContext : CNotationContext :=
  ⟨SimpleC.SL.CArch.Arch32⟩

namespace CNotationContext

noncomputable abbrev sizeof_front_end_type [ctx : CNotationContext]
    (ty : front_end_type) : Int :=
  CNotationSig.sizeof_front_end_type ctx.arch ty

theorem eval_addr [ctx : CNotationContext] : forall R t,
    rvalue_expr_equiv (RE_const (eval_addr_expr R) t) R :=
  CNotationSig.eval_addr ctx.arch

theorem addr_of_array_subst [ctx : CNotationContext] : forall L x t,
    rvalue_expr_equiv
      (RE_const
        (eval_addr_expr (RE_addr_of L) + x * sizeof_front_end_type t) t)
      (RE_addr_of (LE_array_subst L x)) :=
  CNotationSig.addr_of_array_subst ctx.arch

theorem addr_of_array_subst' [ctx : CNotationContext] : forall L x t,
    rvalue_expr_equiv
      (RE_const
        (eval_addr_expr (RE_addr_of L) + sizeof_front_end_type t * x) t)
      (RE_addr_of (LE_array_subst L x)) :=
  CNotationSig.addr_of_array_subst' ctx.arch

theorem const_array_pi [ctx : CNotationContext] : forall p x t,
    rvalue_expr_equiv
      (RE_const (p + x * sizeof_front_end_type t) t)
      (RE_add_pi (RE_const p t) x) :=
  CNotationSig.const_array_pi ctx.arch

theorem const_array_pi' [ctx : CNotationContext] : forall p x t,
    rvalue_expr_equiv
      (RE_const (p + sizeof_front_end_type t * x) t)
      (RE_add_pi (RE_const p t) x) :=
  CNotationSig.const_array_pi' ctx.arch

theorem addr_of_arrow_field [ctx : CNotationContext] : forall L x,
    rvalue_expr_equiv
      (RE_addr_of (LE_dot_field L x))
      (RE_addr_of (LE_arrow_field (RE_addr_of L) x)) :=
  CNotationSig.addr_of_arrow_field ctx.arch

end CNotationContext

-- Transitional 32-bit exports keep the already-migrated facade building until
-- the Arch parameter reaches CommonAssertion and its dependents.
noncomputable abbrev sizeof_front_end_type : front_end_type -> Int :=
  sizeof_front_end_type_of_ptr_size 4

theorem sizeof_int : sizeof_front_end_type FET_int = 4 := rfl

theorem sizeof_char : sizeof_front_end_type FET_char = 1 := rfl

theorem sizeof_int64 : sizeof_front_end_type FET_int64 = 8 := rfl

theorem sizeof_short : sizeof_front_end_type FET_short = 2 := rfl

theorem sizeof_uint : sizeof_front_end_type FET_uint = 4 := rfl

theorem sizeof_uchar : sizeof_front_end_type FET_uchar = 1 := rfl

theorem sizeof_uint64 : sizeof_front_end_type FET_uint64 = 8 := rfl

theorem sizeof_int128 : sizeof_front_end_type FET_int128 = 16 := rfl

theorem sizeof_uint128 : sizeof_front_end_type FET_uint128 = 16 := rfl

theorem sizeof_ushort : sizeof_front_end_type FET_ushort = 2 := rfl

theorem sizeof_float : sizeof_front_end_type FET_float = 4 := rfl

theorem sizeof_double : sizeof_front_end_type FET_double = 8 := rfl

theorem sizeof_long_double : sizeof_front_end_type FET_long_double = 16 := rfl

theorem sizeof_ptr : sizeof_front_end_type FET_ptr = 4 := rfl

theorem eval_addr : forall R t,
    rvalue_expr_equiv (RE_const (eval_addr_expr R) t) R :=
  CNotationSig.eval_addr SimpleC.SL.CArch.Arch32

theorem addr_of_array_subst : forall L x t,
    rvalue_expr_equiv
      (RE_const (eval_addr_expr (RE_addr_of L) + x * sizeof_front_end_type t) t)
      (RE_addr_of (LE_array_subst L x)) :=
  CNotationSig.addr_of_array_subst SimpleC.SL.CArch.Arch32

theorem addr_of_array_subst' : forall L x t,
    rvalue_expr_equiv
      (RE_const (eval_addr_expr (RE_addr_of L) + sizeof_front_end_type t * x) t)
      (RE_addr_of (LE_array_subst L x)) :=
  CNotationSig.addr_of_array_subst' SimpleC.SL.CArch.Arch32

theorem const_array_pi : forall p x t,
    rvalue_expr_equiv
      (RE_const (p + x * sizeof_front_end_type t) t)
      (RE_add_pi (RE_const p t) x) :=
  CNotationSig.const_array_pi SimpleC.SL.CArch.Arch32

theorem const_array_pi' : forall p x t,
    rvalue_expr_equiv
      (RE_const (p + sizeof_front_end_type t * x) t)
      (RE_add_pi (RE_const p t) x) :=
  CNotationSig.const_array_pi' SimpleC.SL.CArch.Arch32

theorem addr_of_arrow_field : forall L x,
    rvalue_expr_equiv
      (RE_addr_of (LE_dot_field L x))
      (RE_addr_of (LE_arrow_field (RE_addr_of L) x)) :=
  CNotationSig.addr_of_arrow_field SimpleC.SL.CArch.Arch32

end SimpleC.SL.CNotation

namespace SimpleC

open SL.CNotation

scoped notation "sizeof" "(" "INT" ")" =>
  CNotationContext.sizeof_front_end_type FET_int
scoped notation "sizeof" "(" "CHAR" ")" =>
  CNotationContext.sizeof_front_end_type FET_char
scoped notation "sizeof" "(" "INT64" ")" =>
  CNotationContext.sizeof_front_end_type FET_int64
scoped notation "sizeof" "(" "SHORT" ")" =>
  CNotationContext.sizeof_front_end_type FET_short
scoped notation "sizeof" "(" "UINT" ")" =>
  CNotationContext.sizeof_front_end_type FET_uint
scoped notation "sizeof" "(" "UCHAR" ")" =>
  CNotationContext.sizeof_front_end_type FET_uchar
scoped notation "sizeof" "(" "UINT64" ")" =>
  CNotationContext.sizeof_front_end_type FET_uint64
scoped notation "sizeof" "(" "INT128" ")" =>
  CNotationContext.sizeof_front_end_type FET_int128
scoped notation "sizeof" "(" "UINT128" ")" =>
  CNotationContext.sizeof_front_end_type FET_uint128
scoped notation "sizeof" "(" "USHORT" ")" =>
  CNotationContext.sizeof_front_end_type FET_ushort
scoped notation "sizeof" "(" "FLOAT" ")" =>
  CNotationContext.sizeof_front_end_type FET_float
scoped notation "sizeof" "(" "DOUBLE" ")" =>
  CNotationContext.sizeof_front_end_type FET_double
scoped notation "sizeof" "(" "LONGDOUBLE" ")" =>
  CNotationContext.sizeof_front_end_type FET_long_double
scoped notation "sizeof" "(" "PTR" ")" =>
  CNotationContext.sizeof_front_end_type FET_ptr
scoped notation "sizeof" "(" "struct" s ")" =>
  CNotationContext.sizeof_front_end_type (FET_struct s)
scoped notation "sizeof" "(" "union" s ")" =>
  CNotationContext.sizeof_front_end_type (FET_union s)
scoped notation "sizeof" "(" s ")" =>
  CNotationContext.sizeof_front_end_type (FET_alias s)

end SimpleC

namespace SimpleC.SL.CNotation

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

theorem const_array_simpl_alias_rule [ctx : CNotationContext]
    (p i : Int) (name field : String) :
    eval_addr_expr
        (RE_addr_of
          (LE_arrow_field
            (RE_const
              (p + i * CNotationContext.sizeof_front_end_type (FET_alias name))
              (FET_alias name))
            field)) =
      eval_addr_expr
        (RE_addr_of
          (LE_arrow_field
            (RE_add_pi (RE_const p (FET_alias name)) i)
            field)) := by
  rel_rw [CNotationContext.const_array_pi (ctx := ctx)]
  rfl

theorem const_array_simpl_alias_rule' [ctx : CNotationContext]
    (p i : Int) (name field : String) :
    eval_addr_expr
        (RE_addr_of
          (LE_arrow_field
            (RE_const
              (p + CNotationContext.sizeof_front_end_type (FET_alias name) * i)
              (FET_alias name))
            field)) =
      eval_addr_expr
        (RE_addr_of
          (LE_arrow_field
            (RE_add_pi (RE_const p (FET_alias name)) i)
            field)) := by
  rel_rw [CNotationContext.const_array_pi' (ctx := ctx)]
  rfl

syntax "const_array_simpl" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| const_array_simpl) => do
      let saved <- saveState
      try
        evalTactic (← `(tactic|
          rel_rw [SimpleC.SL.CNotation.const_array_simpl_alias_rule
            (ctx := inferInstance)]))
      catch _ =>
        restoreState saved
        evalTactic (← `(tactic|
          rel_rw [SimpleC.SL.CNotation.const_array_simpl_alias_rule'
            (ctx := inferInstance)]))

syntax "csimpl" : tactic

macro_rules
  | `(tactic| csimpl) =>
      `(tactic|
        repeat
          first
          | rel_rw [CNotationContext.eval_addr (ctx := inferInstance)]
          | rel_rw [CNotationContext.addr_of_array_subst (ctx := inferInstance)]
          | rel_rw [CNotationContext.addr_of_array_subst' (ctx := inferInstance)]
          | rel_rw [CNotationContext.addr_of_arrow_field (ctx := inferInstance)]
          | const_array_simpl)

end SimpleC.SL.CNotation
