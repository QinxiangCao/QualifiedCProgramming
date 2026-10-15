import SimpleC.SL.CNotation
import Lean.Util.CollectAxioms

open AUXLib
open SimpleC.SL.CNotation
open scoped SimpleC

open Lean Elab Command

private def resolveCNotationApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def cnotationApiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "CNotation API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

private def expectedCNotationAxioms : Array Name := #[
  ``SimpleC.SL.CNotation.eval_addr_expr,
  ``SimpleC.SL.CNotation.sizeof_struct_type,
  ``SimpleC.SL.CNotation.sizeof_union_type,
  ``SimpleC.SL.CNotation.sizeof_enum_type,
  ``SimpleC.SL.CNotation.sizeof_alias_type,
  ``SimpleC.SL.CNotation.rvalue_expr_equiv,
  ``SimpleC.SL.CNotation.lvalue_expr_equiv,
  ``SimpleC.SL.CNotation.rvalue_expr_equiv_refl,
  ``SimpleC.SL.CNotation.lvalue_expr_equiv_refl,
  ``SimpleC.SL.CNotation.rvalue_expr_equiv_sym,
  ``SimpleC.SL.CNotation.lvalue_expr_equiv_sym,
  ``SimpleC.SL.CNotation.rvalue_expr_equiv_trans,
  ``SimpleC.SL.CNotation.lvalue_expr_equiv_trans,
  ``SimpleC.SL.CNotation.LE_arrow_field_congr,
  ``SimpleC.SL.CNotation.LE_array_subst_congr,
  ``SimpleC.SL.CNotation.LE_dot_field_congr,
  ``SimpleC.SL.CNotation.RE_add_pi_congr,
  ``SimpleC.SL.CNotation.RE_sub_pi_congr,
  ``SimpleC.SL.CNotation.RE_addr_of_congr,
  ``SimpleC.SL.CNotation.eval_addr_expr_congr,
  ``SimpleC.SL.CNotation.CNotationSig.eval_addr,
  ``SimpleC.SL.CNotation.CNotationSig.addr_of_array_subst,
  ``SimpleC.SL.CNotation.CNotationSig.addr_of_array_subst',
  ``SimpleC.SL.CNotation.CNotationSig.const_array_pi,
  ``SimpleC.SL.CNotation.CNotationSig.const_array_pi',
  ``SimpleC.SL.CNotation.CNotationSig.addr_of_arrow_field,
  ``SimpleC.SL.CNotation.addr_of_arrow_field_inv,
  ``SimpleC.SL.CNotation.addr_of_LE_var_not_zero,
  ``SimpleC.SL.CNotation.RE_add_pi_inv_l,
  ``SimpleC.SL.CNotation.RE_add_pi_inv_r,
  ``SimpleC.SL.CNotation.RE_sub_pi_inv_l,
  ``SimpleC.SL.CNotation.RE_sub_pi_inv_r]

syntax (name := checkCNotationContract)
  "#check_cnotation_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_cnotation_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveCNotationApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- cnotationApiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "CNotation API type hash changed: expected {expected}, got {actual}"

      let env <- getEnv
      let actualAxioms := env.constants.toList.foldl (init := #[]) fun result entry =>
        let name := entry.1
        match entry.2 with
        | .axiomInfo _ =>
            if name.toString.startsWith "SimpleC.SL.CNotation." then
              result.push name
            else
              result
        | _ => result
      unless actualAxioms.size = expectedCNotationAxioms.size &&
          actualAxioms.all expectedCNotationAxioms.contains &&
          expectedCNotationAxioms.all actualAxioms.contains do
        throwError
          "CNotation source axiom set changed: expected {expectedCNotationAxioms}, got {actualAxioms}"

      let allowedAxioms := expectedCNotationAxioms ++
        #[``propext, ``Classical.choice, ``Quot.sound]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "CNotation declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"CNotation API contract verified for {names.size} declarations and {actualAxioms.size} source axioms"

-- Definitions, inductives, constructors, coercion helper, and source parameters.
#check NULL
#check SimpleC.SL.CNotation.addr
#check front_end_type
#check FET_struct
#check FET_union
#check FET_enum
#check FET_alias
#check FET_int
#check FET_char
#check FET_int64
#check FET_short
#check FET_uint
#check FET_uchar
#check FET_uint64
#check FET_int128
#check FET_uint128
#check FET_ushort
#check FET_float
#check FET_double
#check FET_long_double
#check FET_ptr
#check rvalue_expr
#check lvalue_expr
#check RE_const
#check RE_add_pi
#check RE_sub_pi
#check RE_addr_of
#check LE_var
#check LE_arrow_field
#check LE_array_subst
#check LE_dot_field
#check eval_addr_expr
#check sizeof_struct_type
#check sizeof_union_type
#check sizeof_enum_type
#check sizeof_alias_type
#check sizeof_front_end_type_of_ptr_size
#check sizeof_front_end_type
#check struct_or_union
#check Struct
#check Union
#check composite_definition
#check Composite
#check get_lvalue_expr

-- The five candidate additions are available in both source notation forms.
example (p : addr) : (p # INT128) = RE_const p FET_int128 := rfl
example (p : addr) : (p # UINT128) = RE_const p FET_uint128 := rfl
example (p : addr) : (p # FLOAT) = RE_const p FET_float := rfl
example (p : addr) : (p # DOUBLE) = RE_const p FET_double := rfl
example (p : addr) : (p # LONGDOUBLE) = RE_const p FET_long_double := rfl
example (p : addr) :
    &(p # INT128 ->ₛ "f") = eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const p FET_int128) "f")) := rfl
example (p : addr) :
    &(p # UINT128 ->ₛ "f") = eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const p FET_uint128) "f")) := rfl
example (p : addr) :
    &(p # FLOAT ->ₛ "f") = eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const p FET_float) "f")) := rfl
example (p : addr) :
    &(p # DOUBLE ->ₛ "f") = eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const p FET_double) "f")) := rfl
example (p : addr) :
    &(p # LONGDOUBLE ->ₛ "f") = eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const p FET_long_double) "f")) := rfl

-- Candidate CNotationSig API: one architecture-indexed size definition,
-- fourteen size lemmas, and six source assumptions.
#check CNotationSig.sizeof_front_end_type
#check CNotationSig.sizeof_int
#check CNotationSig.sizeof_char
#check CNotationSig.sizeof_int64
#check CNotationSig.sizeof_short
#check CNotationSig.sizeof_uint
#check CNotationSig.sizeof_uchar
#check CNotationSig.sizeof_uint64
#check CNotationSig.sizeof_int128
#check CNotationSig.sizeof_uint128
#check CNotationSig.sizeof_ushort
#check CNotationSig.sizeof_float
#check CNotationSig.sizeof_double
#check CNotationSig.sizeof_long_double
#check CNotationSig.sizeof_ptr
#check CNotationSig.eval_addr
#check CNotationSig.addr_of_array_subst
#check CNotationSig.addr_of_array_subst'
#check CNotationSig.const_array_pi
#check CNotationSig.const_array_pi'
#check CNotationSig.addr_of_arrow_field

-- CNotation has 32 source assumption families: seven primitive parameters,
-- six relation laws, seven congruence laws, six CNotationSig laws, and six
-- inverse laws. The following names are the transitional Arch32 theorem view.
#check sizeof_int
#check sizeof_char
#check sizeof_int64
#check sizeof_short
#check sizeof_uint
#check sizeof_uchar
#check sizeof_uint64
#check sizeof_int128
#check sizeof_uint128
#check sizeof_ushort
#check sizeof_float
#check sizeof_double
#check sizeof_long_double
#check sizeof_ptr
#check rvalue_expr_equiv
#check lvalue_expr_equiv
#check rvalue_expr_equiv_refl
#check lvalue_expr_equiv_refl
#check rvalue_expr_equiv_sym
#check lvalue_expr_equiv_sym
#check rvalue_expr_equiv_trans
#check lvalue_expr_equiv_trans
#check LE_arrow_field_congr
#check LE_array_subst_congr
#check LE_dot_field_congr
#check RE_add_pi_congr
#check RE_sub_pi_congr
#check RE_addr_of_congr
#check eval_addr_expr_congr
#check eval_addr
#check addr_of_array_subst
#check addr_of_array_subst'
#check const_array_pi
#check const_array_pi'
#check addr_of_arrow_field
#check addr_of_arrow_field_inv
#check addr_of_LE_var_not_zero
#check RE_add_pi_inv_l
#check RE_add_pi_inv_r
#check RE_sub_pi_inv_l
#check RE_sub_pi_inv_r

-- The context selects the architecture used by scoped sizeof notation and
-- by the source-compatible no-argument tactics.
#check CNotationContext
#check CNotationContext.arch
#check CNotationContext.sizeof_front_end_type
#check CNotationContext.eval_addr
#check CNotationContext.addr_of_array_subst
#check CNotationContext.addr_of_array_subst'
#check CNotationContext.const_array_pi
#check CNotationContext.const_array_pi'
#check CNotationContext.addr_of_arrow_field

-- Fixed-width types are independent of pointer width; named composite sizes
-- remain exactly the corresponding source parameters.
example : sizeof_front_end_type_of_ptr_size 4 FET_int = 4 := rfl
example : sizeof_front_end_type_of_ptr_size 8 FET_int128 = 16 := rfl
example : sizeof_front_end_type_of_ptr_size 4 FET_float = 4 := rfl
example : sizeof_front_end_type_of_ptr_size 8 FET_double = 8 := rfl
example : sizeof_front_end_type_of_ptr_size 4 FET_long_double = 16 := rfl
example : sizeof_front_end_type_of_ptr_size 4 FET_ptr = 4 := rfl
example : sizeof_front_end_type_of_ptr_size 8 FET_ptr = 8 := rfl
example (s : String) :
    sizeof_front_end_type_of_ptr_size 8 (FET_struct s) = sizeof_struct_type s := rfl
example (s : String) :
    sizeof_front_end_type_of_ptr_size 8 (FET_union s) = sizeof_union_type s := rfl
example (s : String) :
    sizeof_front_end_type_of_ptr_size 8 (FET_enum s) = sizeof_enum_type s := rfl
example (s : String) :
    sizeof_front_end_type_of_ptr_size 8 (FET_alias s) = sizeof_alias_type s := rfl

namespace Arch32Behavior

local instance : CNotationContext :=
  ⟨SimpleC.SL.CArch.Arch32⟩

example : sizeof(PTR) = 4 := rfl
example : sizeof(INT128) = 16 := rfl
example : sizeof(UINT128) = 16 := rfl
example : sizeof(FLOAT) = 4 := rfl
example : sizeof(DOUBLE) = 8 := rfl
example : sizeof(LONGDOUBLE) = 16 := rfl

example (base : lvalue_expr) :
    let q := eval_addr_expr (RE_addr_of base) + 10 * sizeof(PTR)
    eval_addr_expr (RE_const q FET_ptr) =
      eval_addr_expr (RE_addr_of (LE_array_subst base 10)) := by
  dsimp
  csimpl
  rfl

end Arch32Behavior

namespace Arch64Behavior

local instance : CNotationContext :=
  ⟨SimpleC.SL.CArch.Arch64⟩

example : sizeof(PTR) = 8 := rfl
example : sizeof(INT128) = 16 := rfl
example : sizeof(UINT128) = 16 := rfl
example : sizeof(FLOAT) = 4 := rfl
example : sizeof(DOUBLE) = 8 := rfl
example : sizeof(LONGDOUBLE) = 16 := rfl

example (base : lvalue_expr) :
    let q := eval_addr_expr (RE_addr_of base) + 10 * sizeof(PTR)
    eval_addr_expr (RE_const q FET_ptr) =
      eval_addr_expr (RE_addr_of (LE_array_subst base 10)) := by
  dsimp
  csimpl
  rfl

end Arch64Behavior

-- Coq const_array_simpl matches only an alias-typed constant immediately below
-- eval_addr/addr-of/arrow-field, in either multiplication order.
example (p : addr) :
    let q := p + 10 * sizeof("Node")
    &(q # "Node" ->ₛ "next") = &((p # "Node" + 10) ->ₛ "next") := by
  dsimp
  const_array_simpl
  rfl

example (p : addr) :
    let q := p + sizeof("Node") * 10
    &(q # "Node" ->ₛ "next") = &((p # "Node" + 10) ->ₛ "next") := by
  dsimp
  const_array_simpl
  rfl

-- Coq's `context [...]` match and generalized rewrite both search the whole
-- target, so alias expressions nested in a proposition or on an equality's
-- right side are source successes rather than failure boundaries.
example (p : addr) :
    let q := p + 10 * sizeof("Node")
    (&(q # "Node" ->ₛ "next") = &((p # "Node" + 10) ->ₛ "next")) ∧ True := by
  dsimp
  const_array_simpl
  exact ⟨rfl, True.intro⟩

example (p : addr) :
    let q := p + 10 * sizeof("Node")
    &((p # "Node" + 10) ->ₛ "next") = &(q # "Node" ->ₛ "next") := by
  dsimp
  const_array_simpl
  rfl

example (p i : Int) :
    rvalue_expr_equiv
      (RE_const (p + i * CNotationContext.sizeof_front_end_type FET_ptr) FET_ptr)
      (RE_add_pi (RE_const p FET_ptr) i) := by
  fail_if_success const_array_simpl
  exact CNotationContext.const_array_pi p i FET_ptr

example (p : addr) :
    let q := p + 10 * sizeof(PTR)
    &(q # PTR ->ₛ "next") = &((p # PTR + 10) ->ₛ "next") := by
  dsimp
  fail_if_success const_array_simpl
  rel_rw [CNotationContext.const_array_pi]
  rfl

-- The two proved Equivalence declarations and all seven Proper registrations.
#check rvalue_expr_equiv_equiv
#check lvalue_expr_equiv_equiv

example : AUXLib.Equivalence rvalue_expr_equiv := inferInstance
example : AUXLib.Equivalence lvalue_expr_equiv := inferInstance
example : Proper (rvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_arrow_field := inferInstance
example : Proper (lvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_array_subst := inferInstance
example : Proper (lvalue_expr_equiv ==> Eq ==> lvalue_expr_equiv) LE_dot_field := inferInstance
example : Proper (rvalue_expr_equiv ==> Eq ==> rvalue_expr_equiv) RE_add_pi := inferInstance
example : Proper (rvalue_expr_equiv ==> Eq ==> rvalue_expr_equiv) RE_sub_pi := inferInstance
example : Proper (lvalue_expr_equiv ==> rvalue_expr_equiv) RE_addr_of := inferInstance
example : Proper (rvalue_expr_equiv ==> Eq) eval_addr_expr := inferInstance

namespace SourceTestNotations

local instance : CNotationContext :=
  ⟨SimpleC.SL.CArch.Arch32⟩

-- Coq `TestNotations` ends these twelve goals with `Abort`: they are parser
-- and elaboration checks, not propositions expected to be provable.
#check fun (p : addr) (q : rvalue_expr) =>
  p = &((q + 1) ->ₛ "pstPrev")

#check fun (p : addr) (q : rvalue_expr) =>
  p = &(q ->ₛ "pstPrev")

#check fun (p : addr) =>
  p = &((p # struct "LOS_DL_LIST") ->ₛ "pstPrev")

#check fun (p : addr) =>
  p = &(p # struct "LOS_DL_LIST" ->ₛ "pstPrev")

#check fun (p : addr) =>
  p = &(p # "LOS_DL_LIST" ->ₛ "pstPrev")

#check fun (p : addr) =>
  p = &(p # "LOS_TaskCB" ->ₛ "readWriteCnt"[0 + 1])

#check fun (p : addr) =>
  p = &(((p + 1)) # "LOS_TaskCB" ->ₛ "readWriteCnt"[0 + 1])

#check fun (p : addr) =>
  p = &("g_TaskCB")

#check fun (p : addr) =>
  p = &("g_TaskCB") + sizeof("TaskCB") * 1

#check fun (p : addr) =>
  p = &("g_X") + sizeof(INT) * 1

#check fun (p : addr) (_n : Int) =>
  p = &((p # "LOS_DL_LIST" + 1) ->ₛ "pstPrev")

#check fun (p : addr) (_n : Int) =>
  p = &((p # "LOS_DL_LIST" + (1)) ->ₛ "pstPrev")

-- The six source `Qed` goals exercise the same `csimpl` normalization path.
example (p : addr) :
    &(&(p # "TaskCB" ->ₛ "pend_list") ->ₛ "pstPrev") =
      &(p # "TaskCB" ->ₛ "pend_list" .ₛ "pstPrev") := by
  csimpl
  rfl

example (q : addr) :
    &(q # "TaskCB" ->ₛ "pend_list" .ₛ "pstPrev") =
      &(&(q # "TaskCB" ->ₛ "pend_list") ->ₛ "pstPrev") := by
  csimpl
  rfl

example (p : addr) :
    let q := p + 10 * sizeof("TaskCB")
    &(q # "TaskCB" ->ₛ "pend_list") =
      &((p # "TaskCB" + 10) ->ₛ "pend_list") := by
  dsimp
  csimpl
  rfl

example (p : addr) :
    let q := p + sizeof("TaskCB") * 10
    &(q # "TaskCB" ->ₛ "pend_list") =
      &((p # "TaskCB" + 10) ->ₛ "pend_list") := by
  dsimp
  csimpl
  rfl

example (p q : addr) :
    &(q # "TaskCB" ->ₛ "pend_list") =
      &((p # "TaskCB" + 10) ->ₛ "pend_list") ->
    q = p + sizeof("TaskCB") * 10 := by
  intro h
  revert h
  csimpl
  intro h
  have h' := addr_of_arrow_field_inv _ _ _ h
  cases h'

example :
    let q := eval_addr_expr (RE_addr_of ("x" : lvalue_expr))
    &(q # "LOS_TaskCB" ->ₛ "pend_list") =
      &(&("x") ->ₛ "pend_list") := by
  dsimp
  csimpl
  rfl

end SourceTestNotations

#check_cnotation_contract [
  NULL,
  SimpleC.SL.CNotation.addr,
  front_end_type,
  front_end_type.rec,
  FET_struct,
  FET_union,
  FET_enum,
  FET_alias,
  FET_int,
  FET_char,
  FET_int64,
  FET_short,
  FET_uint,
  FET_uchar,
  FET_uint64,
  FET_int128,
  FET_uint128,
  FET_ushort,
  FET_float,
  FET_double,
  FET_long_double,
  FET_ptr,
  rvalue_expr,
  lvalue_expr,
  rvalue_expr.rec,
  lvalue_expr.rec,
  RE_const,
  RE_add_pi,
  RE_sub_pi,
  RE_addr_of,
  LE_var,
  LE_arrow_field,
  LE_array_subst,
  LE_dot_field,
  eval_addr_expr,
  sizeof_struct_type,
  sizeof_union_type,
  sizeof_enum_type,
  sizeof_alias_type,
  sizeof_front_end_type_of_ptr_size,
  struct_or_union,
  struct_or_union.rec,
  Struct,
  SimpleC.SL.CNotation.Union,
  composite_definition,
  composite_definition.rec,
  Composite,
  get_lvalue_expr,
  addr_notation_result,
  addr_notation_result.from_lvalue,
  instCoeStringLvalue_expr,
  instAddr_notation_resultAddr,
  instAddr_notation_resultRvalue_expr,
  addr_notation,
  rvalue_expr_equiv,
  lvalue_expr_equiv,
  rvalue_expr_equiv_refl,
  lvalue_expr_equiv_refl,
  rvalue_expr_equiv_sym,
  lvalue_expr_equiv_sym,
  rvalue_expr_equiv_trans,
  lvalue_expr_equiv_trans,
  rvalue_expr_equiv_equiv,
  lvalue_expr_equiv_equiv,
  LE_arrow_field_congr,
  LE_array_subst_congr,
  LE_dot_field_congr,
  RE_add_pi_congr,
  RE_sub_pi_congr,
  RE_addr_of_congr,
  eval_addr_expr_congr,
  CNotationSig.sizeof_front_end_type,
  CNotationSig.sizeof_int,
  CNotationSig.sizeof_char,
  CNotationSig.sizeof_int64,
  CNotationSig.sizeof_short,
  CNotationSig.sizeof_uint,
  CNotationSig.sizeof_uchar,
  CNotationSig.sizeof_uint64,
  CNotationSig.sizeof_int128,
  CNotationSig.sizeof_uint128,
  CNotationSig.sizeof_ushort,
  CNotationSig.sizeof_float,
  CNotationSig.sizeof_double,
  CNotationSig.sizeof_long_double,
  CNotationSig.sizeof_ptr,
  CNotationSig.eval_addr,
  CNotationSig.addr_of_array_subst,
  CNotationSig.addr_of_array_subst',
  CNotationSig.const_array_pi,
  CNotationSig.const_array_pi',
  CNotationSig.addr_of_arrow_field,
  CNotationContext,
  CNotationContext.arch,
  defaultCNotationContext,
  CNotationContext.sizeof_front_end_type,
  CNotationContext.eval_addr,
  CNotationContext.addr_of_array_subst,
  CNotationContext.addr_of_array_subst',
  CNotationContext.const_array_pi,
  CNotationContext.const_array_pi',
  CNotationContext.addr_of_arrow_field,
  sizeof_front_end_type,
  sizeof_int,
  sizeof_char,
  sizeof_int64,
  sizeof_short,
  sizeof_uint,
  sizeof_uchar,
  sizeof_uint64,
  sizeof_int128,
  sizeof_uint128,
  sizeof_ushort,
  sizeof_float,
  sizeof_double,
  sizeof_long_double,
  sizeof_ptr,
  eval_addr,
  addr_of_array_subst,
  addr_of_array_subst',
  const_array_pi,
  const_array_pi',
  addr_of_arrow_field,
  addr_of_arrow_field_inv,
  addr_of_LE_var_not_zero,
  RE_add_pi_inv_l,
  RE_add_pi_inv_r,
  RE_sub_pi_inv_l,
  RE_sub_pi_inv_r,
  const_array_simpl_alias_rule,
  const_array_simpl_alias_rule'
] => 4607324453460746894

#print axioms rvalue_expr_equiv_equiv
#print axioms lvalue_expr_equiv_equiv
#print axioms CNotationSig.sizeof_ptr
#print axioms sizeof_ptr
