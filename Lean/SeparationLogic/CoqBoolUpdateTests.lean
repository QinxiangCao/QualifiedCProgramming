import SimpleC.SL.SeparationLogic
import Lean.Util.CollectAxioms

namespace CoqBoolUpdateTests

open SimpleC.SL
open SimpleC.SL.CArch SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.StoreAux.StoreLibSig
open SimpleC.SL.ArrayLib SimpleC.SL.SeparationLogic
open scoped SimpleC SimpleC.SL.SAC

noncomputable section

#check FET_bool
#check CNotationSig.sizeof_bool
#check store_bool
#check undef_store_bool
#check store_bool_undef_store_bool
#check valid_store_bool
#check undef_store_bool_align
#check store_bool_align
#check StoreBoolAsElement
#check BoolArray
#check Array2Lib.Array2LibSig.BoolArray2
#check Array3Lib.Array3LibSig.BoolArray3
#check PtrArray2Lib.PtrArray2LibSig.BoolPtrArray2

section Generic

variable [SacContext] [SacArchContext] [SacEndianContext]
private abbrev Arch := SacContext.arch
private abbrev Endian := SacContext.endian
private abbrev R := SacContext.rules

example : front_end_type_value FET_bool = Int := rfl
example : sizeof_front_end_type_of_ptr_size Arch.ptr_size_Z FET_bool = 1 := rfl
example : sizeof(BOOL) = (1 : Int) := CNotationSig.sizeof_bool Arch

example (x : Int) : (x # BOOL : rvalue_expr) = RE_const x FET_bool := rfl
example (x i : Int) :
    ((x # BOOL) + i : rvalue_expr) = RE_add_pi (RE_const x FET_bool) i := rfl
example (x i : Int) :
    ((x # BOOL) ->ₛ "field"[i] : lvalue_expr) =
      LE_array_subst (LE_arrow_field (RE_const x FET_bool) "field") i := rfl

example (x v : Int) : (x # Bool |-> v) = store_bool Arch R x v := rfl
example (x : Int) : (x # Bool |->_) = undef_store_bool Arch R x := rfl
example (x v : Int) : (x # BOOL |-> v) = store_bool Arch R x v := rfl
example (x : Int) : (x # BOOL |->_) = undef_store_bool Arch R x := rfl

example (x v : Int) :
    store_bool Arch R x v =
      R.andp (R.coq_prop (isvalidptr_char Arch x ∧ (v = 0 ∨ v = 1)))
        (store_byte R x v) := rfl
example (x : Int) :
    undef_store_bool Arch R x =
      R.andp (R.coq_prop (isvalidptr_char Arch x)) (store_byte_noninit R x) := rfl
example (x v : Int) :
    poly_store Arch Endian R FET_bool x v = store_bool Arch R x v := rfl
example (x v : Int) :
    typed_poly_store Arch Endian R FET_bool x v = store_bool Arch R x v := rfl
example (x : Int) :
    poly_undef_store Arch R FET_bool x = undef_store_bool Arch R x := rfl

example (x v : Int) : R.derivable1 (store_bool Arch R x v) (undef_store_bool Arch R x) :=
  store_bool_undef_store_bool R x v
example (x v : Int) :
    R.derivable1 (store_bool Arch R x v) (R.coq_prop (0 <= v ∧ v <= 1)) :=
  valid_store_bool R x v
example (x : Int) :
    R.derivable1 (undef_store_bool Arch R x) (store_align_n Arch R 1) :=
  undef_store_bool_align R x
example (x v : Int) :
    R.derivable1 (store_bool Arch R x v) (store_align_n Arch R 1) :=
  store_bool_align R x v
example (x v : Int) :
    R.derivable1 (poly_store Arch Endian R FET_bool x v)
      (poly_undef_store Arch R FET_bool x) :=
  poly_store_poly_undef_store R x FET_bool v
example (x v : Int) :
    R.derivable1 (typed_poly_store Arch Endian R FET_bool x v)
      (poly_undef_store Arch R FET_bool x) :=
  typed_poly_store_poly_undef_store R x FET_bool v

-- Source-shaped tactic pipelines, including the new polymorphic branches.
example (x v : Int) : (x # Bool |-> v) |-- (x # Bool |->_) := by
  unfold store_bool undef_store_bool
  entailer!
  apply store_byte_store_byte_noinit

example (x v : Int) : (x # Bool |-> v) |-- “0 <= v ∧ v <= 1” := by
  unfold store_bool
  entailer!

example (x v : Int) : (x # Bool |-> v) |-- store_align_n Arch R 1 := by
  sep_apply (store_bool_undef_store_bool R x v)
  sep_apply (undef_store_bool_align R x)
  entailer!

example (x v : Int) :
    poly_store Arch Endian R FET_bool x v |-- (x # Bool |-> v) := by
  poly_store_unfold
  entailer!
example (x v : Int) :
    typed_poly_store Arch Endian R FET_bool x v |-- (x # Bool |-> v) := by
  poly_store_unfold
  entailer!
example (x : Int) :
    poly_undef_store Arch R FET_bool x |-- (x # Bool |->_) := by
  poly_store_unfold
  entailer!

example (P : R.expr) : P |-- P := by
  poly_store_unfold
  guard_target =ₛ SacContext.rules.derivable1 P P
  cancel

example (x v : Int) (Q : R.expr) (h : store_bool Arch R x v |-- Q) :
    poly_store Arch Endian R FET_bool x v |-- Q := by
  poly_store_unfold
  guard_target =ₛ SacContext.rules.derivable1 (store_bool Arch R x v) Q
  exact h

example (x v : Int) (P Q : R.expr) (h : P |-- Q) :
    (x # Bool |-> v) ** P |-- (x # Bool |-> v) ** Q := by
  fail_if_success solve | cancel
  sep_apply h
  cancel

example (x v : Int) (P : R.expr) :
    (x # Bool |-> v) ** P |-- “v = 0 ∨ v = 1” && ((x # Bool |-> v) ** P) := by
  entailer!

example (x : Int) (P : R.expr) :
    (BoolArray Arch Endian R (DerivedPredSig.canonical Arch Endian R)
      (StoreAux.StoreLibSig.canonical Arch Endian R
        (DerivedPredSig.canonical Arch Endian R))).full x 0 [] ** P |-- P := by
  entailer!

end Generic

section Elements

variable (Arch : CArchSig) (Endian : CEndianSig) (R : SeparationLogicSig)
private abbrev D := DerivedPredSig.canonical Arch Endian R
private abbrev S := StoreAux.StoreLibSig.canonical Arch Endian R (D Arch Endian R)
private abbrev E := StoreBoolAsElement Arch Endian R (D Arch Endian R) (S Arch Endian R)
private abbrev A := BoolArray Arch Endian R (D Arch Endian R) (S Arch Endian R)

example : (A Arch Endian R).elementStore = E Arch Endian R := rfl
example : (Array2Lib.Array2LibSig.BoolArray2 Arch Endian R (D Arch Endian R)
    (S Arch Endian R)).elementStore = E Arch Endian R := rfl
example : (Array3Lib.Array3LibSig.BoolArray3 Arch Endian R (D Arch Endian R)
    (S Arch Endian R)).elementStore = E Arch Endian R := rfl
example : (PtrArray2Lib.PtrArray2LibSig.BoolPtrArray2 Arch Endian R (D Arch Endian R)
    (S Arch Endian R)).elementStore = E Arch Endian R := rfl

example : (E Arch Endian R).A = Int := rfl
example : (E Arch Endian R).sizeA = 1 := rfl
example (x lo v : Int) :
    (E Arch Endian R).storeA x lo v = store_bool Arch R (x + lo * 1) v := rfl
example (x lo : Int) :
    (E Arch Endian R).undefstoreA x lo = undef_store_bool Arch R (x + lo * 1) := rfl
example (x lo v : Int) :
    R.derivable1 ((E Arch Endian R).storeA x lo v) ((E Arch Endian R).undefstoreA x lo) :=
  (E Arch Endian R).store_to_undefstore x lo v
example (x n lo v : Int) :
    R.logic_equiv ((E Arch Endian R).storeA (x + n * 1) lo v)
      ((E Arch Endian R).storeA x (lo + n) v) :=
  (E Arch Endian R).storeA_shift x n lo v
example (x n lo : Int) :
    R.logic_equiv ((E Arch Endian R).undefstoreA (x + n * 1) lo)
      ((E Arch Endian R).undefstoreA x (lo + n)) :=
  (E Arch Endian R).undefstoreA_shift x n lo
example (x lo v : Int) :
    R.derivable1 ((E Arch Endian R).storeA x lo v) (store_align_n Arch R 1) :=
  (E Arch Endian R).store_to_align x lo v
example (x lo : Int) :
    R.derivable1 ((E Arch Endian R).undefstoreA x lo) (store_align_n Arch R 1) :=
  (E Arch Endian R).undefstore_to_align x lo
example : 0 < (E Arch Endian R).sizeA ∧ (E Arch Endian R).sizeA < Int.max_unsigned :=
  (E Arch Endian R).sizeA_valid

example (x n : Int) :
    R.logic_equiv ((A Arch Endian R).full x n [])
      (R.andp (R.coq_prop (n = 0)) R.emp) :=
  (A Arch Endian R).full_empty x n
example (x n m : Int) (l : List Int) (h : 0 <= n ∧ n <= m) :
    R.derivable1 ((A Arch Endian R).full x m l)
      (R.sepcon ((A Arch Endian R).full x n (AUXLib.sublist 0 n l))
        ((A Arch Endian R).full (x + n * 1) (m - n) (AUXLib.sublist n m l))) :=
  (A Arch Endian R).full_split_to_full x n m l h
example (x n m : Int) (l1 l2 : List Int) (h : 0 <= n ∧ n <= m) :
    R.derivable1
      (R.sepcon ((A Arch Endian R).full x n l1)
        ((A Arch Endian R).full (x + n * 1) (m - n) l2))
      ((A Arch Endian R).full x m (l1 ++ l2)) :=
  (A Arch Endian R).full_merge_to_full x n m l1 l2 h
example (x m i : Int) :
    (Array2Lib.Array2LibSig.BoolArray2 Arch Endian R (D Arch Endian R)
      (S Arch Endian R)).row_addr x m i = x + i * m * 1 := rfl
example (x m k i : Int) :
    (Array3Lib.Array3LibSig.BoolArray3 Arch Endian R (D Arch Endian R)
      (S Arch Endian R)).plane_addr x m k i = x + i * m * k * 1 := rfl

end Elements

section HeapSemantics

open SimpleC.SL.Mem
open SimpleC.SL.Assertion

theorem bool_heap (Arch : CArchSig) (x v : Int)
    (hx : isvalidptr_char Arch x) (hv : v = 0 ∨ v = 1) :
    store_bool Arch SL x v (single_byte_mem x v) :=
  ⟨⟨hx, hv⟩, v, Byte.eqm_refl v, rfl⟩

theorem invalid_bool (Arch : CArchSig) (x v : Int) (m : mem)
    (hv : v ≠ 0 ∧ v ≠ 1) : ¬store_bool Arch SL x v m := by
  intro h
  rcases h.1.2 with hzero | hone
  · exact hv.1 hzero
  · exact hv.2 hone

example (Arch : CArchSig) :
    store_bool Arch SL 0 0 (single_byte_mem 0 0) :=
  bool_heap Arch 0 0 ⟨by omega, by
    change 0 <= Arch.addr_max_unsigned
    have := Arch.addr_max_unsigned_ge_7
    omega⟩ (Or.inl rfl)
example (Arch : CArchSig) :
    store_bool Arch SL Arch.addr_max_unsigned 1 (single_byte_mem Arch.addr_max_unsigned 1) :=
  bool_heap Arch _ 1 ⟨by have := Arch.addr_max_unsigned_ge_7; omega, le_refl _⟩ (Or.inr rfl)

example (Arch : CArchSig) (x : Int) :
    undef_store_bool Arch SL x = undef_store_uchar Arch SL x := rfl
example (Arch : CArchSig) (x : Int) (hx : isvalidptr_char Arch x) :
    undef_store_bool Arch SL x (single_Noninit_mem x) := ⟨hx, Or.inl rfl⟩
example (Arch : CArchSig) (x : Int) (hx : isvalidptr_char Arch x) :
    undef_store_bool Arch SL x (single_byte_mem x 42) := ⟨hx, Or.inr ⟨42, rfl⟩⟩
example (Arch : CArchSig) (x : Int) (m : mem) :
    ¬store_bool Arch SL x (-1) m := invalid_bool Arch x (-1) m (by decide)
example (Arch : CArchSig) (x : Int) (m : mem) :
    ¬store_bool Arch SL x 2 m := invalid_bool Arch x 2 m (by decide)
example (Arch : CArchSig) (x : Int) (m : mem) :
    ¬store_bool Arch SL x 256 m := invalid_bool Arch x 256 m (by decide)
example (Arch : CArchSig) (v : Int) (m : mem) :
    ¬store_bool Arch SL (-1) v m := by
  intro h
  have : 0 <= (-1 : Int) := h.1.1.1
  omega
example (Arch : CArchSig) (v : Int) (m : mem) :
    ¬store_bool Arch SL (Arch.addr_max_unsigned + 1) v m := by
  intro h
  have : Arch.addr_max_unsigned + 1 <= Arch.addr_max_unsigned := h.1.1.2
  omega
example (m : mem) : ¬store_bool Arch32 SL 4294967296 1 m := by
  intro h
  have : (4294967296 : Int) <= 4294967295 := h.1.1.2
  omega
example : store_bool Arch64 SL 4294967296 1 (single_byte_mem 4294967296 1) :=
  bool_heap Arch64 _ _ (by
    change 0 <= (4294967296 : Int) ∧ (4294967296 : Int) <= 18446744073709551615
    decide) (Or.inr rfl)

end HeapSemantics

section Aggregate

variable (R : AggregateRules)
example (x v : Int) : R.store_bool x v = store_bool R.Arch R x v := rfl
example (x : Int) : R.undef_store_bool x = undef_store_bool R.Arch R x := rfl
example : R.sizeof_front_end_type FET_bool = 1 := R.sizeof_bool
example (x v : Int) : R.derivable1 (R.store_bool x v) (R.undef_store_bool x) :=
  R.store_bool_undef_store_bool x v
example (x v : Int) : R.derivable1 (R.store_bool x v) (R.coq_prop (0 <= v ∧ v <= 1)) :=
  R.valid_store_bool x v
example (x v : Int) : R.derivable1 (R.store_bool x v) (R.store_align_n 1) :=
  R.store_bool_align x v
example (x : Int) : R.derivable1 (R.undef_store_bool x) (R.store_align_n 1) :=
  R.undef_store_bool_align x
example : R.StoreBoolAsElement.A = Int := rfl
example : R.StoreBoolAsElement.sizeA = 1 := rfl

end Aggregate

#check CRules32.sizeof_bool
#check CRules32.store_bool
#check CRules32.undef_store_bool
#check CRules32.store_bool_undef_store_bool
#check CRules32.valid_store_bool
#check CRules32.store_bool_align
#check CRules32.undef_store_bool_align
#check CRules32.StoreBoolAsElement
#check CRules32.BoolArray.full_split_to_full
#check CRules32.BoolArray.full_merge_to_full
#check CRules32.BoolArray2.full_split_to_missing_i
#check CRules32.BoolArray3.full
#check CRules32.BoolPtrArray2.full_split_to_missing_i
#check CRules32.BoolPtrArray2.row_blocks_missing_i_merge_to_full
#check CRules64.sizeof_bool
#check CRules64.store_bool
#check CRules64.undef_store_bool
#check CRules64.store_bool_undef_store_bool
#check CRules64.valid_store_bool
#check CRules64.store_bool_align
#check CRules64.undef_store_bool_align
#check CRules64.StoreBoolAsElement
#check CRules64.BoolArray.full_split_to_full
#check CRules64.BoolArray.full_merge_to_full
#check CRules64.BoolArray2.full_split_to_missing_i
#check CRules64.BoolArray3.full
#check CRules64.BoolPtrArray2.full_split_to_missing_i
#check CRules64.BoolPtrArray2.row_blocks_missing_i_merge_to_full
#check naive_C_Rules32.sizeof_bool
#check naive_C_Rules32.store_bool
#check naive_C_Rules32.undef_store_bool
#check naive_C_Rules32.store_bool_undef_store_bool
#check naive_C_Rules32.valid_store_bool
#check naive_C_Rules32.store_bool_align
#check naive_C_Rules32.undef_store_bool_align
#check naive_C_Rules32.StoreBoolAsElement
#check naive_C_Rules32.BoolArray.full_split_to_full
#check naive_C_Rules32.BoolArray.full_merge_to_full
#check naive_C_Rules32.BoolArray2.full_split_to_missing_i
#check naive_C_Rules32.BoolArray3.full
#check naive_C_Rules32.BoolPtrArray2.full_split_to_missing_i
#check naive_C_Rules32.BoolPtrArray2.row_blocks_missing_i_merge_to_full
#check naive_C_Rules64.sizeof_bool
#check naive_C_Rules64.store_bool
#check naive_C_Rules64.undef_store_bool
#check naive_C_Rules64.store_bool_undef_store_bool
#check naive_C_Rules64.valid_store_bool
#check naive_C_Rules64.store_bool_align
#check naive_C_Rules64.undef_store_bool_align
#check naive_C_Rules64.StoreBoolAsElement
#check naive_C_Rules64.BoolArray.full_split_to_full
#check naive_C_Rules64.BoolArray.full_merge_to_full
#check naive_C_Rules64.BoolArray2.full_split_to_missing_i
#check naive_C_Rules64.BoolArray3.full
#check naive_C_Rules64.BoolPtrArray2.full_split_to_missing_i
#check naive_C_Rules64.BoolPtrArray2.row_blocks_missing_i_merge_to_full
#check Snaive_C_Rules32.sizeof_bool
#check Snaive_C_Rules32.store_bool
#check Snaive_C_Rules32.undef_store_bool
#check Snaive_C_Rules32.store_bool_undef_store_bool
#check Snaive_C_Rules32.valid_store_bool
#check Snaive_C_Rules32.store_bool_align
#check Snaive_C_Rules32.undef_store_bool_align
#check Snaive_C_Rules32.StoreBoolAsElement
#check Snaive_C_Rules32.BoolArray.full_split_to_full
#check Snaive_C_Rules32.BoolArray.full_merge_to_full
#check Snaive_C_Rules32.BoolArray2.full_split_to_missing_i
#check Snaive_C_Rules32.BoolArray3.full
#check Snaive_C_Rules32.BoolPtrArray2.full_split_to_missing_i
#check Snaive_C_Rules32.BoolPtrArray2.row_blocks_missing_i_merge_to_full
#check Snaive_C_Rules64.sizeof_bool
#check Snaive_C_Rules64.store_bool
#check Snaive_C_Rules64.undef_store_bool
#check Snaive_C_Rules64.store_bool_undef_store_bool
#check Snaive_C_Rules64.valid_store_bool
#check Snaive_C_Rules64.store_bool_align
#check Snaive_C_Rules64.undef_store_bool_align
#check Snaive_C_Rules64.StoreBoolAsElement
#check Snaive_C_Rules64.BoolArray.full_split_to_full
#check Snaive_C_Rules64.BoolArray.full_merge_to_full
#check Snaive_C_Rules64.BoolArray2.full_split_to_missing_i
#check Snaive_C_Rules64.BoolArray3.full
#check Snaive_C_Rules64.BoolPtrArray2.full_split_to_missing_i
#check Snaive_C_Rules64.BoolPtrArray2.row_blocks_missing_i_merge_to_full

-- The legacy 32-bit facade remains usable.
#check (fun (R : SeparationLogicSig) => R.store_bool)
#check (fun (R : SeparationLogicSig) => R.undef_store_bool)
#check (fun (R : SeparationLogicSig) => R.valid_store_bool)
#check (fun (R : SeparationLogicSig) => R.store_bool_undef_store_bool)
#check (fun (R : SeparationLogicSig) => R.store_bool_align)
#check (fun (R : SeparationLogicSig) => R.undef_store_bool_align)
#check (fun (R : SeparationLogicSig) => R.StoreBoolAsElement)
#check (fun (R : SeparationLogicSig) => R.BoolArray.full)
#check (fun (R : SeparationLogicSig) => R.BoolArray2.full)
#check (fun (R : SeparationLogicSig) => R.BoolArray3.full)
#check (fun (R : SeparationLogicSig) => R.BoolPtrArray2.full)

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``CNotationSig.sizeof_bool, ``store_bool_undef_store_bool,
      ``valid_store_bool, ``undef_store_bool_align, ``store_bool_align,
      ``bool_heap, ``invalid_bool] do
    let allowed := if name == ``CNotationSig.sizeof_bool then allowed ++
      #[``sizeof_struct_type, ``sizeof_union_type, ``sizeof_enum_type, ``sizeof_alias_type]
      else allowed
    for axiomName in (← Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unexpected axiom {axiomName}"

#print axioms store_bool_undef_store_bool
#print axioms valid_store_bool
#print axioms store_bool_align

end
end CoqBoolUpdateTests
