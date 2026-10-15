import SimpleC.SL.CommonAssertion

namespace CommonAssertionArchTests

open SimpleC.SL.CArch
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

def TestRules : SeparationLogicSig where
  toContext := Facade.Smoke.Ctx
  mstore := fun _ _ _ => False
  mstore_noninit := fun _ _ => False
  mstore_mstore_noninit := by
    intro _ _ _ h
    exact False.elim h
  mstore_eqm := by
    intro _ _ _ _ state h
    exact False.elim h
  dup_mstore_noninit := by
    intro _ state h
    rcases h with ⟨_, _, _, hFalse, _⟩
    exact False.elim hFalse

local instance : SacContext := ⟨TestRules⟩

#check DerivedPredSig.canonical
#check DerivedPredSig.addr_max_unsigned
#check DerivedPredSig.ptr_size
#check DerivedPredSig.ptr_align
#check DerivedPredSig.ptr_size_Z
#check DerivedPredSig.ptr_width_Z
#check DerivedPredSig.aligned
#check DerivedPredSig.valid_addr_range
#check DerivedPredSig.valid_object
#check DerivedPredSig.valid_ptr_value
#check DerivedPredSig.merge_n_bytes
#check DerivedPredSig.store_ptr
#check DerivedPredSig.undef_store_ptr

example : BigEndian.merge_int 1 2 3 4 16909060 := by
  unfold BigEndian.merge_int Z.modulo Z.pow
  native_decide

example : LittleEndian.merge_int 1 2 3 4 67305985 := by
  unfold LittleEndian.merge_int Z.modulo Z.pow
  native_decide

example : ¬BigEndian.merge_int 1 2 3 4 67305985 := by
  unfold BigEndian.merge_int Z.modulo Z.pow
  native_decide

example : ¬LittleEndian.merge_int 1 2 3 4 16909060 := by
  unfold LittleEndian.merge_int Z.modulo Z.pow
  native_decide

section Arch32Big

local instance : SacArchContext := ⟨Arch32⟩
local instance : SacEndianContext := ⟨BigEndian⟩

example (x value : Int) :
    (x # PTR |-> value) = store_ptr Arch32 BigEndian TestRules x value := rfl

example (x value : Int) :
    poly_store Arch32 BigEndian TestRules FET_ptr x value =
      store_ptr Arch32 BigEndian TestRules x value := by
  simp [poly_store]

example (x value : Int) :
    typed_poly_store Arch32 BigEndian TestRules FET_ptr x
        (by simpa [front_end_type_value] using value) =
      store_ptr Arch32 BigEndian TestRules x value := by
  simp [typed_poly_store, front_end_type_value]

example (x value : Int) :
    poly_store Arch32 BigEndian TestRules FET_int x value =
      store_int Arch32 BigEndian TestRules x value := by
  simp [poly_store]

example (x value : Int) :
    store_int Arch32 BigEndian TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (isvalidptr_int Arch32 x ∧ value <= Int.max_signed ∧
            value >= Int.min_signed))
        (store_4byte BigEndian TestRules x value) := rfl

example (x value : Int) :
    store_ptr Arch32 BigEndian TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (isvalidptr Arch32 x ∧ valid_ptr_value Arch32 value))
        (store_4byte BigEndian TestRules x value) := rfl

example (x value : Int) (P : TestRules.expr)
    (hGuard : isvalidptr Arch32 x ∧ valid_ptr_value Arch32 value)
    (hRule : store_ptr Arch32 BigEndian TestRules x value |-- P) :
    store_4byte BigEndian TestRules x value |-- P := by
  sep_apply hRule
  simpl_auto

example (x value : Int)
    (hGuard : isvalidptr Arch32 x ∧ valid_ptr_value Arch32 value) :
    store_4byte BigEndian TestRules x value |--
      store_ptr Arch32 BigEndian TestRules x value := by
  entailer!

end Arch32Big

section Arch32Little

local instance : SacArchContext := ⟨Arch32⟩
local instance : SacEndianContext := ⟨LittleEndian⟩

example (x value : Int) :
    (x # PTR |-> value) = store_ptr Arch32 LittleEndian TestRules x value := rfl

example (x value : Int) :
    poly_store Arch32 LittleEndian TestRules FET_ptr x value =
      store_ptr Arch32 LittleEndian TestRules x value := by
  simp [poly_store]

example (x value : Int) :
    typed_poly_store Arch32 LittleEndian TestRules FET_ptr x
        (by simpa [front_end_type_value] using value) =
      store_ptr Arch32 LittleEndian TestRules x value := by
  simp [typed_poly_store, front_end_type_value]

example (x value : Int) :
    poly_store Arch32 LittleEndian TestRules FET_int x value =
      store_int Arch32 LittleEndian TestRules x value := by
  simp [poly_store]

example (x value : Int) :
    store_int Arch32 LittleEndian TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (isvalidptr_int Arch32 x ∧ value <= Int.max_signed ∧
            value >= Int.min_signed))
        (store_4byte LittleEndian TestRules x value) := rfl

example (x value : Int) :
    store_ptr Arch32 LittleEndian TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (isvalidptr Arch32 x ∧ valid_ptr_value Arch32 value))
        (store_4byte LittleEndian TestRules x value) := rfl

example (x value : Int) (P : TestRules.expr)
    (hGuard : isvalidptr Arch32 x ∧ valid_ptr_value Arch32 value)
    (hRule : store_ptr Arch32 LittleEndian TestRules x value |-- P) :
    store_4byte LittleEndian TestRules x value |-- P := by
  sep_apply hRule
  simpl_auto

end Arch32Little

section Arch64Big

local instance : SacArchContext := ⟨Arch64⟩
local instance : SacEndianContext := ⟨BigEndian⟩

example (x value : Int) :
    (x # PTR |-> value) = store_ptr Arch64 BigEndian TestRules x value := rfl

example (x value : Int) :
    poly_store Arch64 BigEndian TestRules FET_ptr x value =
      store_ptr Arch64 BigEndian TestRules x value := by
  simp [poly_store]

example (x value : Int) :
    typed_poly_store Arch64 BigEndian TestRules FET_ptr x
        (by simpa [front_end_type_value] using value) =
      store_ptr Arch64 BigEndian TestRules x value := by
  simp [typed_poly_store, front_end_type_value]

example (x value : Int) :
    poly_store Arch64 BigEndian TestRules FET_int x value =
      store_int Arch64 BigEndian TestRules x value := by
  simp [poly_store]

example (x value : Int) :
    store_int Arch64 BigEndian TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (isvalidptr_int Arch64 x ∧ value <= Int.max_signed ∧
            value >= Int.min_signed))
        (store_4byte BigEndian TestRules x value) := rfl

example (x value : Int) :
    store_ptr Arch64 BigEndian TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (isvalidptr Arch64 x ∧ valid_ptr_value Arch64 value))
        (store_8byte BigEndian TestRules x value) := rfl

example (x value : Int) (P : TestRules.expr)
    (hGuard : isvalidptr Arch64 x ∧ valid_ptr_value Arch64 value)
    (hRule : store_ptr Arch64 BigEndian TestRules x value |-- P) :
    store_8byte BigEndian TestRules x value |-- P := by
  sep_apply hRule
  simpl_auto

end Arch64Big

section Arch64Little

local instance : SacArchContext := ⟨Arch64⟩
local instance : SacEndianContext := ⟨LittleEndian⟩

example (x value : Int) :
    (x # PTR |-> value) = store_ptr Arch64 LittleEndian TestRules x value := rfl

example (x value : Int) :
    poly_store Arch64 LittleEndian TestRules FET_ptr x value =
      store_ptr Arch64 LittleEndian TestRules x value := by
  simp [poly_store]

example (x value : Int) :
    typed_poly_store Arch64 LittleEndian TestRules FET_ptr x
        (by simpa [front_end_type_value] using value) =
      store_ptr Arch64 LittleEndian TestRules x value := by
  simp [typed_poly_store, front_end_type_value]

example (x value : Int) :
    poly_store Arch64 LittleEndian TestRules FET_int x value =
      store_int Arch64 LittleEndian TestRules x value := by
  simp [poly_store]

example (x value : Int) :
    store_int Arch64 LittleEndian TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (isvalidptr_int Arch64 x ∧ value <= Int.max_signed ∧
            value >= Int.min_signed))
        (store_4byte LittleEndian TestRules x value) := rfl

example (x value : Int) :
    store_ptr Arch64 LittleEndian TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (isvalidptr Arch64 x ∧ valid_ptr_value Arch64 value))
        (store_8byte LittleEndian TestRules x value) := rfl

example (x value : Int) (P : TestRules.expr)
    (hGuard : isvalidptr Arch64 x ∧ valid_ptr_value Arch64 value)
    (hRule : store_ptr Arch64 LittleEndian TestRules x value |-- P) :
    store_8byte LittleEndian TestRules x value |-- P := by
  sep_apply hRule
  simpl_auto

example (xi vi xp vp : Int) (P : TestRules.expr)
    (hInt : isvalidptr_int Arch64 xi ∧ vi <= Int.max_signed ∧
      vi >= Int.min_signed)
    (hPtr : isvalidptr Arch64 xp ∧ valid_ptr_value Arch64 vp)
    (hRule :
      store_int Arch64 LittleEndian TestRules xi vi **
          store_ptr Arch64 LittleEndian TestRules xp vp |-- P) :
    store_4byte LittleEndian TestRules xi vi **
        store_8byte LittleEndian TestRules xp vp |-- P := by
  sep_apply hRule
  simpl_auto

example (x : Int) (Q : Int -> TestRules.expr)
    (h : ∀ value, store_ptr Arch64 LittleEndian TestRules x value |-- Q value) :
    TestRules.exp Int (fun value => store_ptr Arch64 LittleEndian TestRules x value) |--
      TestRules.exp Int Q := by
  rel_rw [h]
  exact TestRules.toContext.derivable1_refl _

end Arch64Little

example (Arch : CArchSig) (h : Arch.ptr_size = 4) :
    DerivedPredSig.ptr_size Arch = 4 := by
  unfold_arch
  exact h

example (Arch : CArchSig) (h : Arch.ptr_size = 4) :
    DerivedPredSig.ptr_size Arch = 4 := by
  fold_arch
  exact h

example : DerivedPredSig.ptr_width_Z Arch64 = 64 := by
  solve_arch

example (q n : Int) (hq : q <= 0) (hn : 0 <= n) : q * n <= 0 := by
  fail_if_success simpl_auto_with (omega)
  simpl_auto_with (nia)

example (A B : Prop) (hAB : A -> B) (hA : A) : B := by
  simpl_auto_with (omega)

structure AutoReflexiveRel (x y : Nat) : Prop where
  eq : x = y

local instance : AUXLib.Equivalence AutoReflexiveRel where
  refl _ := ⟨rfl⟩
  symm _ _ h := ⟨h.eq.symm⟩
  trans _ _ _ hxy hyz := ⟨hxy.eq.trans hyz.eq⟩

example (x : Nat) : AutoReflexiveRel x x := by
  simpl_auto_with (omega)

-- Coq's `simpl_entail_with` only decomposes conjunctions.  In particular it
-- must not commit to the first constructor of an unrelated inductive target.
example (A : Prop) : A ∨ ¬A := by
  simpl_entail_with (omega)
  exact Classical.em A

example (A : Prop) : A ∨ ¬A := by
  simpl_entail
  exact Classical.em A

example (q n : Int) (hq : q <= 0) (hn : 0 <= n) :
    q * n <= 0 ∧ q * (n + 1) <= 0 := by
  simpl_entail_with (nia)

example (q n : Int) (hq : q <= 0) (hn : 0 <= n) (P : TestRules.expr) :
    P |-- “ q * n <= 0 ” := by
  entailer_with (nia)

def CustomPreProcessGoal : Prop :=
  ∀ (q n : Int), q <= 0 -> 0 <= n ->
    ∀ P : TestRules.expr, P |-- “ q * n <= 0 ”

example : CustomPreProcessGoal := by
  LLM_pre_process (nia)

example : CustomPreProcessGoal := by
  LLM_pre_process_tac (nia)

example (P Q : TestRules.expr) (h : P |-- Q) : P |-- Q := by
  Goal_apply_finish h

example (P Q R : TestRules.expr) (h : P |-- Q) : P ** R |-- Q ** R := by
  Goal_apply_finish h

-- `Goal_apply` is transactional: a partial sep_apply result is a failure and
-- the original goal is restored.  `Goal_apply_finish` accepts the same partial
-- application and then runs the source `entailer!` cleanup pipeline.
example (P Q R S : TestRules.expr) (_h : P |-- Q)
    (hGoal : P ** R |-- Q ** S) : P ** R |-- Q ** S := by
  fail_if_success Goal_apply _h
  exact hGoal

example (P Q R S : TestRules.expr) (h : P |-- Q) (hRS : R |-- S) :
    P ** R |-- Q ** S := by
  Goal_apply_finish h

#print axioms DerivedPredSig.ptr_size_32_or_64
#print axioms DerivedPredSig.store_ptr

end CommonAssertionArchTests
