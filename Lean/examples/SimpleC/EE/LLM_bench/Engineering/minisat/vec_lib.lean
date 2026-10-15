import SimpleC.SL.SeparationLogic
import SimpleC.SL.CArch
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Engineering.minisat.vec_lib
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion SimpleC.SL.SeparationLogic
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
export SimpleC.SL.CArch.Arch32 (ptr_size ptr_size_Z addr_max_unsigned)
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

def vec_alloc_ok (stride cap : Int) : Prop :=
  0 < stride ∧ 0 ≤ cap ∧ (0 ≤ cap * stride ∧ cap * stride ≤ Int.max_unsigned)

def vec_growth_ok (stride cap : Int) : Prop :=
  0 < stride ∧ 0 ≤ cap ∧ 2 * cap ≤ Int.max_signed ∧
  2 * cap + 1 ≤ Int.max_signed ∧
  (0 ≤ (2 * cap + 1) * stride ∧ (2 * cap + 1) * stride ≤ Int.max_unsigned) ∧
  (2 * cap + 1) * stride ≤ addr_max_unsigned + 1

def vec_push_result (len oldbuf oldcap newbuf newcap : Int) : Prop :=
  (len < oldcap ∧ newbuf = oldbuf ∧ newcap = oldcap) ∨
  (len = oldcap ∧ newcap = 2 * oldcap + 1)

noncomputable def veci_buffer (buf : addr) (xs : List Int) (cap : Int) : Assertion :=
  intArray.full buf (Zlength xs) xs ** intArray.undef_seg buf (Zlength xs) cap

noncomputable def veci_header (v : addr) (len cap : Int) (buf : addr) : Assertion :=
  ((&((v # "veci_t") ->ₛ "size")) # INT |-> len) **
  ((&((v # "veci_t") ->ₛ "cap")) # INT |-> cap) **
  ((&((v # "veci_t") ->ₛ "ptr")) # PTR |-> buf)

noncomputable def veci_raw (v buf : addr) (cap : Int) (xs : List Int) : Assertion :=
  “ v ≠ 0 ∧ buf ≠ 0 ∧ 0 ≤ Zlength xs ∧ Zlength xs ≤ cap ∧
    4 ≤ cap ∧ cap ≤ Int.max_signed ∧ vec_alloc_ok (sizeof(INT)) cap ” &&
  (veci_header v (Zlength xs) cap buf ** veci_buffer buf xs cap)

noncomputable def store_veci (v : addr) (xs : List Int) : Assertion :=
  EX buf : addr, EX cap : Int, veci_raw v buf cap xs

noncomputable def veci_shell (v : addr) : Assertion :=
  “ v ≠ 0 ” &&
  (((&((v # "veci_t") ->ₛ "size")) # INT |->_) **
   ((&((v # "veci_t") ->ₛ "cap")) # INT |->_) **
   ((&((v # "veci_t") ->ₛ "ptr")) # PTR |->_))

noncomputable def vecp_buffer (buf : addr) (xs : List Int) (cap : Int) : Assertion :=
  ptrArray.full buf (Zlength xs) xs ** ptrArray.undef_seg buf (Zlength xs) cap

noncomputable def vecp_header (v : addr) (len cap : Int) (buf : addr) : Assertion :=
  ((&((v # "vecp_t") ->ₛ "size")) # INT |-> len) **
  ((&((v # "vecp_t") ->ₛ "cap")) # INT |-> cap) **
  ((&((v # "vecp_t") ->ₛ "ptr")) # PTR |-> buf)

noncomputable def vecp_raw (v buf : addr) (cap : Int) (xs : List Int) : Assertion :=
  “ v ≠ 0 ∧ buf ≠ 0 ∧ 0 ≤ Zlength xs ∧ Zlength xs ≤ cap ∧
    4 ≤ cap ∧ cap ≤ Int.max_signed ∧ vec_alloc_ok ptr_size_Z cap ” &&
  (vecp_header v (Zlength xs) cap buf ** vecp_buffer buf xs cap)

noncomputable def store_vecp (v : addr) (xs : List Int) : Assertion :=
  EX buf : addr, EX cap : Int, vecp_raw v buf cap xs

noncomputable def vecp_shell (v : addr) : Assertion :=
  “ v ≠ 0 ” &&
  (((&((v # "vecp_t") ->ₛ "size")) # INT |->_) **
   ((&((v # "vecp_t") ->ₛ "cap")) # INT |->_) **
   ((&((v # "vecp_t") ->ₛ "ptr")) # PTR |->_))

theorem veci_buffer_truncate__resize_prefix (buf : addr) (xs : List Int) (cap k : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength xs) (hc : Zlength xs ≤ cap) :
    intArray.full buf (Zlength xs) xs ** intArray.undef_seg buf (Zlength xs) cap |--
    intArray.full buf k (sublist 0 k xs) ** intArray.undef_seg buf k cap := by
  sep_apply (intArray.full_split_to_seg buf k (Zlength xs) xs hk)
  sep_apply (intArray.seg_to_full buf 0 k (sublist 0 k xs))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (intArray.seg_to_undef_seg buf k (Zlength xs) (sublist k (Zlength xs) xs))
  sep_apply (intArray.undef_seg_merge_to_undef_seg buf k (Zlength xs) cap (by omega))
  cancel

theorem vecp_buffer_truncate__resize_prefix (buf : addr) (xs : List Int) (cap k : Int)
    (hk : 0 ≤ k ∧ k ≤ Zlength xs) (hc : Zlength xs ≤ cap) :
    ptrArray.full buf (Zlength xs) xs ** ptrArray.undef_seg buf (Zlength xs) cap |--
    ptrArray.full buf k (sublist 0 k xs) ** ptrArray.undef_seg buf k cap := by
  sep_apply (ptrArray.full_split_to_seg buf k (Zlength xs) xs hk)
  sep_apply (ptrArray.seg_to_full buf 0 k (sublist 0 k xs))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (ptrArray.seg_to_undef_seg buf k (Zlength xs) (sublist k (Zlength xs) xs))
  sep_apply (ptrArray.undef_seg_merge_to_undef_seg buf k (Zlength xs) cap (by omega))
  cancel

theorem reassociate_sepcon_7_entail__push_nongrowth {P1 P2 P3 P4 P5 P6 P7 Q : Assertion}
    (h : P1 ** P2 ** P3 ** P4 ** P5 ** P6 ** P7 |-- Q) :
    P1 ** (P2 ** (P3 ** (P4 ** (P5 ** (P6 ** P7))))) |-- Q := by
  sep_apply h
  cancel

theorem vec_push_result_from_branches__push_final (len oldbuf oldcap newbuf newcap : Int)
    (hle : len ≤ oldcap) (hnew : len < newcap)
    (hsame : len < oldcap → newbuf = oldbuf ∧ newcap = oldcap)
    (hgrow : len = oldcap → newcap = 2 * oldcap + 1) :
    vec_push_result len oldbuf oldcap newbuf newcap := by
  by_cases h : len < oldcap
  · exact Or.inl ⟨h, hsame h⟩
  · have he : len = oldcap := by omega
    exact Or.inr ⟨he, hgrow he⟩

end SimpleC.EE.LLM_bench.Engineering.minisat.vec_lib
namespace SimpleC.EE.LLM_bench.Engineering.minisat
export vec_lib (vec_alloc_ok vec_growth_ok vec_push_result veci_buffer veci_header veci_raw
  store_veci veci_shell vecp_buffer vecp_header vecp_raw store_vecp vecp_shell ptr_size_Z addr_max_unsigned)
end SimpleC.EE.LLM_bench.Engineering.minisat
