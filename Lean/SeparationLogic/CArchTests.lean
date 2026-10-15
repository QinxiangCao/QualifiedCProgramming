import SimpleC.SL.CArch
import Lean.Util.CollectAxioms

namespace CArchTests

open CompCert
open SimpleC.SL.CArch

-- CArchSig: three parameters, three derived definitions, seven laws, and
-- three validity predicates.
#check CArchSig
#check CArchSig.ptr_size
#check CArchSig.ptr_align
#check CArchSig.addr_max_unsigned
#check CArchSig.ptr_size_Z
#check CArchSig.ptr_width_Z
#check CArchSig.aligned
#check CArchSig.ptr_size_pos
#check CArchSig.ptr_size_32_or_64
#check CArchSig.ptr_align_pos
#check CArchSig.ptr_aligned_aligned_4
#check CArchSig.addr_max_unsigned_ge_7
#check CArchSig.ptr_size_fits_addr
#check CArchSig.int_max_fits_addr
#check CArchSig.valid_addr_range
#check CArchSig.valid_object
#check CArchSig.valid_ptr_value

-- Both concrete architectures retain the complete source module surface.
#check Arch32
#check Arch32.ptr_size
#check Arch32.ptr_align
#check Arch32.addr_max_unsigned
#check Arch32.ptr_size_Z
#check Arch32.ptr_width_Z
#check Arch32.aligned
#check Arch32.ptr_size_pos
#check Arch32.ptr_size_32_or_64
#check Arch32.ptr_align_pos
#check Arch32.ptr_aligned_aligned_4
#check Arch32.addr_max_unsigned_ge_7
#check Arch32.ptr_size_fits_addr
#check Arch32.int_max_fits_addr
#check Arch32.valid_addr_range
#check Arch32.valid_object
#check Arch32.valid_ptr_value

#check Arch64
#check Arch64.ptr_size
#check Arch64.ptr_align
#check Arch64.addr_max_unsigned
#check Arch64.ptr_size_Z
#check Arch64.ptr_width_Z
#check Arch64.aligned
#check Arch64.ptr_size_pos
#check Arch64.ptr_size_32_or_64
#check Arch64.ptr_align_pos
#check Arch64.ptr_aligned_aligned_4
#check Arch64.addr_max_unsigned_ge_7
#check Arch64.ptr_size_fits_addr
#check Arch64.int_max_fits_addr
#check Arch64.valid_addr_range
#check Arch64.valid_object
#check Arch64.valid_ptr_value

-- CEndianSig: seven operations and thirteen laws.
#check CEndianSig
#check CEndianSig.bytes_eqm
#check CEndianSig.n_bytes_to_Z
#check CEndianSig.Z_to_n_bytes
#check CEndianSig.merge_n_bytes
#check CEndianSig.merge_short
#check CEndianSig.merge_int
#check CEndianSig.merge_int64
#check CEndianSig.eqm_bytes_to_Z_eq
#check CEndianSig.Z_to_n_bytes_to_Z
#check CEndianSig.merge_n_bytes_self
#check CEndianSig.merge_byte_equiv_merge_n_bytes
#check CEndianSig.merge_short_equiv_merge_n_bytes
#check CEndianSig.merge_int_equiv_merge_n_bytes
#check CEndianSig.merge_int64_equiv_merge_n_bytes
#check CEndianSig.merge_short_eqm
#check CEndianSig.merge_int_eqm
#check CEndianSig.merge_int64_eqm
#check CEndianSig.merge_short_value_eqm
#check CEndianSig.merge_int_value_eqm
#check CEndianSig.merge_int64_value_eqm

-- Lean Vector compatibility for Coq's visible nil/cons eliminators.
#check vector_cons
#check vector_head
#check vector_tail
#check vector_head_cons
#check vector_tail_cons
#check vector_cons_eta

-- BigEndian additionally exposes the source recursion and range helpers.
#check BigEndian
#check BigEndian.bytes_eqm
#check BigEndian.n_bytes_to_Z
#check BigEndian.Z_to_n_bytes
#check BigEndian.n_bytes_to_Z_cons
#check BigEndian.Z_to_n_bytes_succ
#check BigEndian.merge_n_bytes
#check BigEndian.merge_short
#check BigEndian.merge_int
#check BigEndian.merge_int64
#check BigEndian.eqm_bytes_to_Z_eq
#check BigEndian.Z_to_n_bytes_to_Z
#check BigEndian.n_bytes_to_Z_range
#check BigEndian.merge_n_bytes_self
#check BigEndian.merge_byte_equiv_merge_n_bytes
#check BigEndian.merge_short_equiv_merge_n_bytes
#check BigEndian.merge_int_equiv_merge_n_bytes
#check BigEndian.merge_int64_equiv_merge_n_bytes
#check BigEndian.merge_short_eqm
#check BigEndian.merge_int_eqm
#check BigEndian.merge_int64_eqm
#check BigEndian.merge_short_value_eqm
#check BigEndian.merge_int_value_eqm
#check BigEndian.merge_int64_value_eqm

-- LittleEndian has the same interface, except that its source unfolds
-- Z_to_n_bytes directly and therefore has no separate succ lemma.
#check LittleEndian
#check LittleEndian.bytes_eqm
#check LittleEndian.n_bytes_to_Z
#check LittleEndian.Z_to_n_bytes
#check LittleEndian.n_bytes_to_Z_cons
#check LittleEndian.merge_n_bytes
#check LittleEndian.merge_short
#check LittleEndian.merge_int
#check LittleEndian.merge_int64
#check LittleEndian.eqm_bytes_to_Z_eq
#check LittleEndian.Z_to_n_bytes_to_Z
#check LittleEndian.n_bytes_to_Z_range
#check LittleEndian.merge_n_bytes_self
#check LittleEndian.merge_byte_equiv_merge_n_bytes
#check LittleEndian.merge_short_equiv_merge_n_bytes
#check LittleEndian.merge_int_equiv_merge_n_bytes
#check LittleEndian.merge_int64_equiv_merge_n_bytes
#check LittleEndian.merge_short_eqm
#check LittleEndian.merge_int_eqm
#check LittleEndian.merge_int64_eqm
#check LittleEndian.merge_short_value_eqm
#check LittleEndian.merge_int_value_eqm
#check LittleEndian.merge_int64_value_eqm

-- Architecture constants, derived widths, and exact boundary behavior.
example : Arch32.ptr_size = 4 := rfl
example : Arch32.ptr_align = 4 := rfl
example : Arch32.ptr_size_Z = 4 := rfl
example : Arch32.ptr_width_Z = 32 := rfl
example : Arch32.addr_max_unsigned = Int.max_unsigned := rfl
example : Arch64.ptr_size = 8 := rfl
example : Arch64.ptr_align = 8 := rfl
example : Arch64.ptr_size_Z = 8 := rfl
example : Arch64.ptr_width_Z = 64 := rfl
example : Arch64.addr_max_unsigned = Int64.max_unsigned := rfl

example : CArchSig.ptr_size_Z Arch32 = 4 := rfl
example : CArchSig.ptr_width_Z Arch64 = 64 := rfl
example : Arch32.aligned 4 (-8) := by
  unfold Arch32.aligned Z.modulo
  native_decide
example : Arch64.aligned 8 (-16) := by
  unfold Arch64.aligned Z.modulo
  native_decide
example : ¬Arch64.aligned 8 12 := by
  unfold Arch64.aligned Z.modulo
  native_decide
example : Arch32.valid_addr_range Int.max_unsigned 1 := by
  unfold Arch32.valid_addr_range Arch32.addr_max_unsigned Int.max_unsigned
  native_decide
example : ¬Arch32.valid_addr_range Int.max_unsigned 2 := by
  unfold Arch32.valid_addr_range Arch32.addr_max_unsigned Int.max_unsigned
  native_decide
example : Arch32.valid_addr_range 0 0 := by
  unfold Arch32.valid_addr_range Arch32.addr_max_unsigned Int.max_unsigned
  native_decide
example : Arch64.valid_object 16 8 8 := by
  unfold Arch64.valid_object Arch64.valid_addr_range Arch64.aligned
    Arch64.addr_max_unsigned Int64.max_unsigned Z.modulo
  native_decide
example : ¬Arch64.valid_object 12 8 8 := by
  unfold Arch64.valid_object Arch64.valid_addr_range Arch64.aligned
    Arch64.addr_max_unsigned Int64.max_unsigned Z.modulo
  native_decide
example : Arch64.valid_ptr_value Int64.max_unsigned := by
  unfold Arch64.valid_ptr_value Arch64.addr_max_unsigned
  native_decide
example : ¬Arch64.valid_ptr_value (Int64.max_unsigned + 1) := by
  unfold Arch64.valid_ptr_value Arch64.addr_max_unsigned Int64.max_unsigned
  native_decide

-- Byte equivalence is pointwise and normalizes every byte modulo 256.
example : BigEndian.bytes_eqm 2 #v[-1, 256] #v[255, 0] := by
  simp only [BigEndian.bytes_eqm]
  change Byte.eqm (-1) 255 ∧ Byte.eqm 256 0 ∧ True
  exact ⟨⟨-1, by native_decide⟩, ⟨⟨1, by native_decide⟩, trivial⟩⟩
example : LittleEndian.bytes_eqm 2 #v[-1, 256] #v[255, 0] := by
  simp only [LittleEndian.bytes_eqm]
  change Byte.eqm (-1) 255 ∧ Byte.eqm 256 0 ∧ True
  exact ⟨⟨-1, by native_decide⟩, ⟨⟨1, by native_decide⟩, trivial⟩⟩
example : ¬BigEndian.bytes_eqm 2 #v[1, 2] #v[1, 3] := by
  intro h
  have heq := BigEndian.eqm_bytes_to_Z_eq 2 #v[1, 2] #v[1, 3] h
  have hne : BigEndian.n_bytes_to_Z 2 #v[1, 2] ≠
      BigEndian.n_bytes_to_Z 2 #v[1, 3] := by native_decide
  exact hne heq

-- Big endian places the first byte at the highest position.
example : BigEndian.n_bytes_to_Z 1 #v[35] = 35 := by native_decide
example : BigEndian.n_bytes_to_Z 2 #v[1, 2] = 258 := by native_decide
example : BigEndian.n_bytes_to_Z 4 #v[1, 2, 3, 4] = 16909060 := by
  native_decide
example : BigEndian.n_bytes_to_Z 8 #v[1, 2, 3, 4, 5, 6, 7, 8] =
    72623859790382856 := by native_decide
example : BigEndian.n_bytes_to_Z 2 #v[-1, 256] = 65280 := by native_decide

example : BigEndian.Z_to_n_bytes 35 1 = #v[35] := by native_decide
example : BigEndian.Z_to_n_bytes 258 2 = #v[1, 2] := by native_decide
example : BigEndian.Z_to_n_bytes 16909060 4 = #v[1, 2, 3, 4] := by
  native_decide
example : BigEndian.Z_to_n_bytes 72623859790382856 8 =
    #v[1, 2, 3, 4, 5, 6, 7, 8] := by native_decide
example : BigEndian.Z_to_n_bytes 291 1 = #v[35] := by native_decide
example : BigEndian.Z_to_n_bytes (-1) 4 = #v[255, 255, 255, 255] := by
  native_decide

-- Little endian places the first byte at the lowest position.
example : LittleEndian.n_bytes_to_Z 1 #v[35] = 35 := by native_decide
example : LittleEndian.n_bytes_to_Z 2 #v[1, 2] = 513 := by native_decide
example : LittleEndian.n_bytes_to_Z 4 #v[1, 2, 3, 4] = 67305985 := by
  native_decide
example : LittleEndian.n_bytes_to_Z 8 #v[1, 2, 3, 4, 5, 6, 7, 8] =
    578437695752307201 := by native_decide
example : LittleEndian.n_bytes_to_Z 2 #v[-1, 256] = 255 := by native_decide

example : LittleEndian.Z_to_n_bytes 35 1 = #v[35] := by native_decide
example : LittleEndian.Z_to_n_bytes 258 2 = #v[2, 1] := by native_decide
example : LittleEndian.Z_to_n_bytes 16909060 4 = #v[4, 3, 2, 1] := by
  native_decide
example : LittleEndian.Z_to_n_bytes 72623859790382856 8 =
    #v[8, 7, 6, 5, 4, 3, 2, 1] := by native_decide
example : LittleEndian.Z_to_n_bytes 291 1 = #v[35] := by native_decide
example : LittleEndian.Z_to_n_bytes (-1) 4 = #v[255, 255, 255, 255] := by
  native_decide

-- The same bytes decode differently, and each merge relation follows its
-- concrete byte order while retaining modulo wrapping.
example : BigEndian.merge_int 1 2 3 4 16909060 := by
  unfold BigEndian.merge_int Z.modulo Z.pow
  native_decide
example : ¬BigEndian.merge_int 1 2 3 4 67305985 := by
  unfold BigEndian.merge_int Z.modulo Z.pow
  native_decide
example : LittleEndian.merge_int 1 2 3 4 67305985 := by
  unfold LittleEndian.merge_int Z.modulo Z.pow
  native_decide
example : ¬LittleEndian.merge_int 1 2 3 4 16909060 := by
  unfold LittleEndian.merge_int Z.modulo Z.pow
  native_decide
example : BigEndian.merge_int 1 2 3 4 (16909060 + Z.pow 2 32) := by
  unfold BigEndian.merge_int Z.modulo Z.pow
  native_decide
example : LittleEndian.merge_int 1 2 3 4 (67305985 + Z.pow 2 32) := by
  unfold LittleEndian.merge_int Z.modulo Z.pow
  native_decide

-- Packaged module-type values preserve the concrete computation.
example : CEndianSig.n_bytes_to_Z BigEndian 4 #v[1, 2, 3, 4] = 16909060 := by
  native_decide
example : CEndianSig.n_bytes_to_Z LittleEndian 4 #v[1, 2, 3, 4] = 67305985 := by
  native_decide
example : CEndianSig.Z_to_n_bytes BigEndian 16909060 4 = #v[1, 2, 3, 4] := by
  native_decide
example : CEndianSig.Z_to_n_bytes LittleEndian 16909060 4 = #v[4, 3, 2, 1] := by
  native_decide

#print axioms Arch64.ptr_aligned_aligned_4
#print axioms BigEndian.Z_to_n_bytes_to_Z
#print axioms BigEndian.n_bytes_to_Z_range
#print axioms BigEndian.merge_int64_eqm
#print axioms LittleEndian.Z_to_n_bytes_to_Z
#print axioms LittleEndian.n_bytes_to_Z_range
#print axioms LittleEndian.merge_int64_eqm

end CArchTests
