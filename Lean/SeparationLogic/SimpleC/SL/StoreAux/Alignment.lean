import SimpleC.SL.StoreAux.Relations

namespace SimpleC.SL.StoreAux.StoreLibSig

open AUXLib
open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.FloatLib
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

section Canonical

variable {Arch : CArchSig} {Endian : CEndianSig}

local notation "store_2byte" => DerivedPredSig.store_2byte Endian
local notation "store_4byte" => DerivedPredSig.store_4byte Endian
local notation "store_8byte" => DerivedPredSig.store_8byte Endian
local notation "store_16byte" => DerivedPredSig.store_16byte Endian
local notation "store_char" => DerivedPredSig.store_char Arch
local notation "undef_store_char" => DerivedPredSig.undef_store_char Arch
local notation "store_uchar" => DerivedPredSig.store_uchar Arch
local notation "undef_store_uchar" => DerivedPredSig.undef_store_uchar Arch
local notation "store_short" => DerivedPredSig.store_short Arch Endian
local notation "undef_store_short" => DerivedPredSig.undef_store_short Arch
local notation "store_ushort" => DerivedPredSig.store_ushort Arch Endian
local notation "undef_store_ushort" => DerivedPredSig.undef_store_ushort Arch
local notation "store_int" => DerivedPredSig.store_int Arch Endian
local notation "undef_store_int" => DerivedPredSig.undef_store_int Arch
local notation "store_uint" => DerivedPredSig.store_uint Arch Endian
local notation "undef_store_uint" => DerivedPredSig.undef_store_uint Arch
local notation "store_int64" => DerivedPredSig.store_int64 Arch Endian
local notation "undef_store_int64" => DerivedPredSig.undef_store_int64 Arch
local notation "store_uint64" => DerivedPredSig.store_uint64 Arch Endian
local notation "undef_store_uint64" => DerivedPredSig.undef_store_uint64 Arch
local notation "store_int128" => DerivedPredSig.store_int128 Arch Endian
local notation "undef_store_int128" => DerivedPredSig.undef_store_int128 Arch
local notation "store_uint128" => DerivedPredSig.store_uint128 Arch Endian
local notation "undef_store_uint128" => DerivedPredSig.undef_store_uint128 Arch
local notation "store_float" => DerivedPredSig.store_float Arch Endian
local notation "undef_store_float" => DerivedPredSig.undef_store_float Arch
local notation "store_double" => DerivedPredSig.store_double Arch Endian
local notation "undef_store_double" => DerivedPredSig.undef_store_double Arch
local notation "store_long_double" => DerivedPredSig.store_long_double Arch Endian
local notation "undef_store_long_double" => DerivedPredSig.undef_store_long_double Arch
local notation "store_finite_float" => DerivedPredSig.store_finite_float Arch Endian
local notation "store_finite_double" => DerivedPredSig.store_finite_double Arch Endian
local notation "store_finite_long_double" =>
  DerivedPredSig.store_finite_long_double Arch Endian
local notation "store_ptr" => DerivedPredSig.store_ptr Arch Endian
local notation "undef_store_ptr" => DerivedPredSig.undef_store_ptr Arch
local notation "store_align4_list" => DerivedPredSig.store_align4_list Arch
local notation "store_align4_n" => DerivedPredSig.store_align4_n Arch
local notation "store_align_list" => DerivedPredSig.store_align_list Arch
local notation "store_align_n" => DerivedPredSig.store_align_n Arch
local notation "isvalidptr_char" => DerivedPredSig.isvalidptr_char Arch
local notation "isvalidptr_short" => DerivedPredSig.isvalidptr_short Arch
local notation "isvalidptr_int" => DerivedPredSig.isvalidptr_int Arch
local notation "isvalidptr_int64" => DerivedPredSig.isvalidptr_int64 Arch
local notation "isvalidptr_int128" => DerivedPredSig.isvalidptr_int128 Arch
local notation "isvalidptr_float" => DerivedPredSig.isvalidptr_float Arch
local notation "isvalidptr_double" => DerivedPredSig.isvalidptr_double Arch
local notation "isvalidptr_long_double" => DerivedPredSig.isvalidptr_long_double Arch
local notation "isvalidptr" => DerivedPredSig.isvalidptr Arch
local notation "valid_ptr_value" => DerivedPredSig.valid_ptr_value Arch

theorem valid_store_char (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_char CRules x v)
      (CRules.coq_prop
        ((Byte.min_signed <= v ∧ v <= Byte.max_signed) ∧ isvalidptr_char x)) := by
  intro _ h
  exact ⟨⟨h.1.2.2, h.1.2.1⟩, h.1.1⟩

theorem valid_store_uchar (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uchar CRules x v)
      (CRules.coq_prop ((0 <= v ∧ v <= Byte.max_unsigned) ∧ isvalidptr_char x)) := by
  intro _ h
  exact ⟨h.1.2, h.1.1⟩

theorem valid_undef_store_char (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_char CRules x)
      (CRules.coq_prop (isvalidptr_char x)) := by
  intro _ h
  exact h.1

theorem valid_undef_store_uchar (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_uchar CRules x)
      (CRules.coq_prop (isvalidptr_char x)) := by
  intro _ h
  exact h.1

theorem valid_store_short (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_short CRules x v)
      (CRules.coq_prop ((-32768 <= v ∧ v <= 32767) ∧ isvalidptr_short x)) := by
  intro _ h
  exact ⟨⟨h.1.2.2, h.1.2.1⟩, h.1.1⟩

theorem valid_store_ushort (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_ushort CRules x v)
      (CRules.coq_prop ((0 <= v ∧ v <= 65535) ∧ isvalidptr_short x)) := by
  intro _ h
  exact ⟨h.1.2, h.1.1⟩

theorem valid_undef_store_short (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_short CRules x)
      (CRules.coq_prop (isvalidptr_short x)) := by
  intro _ h
  exact h.1

theorem valid_undef_store_ushort (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_ushort CRules x)
      (CRules.coq_prop (isvalidptr_short x)) := by
  intro _ h
  exact h.1

theorem valid_store_int (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int CRules x v)
      (CRules.coq_prop
        ((Int.min_signed <= v ∧ v <= Int.max_signed) ∧ isvalidptr_int x)) := by
  intro _ h
  exact ⟨⟨h.1.2.2, h.1.2.1⟩, h.1.1⟩

theorem valid_store_uint (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint CRules x v)
      (CRules.coq_prop ((0 <= v ∧ v <= Int.max_unsigned) ∧ isvalidptr_int x)) := by
  intro _ h
  exact ⟨h.1.2, h.1.1⟩

theorem valid_undef_store_int (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_int CRules x)
      (CRules.coq_prop (isvalidptr_int x)) := by
  intro _ h
  exact h.1

theorem valid_undef_store_uint (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_uint CRules x)
      (CRules.coq_prop (isvalidptr_int x)) := by
  intro _ h
  exact h.1

theorem valid_store_int64 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int64 CRules x v)
      (CRules.coq_prop
        ((Int64.min_signed <= v ∧ v <= Int64.max_signed) ∧ isvalidptr_int64 x)) := by
  intro _ h
  exact ⟨⟨h.1.2.2, h.1.2.1⟩, h.1.1⟩

theorem valid_store_uint64 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint64 CRules x v)
      (CRules.coq_prop ((0 <= v ∧ v <= Int64.max_unsigned) ∧ isvalidptr_int64 x)) := by
  intro _ h
  exact ⟨h.1.2, h.1.1⟩

theorem valid_undef_store_int64 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_int64 CRules x)
      (CRules.coq_prop (isvalidptr_int64 x)) := by
  intro _ h
  exact h.1

theorem valid_undef_store_uint64 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_uint64 CRules x)
      (CRules.coq_prop (isvalidptr_int64 x)) := by
  intro _ h
  exact h.1

theorem valid_store_int128 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int128 CRules x v)
      (CRules.coq_prop
        ((SimpleC.SL.IntLib.Int128.min_signed <= v ∧
            v <= SimpleC.SL.IntLib.Int128.max_signed) ∧ isvalidptr_int128 x)) := by
  intro _ h
  exact ⟨⟨h.1.2.2, h.1.2.1⟩, h.1.1⟩

theorem valid_store_uint128 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint128 CRules x v)
      (CRules.coq_prop
        ((0 <= v ∧ v <= SimpleC.SL.IntLib.Int128.max_unsigned) ∧
          isvalidptr_int128 x)) := by
  intro _ h
  exact ⟨h.1.2, h.1.1⟩

theorem valid_undef_store_int128 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_int128 CRules x)
      (CRules.coq_prop (isvalidptr_int128 x)) := by
  intro _ h
  exact h.1

theorem valid_undef_store_uint128 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_uint128 CRules x)
      (CRules.coq_prop (isvalidptr_int128 x)) := by
  intro _ h
  exact h.1

theorem valid_store_float (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_float CRules x v)
      (CRules.coq_prop (isvalidptr_float x)) := by
  intro _ h
  exact h.1.1

theorem valid_store_double (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_double CRules x v)
      (CRules.coq_prop (isvalidptr_double x)) := by
  intro _ h
  exact h.1.1

theorem valid_store_long_double
    (CRules : SeparationLogicSig) (x : Int) (v : fp128) :
    CRules.derivable1 (store_long_double CRules x v)
      (CRules.coq_prop (isvalidptr_long_double x)) := by
  intro _ h
  exact h.1.1

theorem valid_store_finite_float
    (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_finite_float CRules x v)
      (CRules.coq_prop (fp32_isFinite v ∧ isvalidptr_float x)) := by
  intro _ h
  exact ⟨h.1, h.2.1.1⟩

theorem valid_store_finite_double
    (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_finite_double CRules x v)
      (CRules.coq_prop (fp64_isFinite v ∧ isvalidptr_double x)) := by
  intro _ h
  exact ⟨h.1, h.2.1.1⟩

theorem valid_store_finite_long_double
    (CRules : SeparationLogicSig) (x : Int) (v : fp128) :
    CRules.derivable1 (store_finite_long_double CRules x v)
      (CRules.coq_prop (fp128_isFinite v ∧ isvalidptr_long_double x)) := by
  intro _ h
  exact ⟨h.1, h.2.1.1⟩

theorem valid_store_ptr (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_ptr CRules x v)
      (CRules.coq_prop (isvalidptr x ∧ valid_ptr_value v)) := by
  intro _ h
  exact ⟨h.1.1, h.1.2⟩

theorem valid_undef_store_ptr (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_ptr CRules x)
      (CRules.coq_prop (isvalidptr x)) := by
  intro _ h
  exact h.1

private theorem singleton_interval0 (x : Int) (h : isvalidptr_char x) :
    Zlength ([x] : List Int) = 1 ∧ interval_list 0 0 Arch.addr_max_unsigned ([x] : List Int) := by
  unfold DerivedPredSig.isvalidptr_char at h
  change x >= 0 ∧ x <= Arch.addr_max_unsigned at h
  exact ⟨by simp, interval_list_cons [] x interval_list_nil h.1 (by omega) .nil⟩

private theorem singleton_interval3 (x : Int) (hlo : 0 <= x)
    (hhi : x + 3 <= Arch.addr_max_unsigned) :
    Zlength ([x] : List Int) = 1 ∧ interval_list 3 0 Arch.addr_max_unsigned ([x] : List Int) :=
  ⟨by simp, interval_list_cons [] x interval_list_nil hlo hhi .nil⟩

theorem undef_store_char_align (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_char CRules x) (store_align_n CRules 1) := by
  intro state h
  refine ⟨[x], singleton_interval0 x h.1, ?_⟩
  exact ⟨h.1, CRules.toContext.derivable1_sepcon_emp_r _ state h.2⟩

theorem store_char_align (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_char CRules x v) (store_align_n CRules 1) := by
  intro state h
  exact undef_store_char_align CRules x state
    (store_char_undef_store_char CRules x v state h)

theorem store_byte_align1 (CRules : SeparationLogicSig) (x : Int)
    (hvalid : isvalidptr_char x) :
    CRules.derivable1 (store_byte_noninit CRules x) (store_align_n CRules 1) := by
  intro state h
  refine ⟨[x], singleton_interval0 x hvalid, ?_⟩
  exact ⟨hvalid, CRules.toContext.derivable1_sepcon_emp_r _ state h⟩

theorem undef_store_uchar_align (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_uchar CRules x) (store_align_n CRules 1) := by
  simpa [DerivedPredSig.undef_store_uchar,
    DerivedPredSig.undef_store_char] using undef_store_char_align CRules x

theorem store_uchar_align (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uchar CRules x v) (store_align_n CRules 1) := by
  intro state h
  exact undef_store_uchar_align CRules x state
    (store_uchar_undef_store_uchar CRules x v state h)

private theorem undef_store_word_align4 (CRules : SeparationLogicSig) (x : Int)
    (state : CRules.model)
    (h : isvalidptr_int x)
    (hstore : store_4byte_noninit CRules x state) :
    store_align4_n CRules 1 state := by
  have hhi : x + 3 <= Arch.addr_max_unsigned := h.2.1
  refine ⟨[x], singleton_interval3 x h.1 hhi, ?_⟩
  exact ⟨h, CRules.toContext.derivable1_sepcon_emp_r _ _ hstore⟩

theorem undef_store_int_align4 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_int CRules x) (store_align4_n CRules 1) := by
  intro _ h
  exact undef_store_word_align4 CRules x _ h.1 h.2

theorem store_int_align4 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int CRules x v) (store_align4_n CRules 1) := by
  intro state h
  exact undef_store_int_align4 CRules x state
    (store_int_undef_store_int CRules x v state h)

theorem undef_store_uint_align4 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_uint CRules x) (store_align4_n CRules 1) := by
  simpa [DerivedPredSig.undef_store_uint,
    DerivedPredSig.undef_store_int] using undef_store_int_align4 CRules x

theorem store_uint_align4 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint CRules x v) (store_align4_n CRules 1) := by
  intro state h
  exact undef_store_uint_align4 CRules x state
    (store_uint_undef_store_uint CRules x v state h)

private theorem sepcon_right_mono (CRules : SeparationLogicSig)
    (P : CRules.expr) {Q R : CRules.expr} (h : CRules.derivable1 Q R) :
    CRules.derivable1 (CRules.sepcon P Q) (CRules.sepcon P R) :=
  CRules.toContext.derivable1_sepcon_mono P P Q R
    (CRules.toContext.derivable1_refl P) h

private theorem store8_split4 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (store_8byte_noninit CRules x)
      (CRules.sepcon (store_4byte_noninit CRules x)
        (store_4byte_noninit CRules (x + 4))) := by
  unfold store_8byte_noninit store_4byte_noninit
  simp only [Int.add_assoc]
  let b0 := store_byte_noninit CRules x
  let b1 := store_byte_noninit CRules (x + 1)
  let b2 := store_byte_noninit CRules (x + 2)
  let b3 := store_byte_noninit CRules (x + 3)
  let rest := CRules.sepcon (store_byte_noninit CRules (x + 4))
    (CRules.sepcon (store_byte_noninit CRules (x + 5))
      (CRules.sepcon (store_byte_noninit CRules (x + 6))
        (store_byte_noninit CRules (x + 7))))
  change CRules.derivable1
    (CRules.sepcon b0 (CRules.sepcon b1 (CRules.sepcon b2 (CRules.sepcon b3 rest))))
    (CRules.sepcon (CRules.sepcon b0 (CRules.sepcon b1 (CRules.sepcon b2 b3))) rest)
  have h1 : CRules.derivable1
      (CRules.sepcon b0 (CRules.sepcon b1 (CRules.sepcon b2 (CRules.sepcon b3 rest))))
      (CRules.sepcon b0 (CRules.sepcon b1 (CRules.sepcon (CRules.sepcon b2 b3) rest))) :=
    sepcon_right_mono CRules b0 <| sepcon_right_mono CRules b1 <|
      CRules.toContext.derivable1_sepcon_assoc1 b2 b3 rest
  have h2 : CRules.derivable1
      (CRules.sepcon b0 (CRules.sepcon b1 (CRules.sepcon (CRules.sepcon b2 b3) rest)))
      (CRules.sepcon b0 (CRules.sepcon (CRules.sepcon b1 (CRules.sepcon b2 b3)) rest)) :=
    sepcon_right_mono CRules b0 <|
      CRules.toContext.derivable1_sepcon_assoc1 b1 (CRules.sepcon b2 b3) rest
  have h3 : CRules.derivable1
      (CRules.sepcon b0 (CRules.sepcon (CRules.sepcon b1 (CRules.sepcon b2 b3)) rest))
      (CRules.sepcon (CRules.sepcon b0 (CRules.sepcon b1 (CRules.sepcon b2 b3))) rest) :=
    CRules.toContext.derivable1_sepcon_assoc1
      b0 (CRules.sepcon b1 (CRules.sepcon b2 b3)) rest
  exact CRules.toContext.derivable1_trans _ _ _ h1
    (CRules.toContext.derivable1_trans _ _ _ h2 h3)

private theorem int64_valid_words (x : Int) (h : isvalidptr_int64 x) :
    isvalidptr_int x ∧ isvalidptr_int (x + 4) := by
  unfold DerivedPredSig.isvalidptr_int64 at h
  rcases h with ⟨hlo, hhi, halign⟩
  have halign4 : aligned_4 (x + 4) := by
    unfold aligned_4 at halign ⊢
    omega
  constructor
  · exact ⟨hlo, by omega, halign⟩
  · exact ⟨by omega, by omega, halign4⟩

private theorem undef_store_int64_align4_core (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_int64 CRules x) (store_align4_n CRules 2) := by
  intro state h
  have hv := int64_valid_words x h.1
  refine ⟨[x, x + 4], ?_, ?_⟩
  · constructor
    · simp [Zlength]
    · exact interval_list_cons [x + 4] x
        (interval_list_cons [] (x + 4) interval_list_nil hv.2.1 hv.2.2.1 .nil)
        hv.1.1 hv.1.2.1 (.cons (by left; omega) .nil)
  · refine ⟨hv.1, ?_⟩
    have hsplit := store8_split4 CRules x state h.2
    rcases hsplit with ⟨left, right, hjoin, hleft, hright⟩
    exact ⟨left, right, hjoin, hleft,
      ⟨hv.2, CRules.toContext.derivable1_sepcon_emp_r _ right hright⟩⟩

theorem undef_store_int64_align4 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_int64 CRules x) (store_align4_n CRules 2) :=
  undef_store_int64_align4_core CRules x

theorem store_int64_align4 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int64 CRules x v) (store_align4_n CRules 2) := by
  intro state h
  exact undef_store_int64_align4 CRules x state
    (store_int64_undef_store_int64 CRules x v state h)

theorem undef_store_uint64_align4 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_uint64 CRules x) (store_align4_n CRules 2) := by
  simpa [DerivedPredSig.undef_store_uint64,
    DerivedPredSig.undef_store_int64] using
    undef_store_int64_align4 CRules x

theorem store_uint64_align4 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint64 CRules x v) (store_align4_n CRules 2) := by
  intro state h
  exact undef_store_uint64_align4 CRules x state
    (store_uint64_undef_store_uint64 CRules x v state h)

theorem aligned_8_aligned_4 (x : Int) (h : aligned_8 x) : aligned_4 x := by
  unfold aligned_8 aligned_4 at *
  omega

theorem store_float_aligned4
    (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_float CRules x v) (CRules.coq_prop (aligned_4 x)) := by
  intro _ h
  exact h.1.1.2.2

theorem store_double_aligned8
    (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_double CRules x v) (CRules.coq_prop (aligned_8 x)) := by
  intro _ h
  exact h.1.1.2.2

theorem store_finite_float_aligned4
    (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_finite_float CRules x v)
      (CRules.coq_prop (aligned_4 x)) := by
  intro state h
  exact store_float_aligned4 CRules x v state h.2

theorem store_finite_double_aligned8
    (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_finite_double CRules x v)
      (CRules.coq_prop (aligned_8 x)) := by
  intro state h
  exact store_double_aligned8 CRules x v state h.2

theorem store_long_double_aligned8
    (CRules : SeparationLogicSig) (x : Int) (v : fp128) :
    CRules.derivable1 (store_long_double CRules x v)
      (CRules.coq_prop (aligned_8 x)) := by
  intro _ h
  exact h.1.1.2.2

theorem store_finite_long_double_aligned8
    (CRules : SeparationLogicSig) (x : Int) (v : fp128) :
    CRules.derivable1 (store_finite_long_double CRules x v)
      (CRules.coq_prop (aligned_8 x)) := by
  intro state h
  exact store_long_double_aligned8 CRules x v state h.2

theorem undef_store_float_align4 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_float CRules x) (store_align4_n CRules 1) := by
  intro _ h
  exact undef_store_word_align4 CRules x _ h.1 h.2

theorem store_float_align4
    (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_float CRules x v) (store_align4_n CRules 1) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_float_undef_store_float CRules x v)
    (undef_store_float_align4 CRules x)

theorem undef_store_double_align4 (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_double CRules x) (store_align4_n CRules 2) := by
  intro state h
  have hvalid : isvalidptr_int64 x := by
    exact ⟨h.1.1, h.1.2.1, aligned_8_aligned_4 x h.1.2.2⟩
  exact undef_store_int64_align4 CRules x state ⟨hvalid, h.2⟩

theorem store_double_align4
    (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_double CRules x v) (store_align4_n CRules 2) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_double_undef_store_double CRules x v)
    (undef_store_double_align4 CRules x)

private theorem ptr_valid_int_of_size4 (x : Int) (hsize : Arch.ptr_size = 4)
    (h : isvalidptr x) : isvalidptr_int x := by
  change x >= 0 ∧ x + Arch.ptr_size_Z - 1 <= Arch.addr_max_unsigned ∧
    Z.modulo x Arch.ptr_align = 0 at h
  change x >= 0 ∧ x + 3 <= Arch.addr_max_unsigned ∧ aligned_4 x
  rcases h with ⟨hlo, hhi, halign⟩
  refine ⟨hlo, ?_, ?_⟩
  · unfold CArchSig.ptr_size_Z at hhi
    rw [hsize] at hhi
    simp at hhi
    omega
  · unfold aligned_4
    have h4 := Arch.ptr_aligned_aligned_4 x halign
    unfold Z.modulo at h4
    rw [Int.fmod_eq_emod_of_nonneg x (by decide)] at h4
    exact h4

theorem undef_store_ptr_align4 (CRules : SeparationLogicSig) (x : Int)
    (hsize : Arch.ptr_size = 4) :
    CRules.derivable1 (undef_store_ptr CRules x) (store_align4_n CRules 1) := by
  intro _ h
  simp only [DerivedPredSig.undef_store_ptr, hsize] at h
  exact undef_store_word_align4 CRules x _
    (ptr_valid_int_of_size4 x hsize h.1) h.2

theorem store_ptr_align4 (CRules : SeparationLogicSig) (x v : Int)
    (hsize : Arch.ptr_size = 4) :
    CRules.derivable1 (store_ptr CRules x v) (store_align4_n CRules 1) := by
  intro state h
  exact undef_store_ptr_align4 CRules x hsize state
    (store_ptr_undef_store_ptr CRules x v state h)

theorem store_byte_valid (CRules : SeparationLogicSig) (x y : Int) :
    CRules.derivable1
      (CRules.sepcon (store_byte_noninit CRules x) (store_byte_noninit CRules y))
      (CRules.coq_prop (x < y ∨ y < x)) := by
  intro state h
  by_cases heq : x = y
  · subst y
    exact False.elim (dup_store_byte_noninit CRules x state h)
  · by_cases hlt : x < y
    · exact Or.inl hlt
    · exact Or.inr (by omega)

private theorem derivable_of_false (CRules : SeparationLogicSig)
    {P Q : CRules.expr} (h : CRules.derivable1 P (CRules.coq_prop False)) :
    CRules.derivable1 P Q := by
  intro state hP
  exact False.elim (h state hP)

private theorem store_4byte_valid_proof [SacContext] (x y : Int) :
    SacContext.rules.derivable1
      (SacContext.rules.sepcon
        (store_4byte_noninit SacContext.rules x)
        (store_4byte_noninit SacContext.rules y))
      (SacContext.rules.coq_prop (x + 3 < y ∨ y + 3 < x)) := by
  by_cases hxy : x + 3 < y
  · exact dump_spatial_left SacContext.rules _ _ (Or.inl hxy)
  by_cases hyx : y + 3 < x
  · exact dump_spatial_left SacContext.rules _ _ (Or.inr hyx)
  have hoverlap :
      x = y - 3 ∨ x = y - 2 ∨ x = y - 1 ∨ x = y ∨
        x = y + 1 ∨ x = y + 2 ∨ x = y + 3 := by
    omega
  rcases hoverlap with h | h | h | h | h | h | h
  · have heq : x + 3 = y := by omega
    have hfalse : SacContext.rules.derivable1
        (SacContext.rules.sepcon (store_4byte_noninit SacContext.rules x)
          (store_4byte_noninit SacContext.rules y))
        (SacContext.rules.coq_prop False) := by
      unfold store_4byte_noninit
      rw [show x + 3 = y from heq]
      sep_apply_l_atomic (dup_store_byte_noninit SacContext.rules y)
      entailer!
    exact derivable_of_false SacContext.rules hfalse
  · have heq : x + 2 = y := by omega
    have hfalse : SacContext.rules.derivable1
        (SacContext.rules.sepcon (store_4byte_noninit SacContext.rules x)
          (store_4byte_noninit SacContext.rules y))
        (SacContext.rules.coq_prop False) := by
      unfold store_4byte_noninit
      rw [show x + 2 = y from heq]
      sep_apply_l_atomic (dup_store_byte_noninit SacContext.rules y)
      entailer!
    exact derivable_of_false SacContext.rules hfalse
  · have heq : x + 1 = y := by omega
    have hfalse : SacContext.rules.derivable1
        (SacContext.rules.sepcon (store_4byte_noninit SacContext.rules x)
          (store_4byte_noninit SacContext.rules y))
        (SacContext.rules.coq_prop False) := by
      unfold store_4byte_noninit
      rw [show x + 1 = y from heq]
      sep_apply_l_atomic (dup_store_byte_noninit SacContext.rules y)
      entailer!
    exact derivable_of_false SacContext.rules hfalse
  · have hfalse : SacContext.rules.derivable1
        (SacContext.rules.sepcon (store_4byte_noninit SacContext.rules x)
          (store_4byte_noninit SacContext.rules y))
        (SacContext.rules.coq_prop False) := by
      unfold store_4byte_noninit
      rw [h]
      sep_apply_l_atomic (dup_store_byte_noninit SacContext.rules y)
      entailer!
    exact derivable_of_false SacContext.rules hfalse
  · have heq : x = y + 1 := h
    have hfalse : SacContext.rules.derivable1
        (SacContext.rules.sepcon (store_4byte_noninit SacContext.rules x)
          (store_4byte_noninit SacContext.rules y))
        (SacContext.rules.coq_prop False) := by
      unfold store_4byte_noninit
      rw [heq]
      sep_apply_l_atomic (dup_store_byte_noninit SacContext.rules (y + 1))
      entailer!
    exact derivable_of_false SacContext.rules hfalse
  · have heq : x = y + 2 := h
    have hfalse : SacContext.rules.derivable1
        (SacContext.rules.sepcon (store_4byte_noninit SacContext.rules x)
          (store_4byte_noninit SacContext.rules y))
        (SacContext.rules.coq_prop False) := by
      unfold store_4byte_noninit
      rw [heq]
      sep_apply_l_atomic (dup_store_byte_noninit SacContext.rules (y + 2))
      entailer!
    exact derivable_of_false SacContext.rules hfalse
  · have heq : x = y + 3 := h
    have hfalse : SacContext.rules.derivable1
        (SacContext.rules.sepcon (store_4byte_noninit SacContext.rules x)
          (store_4byte_noninit SacContext.rules y))
        (SacContext.rules.coq_prop False) := by
      unfold store_4byte_noninit
      rw [heq]
      sep_apply_l_atomic (dup_store_byte_noninit SacContext.rules (y + 3))
      entailer!
    exact derivable_of_false SacContext.rules hfalse

theorem store_4byte_valid (CRules : SeparationLogicSig) (x y : Int) :
    CRules.derivable1
      (CRules.sepcon (store_4byte_noninit CRules x) (store_4byte_noninit CRules y))
      (CRules.coq_prop (x + 3 < y ∨ y + 3 < x)) := by
  letI : SacContext := ⟨CRules⟩
  exact store_4byte_valid_proof x y

private theorem sepcon_left_pure (CRules : SeparationLogicSig) (P : Prop)
    (Q : CRules.expr) :
    CRules.derivable1 (CRules.sepcon (CRules.coq_prop P) Q) (CRules.coq_prop P) := by
  intro _ h
  rcases h with ⟨_, _, _, hP, _⟩
  exact hP

private theorem sepcon_right_pure (CRules : SeparationLogicSig) (P : Prop)
    (Q : CRules.expr) :
    CRules.derivable1 (CRules.sepcon Q (CRules.coq_prop P)) (CRules.coq_prop P) := by
  intro _ h
  rcases h with ⟨_, _, _, _, hP⟩
  exact hP

theorem store_align4_valid (CRules : SeparationLogicSig) (x : Int) (l : List Int) :
    CRules.derivable1
      (CRules.sepcon (store_align4_list CRules l) (store_4byte_noninit CRules x))
      (CRules.coq_prop (Forall (fun x' => x + 3 < x' ∨ x' + 3 < x) l)) := by
  induction l with
  | nil => exact dump_spatial_left CRules _ _ .nil
  | cons a l ih =>
      let A := store_4byte_noninit CRules a
      let L := store_align4_list CRules l
      let X := store_4byte_noninit CRules x
      have hspatial : CRules.derivable1
          (CRules.sepcon
            (CRules.andp (CRules.coq_prop
              (DerivedPredSig.isvalidptr_int Arch a))
              (CRules.sepcon A L)) X)
          (CRules.sepcon (CRules.sepcon A L) X) :=
        CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_andp_elim2 _ _)
          (CRules.toContext.derivable1_refl X)
      have hreorder : CRules.derivable1
          (CRules.sepcon (CRules.sepcon A L) X)
          (CRules.sepcon (CRules.sepcon A X) L) := by
        exact CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_comm (CRules.sepcon A L) X)
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_assoc1 X A L)
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (CRules.toContext.derivable1_sepcon_comm X A)
              (CRules.toContext.derivable1_refl L)))
      have hheadRaw : CRules.derivable1
          (CRules.sepcon
            (CRules.andp (CRules.coq_prop
              (DerivedPredSig.isvalidptr_int Arch a))
              (CRules.sepcon A L)) X)
          (CRules.coq_prop (a + 3 < x ∨ x + 3 < a)) := by
        exact CRules.toContext.derivable1_trans _ _ _ hspatial
          (CRules.toContext.derivable1_trans _ _ _ hreorder
            (CRules.toContext.derivable1_trans _ _ _
              (CRules.toContext.derivable1_sepcon_mono _ _ _ _
                (store_4byte_valid CRules a x)
                (CRules.toContext.derivable1_truep_intros L))
              (sepcon_left_pure CRules _ CRules.truep)))
      have htail : CRules.derivable1
          (CRules.sepcon
            (CRules.andp (CRules.coq_prop
              (DerivedPredSig.isvalidptr_int Arch a))
              (CRules.sepcon A L)) X)
          (CRules.coq_prop (Forall (fun x' => x + 3 < x' ∨ x' + 3 < x) l)) := by
        exact CRules.toContext.derivable1_trans _ _ _ hspatial
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.logic_equiv_sepcon_assoc A L X).right
            (CRules.toContext.derivable1_trans _ _ _
              (CRules.toContext.derivable1_sepcon_mono _ _ _ _
                (CRules.toContext.derivable1_truep_intros A) ih)
              (sepcon_right_pure CRules _ CRules.truep)))
      change CRules.derivable1
        (CRules.sepcon
          (CRules.andp (CRules.coq_prop
            (DerivedPredSig.isvalidptr_int Arch a))
            (CRules.sepcon A L)) X)
        (CRules.coq_prop
          (Forall (fun x' => x + 3 < x' ∨ x' + 3 < x) (a :: l)))
      intro state h
      exact .cons
        ((hheadRaw state h).elim (fun ha => Or.inr ha) (fun hx => Or.inl hx))
        (htail state h)

theorem store_align4_n_valid (CRules : SeparationLogicSig) (n : Int) :
    CRules.derivable1 (store_align4_n CRules n)
      (CRules.coq_prop (n <= Arch.addr_max_unsigned / 4 + 1)) := by
  intro _ h
  rcases h with ⟨l, hproperties, _⟩
  have hrange := interval_list_range l 3 0 Arch.addr_max_unsigned
    (by omega) (by have := Arch.addr_max_unsigned_ge_7; omega) hproperties.2
  rw [hproperties.1] at hrange
  have hrange' : n * 4 <= Arch.addr_max_unsigned + 4 := by omega
  have hdiv := Int.ediv_le_ediv (show (0 : Int) < 4 by omega) hrange'
  have hleft : (n * 4) / 4 = n := by
    rw [Int.mul_comm, Int.mul_ediv_cancel_left n (by omega)]
  have hright : (Arch.addr_max_unsigned + 4) / 4 = Arch.addr_max_unsigned / 4 + 1 := by
    rw [Int.add_comm, Int.add_ediv_of_dvd_left (Int.dvd_refl 4)]
    omega
  calc
    n = (n * 4) / 4 := hleft.symm
    _ <= (Arch.addr_max_unsigned + 4) / 4 := hdiv
    _ = Arch.addr_max_unsigned / 4 + 1 := hright

private theorem forall_append {A : Type} {P : A -> Prop} {l1 l2 : List A}
    (h1 : Forall P l1) (h2 : Forall P l2) : Forall P (l1 ++ l2) := by
  induction h1 with
  | nil => exact h2
  | cons hhead _ ih => exact .cons hhead ih

private theorem store_align4_lists_merge (CRules : SeparationLogicSig)
    (l1 l2 : List Int)
    (h1 : interval_list 3 0 Arch.addr_max_unsigned l1)
    (h2 : interval_list 3 0 Arch.addr_max_unsigned l2) :
    CRules.derivable1
      (CRules.sepcon (store_align4_list CRules l1) (store_align4_list CRules l2))
      (CRules.andp
        (CRules.coq_prop (interval_list 3 0 Arch.addr_max_unsigned (l1 ++ l2)))
        (store_align4_list CRules (l1 ++ l2))) := by
  induction h1 with
  | interval_list_nil =>
      simp only [List.nil_append, DerivedPredSig.store_align4_list]
      intro state h
      exact ⟨h2, (sepcon_emp_logic_equiv' CRules _).left state h⟩
  | interval_list_cons l x htail hlo hhi hsep ih =>
      let A := store_4byte_noninit CRules x
      let Tail := store_align4_list CRules l
      let Other := store_align4_list CRules l2
      let Merged := store_align4_list CRules (l ++ l2)
      let Premise := CRules.sepcon
        (CRules.andp (CRules.coq_prop
          (DerivedPredSig.isvalidptr_int Arch x))
          (CRules.sepcon A Tail)) Other
      have hbase : CRules.derivable1 Premise
          (CRules.sepcon (CRules.sepcon A Tail) Other) :=
        CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_andp_elim2 _ _)
          (CRules.toContext.derivable1_refl Other)
      have hassoc : CRules.derivable1 Premise
          (CRules.sepcon A (CRules.sepcon Tail Other)) :=
        CRules.toContext.derivable1_trans _ _ _ hbase
          (CRules.toContext.logic_equiv_sepcon_assoc A Tail Other).right
      have ihInterval : CRules.derivable1
          (CRules.sepcon Tail Other)
          (CRules.coq_prop (interval_list 3 0 Arch.addr_max_unsigned (l ++ l2))) :=
        CRules.toContext.derivable1_trans _ _ _ ih
          (CRules.toContext.derivable1_andp_elim1 _ _)
      have ihSpatial : CRules.derivable1
          (CRules.sepcon Tail Other) Merged :=
        CRules.toContext.derivable1_trans _ _ _ ih
          (CRules.toContext.derivable1_andp_elim2 _ _)
      have htailInterval : CRules.derivable1 Premise
          (CRules.coq_prop (interval_list 3 0 Arch.addr_max_unsigned (l ++ l2))) := by
        exact CRules.toContext.derivable1_trans _ _ _ hassoc
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (CRules.toContext.derivable1_truep_intros A) ihInterval)
            (sepcon_right_pure CRules _ CRules.truep))
      have hspatial : CRules.derivable1 Premise (CRules.sepcon A Merged) :=
        CRules.toContext.derivable1_trans _ _ _ hassoc
          (CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_refl A) ihSpatial)
      have hcrossReorder : CRules.derivable1 Premise
          (CRules.sepcon (CRules.sepcon Other A) Tail) := by
        exact CRules.toContext.derivable1_trans _ _ _ hbase
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_comm (CRules.sepcon A Tail) Other)
            (CRules.toContext.derivable1_sepcon_assoc1 Other A Tail))
      have hcrossOther : CRules.derivable1 Premise
          (CRules.coq_prop
            (Forall (fun x' => x + 3 < x' ∨ x' + 3 < x) l2)) := by
        exact CRules.toContext.derivable1_trans _ _ _ hcrossReorder
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (store_align4_valid CRules x l2)
              (CRules.toContext.derivable1_truep_intros Tail))
            (sepcon_left_pure CRules _ CRules.truep))
      simp only [List.cons_append, DerivedPredSig.store_align4_list]
      change CRules.derivable1 Premise
        (CRules.andp
          (CRules.coq_prop
            (interval_list 3 0 Arch.addr_max_unsigned (x :: (l ++ l2))))
          (CRules.andp (CRules.coq_prop
            (DerivedPredSig.isvalidptr_int Arch x))
            (CRules.sepcon A Merged)))
      intro state h
      have hxvalid : DerivedPredSig.isvalidptr_int
          Arch x := by
        rcases h with ⟨_, _, _, hxStore, _⟩
        exact hxStore.1
      exact ⟨
        interval_list_cons (l ++ l2) x (htailInterval state h) hlo hhi
          (forall_append hsep (hcrossOther state h)),
        ⟨hxvalid, hspatial state h⟩⟩

theorem store_align4_merge (CRules : SeparationLogicSig) (n m : Int) :
    CRules.derivable1
      (CRules.sepcon (store_align4_n CRules n) (store_align4_n CRules m))
      (store_align4_n CRules (n + m)) := by
  intro state h
  rcases h with ⟨s1, s2, hjoin, ⟨l1, hp1, hs1⟩, ⟨l2, hp2, hs2⟩⟩
  have hlen1 : Zlength l1 = n := hp1.1
  have hlen2 : Zlength l2 = m := hp2.1
  have hmerged := store_align4_lists_merge CRules l1 l2 hp1.2 hp2.2 state
    ⟨s1, s2, hjoin, hs1, hs2⟩
  refine ⟨l1 ++ l2, ?_, hmerged.2⟩
  constructor
  · simp only [Zlength, List.length_append]
    unfold Zlength at hlen1 hlen2
    calc
      Int.ofNat (l1.length + l2.length) =
          Int.ofNat l1.length + Int.ofNat l2.length := rfl
      _ = n + Int.ofNat l2.length :=
        congrArg (fun a : Int => a + Int.ofNat l2.length) hlen1
      _ = n + m := congrArg (fun b : Int => n + b) hlen2
  · exact hmerged.1

theorem store_align_valid (CRules : SeparationLogicSig) (x : Int) (l : List Int) :
    CRules.derivable1
      (CRules.sepcon (store_align_list CRules l) (store_byte_noninit CRules x))
      (CRules.coq_prop (Forall (fun x' => x + 0 < x' ∨ x' + 0 < x) l)) := by
  induction l with
  | nil => exact dump_spatial_left CRules _ _ .nil
  | cons a l ih =>
      let A := store_byte_noninit CRules a
      let L := store_align_list CRules l
      let X := store_byte_noninit CRules x
      have hspatial : CRules.derivable1
          (CRules.sepcon
            (CRules.andp (CRules.coq_prop (isvalidptr_char a)) (CRules.sepcon A L)) X)
          (CRules.sepcon (CRules.sepcon A L) X) :=
        CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_andp_elim2 _ _)
          (CRules.toContext.derivable1_refl X)
      have hreorder : CRules.derivable1
          (CRules.sepcon (CRules.sepcon A L) X)
          (CRules.sepcon (CRules.sepcon A X) L) := by
        exact CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_comm (CRules.sepcon A L) X)
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_assoc1 X A L)
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (CRules.toContext.derivable1_sepcon_comm X A)
              (CRules.toContext.derivable1_refl L)))
      have hheadRaw : CRules.derivable1
          (CRules.sepcon
            (CRules.andp (CRules.coq_prop (isvalidptr_char a)) (CRules.sepcon A L)) X)
          (CRules.coq_prop (a < x ∨ x < a)) := by
        exact CRules.toContext.derivable1_trans _ _ _ hspatial
          (CRules.toContext.derivable1_trans _ _ _ hreorder
            (CRules.toContext.derivable1_trans _ _ _
              (CRules.toContext.derivable1_sepcon_mono _ _ _ _
                (store_byte_valid CRules a x)
                (CRules.toContext.derivable1_truep_intros L))
              (sepcon_left_pure CRules _ CRules.truep)))
      have htail : CRules.derivable1
          (CRules.sepcon
            (CRules.andp (CRules.coq_prop (isvalidptr_char a)) (CRules.sepcon A L)) X)
          (CRules.coq_prop (Forall (fun x' => x + 0 < x' ∨ x' + 0 < x) l)) := by
        exact CRules.toContext.derivable1_trans _ _ _ hspatial
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.logic_equiv_sepcon_assoc A L X).right
            (CRules.toContext.derivable1_trans _ _ _
              (CRules.toContext.derivable1_sepcon_mono _ _ _ _
                (CRules.toContext.derivable1_truep_intros A) ih)
              (sepcon_right_pure CRules _ CRules.truep)))
      change CRules.derivable1
        (CRules.sepcon
          (CRules.andp (CRules.coq_prop (isvalidptr_char a)) (CRules.sepcon A L)) X)
        (CRules.coq_prop
          (Forall (fun x' => x + 0 < x' ∨ x' + 0 < x) (a :: l)))
      intro state h
      exact .cons
        ((hheadRaw state h).elim
          (fun ha => Or.inr (by omega)) (fun hx => Or.inl (by omega)))
        (htail state h)

private theorem store_align_lists_merge (CRules : SeparationLogicSig)
    (l1 l2 : List Int)
    (h1 : interval_list 0 0 Arch.addr_max_unsigned l1)
    (h2 : interval_list 0 0 Arch.addr_max_unsigned l2) :
    CRules.derivable1
      (CRules.sepcon (store_align_list CRules l1) (store_align_list CRules l2))
      (CRules.andp
        (CRules.coq_prop (interval_list 0 0 Arch.addr_max_unsigned (l1 ++ l2)))
        (store_align_list CRules (l1 ++ l2))) := by
  induction h1 with
  | interval_list_nil =>
      simp only [List.nil_append, DerivedPredSig.store_align_list]
      intro state h
      exact ⟨h2, (sepcon_emp_logic_equiv' CRules _).left state h⟩
  | interval_list_cons l x htail hlo hhi hsep ih =>
      let A := store_byte_noninit CRules x
      let Tail := store_align_list CRules l
      let Other := store_align_list CRules l2
      let Merged := store_align_list CRules (l ++ l2)
      let Premise := CRules.sepcon
        (CRules.andp (CRules.coq_prop (isvalidptr_char x)) (CRules.sepcon A Tail)) Other
      have hbase : CRules.derivable1 Premise
          (CRules.sepcon (CRules.sepcon A Tail) Other) :=
        CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_andp_elim2 _ _)
          (CRules.toContext.derivable1_refl Other)
      have hassoc : CRules.derivable1 Premise
          (CRules.sepcon A (CRules.sepcon Tail Other)) :=
        CRules.toContext.derivable1_trans _ _ _ hbase
          (CRules.toContext.logic_equiv_sepcon_assoc A Tail Other).right
      have ihInterval : CRules.derivable1
          (CRules.sepcon Tail Other)
          (CRules.coq_prop (interval_list 0 0 Arch.addr_max_unsigned (l ++ l2))) :=
        CRules.toContext.derivable1_trans _ _ _ ih
          (CRules.toContext.derivable1_andp_elim1 _ _)
      have ihSpatial : CRules.derivable1
          (CRules.sepcon Tail Other) Merged :=
        CRules.toContext.derivable1_trans _ _ _ ih
          (CRules.toContext.derivable1_andp_elim2 _ _)
      have htailInterval : CRules.derivable1 Premise
          (CRules.coq_prop (interval_list 0 0 Arch.addr_max_unsigned (l ++ l2))) := by
        exact CRules.toContext.derivable1_trans _ _ _ hassoc
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (CRules.toContext.derivable1_truep_intros A) ihInterval)
            (sepcon_right_pure CRules _ CRules.truep))
      have hspatial : CRules.derivable1 Premise (CRules.sepcon A Merged) :=
        CRules.toContext.derivable1_trans _ _ _ hassoc
          (CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_refl A) ihSpatial)
      have hcrossReorder : CRules.derivable1 Premise
          (CRules.sepcon (CRules.sepcon Other A) Tail) := by
        exact CRules.toContext.derivable1_trans _ _ _ hbase
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_comm (CRules.sepcon A Tail) Other)
            (CRules.toContext.derivable1_sepcon_assoc1 Other A Tail))
      have hcrossOther : CRules.derivable1 Premise
          (CRules.coq_prop
            (Forall (fun x' => x + 0 < x' ∨ x' + 0 < x) l2)) := by
        exact CRules.toContext.derivable1_trans _ _ _ hcrossReorder
          (CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (store_align_valid CRules x l2)
              (CRules.toContext.derivable1_truep_intros Tail))
            (sepcon_left_pure CRules _ CRules.truep))
      simp only [List.cons_append, DerivedPredSig.store_align_list]
      change CRules.derivable1 Premise
        (CRules.andp
          (CRules.coq_prop
            (interval_list 0 0 Arch.addr_max_unsigned (x :: (l ++ l2))))
          (CRules.andp (CRules.coq_prop (isvalidptr_char x))
            (CRules.sepcon A Merged)))
      intro state h
      have hxvalid : isvalidptr_char x := by
        rcases h with ⟨_, _, _, hxStore, _⟩
        exact hxStore.1
      exact ⟨
        interval_list_cons (l ++ l2) x (htailInterval state h) hlo hhi
          (forall_append hsep (hcrossOther state h)),
        ⟨hxvalid, hspatial state h⟩⟩

theorem store_align_merge (CRules : SeparationLogicSig) (n m : Int) :
    CRules.derivable1
      (CRules.sepcon (store_align_n CRules n) (store_align_n CRules m))
      (store_align_n CRules (n + m)) := by
  intro state h
  rcases h with ⟨s1, s2, hjoin, ⟨l1, hp1, hs1⟩, ⟨l2, hp2, hs2⟩⟩
  have hlen1 : Zlength l1 = n := hp1.1
  have hlen2 : Zlength l2 = m := hp2.1
  have hmerged := store_align_lists_merge CRules l1 l2 hp1.2 hp2.2 state
    ⟨s1, s2, hjoin, hs1, hs2⟩
  refine ⟨l1 ++ l2, ?_, hmerged.2⟩
  constructor
  · simp only [Zlength, List.length_append]
    unfold Zlength at hlen1 hlen2
    calc
      Int.ofNat (l1.length + l2.length) =
          Int.ofNat l1.length + Int.ofNat l2.length := rfl
      _ = n + Int.ofNat l2.length :=
        congrArg (fun a : Int => a + Int.ofNat l2.length) hlen1
      _ = n + m := congrArg (fun b : Int => n + b) hlen2
  · exact hmerged.1

private theorem short_valid_chars (x : Int) (h : isvalidptr_short x) :
    isvalidptr_char x ∧ isvalidptr_char (x + 1) := by
  unfold DerivedPredSig.isvalidptr_short at h
  unfold DerivedPredSig.isvalidptr_char
  omega

theorem undef_store_short_align (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_short CRules x) (store_align_n CRules 2) := by
  unfold DerivedPredSig.undef_store_short store_2byte_noninit
  apply coq_prop_andp_left
  intro hvalid
  have hv := short_valid_chars x hvalid
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_byte_align1 CRules x hv.1)
      (store_byte_align1 CRules (x + 1) hv.2))
    (by simpa using store_align_merge CRules 1 1)

theorem store_short_align (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_short CRules x v) (store_align_n CRules 2) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_short_undef_store_short CRules x v)
    (undef_store_short_align CRules x)

theorem undef_store_ushort_align (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_ushort CRules x) (store_align_n CRules 2) := by
  simpa [DerivedPredSig.undef_store_ushort,
    DerivedPredSig.undef_store_short] using undef_store_short_align CRules x

theorem store_ushort_align (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_ushort CRules x v) (store_align_n CRules 2) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_ushort_undef_store_ushort CRules x v)
    (undef_store_ushort_align CRules x)

theorem store_bytes_noninit_align (CRules : SeparationLogicSig)
    (n : Nat) (x : Int) (hlo : 0 <= x)
    (hhi : x + Int.ofNat n - 1 <= Arch.addr_max_unsigned) :
    CRules.derivable1 (store_bytes_noninit CRules x n)
      (store_align_n CRules (Int.ofNat n)) := by
  induction n generalizing x with
  | zero =>
      intro state h
      exact ⟨[], ⟨by simp [Zlength], interval_list_nil⟩, h⟩
  | succ n ih =>
      have hsucc : Int.ofNat (n + 1) = Int.ofNat n + 1 :=
        Int.natCast_succ n
      rw [hsucc] at hhi ⊢
      have hn : 0 <= Int.ofNat n := Int.ofNat_zero_le n
      have hvalid : isvalidptr_char x := by
        unfold DerivedPredSig.isvalidptr_char
        change x >= 0 ∧ x <= Arch.addr_max_unsigned
        constructor
        · exact hlo
        · omega
      have htail := ih (x + 1) (by omega) (by omega)
      have hparts := CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (store_byte_align1 CRules x hvalid) htail
      exact CRules.toContext.derivable1_trans _ _ _ hparts
        (by simpa [Int.add_comm] using store_align_merge CRules 1 (Int.ofNat n))

theorem undef_store_int128_align (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_int128 CRules x) (store_align_n CRules 16) := by
  unfold DerivedPredSig.undef_store_int128 store_16byte_noninit
  apply coq_prop_andp_left
  intro hvalid
  unfold DerivedPredSig.isvalidptr_int128 at hvalid
  change x >= 0 ∧ x + 15 <= Arch.addr_max_unsigned ∧ aligned_4 x at hvalid
  apply store_bytes_noninit_align CRules 16 x hvalid.1
  change x + 16 - 1 <= Arch.addr_max_unsigned
  omega

theorem store_int128_align (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int128 CRules x v) (store_align_n CRules 16) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_int128_undef_store_int128 CRules x v)
    (undef_store_int128_align CRules x)

theorem undef_store_uint128_align (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_uint128 CRules x) (store_align_n CRules 16) := by
  simpa [DerivedPredSig.undef_store_uint128,
    DerivedPredSig.undef_store_int128] using
    undef_store_int128_align CRules x

theorem store_uint128_align (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint128 CRules x v) (store_align_n CRules 16) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_uint128_undef_store_uint128 CRules x v)
    (undef_store_uint128_align CRules x)

theorem store_align_n_valid (CRules : SeparationLogicSig) (n : Int) :
    CRules.derivable1 (store_align_n CRules n)
      (CRules.coq_prop (n <= Arch.addr_max_unsigned / 1 + 1)) := by
  intro _ h
  rcases h with ⟨l, hproperties, _⟩
  have hrange := interval_list_range l 0 0 Arch.addr_max_unsigned
    (by omega) (by have := Arch.addr_max_unsigned_ge_7; omega) hproperties.2
  rw [hproperties.1] at hrange
  simpa using hrange

private theorem word_valid_chars (x : Int) (h : isvalidptr_int x) :
    isvalidptr_char x ∧ isvalidptr_char (x + 1) ∧
      isvalidptr_char (x + 2) ∧ isvalidptr_char (x + 3) := by
  unfold DerivedPredSig.isvalidptr_int at h
  change x >= 0 ∧ x + 3 <= Arch.addr_max_unsigned ∧ aligned_4 x at h
  unfold DerivedPredSig.isvalidptr_char
  change (x >= 0 ∧ x <= Arch.addr_max_unsigned) ∧
    (x + 1 >= 0 ∧ x + 1 <= Arch.addr_max_unsigned) ∧
    (x + 2 >= 0 ∧ x + 2 <= Arch.addr_max_unsigned) ∧
    (x + 3 >= 0 ∧ x + 3 <= Arch.addr_max_unsigned)
  omega

private theorem store_4byte_align (CRules : SeparationLogicSig) (x : Int)
    (hvalid : isvalidptr_int x) :
    CRules.derivable1 (store_4byte_noninit CRules x) (store_align_n CRules 4) := by
  have hv := word_valid_chars x hvalid
  let One := store_align_n CRules 1
  have hbytes : CRules.derivable1 (store_4byte_noninit CRules x)
      (CRules.sepcon One (CRules.sepcon One (CRules.sepcon One One))) := by
    unfold store_4byte_noninit
    exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_byte_align1 CRules x hv.1)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (store_byte_align1 CRules (x + 1) hv.2.1)
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (store_byte_align1 CRules (x + 2) hv.2.2.1)
          (store_byte_align1 CRules (x + 3) hv.2.2.2)))
  have hmerge11 : CRules.derivable1 (CRules.sepcon One One)
      (store_align_n CRules 2) := by
    simpa [One] using store_align_merge CRules 1 1
  have hmerge12 : CRules.derivable1
      (CRules.sepcon One (store_align_n CRules 2))
      (store_align_n CRules 3) := by
    simpa [One] using store_align_merge CRules 1 2
  have hmerge13 : CRules.derivable1
      (CRules.sepcon One (store_align_n CRules 3))
      (store_align_n CRules 4) := by
    simpa [One] using store_align_merge CRules 1 3
  exact CRules.toContext.derivable1_trans _ _ _ hbytes
    (CRules.toContext.derivable1_trans _ _ _
      (sepcon_right_mono CRules One (sepcon_right_mono CRules One hmerge11))
      (CRules.toContext.derivable1_trans _ _ _
        (sepcon_right_mono CRules One hmerge12) hmerge13))

private theorem store_align4_list_to_store_align (CRules : SeparationLogicSig) :
    forall l,
      CRules.derivable1 (store_align4_list CRules l)
        (store_align_n CRules (4 * Zlength l)) := by
  intro l
  induction l with
  | nil =>
      intro state h
      exact ⟨[], ⟨by simp, interval_list_nil⟩, h⟩
  | cons x l ih =>
      simp only [DerivedPredSig.store_align4_list]
      apply coq_prop_andp_left
      intro hvalid
      have hmerged := CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (store_4byte_align CRules x hvalid) ih)
        (store_align_merge CRules 4 (4 * Zlength l))
      have hlen : 4 + 4 * Zlength l = 4 * Zlength (x :: l) := by
        rw [Zlength_cons]
        omega
      rw [hlen] at hmerged
      exact hmerged

theorem store_align4_to_store_align (CRules : SeparationLogicSig) (n : Int) :
    CRules.derivable1 (store_align4_n CRules n) (store_align_n CRules (4 * n)) := by
  intro state h
  rcases h with ⟨l, hproperties, hstore⟩
  have hconverted := store_align4_list_to_store_align CRules l state hstore
  have hlen : 4 * Zlength l = 4 * n :=
    congrArg (fun z : Int => 4 * z) hproperties.1
  rw [hlen] at hconverted
  exact hconverted

theorem store_float_align
    (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_float CRules x v) (store_align_n CRules 4) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_float_align4 CRules x v)
    (by simpa using store_align4_to_store_align CRules 1)

theorem store_double_align
    (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_double CRules x v) (store_align_n CRules 8) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_double_align4 CRules x v)
    (by simpa using store_align4_to_store_align CRules 2)

theorem undef_store_long_double_align (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_long_double CRules x) (store_align_n CRules 16) := by
  unfold DerivedPredSig.undef_store_long_double store_16byte_noninit
  apply coq_prop_andp_left
  intro hvalid
  unfold DerivedPredSig.isvalidptr_long_double at hvalid
  change x >= 0 ∧ x + 15 <= Arch.addr_max_unsigned ∧ aligned_8 x at hvalid
  apply store_bytes_noninit_align CRules 16 x hvalid.1
  change x + 16 - 1 <= Arch.addr_max_unsigned
  omega

theorem store_long_double_align
    (CRules : SeparationLogicSig) (x : Int) (v : fp128) :
    CRules.derivable1 (store_long_double CRules x v) (store_align_n CRules 16) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_long_double_undef_store_long_double CRules x v)
    (undef_store_long_double_align CRules x)

theorem store_finite_float_align
    (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_finite_float CRules x v) (store_align_n CRules 4) := by
  intro state h
  exact store_float_align CRules x v state h.2

theorem store_finite_double_align
    (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_finite_double CRules x v) (store_align_n CRules 8) := by
  intro state h
  exact store_double_align CRules x v state h.2

theorem store_finite_long_double_align
    (CRules : SeparationLogicSig) (x : Int) (v : fp128) :
    CRules.derivable1 (store_finite_long_double CRules x v)
      (store_align_n CRules 16) := by
  intro state h
  exact store_long_double_align CRules x v state h.2

private theorem ptr_valid_int64_of_size8 (x : Int) (hsize : Arch.ptr_size = 8)
    (h : isvalidptr x) : isvalidptr_int64 x := by
  change x >= 0 ∧ x + Arch.ptr_size_Z - 1 <= Arch.addr_max_unsigned ∧
    Z.modulo x Arch.ptr_align = 0 at h
  change x >= 0 ∧ x + 7 <= Arch.addr_max_unsigned ∧ aligned_4 x
  rcases h with ⟨hlo, hhi, halign⟩
  refine ⟨hlo, ?_, ?_⟩
  · unfold CArchSig.ptr_size_Z at hhi
    rw [hsize] at hhi
    simp at hhi
    omega
  · unfold aligned_4
    have h4 := Arch.ptr_aligned_aligned_4 x halign
    unfold Z.modulo at h4
    rw [Int.fmod_eq_emod_of_nonneg x (by decide)] at h4
    exact h4

theorem undef_store_ptr_undef_store_uint64 (CRules : SeparationLogicSig) (x : Int)
    (hsize : Arch.ptr_size = 8) :
    CRules.derivable1 (undef_store_ptr CRules x) (undef_store_uint64 CRules x) := by
  intro _ h
  simp only [DerivedPredSig.undef_store_ptr, hsize] at h
  exact ⟨ptr_valid_int64_of_size8 x hsize h.1, h.2⟩

theorem undef_store_ptr_undef_store_int64 (CRules : SeparationLogicSig) (x : Int)
    (hsize : Arch.ptr_size = 8) :
    CRules.derivable1 (undef_store_ptr CRules x) (undef_store_int64 CRules x) := by
  simpa [DerivedPredSig.undef_store_uint64,
    DerivedPredSig.undef_store_int64] using
    undef_store_ptr_undef_store_uint64 CRules x hsize

theorem undef_store_ptr_align (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1 (undef_store_ptr CRules x)
      (store_align_n CRules Arch.ptr_size_Z) := by
  rcases Arch.ptr_size_32_or_64 with hsize | hsize
  · exact CRules.toContext.derivable1_trans _ _ _
      (undef_store_ptr_align4 CRules x hsize)
      (by simpa [CArchSig.ptr_size_Z, hsize] using
        store_align4_to_store_align CRules 1)
  · exact CRules.toContext.derivable1_trans _ _ _
      (undef_store_ptr_undef_store_uint64 CRules x hsize)
      (CRules.toContext.derivable1_trans _ _ _
        (undef_store_uint64_align4 CRules x)
        (by simpa [CArchSig.ptr_size_Z, hsize] using
          store_align4_to_store_align CRules 2))

theorem store_ptr_align (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_ptr CRules x v)
      (store_align_n CRules Arch.ptr_size_Z) :=
  CRules.toContext.derivable1_trans _ _ _
    (store_ptr_undef_store_ptr CRules x v)
    (undef_store_ptr_align CRules x)

theorem store_ptr_store_uint (CRules : SeparationLogicSig) (x v : Int)
    (hsize : Arch.ptr_size = 4) (haddr : Arch.addr_max_unsigned = Int.max_unsigned) :
    CRules.derivable1 (store_ptr CRules x v) (store_uint CRules x v) := by
  intro state h
  simp only [DerivedPredSig.store_ptr, hsize] at h
  have hvalid := ptr_valid_int_of_size4 x hsize h.1.1
  have hvalue : 0 <= v ∧ v <= Int.max_unsigned := by
    unfold DerivedPredSig.valid_ptr_value CArchSig.valid_ptr_value at h
    rw [haddr] at h
    exact h.1.2
  exact ⟨⟨hvalid, hvalue⟩, h.2⟩

theorem store_ptr_store_uint64 (CRules : SeparationLogicSig) (x v : Int)
    (hsize : Arch.ptr_size = 8) (haddr : Arch.addr_max_unsigned = Int64.max_unsigned) :
    CRules.derivable1 (store_ptr CRules x v) (store_uint64 CRules x v) := by
  intro state h
  simp only [DerivedPredSig.store_ptr, hsize] at h
  have hvalid : isvalidptr_int64 x := by
    unfold DerivedPredSig.isvalidptr at h
    unfold DerivedPredSig.isvalidptr_int64
    change x >= 0 ∧ x + 7 <= Arch.addr_max_unsigned ∧ aligned_4 x
    rcases h.1.1 with ⟨hlo, hhi, halign⟩
    refine ⟨hlo, ?_, ?_⟩
    · change x + Int.ofNat Arch.ptr_size - 1 <= Arch.addr_max_unsigned at hhi
      rw [hsize] at hhi
      simp at hhi
      omega
    · unfold aligned_4
      have h4 := Arch.ptr_aligned_aligned_4 x halign
      unfold Z.modulo at h4
      rw [Int.fmod_eq_emod_of_nonneg x (by decide)] at h4
      exact h4
  have hvalue : 0 <= v ∧ v <= Int64.max_unsigned := by
    unfold DerivedPredSig.valid_ptr_value CArchSig.valid_ptr_value at h
    rw [haddr] at h
    exact h.1.2
  exact ⟨⟨hvalid, hvalue⟩, h.2⟩

end Canonical

end SimpleC.SL.StoreAux.StoreLibSig
