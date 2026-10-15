import SimpleC.SL.StoreAux.Generic

namespace SimpleC.SL.StoreAux.StoreLibSig

open SimpleC.SL.CNotation
open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.IntLib
open SimpleC.SL.FloatLib
open Unifysl.LogicGenerator.demo932

private theorem false_sepcon_elim (CRules : SeparationLogicSig) (Q : CRules.expr) :
    CRules.derivable1
      (CRules.sepcon (CRules.coq_prop False) Q) (CRules.coq_prop False) := by
  intro state h
  rcases h with ⟨_, _, _, hfalse, _⟩
  exact hfalse

private theorem absorb_false (CRules : SeparationLogicSig)
    (P Q : CRules.expr) (hP : CRules.derivable1 P (CRules.coq_prop False)) :
    CRules.derivable1 (CRules.sepcon P Q) (CRules.coq_prop False) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _ hP
      (CRules.toContext.derivable1_truep_intros Q))
    (false_sepcon_elim CRules CRules.truep)

private theorem dup_sepcon_prefix (CRules : SeparationLogicSig)
    (A Q : CRules.expr)
    (hdup : CRules.derivable1 (CRules.sepcon A A) (CRules.coq_prop False)) :
    CRules.derivable1
      (CRules.sepcon (CRules.sepcon A Q) (CRules.sepcon A Q))
      (CRules.coq_prop False) := by
  have hleft :
      CRules.derivable1 (CRules.sepcon (CRules.sepcon A Q) A)
        (CRules.coq_prop False) := by
    exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_comm (CRules.sepcon A Q) A)
      (CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.derivable1_sepcon_assoc1 A A Q)
        (absorb_false CRules (CRules.sepcon A A) Q hdup))
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_assoc1 (CRules.sepcon A Q) A Q)
    (absorb_false CRules (CRules.sepcon (CRules.sepcon A Q) A) Q hleft)

section Canonical

variable {Arch : CArchSig} {Endian : CEndianSig}

local notation "merge_short" => DerivedPredSig.merge_short Endian
local notation "merge_int" => DerivedPredSig.merge_int Endian
local notation "merge_int64" => DerivedPredSig.merge_int64 Endian
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
local notation "undef_store_finite_float" => DerivedPredSig.undef_store_finite_float Arch
local notation "store_finite_double" => DerivedPredSig.store_finite_double Arch Endian
local notation "undef_store_finite_double" => DerivedPredSig.undef_store_finite_double Arch
local notation "store_finite_long_double" =>
  DerivedPredSig.store_finite_long_double Arch Endian
local notation "undef_store_finite_long_double" =>
  DerivedPredSig.undef_store_finite_long_double Arch
local notation "store_ptr" => DerivedPredSig.store_ptr Arch Endian
local notation "undef_store_ptr" => DerivedPredSig.undef_store_ptr Arch
local notation "typed_poly_store" => DerivedPredSig.typed_poly_store Arch Endian
local notation "poly_store" => DerivedPredSig.poly_store Arch Endian
local notation "poly_undef_store" => DerivedPredSig.poly_undef_store Arch
local notation "isvalidptr_char" => DerivedPredSig.isvalidptr_char Arch
local notation "isvalidptr_short" => DerivedPredSig.isvalidptr_short Arch
local notation "isvalidptr_int" => DerivedPredSig.isvalidptr_int Arch
local notation "isvalidptr_int64" => DerivedPredSig.isvalidptr_int64 Arch
local notation "isvalidptr_int128" => DerivedPredSig.isvalidptr_int128 Arch

def merge_int64_by_ints (Endian : CEndianSig) (w1 w2 v : Int) : Prop :=
  ∃ b1 b2 b3 b4 b5 b6 b7 b8,
    DerivedPredSig.merge_int Endian b1 b2 b3 b4 w1 ∧
    DerivedPredSig.merge_int Endian b5 b6 b7 b8 w2 ∧
    DerivedPredSig.merge_int64 Endian b1 b2 b3 b4 b5 b6 b7 b8 v

def signed_int_of_bytes (Endian : CEndianSig) (b1 b2 b3 b4 : Int) : Int :=
  signed_last_nbits
    (DerivedPredSig.n_bytes_to_Z Endian 4 (DerivedPredSig.vec4 b1 b2 b3 b4)) 32

def unsigned_int_of_bytes (Endian : CEndianSig) (b1 b2 b3 b4 : Int) : Int :=
  unsigned_last_nbits
    (DerivedPredSig.n_bytes_to_Z Endian 4 (DerivedPredSig.vec4 b1 b2 b3 b4)) 32

theorem merge_int_signed_of_bytes (b1 b2 b3 b4 : Int) :
    merge_int b1 b2 b3 b4 (signed_int_of_bytes Endian b1 b2 b3 b4) := by
  apply Endian.merge_int_value_eqm b1 b2 b3 b4 _ _
    (signed_Lastnbits_mod_correct _ 32 (by omega))
  exact (Endian.merge_int_equiv_merge_n_bytes b1 b2 b3 b4 _).mpr
    (Endian.merge_n_bytes_self 4 (DerivedPredSig.vec4 b1 b2 b3 b4))

theorem merge_int_unsigned_of_bytes (b1 b2 b3 b4 : Int) :
    merge_int b1 b2 b3 b4 (unsigned_int_of_bytes Endian b1 b2 b3 b4) := by
  apply Endian.merge_int_value_eqm b1 b2 b3 b4 _ _
    (unsigned_Lastnbits_mod_correct _ 32 (by omega))
  exact (Endian.merge_int_equiv_merge_n_bytes b1 b2 b3 b4 _).mpr
    (Endian.merge_n_bytes_self 4 (DerivedPredSig.vec4 b1 b2 b3 b4))

theorem signed_int_of_bytes_range (b1 b2 b3 b4 : Int) :
    Int.min_signed <= signed_int_of_bytes Endian b1 b2 b3 b4 ∧
      signed_int_of_bytes Endian b1 b2 b3 b4 <= Int.max_signed := by
  have h := signed_Lastnbits_range
    (DerivedPredSig.n_bytes_to_Z Endian 4 (DerivedPredSig.vec4 b1 b2 b3 b4)) 32
    (by omega)
  rw [show Z.pow 2 (32 - 1) = 2147483648 by decide] at h
  constructor
  · simpa [signed_int_of_bytes, Int.min_signed, Int.half_modulus,
      Int.modulus] using h.1
  · simpa [signed_int_of_bytes, Int.max_signed, Int.half_modulus,
      Int.modulus] using (show
        signed_last_nbits
          (DerivedPredSig.n_bytes_to_Z Endian 4 (DerivedPredSig.vec4 b1 b2 b3 b4)) 32
            <= 2147483647 by omega)

theorem unsigned_int_of_bytes_range (b1 b2 b3 b4 : Int) :
    0 <= unsigned_int_of_bytes Endian b1 b2 b3 b4 ∧
      unsigned_int_of_bytes Endian b1 b2 b3 b4 <= Int.max_unsigned := by
  have h := unsigned_Lastnbits_range
    (DerivedPredSig.n_bytes_to_Z Endian 4 (DerivedPredSig.vec4 b1 b2 b3 b4)) 32
    (by omega)
  rw [show Z.pow 2 32 = 4294967296 by decide] at h
  exact ⟨by simpa [unsigned_int_of_bytes] using h.1,
    by simpa [unsigned_int_of_bytes, Int.max_unsigned, Int.modulus] using (show
      unsigned_last_nbits
        (DerivedPredSig.n_bytes_to_Z Endian 4 (DerivedPredSig.vec4 b1 b2 b3 b4)) 32
          <= 4294967295 by omega)⟩

private theorem sepcon8_split4 (CRules : SeparationLogicSig)
    (A0 A1 A2 A3 A4 A5 A6 A7 : CRules.expr) :
    CRules.derivable1
      (CRules.sepcon A0 (CRules.sepcon A1 (CRules.sepcon A2
        (CRules.sepcon A3 (CRules.sepcon A4 (CRules.sepcon A5
          (CRules.sepcon A6 A7)))))))
      (CRules.sepcon
        (CRules.sepcon A0 (CRules.sepcon A1 (CRules.sepcon A2 A3)))
        (CRules.sepcon A4 (CRules.sepcon A5 (CRules.sepcon A6 A7)))) := by
  have h1 := CRules.toContext.derivable1_sepcon_mono A0 A0 _ _
    (CRules.toContext.derivable1_refl A0) <|
      CRules.toContext.derivable1_sepcon_mono A1 A1 _ _
        (CRules.toContext.derivable1_refl A1) <|
          CRules.toContext.derivable1_sepcon_assoc1 A2 A3
            (CRules.sepcon A4 (CRules.sepcon A5 (CRules.sepcon A6 A7)))
  have h2 := CRules.toContext.derivable1_sepcon_mono A0 A0 _ _
    (CRules.toContext.derivable1_refl A0) <|
      CRules.toContext.derivable1_sepcon_assoc1 A1 (CRules.sepcon A2 A3)
        (CRules.sepcon A4 (CRules.sepcon A5 (CRules.sepcon A6 A7)))
  have h3 := CRules.toContext.derivable1_sepcon_assoc1 A0
    (CRules.sepcon A1 (CRules.sepcon A2 A3))
    (CRules.sepcon A4 (CRules.sepcon A5 (CRules.sepcon A6 A7)))
  exact CRules.toContext.derivable1_trans _ _ _ h1
    (CRules.toContext.derivable1_trans _ _ _ h2 h3)

private theorem int64_valid_word_parts (p : Int) (h : isvalidptr_int64 p) :
    isvalidptr_int p ∧ isvalidptr_int (p + 4) ∧ aligned_4 p := by
  unfold DerivedPredSig.isvalidptr_int64 at h
  unfold DerivedPredSig.isvalidptr_int
  rcases h with ⟨hlo, hhi, halign⟩
  have halign4 : aligned_4 (p + 4) := by
    unfold aligned_4 at halign ⊢
    omega
  exact ⟨⟨hlo, by omega, halign⟩,
    ⟨by omega, by omega, halign4⟩, halign⟩

set_option maxHeartbeats 1000000 in
private theorem store_8byte_to_signed_words (CRules : SeparationLogicSig)
    (p v : Int) (Range : Prop) (hrange : Range) (hvalid : isvalidptr_int64 p) :
    CRules.derivable1 (store_8byte CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 =>
        CRules.andp
          (CRules.coq_prop
            (merge_int64_by_ints Endian v1 v2 v ∧ Range ∧ aligned_4 p))
          (CRules.sepcon (store_int CRules p v1) (store_int CRules (p + 4) v2))) := by
  intro state h
  rcases h with ⟨z1, z2, z3, z4, z5, z6, z7, z8, hmerge, hstores⟩
  let v1 := signed_int_of_bytes Endian z1 z2 z3 z4
  let v2 := signed_int_of_bytes Endian z5 z6 z7 z8
  have hv := int64_valid_word_parts p hvalid
  have hr1 := signed_int_of_bytes_range (Endian := Endian) z1 z2 z3 z4
  have hr2 := signed_int_of_bytes_range (Endian := Endian) z5 z6 z7 z8
  have hm1 := merge_int_signed_of_bytes (Endian := Endian) z1 z2 z3 z4
  have hm2 := merge_int_signed_of_bytes (Endian := Endian) z5 z6 z7 z8
  let B0 := store_byte CRules p z1
  let B1 := store_byte CRules (p + 1) z2
  let B2 := store_byte CRules (p + 2) z3
  let B3 := store_byte CRules (p + 3) z4
  let B4 := store_byte CRules (p + 4) z5
  let B5 := store_byte CRules (p + 5) z6
  let B6 := store_byte CRules (p + 6) z7
  let B7 := store_byte CRules (p + 7) z8
  have hleft : CRules.derivable1
      (CRules.sepcon B0 (CRules.sepcon B1 (CRules.sepcon B2 B3)))
      (store_int CRules p v1) := by
    intro s hs
    exact ⟨⟨hv.1, hr1.2, hr1.1⟩, ⟨z1, z2, z3, z4, hm1, hs⟩⟩
  have hright : CRules.derivable1
      (CRules.sepcon B4 (CRules.sepcon B5 (CRules.sepcon B6 B7)))
      (store_int CRules (p + 4) v2) := by
    intro s hs
    have hs' : CRules.sepcon (store_byte CRules (p + 4) z5)
        (CRules.sepcon (store_byte CRules (p + 4 + 1) z6)
          (CRules.sepcon (store_byte CRules (p + 4 + 2) z7)
            (store_byte CRules (p + 4 + 3) z8))) s := by
      simpa [B4, B5, B6, B7, Int.add_assoc] using hs
    exact ⟨⟨hv.2.1, hr2.2, hr2.1⟩, ⟨z5, z6, z7, z8, hm2, hs'⟩⟩
  have hsplit := sepcon8_split4 CRules B0 B1 B2 B3 B4 B5 B6 B7 state
    (by simpa [B0, B1, B2, B3, B4, B5, B6, B7] using hstores)
  refine ⟨v1, v2, ?_, ?_⟩
  · exact ⟨⟨z1, z2, z3, z4, z5, z6, z7, z8, hm1, hm2, hmerge⟩,
      hrange, hv.2.2⟩
  · exact CRules.toContext.derivable1_sepcon_mono _ _ _ _ hleft hright state hsplit

set_option maxHeartbeats 1000000 in
private theorem store_8byte_to_unsigned_words (CRules : SeparationLogicSig)
    (p v : Int) (Range : Prop) (hrange : Range) (hvalid : isvalidptr_int64 p) :
    CRules.derivable1 (store_8byte CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 =>
        CRules.andp
          (CRules.coq_prop
            (merge_int64_by_ints Endian v1 v2 v ∧ Range ∧ aligned_4 p))
          (CRules.sepcon (store_uint CRules p v1) (store_uint CRules (p + 4) v2))) := by
  intro state h
  rcases h with ⟨z1, z2, z3, z4, z5, z6, z7, z8, hmerge, hstores⟩
  let v1 := unsigned_int_of_bytes Endian z1 z2 z3 z4
  let v2 := unsigned_int_of_bytes Endian z5 z6 z7 z8
  have hv := int64_valid_word_parts p hvalid
  have hr1 := unsigned_int_of_bytes_range (Endian := Endian) z1 z2 z3 z4
  have hr2 := unsigned_int_of_bytes_range (Endian := Endian) z5 z6 z7 z8
  have hm1 := merge_int_unsigned_of_bytes (Endian := Endian) z1 z2 z3 z4
  have hm2 := merge_int_unsigned_of_bytes (Endian := Endian) z5 z6 z7 z8
  let B0 := store_byte CRules p z1
  let B1 := store_byte CRules (p + 1) z2
  let B2 := store_byte CRules (p + 2) z3
  let B3 := store_byte CRules (p + 3) z4
  let B4 := store_byte CRules (p + 4) z5
  let B5 := store_byte CRules (p + 5) z6
  let B6 := store_byte CRules (p + 6) z7
  let B7 := store_byte CRules (p + 7) z8
  have hleft : CRules.derivable1
      (CRules.sepcon B0 (CRules.sepcon B1 (CRules.sepcon B2 B3)))
      (store_uint CRules p v1) := by
    intro s hs
    exact ⟨⟨hv.1, hr1.1, hr1.2⟩, ⟨z1, z2, z3, z4, hm1, hs⟩⟩
  have hright : CRules.derivable1
      (CRules.sepcon B4 (CRules.sepcon B5 (CRules.sepcon B6 B7)))
      (store_uint CRules (p + 4) v2) := by
    intro s hs
    have hs' : CRules.sepcon (store_byte CRules (p + 4) z5)
        (CRules.sepcon (store_byte CRules (p + 4 + 1) z6)
          (CRules.sepcon (store_byte CRules (p + 4 + 2) z7)
            (store_byte CRules (p + 4 + 3) z8))) s := by
      simpa [B4, B5, B6, B7, Int.add_assoc] using hs
    exact ⟨⟨hv.2.1, hr2.1, hr2.2⟩, ⟨z5, z6, z7, z8, hm2, hs'⟩⟩
  have hsplit := sepcon8_split4 CRules B0 B1 B2 B3 B4 B5 B6 B7 state
    (by simpa [B0, B1, B2, B3, B4, B5, B6, B7] using hstores)
  refine ⟨v1, v2, ?_, ?_⟩
  · exact ⟨⟨z1, z2, z3, z4, z5, z6, z7, z8, hm1, hm2, hmerge⟩,
      hrange, hv.2.2⟩
  · exact CRules.toContext.derivable1_sepcon_mono _ _ _ _ hleft hright state hsplit

theorem store_int64_store_int (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_int64 CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 =>
        CRules.andp (CRules.coq_prop
          (merge_int64_by_ints Endian v1 v2 v ∧
            (Int64.min_signed <= v ∧ v <= Int64.max_signed) ∧ aligned_4 p))
          (CRules.sepcon (store_int CRules p v1) (store_int CRules (p + 4) v2))) := by
  intro state h
  exact store_8byte_to_signed_words CRules p v _ ⟨h.1.2.2, h.1.2.1⟩ h.1.1 state h.2

theorem store_uint64_store_uint (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_uint64 CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 =>
        CRules.andp (CRules.coq_prop
          (merge_int64_by_ints Endian v1 v2 v ∧
            (0 <= v ∧ v <= Int64.max_unsigned) ∧ aligned_4 p))
          (CRules.sepcon (store_uint CRules p v1) (store_uint CRules (p + 4) v2))) := by
  intro state h
  exact store_8byte_to_unsigned_words CRules p v _ h.1.2 h.1.1 state h.2

theorem store_int64_store_uint (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_int64 CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 =>
        CRules.andp (CRules.coq_prop
          (merge_int64_by_ints Endian v1 v2 v ∧
            (Int64.min_signed <= v ∧ v <= Int64.max_signed) ∧ aligned_4 p))
          (CRules.sepcon (store_uint CRules p v1) (store_uint CRules (p + 4) v2))) := by
  intro state h
  exact store_8byte_to_unsigned_words CRules p v _ ⟨h.1.2.2, h.1.2.1⟩ h.1.1 state h.2

theorem store_uint64_store_int (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_uint64 CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 =>
        CRules.andp (CRules.coq_prop
          (merge_int64_by_ints Endian v1 v2 v ∧
            (0 <= v ∧ v <= Int64.max_unsigned) ∧ aligned_4 p))
          (CRules.sepcon (store_int CRules p v1) (store_int CRules (p + 4) v2))) := by
  intro state h
  exact store_8byte_to_signed_words CRules p v _ h.1.2 h.1.1 state h.2

theorem store_byte_store_byte_noinit (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_byte CRules p v) (store_byte_noninit CRules p) := by
  intro state h
  exact CRules.mstore_mstore_noninit p v state h

theorem store_2byte_store_2byte_noinit (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_2byte CRules p v) (store_2byte_noninit CRules p) := by
  unfold DerivedPredSig.store_2byte store_2byte_noninit
  apply Automation.exp_left_rule
  intro z1
  apply Automation.exp_left_rule
  intro z2
  apply coq_prop_andp_left
  intro _
  exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (store_byte_store_byte_noinit CRules p z1)
    (store_byte_store_byte_noinit CRules (p + 1) z2)

theorem store_4byte_store_4byte_noinit (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_4byte CRules p v) (store_4byte_noninit CRules p) := by
  unfold DerivedPredSig.store_4byte store_4byte_noninit
  apply Automation.exp_left_rule
  intro z1
  apply Automation.exp_left_rule
  intro z2
  apply Automation.exp_left_rule
  intro z3
  apply Automation.exp_left_rule
  intro z4
  apply coq_prop_andp_left
  intro _
  exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (store_byte_store_byte_noinit CRules p z1)
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_byte_store_byte_noinit CRules (p + 1) z2)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (store_byte_store_byte_noinit CRules (p + 2) z3)
        (store_byte_store_byte_noinit CRules (p + 3) z4)))

theorem store_8byte_store_8byte_noinit (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_8byte CRules p v) (store_8byte_noninit CRules p) := by
  unfold DerivedPredSig.store_8byte store_8byte_noninit
  apply Automation.exp_left_rule
  intro z1
  apply Automation.exp_left_rule
  intro z2
  apply Automation.exp_left_rule
  intro z3
  apply Automation.exp_left_rule
  intro z4
  apply Automation.exp_left_rule
  intro z5
  apply Automation.exp_left_rule
  intro z6
  apply Automation.exp_left_rule
  intro z7
  apply Automation.exp_left_rule
  intro z8
  apply coq_prop_andp_left
  intro _
  exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (store_byte_store_byte_noinit CRules p z1)
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_byte_store_byte_noinit CRules (p + 1) z2)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (store_byte_store_byte_noinit CRules (p + 2) z3)
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (store_byte_store_byte_noinit CRules (p + 3) z4)
          (CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (store_byte_store_byte_noinit CRules (p + 4) z5)
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (store_byte_store_byte_noinit CRules (p + 5) z6)
              (CRules.toContext.derivable1_sepcon_mono _ _ _ _
                (store_byte_store_byte_noinit CRules (p + 6) z7)
                (store_byte_store_byte_noinit CRules (p + 7) z8)))))))

theorem store_bytes_store_bytes_noninit (CRules : SeparationLogicSig)
    (n : Nat) (p : Int) (bytes : Vector Int n) :
    CRules.derivable1 (store_bytes CRules p n bytes)
      (store_bytes_noninit CRules p n) := by
  induction n generalizing p with
  | zero =>
      intro state h
      exact h
  | succ n ih =>
      intro state h
      rcases h with ⟨left, right, hjoin, hhead, htail⟩
      exact ⟨left, right, hjoin,
        CRules.mstore_mstore_noninit p
          (SimpleC.SL.CArch.vector_head bytes) left hhead,
        ih (p + 1) (SimpleC.SL.CArch.vector_tail bytes) right htail⟩

theorem store_16byte_store_16byte_noinit (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_16byte CRules p v) (store_16byte_noninit CRules p) := by
  unfold DerivedPredSig.store_16byte store_16byte_noninit
  apply Automation.exp_left_rule
  intro bytes
  apply coq_prop_andp_left
  intro _
  exact store_bytes_store_bytes_noninit CRules 16 p bytes

theorem store_ptr_undef_store_ptr (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_ptr CRules p v) (undef_store_ptr CRules p) := by
  rcases Arch.ptr_size_32_or_64 with hsize | hsize
  · intro state h
    simp only [DerivedPredSig.store_ptr, DerivedPredSig.undef_store_ptr,
      hsize] at h ⊢
    exact ⟨h.1.1, store_4byte_store_4byte_noinit CRules p v state h.2⟩
  · intro state h
    simp only [DerivedPredSig.store_ptr, DerivedPredSig.undef_store_ptr,
      hsize] at h ⊢
    exact ⟨h.1.1, store_8byte_store_8byte_noinit CRules p v state h.2⟩

theorem store_int_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int CRules x v)
      (CRules.coq_prop (Int.min_signed <= v ∧ v <= Int.max_signed)) := by
  intro _ h
  exact ⟨h.1.2.2, h.1.2.1⟩

theorem store_int_undef_store_int (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int CRules x v) (undef_store_int CRules x) := by
  intro state h
  exact ⟨h.1.1, store_4byte_store_4byte_noinit CRules x v state h.2⟩

theorem store_char_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_char CRules x v)
      (CRules.coq_prop (Byte.min_signed <= v ∧ v <= Byte.max_signed)) := by
  intro _ h
  exact ⟨h.1.2.2, h.1.2.1⟩

theorem store_char_undef_store_char (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_char CRules x v) (undef_store_char CRules x) := by
  intro state h
  exact ⟨h.1.1, store_byte_store_byte_noinit CRules x v state h.2⟩

theorem store_short_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_short CRules x v)
      (CRules.coq_prop (-32768 <= v ∧ v <= 32767)) := by
  intro _ h
  exact ⟨h.1.2.2, h.1.2.1⟩

theorem store_short_undef_store_short (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_short CRules x v) (undef_store_short CRules x) := by
  intro state h
  exact ⟨h.1.1, store_2byte_store_2byte_noinit CRules x v state h.2⟩

theorem store_int64_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int64 CRules x v)
      (CRules.coq_prop (Int64.min_signed <= v ∧ v <= Int64.max_signed)) := by
  intro _ h
  exact ⟨h.1.2.2, h.1.2.1⟩

theorem store_int64_undef_store_int64 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int64 CRules x v) (undef_store_int64 CRules x) := by
  intro state h
  exact ⟨h.1.1, store_8byte_store_8byte_noinit CRules x v state h.2⟩

theorem store_uint_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint CRules x v)
      (CRules.coq_prop (0 <= v ∧ v <= Int.max_unsigned)) := by
  intro _ h
  exact h.1.2

theorem store_uint_undef_store_uint (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint CRules x v) (undef_store_uint CRules x) := by
  intro state h
  exact ⟨h.1.1, store_4byte_store_4byte_noinit CRules x v state h.2⟩

theorem store_uchar_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uchar CRules x v)
      (CRules.coq_prop (0 <= v ∧ v <= Byte.max_unsigned)) := by
  intro _ h
  exact h.1.2

theorem store_uchar_undef_store_uchar (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uchar CRules x v) (undef_store_uchar CRules x) := by
  intro state h
  exact ⟨h.1.1, store_byte_store_byte_noinit CRules x v state h.2⟩

theorem store_ushort_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_ushort CRules x v)
      (CRules.coq_prop (0 <= v ∧ v <= 65535)) := by
  intro _ h
  exact h.1.2

theorem store_ushort_undef_store_ushort (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_ushort CRules x v) (undef_store_ushort CRules x) := by
  intro state h
  exact ⟨h.1.1, store_2byte_store_2byte_noinit CRules x v state h.2⟩

theorem store_uint64_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint64 CRules x v)
      (CRules.coq_prop (0 <= v ∧ v <= Int64.max_unsigned)) := by
  intro _ h
  exact h.1.2

theorem store_uint64_undef_store_uint64 (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint64 CRules x v) (undef_store_uint64 CRules x) := by
  intro state h
  exact ⟨h.1.1, store_8byte_store_8byte_noinit CRules x v state h.2⟩

theorem store_int128_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int128 CRules x v)
      (CRules.coq_prop
        (SimpleC.SL.IntLib.Int128.min_signed <= v ∧
          v <= SimpleC.SL.IntLib.Int128.max_signed)) := by
  intro _ h
  exact ⟨h.1.2.2, h.1.2.1⟩

theorem store_int128_undef_store_int128
    (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int128 CRules x v) (undef_store_int128 CRules x) := by
  intro state h
  exact ⟨h.1.1, store_16byte_store_16byte_noinit CRules x v state h.2⟩

theorem store_uint128_range (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint128 CRules x v)
      (CRules.coq_prop
        (0 <= v ∧ v <= SimpleC.SL.IntLib.Int128.max_unsigned)) := by
  intro _ h
  exact h.1.2

theorem store_uint128_undef_store_uint128
    (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint128 CRules x v) (undef_store_uint128 CRules x) := by
  intro state h
  exact ⟨h.1.1, store_16byte_store_16byte_noinit CRules x v state h.2⟩

theorem store_float_undef_store_float
    (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_float CRules x v) (undef_store_float CRules x) := by
  intro state h
  exact ⟨h.1.1, store_4byte_store_4byte_noinit CRules x (bits_of_fp32 v) state h.2⟩

theorem store_double_undef_store_double
    (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_double CRules x v) (undef_store_double CRules x) := by
  intro state h
  exact ⟨h.1.1, store_8byte_store_8byte_noinit CRules x (bits_of_fp64 v) state h.2⟩

theorem store_long_double_undef_store_long_double
    (CRules : SeparationLogicSig) (x : Int) (v : fp128) :
    CRules.derivable1 (store_long_double CRules x v)
      (undef_store_long_double CRules x) := by
  intro state h
  exact ⟨h.1.1,
    store_16byte_store_16byte_noinit CRules x (bits_of_fp128 v) state h.2⟩

theorem store_finite_float_undef_store_finite_float
    (CRules : SeparationLogicSig) (x : Int) (v : fp32) :
    CRules.derivable1 (store_finite_float CRules x v)
      (undef_store_finite_float CRules x) := by
  intro state h
  exact store_float_undef_store_float CRules x v state h.2

theorem store_finite_double_undef_store_finite_double
    (CRules : SeparationLogicSig) (x : Int) (v : fp64) :
    CRules.derivable1 (store_finite_double CRules x v)
      (undef_store_finite_double CRules x) := by
  intro state h
  exact store_double_undef_store_double CRules x v state h.2

theorem store_finite_long_double_undef_store_finite_long_double
    (CRules : SeparationLogicSig) (x : Int) (v : fp128) :
    CRules.derivable1 (store_finite_long_double CRules x v)
      (undef_store_finite_long_double CRules x) := by
  intro state h
  exact store_long_double_undef_store_long_double CRules x v state h.2

theorem poly_store_poly_undef_store (CRules : SeparationLogicSig)
    (x : Int) (ty : front_end_type) (v : Int) :
    CRules.derivable1 (poly_store CRules ty x v) (poly_undef_store CRules ty x) := by
  cases ty with
  | FET_struct _ | FET_union _ | FET_enum _ | FET_alias _ =>
      exact CRules.toContext.derivable1_refl _
  | FET_int => exact store_int_undef_store_int CRules x v
  | FET_char => exact store_char_undef_store_char CRules x v
  | FET_int64 => exact store_int64_undef_store_int64 CRules x v
  | FET_short => exact store_short_undef_store_short CRules x v
  | FET_uint => exact store_uint_undef_store_uint CRules x v
  | FET_uchar => exact store_uchar_undef_store_uchar CRules x v
  | FET_uint64 => exact store_uint64_undef_store_uint64 CRules x v
  | FET_int128 => exact store_int128_undef_store_int128 CRules x v
  | FET_uint128 => exact store_uint128_undef_store_uint128 CRules x v
  | FET_ushort => exact store_ushort_undef_store_ushort CRules x v
  | FET_float => exact store_float_undef_store_float CRules x (fp32_of_bits v)
  | FET_double => exact store_double_undef_store_double CRules x (fp64_of_bits v)
  | FET_long_double =>
      exact store_long_double_undef_store_long_double CRules x (fp128_of_bits v)
  | FET_ptr => exact store_ptr_undef_store_ptr CRules x v

theorem typed_poly_store_poly_undef_store (CRules : SeparationLogicSig)
    (x : Int) (ty : front_end_type) (v : front_end_type_value ty) :
    CRules.derivable1 (typed_poly_store CRules ty x v) (poly_undef_store CRules ty x) := by
  cases ty with
  | FET_struct _ | FET_union _ | FET_enum _ | FET_alias _ =>
      exact CRules.toContext.derivable1_refl _
  | FET_int => exact store_int_undef_store_int CRules x v
  | FET_char => exact store_char_undef_store_char CRules x v
  | FET_int64 => exact store_int64_undef_store_int64 CRules x v
  | FET_short => exact store_short_undef_store_short CRules x v
  | FET_uint => exact store_uint_undef_store_uint CRules x v
  | FET_uchar => exact store_uchar_undef_store_uchar CRules x v
  | FET_uint64 => exact store_uint64_undef_store_uint64 CRules x v
  | FET_int128 => exact store_int128_undef_store_int128 CRules x v
  | FET_uint128 => exact store_uint128_undef_store_uint128 CRules x v
  | FET_ushort => exact store_ushort_undef_store_ushort CRules x v
  | FET_float => exact store_float_undef_store_float CRules x v
  | FET_double => exact store_double_undef_store_double CRules x v
  | FET_long_double => exact store_long_double_undef_store_long_double CRules x v
  | FET_ptr => exact store_ptr_undef_store_ptr CRules x v

theorem dup_mstore (CRules : SeparationLogicSig) (x v1 v2 : Int) :
    CRules.derivable1
      (CRules.sepcon (CRules.mstore x v1) (CRules.mstore x v2))
      (CRules.coq_prop False) := by
  have hinit (v : Int) :
      CRules.derivable1 (CRules.mstore x v) (CRules.mstore_noninit x) := by
    intro state h
    exact CRules.mstore_mstore_noninit x v state h
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _ (hinit v1) (hinit v2))
    (CRules.dup_mstore_noninit x)

theorem dup_store_byte_noninit (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1
      (CRules.sepcon (store_byte_noninit CRules x) (store_byte_noninit CRules x))
      (CRules.coq_prop False) :=
  CRules.dup_mstore_noninit x

theorem dup_store_byte (CRules : SeparationLogicSig) (x v1 v2 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_byte CRules x v1) (store_byte CRules x v2))
      (CRules.coq_prop False) :=
  dup_mstore CRules x v1 v2

theorem dup_store_2bytes_noninit (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1
      (CRules.sepcon (store_2byte_noninit CRules x) (store_2byte_noninit CRules x))
      (CRules.coq_prop False) := by
  unfold store_2byte_noninit
  exact dup_sepcon_prefix CRules _ _ (dup_store_byte_noninit CRules x)

theorem dup_store_2bytes (CRules : SeparationLogicSig) (x v1 v2 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_2byte CRules x v1) (store_2byte CRules x v2))
      (CRules.coq_prop False) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_2byte_store_2byte_noinit CRules x v1)
      (store_2byte_store_2byte_noinit CRules x v2))
    (dup_store_2bytes_noninit CRules x)

theorem dup_store_4bytes_noninit (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1
      (CRules.sepcon (store_4byte_noninit CRules x) (store_4byte_noninit CRules x))
      (CRules.coq_prop False) := by
  unfold store_4byte_noninit
  exact dup_sepcon_prefix CRules _ _ (dup_store_byte_noninit CRules x)

theorem dup_store_4bytes (CRules : SeparationLogicSig) (x v1 v2 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_4byte CRules x v1) (store_4byte CRules x v2))
      (CRules.coq_prop False) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_4byte_store_4byte_noinit CRules x v1)
      (store_4byte_store_4byte_noinit CRules x v2))
    (dup_store_4bytes_noninit CRules x)

theorem dup_store_8bytes_noninit (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1
      (CRules.sepcon (store_8byte_noninit CRules x) (store_8byte_noninit CRules x))
      (CRules.coq_prop False) := by
  unfold store_8byte_noninit
  exact dup_sepcon_prefix CRules _ _ (dup_store_byte_noninit CRules x)

theorem dup_store_8bytes (CRules : SeparationLogicSig) (x v1 v2 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_8byte CRules x v1) (store_8byte CRules x v2))
      (CRules.coq_prop False) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_8byte_store_8byte_noinit CRules x v1)
      (store_8byte_store_8byte_noinit CRules x v2))
    (dup_store_8bytes_noninit CRules x)

theorem dup_undef_store_int (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1
      (CRules.sepcon (undef_store_int CRules x) (undef_store_int CRules x))
      (CRules.coq_prop False) := by
  have herase :
      CRules.derivable1 (undef_store_int CRules x) (store_4byte_noninit CRules x) := by
    intro _ h
    exact h.2
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _ herase herase)
    (dup_store_4bytes_noninit CRules x)

theorem dup_store_int (CRules : SeparationLogicSig) (x v1 v2 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_int CRules x v1) (store_int CRules x v2))
      (CRules.coq_prop False) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_int_undef_store_int CRules x v1)
      (store_int_undef_store_int CRules x v2))
    (dup_undef_store_int CRules x)

theorem dup_undef_store_ptr (CRules : SeparationLogicSig) (x : Int) :
    CRules.derivable1
      (CRules.sepcon (undef_store_ptr CRules x) (undef_store_ptr CRules x))
      (CRules.coq_prop False) := by
  rcases Arch.ptr_size_32_or_64 with hsize | hsize
  · have herase : CRules.derivable1 (undef_store_ptr CRules x)
        (store_4byte_noninit CRules x) := by
      intro _ h
      simpa [DerivedPredSig.undef_store_ptr, hsize] using h.2
    exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _ herase herase)
      (dup_store_4bytes_noninit CRules x)
  · have herase : CRules.derivable1 (undef_store_ptr CRules x)
        (store_8byte_noninit CRules x) := by
      intro _ h
      simpa [DerivedPredSig.undef_store_ptr, hsize] using h.2
    exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _ herase herase)
      (dup_store_8bytes_noninit CRules x)

theorem dup_store_ptr (CRules : SeparationLogicSig) (x v1 v2 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_ptr CRules x v1) (store_ptr CRules x v2))
      (CRules.coq_prop False) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (store_ptr_undef_store_ptr CRules x v1)
      (store_ptr_undef_store_ptr CRules x v2))
    (dup_undef_store_ptr CRules x)

theorem store_byte_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_byte CRules x v)
      (store_byte CRules x (signed_last_nbits v 8)) :=
  store_byte_eqm CRules x v (signed_last_nbits v 8) (UByte_cast_correct v)

theorem store_byte_cast' (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_byte CRules x v)
      (store_byte CRules x (unsigned_last_nbits v 8)) :=
  store_byte_eqm CRules x v (unsigned_last_nbits v 8) (Byte_cast_correct v)

private theorem store_2byte_map (CRules : SeparationLogicSig)
    (f : Int -> Int) (x v v' : Int)
    (hbyte : forall p z,
      CRules.derivable1 (store_byte CRules p z) (store_byte CRules p (f z)))
    (hmerge : forall z1 z2, merge_short z1 z2 v -> merge_short (f z1) (f z2) v') :
    CRules.derivable1 (store_2byte CRules x v) (store_2byte CRules x v') := by
  unfold DerivedPredSig.store_2byte
  apply Automation.exp_left_rule
  intro z1
  apply Automation.exp_left_rule
  intro z2
  apply coq_prop_andp_left
  intro hm
  refine Automation.exp_right_rule (CRules := CRules) (f z1) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z2) ?_
  apply split_pure_and_spatial_goals
  · exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (hbyte x z1) (hbyte (x + 1) z2)
  · exact dump_spatial_left CRules _ _ (hmerge z1 z2 hm)

private theorem store_4byte_map (CRules : SeparationLogicSig)
    (f : Int -> Int) (x v v' : Int)
    (hbyte : forall p z,
      CRules.derivable1 (store_byte CRules p z) (store_byte CRules p (f z)))
    (hmerge : forall z1 z2 z3 z4,
      merge_int z1 z2 z3 z4 v -> merge_int (f z1) (f z2) (f z3) (f z4) v') :
    CRules.derivable1 (store_4byte CRules x v) (store_4byte CRules x v') := by
  unfold DerivedPredSig.store_4byte
  apply Automation.exp_left_rule
  intro z1
  apply Automation.exp_left_rule
  intro z2
  apply Automation.exp_left_rule
  intro z3
  apply Automation.exp_left_rule
  intro z4
  apply coq_prop_andp_left
  intro hm
  refine Automation.exp_right_rule (CRules := CRules) (f z1) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z2) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z3) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z4) ?_
  apply split_pure_and_spatial_goals
  · exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (hbyte x z1)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (hbyte (x + 1) z2)
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (hbyte (x + 2) z3) (hbyte (x + 3) z4)))
  · exact dump_spatial_left CRules _ _ (hmerge z1 z2 z3 z4 hm)

private theorem store_8byte_map (CRules : SeparationLogicSig)
    (f : Int -> Int) (x v v' : Int)
    (hbyte : forall p z,
      CRules.derivable1 (store_byte CRules p z) (store_byte CRules p (f z)))
    (hmerge : forall z1 z2 z3 z4 z5 z6 z7 z8,
      merge_int64 z1 z2 z3 z4 z5 z6 z7 z8 v ->
      merge_int64 (f z1) (f z2) (f z3) (f z4) (f z5) (f z6) (f z7) (f z8) v') :
    CRules.derivable1 (store_8byte CRules x v) (store_8byte CRules x v') := by
  unfold DerivedPredSig.store_8byte
  apply Automation.exp_left_rule
  intro z1
  apply Automation.exp_left_rule
  intro z2
  apply Automation.exp_left_rule
  intro z3
  apply Automation.exp_left_rule
  intro z4
  apply Automation.exp_left_rule
  intro z5
  apply Automation.exp_left_rule
  intro z6
  apply Automation.exp_left_rule
  intro z7
  apply Automation.exp_left_rule
  intro z8
  apply coq_prop_andp_left
  intro hm
  refine Automation.exp_right_rule (CRules := CRules) (f z1) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z2) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z3) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z4) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z5) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z6) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z7) ?_
  refine Automation.exp_right_rule (CRules := CRules) (f z8) ?_
  apply split_pure_and_spatial_goals
  · exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (hbyte x z1)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (hbyte (x + 1) z2)
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (hbyte (x + 2) z3)
          (CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (hbyte (x + 3) z4)
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (hbyte (x + 4) z5)
              (CRules.toContext.derivable1_sepcon_mono _ _ _ _
                (hbyte (x + 5) z6)
                (CRules.toContext.derivable1_sepcon_mono _ _ _ _
                  (hbyte (x + 6) z7) (hbyte (x + 7) z8)))))))
  · exact dump_spatial_left CRules _ _
      (hmerge z1 z2 z3 z4 z5 z6 z7 z8 hm)

private theorem emod_unsigned_last_nbits (x n modulus : Int)
    (hn : n > 0) (hmod : modulus = Z.pow 2 n) (hp : 0 <= modulus) :
    unsigned_last_nbits x n % modulus = x % modulus := by
  rw [← Int.fmod_eq_emod_of_nonneg (unsigned_last_nbits x n) hp]
  rw [← Int.fmod_eq_emod_of_nonneg x hp]
  rw [hmod]
  exact (unsigned_Lastnbits_mod_correct x n hn).symm

private theorem emod_signed_last_nbits (x n modulus : Int)
    (hn : n > 0) (hmod : modulus = Z.pow 2 n) (hp : 0 <= modulus) :
    signed_last_nbits x n % modulus = x % modulus := by
  rw [← Int.fmod_eq_emod_of_nonneg (signed_last_nbits x n) hp]
  rw [← Int.fmod_eq_emod_of_nonneg x hp]
  rw [hmod]
  exact (signed_Lastnbits_mod_correct x n hn).symm

private theorem merge_short_unsigned_cast (z1 z2 v : Int)
    (h : merge_short z1 z2 v) :
    merge_short (unsigned_last_nbits z1 8) (unsigned_last_nbits z2 8)
      (unsigned_last_nbits v 16) := by
  apply Endian.merge_short_value_eqm
    (unsigned_last_nbits z1 8) (unsigned_last_nbits z2 8)
    v (unsigned_last_nbits v 16)
    (unsigned_Lastnbits_mod_correct v 16 (by omega))
  exact Endian.merge_short_eqm z1 z2 _ _ v
    (byte_eqm_unsigned_last_8 z1)
    (byte_eqm_unsigned_last_8 z2) h

private theorem merge_short_signed_cast (z1 z2 v : Int)
    (h : merge_short z1 z2 v) :
    merge_short (signed_last_nbits z1 8) (signed_last_nbits z2 8)
      (signed_last_nbits v 16) := by
  apply Endian.merge_short_value_eqm
    (signed_last_nbits z1 8) (signed_last_nbits z2 8)
    v (signed_last_nbits v 16)
    (signed_Lastnbits_mod_correct v 16 (by omega))
  exact Endian.merge_short_eqm z1 z2 _ _ v
    (byte_eqm_signed_last_8 z1)
    (byte_eqm_signed_last_8 z2) h

private theorem merge_int_unsigned_cast (z1 z2 z3 z4 v : Int)
    (h : merge_int z1 z2 z3 z4 v) :
    merge_int (unsigned_last_nbits z1 8) (unsigned_last_nbits z2 8)
      (unsigned_last_nbits z3 8) (unsigned_last_nbits z4 8)
      (unsigned_last_nbits v 32) := by
  apply Endian.merge_int_value_eqm
    (unsigned_last_nbits z1 8) (unsigned_last_nbits z2 8)
    (unsigned_last_nbits z3 8) (unsigned_last_nbits z4 8)
    v (unsigned_last_nbits v 32)
    (unsigned_Lastnbits_mod_correct v 32 (by omega))
  exact Endian.merge_int_eqm z1 z2 z3 z4 _ _ _ _ v
    (byte_eqm_unsigned_last_8 z1)
    (byte_eqm_unsigned_last_8 z2)
    (byte_eqm_unsigned_last_8 z3)
    (byte_eqm_unsigned_last_8 z4) h

private theorem merge_int_signed_cast (z1 z2 z3 z4 v : Int)
    (h : merge_int z1 z2 z3 z4 v) :
    merge_int (signed_last_nbits z1 8) (signed_last_nbits z2 8)
      (signed_last_nbits z3 8) (signed_last_nbits z4 8)
      (signed_last_nbits v 32) := by
  apply Endian.merge_int_value_eqm
    (signed_last_nbits z1 8) (signed_last_nbits z2 8)
    (signed_last_nbits z3 8) (signed_last_nbits z4 8)
    v (signed_last_nbits v 32)
    (signed_Lastnbits_mod_correct v 32 (by omega))
  exact Endian.merge_int_eqm z1 z2 z3 z4 _ _ _ _ v
    (byte_eqm_signed_last_8 z1)
    (byte_eqm_signed_last_8 z2)
    (byte_eqm_signed_last_8 z3)
    (byte_eqm_signed_last_8 z4) h

private theorem merge_int64_unsigned_cast (z1 z2 z3 z4 z5 z6 z7 z8 v : Int)
    (h : merge_int64 z1 z2 z3 z4 z5 z6 z7 z8 v) :
    merge_int64 (unsigned_last_nbits z1 8) (unsigned_last_nbits z2 8)
      (unsigned_last_nbits z3 8) (unsigned_last_nbits z4 8)
      (unsigned_last_nbits z5 8) (unsigned_last_nbits z6 8)
      (unsigned_last_nbits z7 8) (unsigned_last_nbits z8 8)
      (unsigned_last_nbits v 64) := by
  apply Endian.merge_int64_value_eqm
    (unsigned_last_nbits z1 8) (unsigned_last_nbits z2 8)
    (unsigned_last_nbits z3 8) (unsigned_last_nbits z4 8)
    (unsigned_last_nbits z5 8) (unsigned_last_nbits z6 8)
    (unsigned_last_nbits z7 8) (unsigned_last_nbits z8 8) v
    (unsigned_last_nbits v 64) (unsigned_Lastnbits_mod_correct v 64 (by omega))
  exact Endian.merge_int64_eqm z1 z2 z3 z4 z5 z6 z7 z8 _ _ _ _ _ _ _ _ v
    (byte_eqm_unsigned_last_8 z1)
    (byte_eqm_unsigned_last_8 z2)
    (byte_eqm_unsigned_last_8 z3)
    (byte_eqm_unsigned_last_8 z4)
    (byte_eqm_unsigned_last_8 z5)
    (byte_eqm_unsigned_last_8 z6)
    (byte_eqm_unsigned_last_8 z7)
    (byte_eqm_unsigned_last_8 z8) h

private theorem merge_int64_signed_cast (z1 z2 z3 z4 z5 z6 z7 z8 v : Int)
    (h : merge_int64 z1 z2 z3 z4 z5 z6 z7 z8 v) :
    merge_int64 (signed_last_nbits z1 8) (signed_last_nbits z2 8)
      (signed_last_nbits z3 8) (signed_last_nbits z4 8)
      (signed_last_nbits z5 8) (signed_last_nbits z6 8)
      (signed_last_nbits z7 8) (signed_last_nbits z8 8)
      (signed_last_nbits v 64) := by
  apply Endian.merge_int64_value_eqm
    (signed_last_nbits z1 8) (signed_last_nbits z2 8)
    (signed_last_nbits z3 8) (signed_last_nbits z4 8)
    (signed_last_nbits z5 8) (signed_last_nbits z6 8)
    (signed_last_nbits z7 8) (signed_last_nbits z8 8) v
    (signed_last_nbits v 64) (signed_Lastnbits_mod_correct v 64 (by omega))
  exact Endian.merge_int64_eqm z1 z2 z3 z4 z5 z6 z7 z8 _ _ _ _ _ _ _ _ v
    (byte_eqm_signed_last_8 z1)
    (byte_eqm_signed_last_8 z2)
    (byte_eqm_signed_last_8 z3)
    (byte_eqm_signed_last_8 z4)
    (byte_eqm_signed_last_8 z5)
    (byte_eqm_signed_last_8 z6)
    (byte_eqm_signed_last_8 z7)
    (byte_eqm_signed_last_8 z8) h

theorem store_char_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_char CRules x v)
      (store_uchar CRules x (unsigned_last_nbits v 8)) := by
  intro state h
  have hr := unsigned_Lastnbits_range v 8 (by omega)
  rw [show Z.pow 2 8 = 256 by decide] at hr
  exact ⟨⟨h.1.1, hr.1, by simpa [Byte.max_unsigned] using (show
    unsigned_last_nbits v 8 <= 255 by omega)⟩,
    store_byte_cast' CRules x v state h.2⟩

theorem store_uchar_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uchar CRules x v)
      (store_char CRules x (signed_last_nbits v 8)) := by
  intro state h
  have hr := signed_Lastnbits_range v 8 (by omega)
  rw [show Z.pow 2 (8 - 1) = 128 by decide] at hr
  exact ⟨⟨h.1.1, by simpa [Byte.max_signed] using (show
    signed_last_nbits v 8 <= 127 by omega), by simpa [Byte.min_signed] using hr.1⟩,
    store_byte_cast CRules x v state h.2⟩

theorem store_short_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_short CRules x v)
      (store_ushort CRules x (unsigned_last_nbits v 16)) := by
  intro state h
  have hr := unsigned_Lastnbits_range v 16 (by omega)
  rw [show Z.pow 2 16 = 65536 by decide] at hr
  exact ⟨⟨h.1.1, hr.1, by omega⟩,
    store_2byte_map CRules (fun z => unsigned_last_nbits z 8) x v
      (unsigned_last_nbits v 16) (fun p z => store_byte_cast' CRules p z)
      (fun z1 z2 => merge_short_unsigned_cast z1 z2 v) state h.2⟩

theorem store_ushort_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_ushort CRules x v)
      (store_short CRules x (signed_last_nbits v 16)) := by
  intro state h
  have hr := signed_Lastnbits_range v 16 (by omega)
  rw [show Z.pow 2 (16 - 1) = 32768 by decide] at hr
  exact ⟨⟨h.1.1, by omega, hr.1⟩,
    store_2byte_map CRules (fun z => signed_last_nbits z 8) x v
      (signed_last_nbits v 16) (fun p z => store_byte_cast CRules p z)
      (fun z1 z2 => merge_short_signed_cast z1 z2 v) state h.2⟩

theorem store_int_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int CRules x v)
      (store_uint CRules x (unsigned_last_nbits v 32)) := by
  intro state h
  have hr := unsigned_Lastnbits_range v 32 (by omega)
  rw [show Z.pow 2 32 = 4294967296 by decide] at hr
  exact ⟨⟨h.1.1, hr.1, by simpa [Int.max_unsigned, Int.modulus] using (show
    unsigned_last_nbits v 32 <= 4294967295 by omega)⟩,
    store_4byte_map CRules (fun z => unsigned_last_nbits z 8) x v
      (unsigned_last_nbits v 32) (fun p z => store_byte_cast' CRules p z)
      (fun z1 z2 z3 z4 => merge_int_unsigned_cast z1 z2 z3 z4 v) state h.2⟩

theorem store_uint_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint CRules x v)
      (store_int CRules x (signed_last_nbits v 32)) := by
  intro state h
  have hr := signed_Lastnbits_range v 32 (by omega)
  rw [show Z.pow 2 (32 - 1) = 2147483648 by decide] at hr
  exact ⟨⟨h.1.1, by simpa [Int.max_signed, Int.half_modulus, Int.modulus] using (show
    signed_last_nbits v 32 <= 2147483647 by omega),
    by simpa [Int.min_signed, Int.half_modulus, Int.modulus] using hr.1⟩,
    store_4byte_map CRules (fun z => signed_last_nbits z 8) x v
      (signed_last_nbits v 32) (fun p z => store_byte_cast CRules p z)
      (fun z1 z2 z3 z4 => merge_int_signed_cast z1 z2 z3 z4 v) state h.2⟩

theorem store_int64_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_int64 CRules x v)
      (store_uint64 CRules x (unsigned_last_nbits v 64)) := by
  intro state h
  have hr := unsigned_Lastnbits_range v 64 (by omega)
  rw [show Z.pow 2 64 = 18446744073709551616 by decide] at hr
  exact ⟨⟨h.1.1, hr.1, by simpa [Int64.max_unsigned, Int64.modulus] using (show
    unsigned_last_nbits v 64 <= 18446744073709551615 by omega)⟩,
    store_8byte_map CRules (fun z => unsigned_last_nbits z 8) x v
      (unsigned_last_nbits v 64) (fun p z => store_byte_cast' CRules p z)
      (fun z1 z2 z3 z4 z5 z6 z7 z8 =>
        merge_int64_unsigned_cast z1 z2 z3 z4 z5 z6 z7 z8 v) state h.2⟩

theorem store_uint64_cast (CRules : SeparationLogicSig) (x v : Int) :
    CRules.derivable1 (store_uint64 CRules x v)
      (store_int64 CRules x (signed_last_nbits v 64)) := by
  intro state h
  have hr := signed_Lastnbits_range v 64 (by omega)
  rw [show Z.pow 2 (64 - 1) = 9223372036854775808 by decide] at hr
  exact ⟨⟨h.1.1, by simpa [Int64.max_signed, Int64.half_modulus, Int64.modulus] using (show
    signed_last_nbits v 64 <= 9223372036854775807 by omega),
    by simpa [Int64.min_signed, Int64.half_modulus, Int64.modulus] using hr.1⟩,
    store_8byte_map CRules (fun z => signed_last_nbits z 8) x v
      (signed_last_nbits v 64) (fun p z => store_byte_cast CRules p z)
      (fun z1 z2 z3 z4 z5 z6 z7 z8 =>
        merge_int64_signed_cast z1 z2 z3 z4 z5 z6 z7 z8 v) state h.2⟩

private theorem valid_int_to_chars (p : Int) (h : isvalidptr_int p) :
    aligned_4 p ∧ isvalidptr_char p ∧ isvalidptr_char (p + 1) ∧
      isvalidptr_char (p + 2) ∧ isvalidptr_char (p + 3) := by
  unfold DerivedPredSig.isvalidptr_int at h
  unfold DerivedPredSig.isvalidptr_char
  rcases h with ⟨hlo, hhi, halign⟩
  exact ⟨halign,
    ⟨hlo, by omega⟩,
    ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩,
    ⟨by omega, hhi⟩⟩

private theorem chars_to_valid_int (p : Int) (halign : aligned_4 p)
    (h0 : isvalidptr_char p) (_h1 : isvalidptr_char (p + 1))
    (_h2 : isvalidptr_char (p + 2)) (h3 : isvalidptr_char (p + 3)) :
    isvalidptr_int p := by
  unfold DerivedPredSig.isvalidptr_char at h0 h3
  unfold DerivedPredSig.isvalidptr_int
  exact ⟨h0.1, h3.2, halign⟩

private theorem emod_signed_repr (z : Int) :
    Byte.signed (Byte.repr z) % (2 : Int) ^ 8 = z % (2 : Int) ^ 8 := by
  have h := Byte.eqm_mod_eq z (Byte.signed (Byte.repr z)) (Byte.eqm_signed_repr z)
  change Int.fmod z 256 = Int.fmod (Byte.signed (Byte.repr z)) 256 at h
  rw [Int.fmod_eq_emod_of_nonneg z (by decide)] at h
  rw [Int.fmod_eq_emod_of_nonneg (Byte.signed (Byte.repr z)) (by decide)] at h
  exact h.symm

private theorem merge_int_signed_repr (z1 z2 z3 z4 v : Int)
    (h : merge_int z1 z2 z3 z4 v) :
    merge_int (Byte.signed (Byte.repr z1)) (Byte.signed (Byte.repr z2))
      (Byte.signed (Byte.repr z3)) (Byte.signed (Byte.repr z4)) v := by
  exact Endian.merge_int_eqm z1 z2 z3 z4 _ _ _ _ v
    (Byte.eqm_signed_repr z1) (Byte.eqm_signed_repr z2)
    (Byte.eqm_signed_repr z3) (Byte.eqm_signed_repr z4) h

private theorem byte_to_signed_char (CRules : SeparationLogicSig)
    (p z : Int) (hvalid : isvalidptr_char p) :
    CRules.derivable1 (store_byte CRules p z)
      (store_char CRules p (Byte.signed (Byte.repr z))) := by
  intro state hstore
  have hr := Byte.signed_range (Byte.repr z)
  exact ⟨⟨hvalid, hr.2, hr.1⟩,
    store_byte_eqm CRules p z (Byte.signed (Byte.repr z))
      (Byte.eqm_signed_repr z) state hstore⟩

private theorem char_to_byte (CRules : SeparationLogicSig) (p z : Int) :
    CRules.derivable1 (store_char CRules p z) (store_byte CRules p z) := by
  intro _ h
  exact h.2

private theorem chars4_to_bytes4 (CRules : SeparationLogicSig)
    (p z1 z2 z3 z4 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_char CRules p z1)
        (CRules.sepcon (store_char CRules (p + 1) z2)
          (CRules.sepcon (store_char CRules (p + 2) z3)
            (store_char CRules (p + 3) z4))))
      (CRules.sepcon (store_byte CRules p z1)
        (CRules.sepcon (store_byte CRules (p + 1) z2)
          (CRules.sepcon (store_byte CRules (p + 2) z3)
            (store_byte CRules (p + 3) z4)))) :=
  CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (char_to_byte CRules p z1)
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (char_to_byte CRules (p + 1) z2)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (char_to_byte CRules (p + 2) z3)
        (char_to_byte CRules (p + 3) z4)))

private theorem chars4_valid (CRules : SeparationLogicSig)
    (p z1 z2 z3 z4 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_char CRules p z1)
        (CRules.sepcon (store_char CRules (p + 1) z2)
          (CRules.sepcon (store_char CRules (p + 2) z3)
            (store_char CRules (p + 3) z4))))
      (CRules.coq_prop
        (isvalidptr_char p ∧ isvalidptr_char (p + 1) ∧
          isvalidptr_char (p + 2) ∧ isvalidptr_char (p + 3))) := by
  intro _ h
  rcases h with ⟨_, _, _, h1, hrest⟩
  rcases hrest with ⟨_, _, _, h2, hrest⟩
  rcases hrest with ⟨_, _, _, h3, h4⟩
  exact ⟨h1.1.1, h2.1.1, h3.1.1, h4.1.1⟩

private theorem bytes4_to_signed_chars4 (CRules : SeparationLogicSig)
    (p z1 z2 z3 z4 : Int) (hvalid : isvalidptr_int p) :
    CRules.derivable1
      (CRules.sepcon (store_byte CRules p z1)
        (CRules.sepcon (store_byte CRules (p + 1) z2)
          (CRules.sepcon (store_byte CRules (p + 2) z3)
            (store_byte CRules (p + 3) z4))))
      (CRules.sepcon (store_char CRules p (Byte.signed (Byte.repr z1)))
        (CRules.sepcon (store_char CRules (p + 1) (Byte.signed (Byte.repr z2)))
          (CRules.sepcon (store_char CRules (p + 2) (Byte.signed (Byte.repr z3)))
            (store_char CRules (p + 3) (Byte.signed (Byte.repr z4)))))) := by
  have hv := valid_int_to_chars p hvalid
  exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (byte_to_signed_char CRules p z1 hv.2.1)
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (byte_to_signed_char CRules (p + 1) z2 hv.2.2.1)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (byte_to_signed_char CRules (p + 2) z3 hv.2.2.2.1)
        (byte_to_signed_char CRules (p + 3) z4 hv.2.2.2.2)))

theorem store_int_store_char (CRules : SeparationLogicSig) (p v : Int) :
    CRules.logic_equiv (store_int CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 =>
        CRules.exp Int fun v3 => CRules.exp Int fun v4 =>
          CRules.andp (CRules.coq_prop (merge_int v1 v2 v3 v4 v))
            (CRules.andp
              (CRules.coq_prop (Int.min_signed <= v ∧ v <= Int.max_signed))
              (CRules.andp (CRules.coq_prop (aligned_4 p))
                (CRules.sepcon (store_char CRules p v1)
                  (CRules.sepcon (store_char CRules (p + 1) v2)
                    (CRules.sepcon (store_char CRules (p + 2) v3)
                      (store_char CRules (p + 3) v4))))))) := by
  constructor
  · intro state h
    rcases h.2 with ⟨z1, z2, z3, z4, hmerge, hbytes⟩
    have hv := valid_int_to_chars p h.1.1
    exact ⟨Byte.signed (Byte.repr z1), Byte.signed (Byte.repr z2),
      Byte.signed (Byte.repr z3), Byte.signed (Byte.repr z4),
      merge_int_signed_repr z1 z2 z3 z4 v hmerge,
      ⟨h.1.2.2, h.1.2.1⟩, hv.1,
      bytes4_to_signed_chars4 CRules p z1 z2 z3 z4 h.1.1 state hbytes⟩
  · intro state h
    rcases h with ⟨z1, z2, z3, z4, hmerge, hrange, halign, hchars⟩
    have hv := chars4_valid CRules p z1 z2 z3 z4 state hchars
    exact ⟨⟨chars_to_valid_int p halign hv.1 hv.2.1 hv.2.2.1 hv.2.2.2,
      hrange.2, hrange.1⟩,
      ⟨z1, z2, z3, z4,
        hmerge,
        chars4_to_bytes4 CRules p z1 z2 z3 z4 state hchars⟩⟩

theorem store_uint_store_char (CRules : SeparationLogicSig) (p v : Int) :
    CRules.logic_equiv (store_uint CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 =>
        CRules.exp Int fun v3 => CRules.exp Int fun v4 =>
          CRules.andp (CRules.coq_prop (merge_int v1 v2 v3 v4 v))
            (CRules.andp (CRules.coq_prop (0 <= v ∧ v <= Int.max_unsigned))
              (CRules.andp (CRules.coq_prop (aligned_4 p))
                (CRules.sepcon (store_char CRules p v1)
                  (CRules.sepcon (store_char CRules (p + 1) v2)
                    (CRules.sepcon (store_char CRules (p + 2) v3)
                      (store_char CRules (p + 3) v4))))))) := by
  constructor
  · intro state h
    rcases h.2 with ⟨z1, z2, z3, z4, hmerge, hbytes⟩
    have hv := valid_int_to_chars p h.1.1
    exact ⟨Byte.signed (Byte.repr z1), Byte.signed (Byte.repr z2),
      Byte.signed (Byte.repr z3), Byte.signed (Byte.repr z4),
      merge_int_signed_repr z1 z2 z3 z4 v hmerge, h.1.2, hv.1,
      bytes4_to_signed_chars4 CRules p z1 z2 z3 z4 h.1.1 state hbytes⟩
  · intro state h
    rcases h with ⟨z1, z2, z3, z4, hmerge, hrange, halign, hchars⟩
    have hv := chars4_valid CRules p z1 z2 z3 z4 state hchars
    exact ⟨⟨chars_to_valid_int p halign hv.1 hv.2.1 hv.2.2.1 hv.2.2.2,
      hrange⟩,
      ⟨z1, z2, z3, z4,
        hmerge,
        chars4_to_bytes4 CRules p z1 z2 z3 z4 state hchars⟩⟩

private theorem bytes4_noninit_to_undef_chars4 (CRules : SeparationLogicSig)
    (p : Int) (hvalid : isvalidptr_int p) :
    CRules.derivable1 (store_4byte_noninit CRules p)
      (CRules.sepcon (undef_store_char CRules p)
        (CRules.sepcon (undef_store_char CRules (p + 1))
          (CRules.sepcon (undef_store_char CRules (p + 2))
            (undef_store_char CRules (p + 3))))) := by
  have hv := valid_int_to_chars p hvalid
  unfold store_4byte_noninit
  exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (by intro _ h; exact ⟨hv.2.1, h⟩)
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (by intro _ h; exact ⟨hv.2.2.1, h⟩)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (by intro _ h; exact ⟨hv.2.2.2.1, h⟩)
        (by intro _ h; exact ⟨hv.2.2.2.2, h⟩)))

private theorem undef_chars4_to_bytes4_noninit (CRules : SeparationLogicSig)
    (p : Int) :
    CRules.derivable1
      (CRules.sepcon (undef_store_char CRules p)
        (CRules.sepcon (undef_store_char CRules (p + 1))
          (CRules.sepcon (undef_store_char CRules (p + 2))
            (undef_store_char CRules (p + 3)))))
      (store_4byte_noninit CRules p) := by
  unfold store_4byte_noninit
  exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (by intro _ h; exact h.2)
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (by intro _ h; exact h.2)
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (by intro _ h; exact h.2)
        (by intro _ h; exact h.2)))

private theorem undef_chars4_valid (CRules : SeparationLogicSig) (p : Int) :
    CRules.derivable1
      (CRules.sepcon (undef_store_char CRules p)
        (CRules.sepcon (undef_store_char CRules (p + 1))
          (CRules.sepcon (undef_store_char CRules (p + 2))
            (undef_store_char CRules (p + 3)))))
      (CRules.coq_prop
        (isvalidptr_char p ∧ isvalidptr_char (p + 1) ∧
          isvalidptr_char (p + 2) ∧ isvalidptr_char (p + 3))) := by
  intro _ h
  rcases h with ⟨_, _, _, h1, hrest⟩
  rcases hrest with ⟨_, _, _, h2, hrest⟩
  rcases hrest with ⟨_, _, _, h3, h4⟩
  exact ⟨h1.1, h2.1, h3.1, h4.1⟩

theorem undef_store_uint_undef_store_char (CRules : SeparationLogicSig) (p : Int) :
    CRules.logic_equiv (undef_store_uint CRules p)
      (CRules.andp (CRules.coq_prop (aligned_4 p))
        (CRules.sepcon (undef_store_char CRules p)
          (CRules.sepcon (undef_store_char CRules (p + 1))
            (CRules.sepcon (undef_store_char CRules (p + 2))
              (undef_store_char CRules (p + 3)))))) := by
  constructor
  · intro state h
    have hv := valid_int_to_chars p h.1
    exact ⟨hv.1, bytes4_noninit_to_undef_chars4 CRules p h.1 state h.2⟩
  · intro state h
    have hv := undef_chars4_valid CRules p state h.2
    exact ⟨chars_to_valid_int p h.1 hv.1 hv.2.1 hv.2.2.1 hv.2.2.2,
      undef_chars4_to_bytes4_noninit CRules p state h.2⟩

theorem undef_store_int_undef_store_char (CRules : SeparationLogicSig) (p : Int) :
    CRules.logic_equiv (undef_store_int CRules p)
      (CRules.andp (CRules.coq_prop (aligned_4 p))
        (CRules.sepcon (undef_store_char CRules p)
          (CRules.sepcon (undef_store_char CRules (p + 1))
            (CRules.sepcon (undef_store_char CRules (p + 2))
              (undef_store_char CRules (p + 3)))))) := by
  simpa [DerivedPredSig.undef_store_int,
    DerivedPredSig.undef_store_uint] using
    undef_store_uint_undef_store_char CRules p

private theorem sepcon8_mono (CRules : SeparationLogicSig)
    {A0 A1 A2 A3 A4 A5 A6 A7 B0 B1 B2 B3 B4 B5 B6 B7 : CRules.expr}
    (h0 : CRules.derivable1 A0 B0) (h1 : CRules.derivable1 A1 B1)
    (h2 : CRules.derivable1 A2 B2) (h3 : CRules.derivable1 A3 B3)
    (h4 : CRules.derivable1 A4 B4) (h5 : CRules.derivable1 A5 B5)
    (h6 : CRules.derivable1 A6 B6) (h7 : CRules.derivable1 A7 B7) :
    CRules.derivable1
      (CRules.sepcon A0 (CRules.sepcon A1 (CRules.sepcon A2
        (CRules.sepcon A3 (CRules.sepcon A4 (CRules.sepcon A5
          (CRules.sepcon A6 A7)))))))
      (CRules.sepcon B0 (CRules.sepcon B1 (CRules.sepcon B2
        (CRules.sepcon B3 (CRules.sepcon B4 (CRules.sepcon B5
          (CRules.sepcon B6 B7))))))) :=
  CRules.toContext.derivable1_sepcon_mono _ _ _ _ h0 <|
    CRules.toContext.derivable1_sepcon_mono _ _ _ _ h1 <|
      CRules.toContext.derivable1_sepcon_mono _ _ _ _ h2 <|
        CRules.toContext.derivable1_sepcon_mono _ _ _ _ h3 <|
          CRules.toContext.derivable1_sepcon_mono _ _ _ _ h4 <|
            CRules.toContext.derivable1_sepcon_mono _ _ _ _ h5 <|
              CRules.toContext.derivable1_sepcon_mono _ _ _ _ h6 h7

private theorem int64_valid_chars (p : Int) (h : isvalidptr_int64 p) :
    aligned_4 p ∧ isvalidptr_char p ∧ isvalidptr_char (p + 1) ∧
      isvalidptr_char (p + 2) ∧ isvalidptr_char (p + 3) ∧
      isvalidptr_char (p + 4) ∧ isvalidptr_char (p + 5) ∧
      isvalidptr_char (p + 6) ∧ isvalidptr_char (p + 7) := by
  unfold DerivedPredSig.isvalidptr_int64 at h
  unfold DerivedPredSig.isvalidptr_char
  rcases h with ⟨hlo, hhi, halign⟩
  exact ⟨halign, ⟨hlo, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, hhi⟩⟩

private theorem int64_valid_of_char_ends (p : Int) (halign : aligned_4 p)
    (hfirst : isvalidptr_char p) (hlast : isvalidptr_char (p + 7)) :
    isvalidptr_int64 p := by
  unfold DerivedPredSig.isvalidptr_char at hfirst hlast
  unfold DerivedPredSig.isvalidptr_int64
  exact ⟨hfirst.1, by omega, halign⟩

private theorem byte_eqm_unsigned_repr (z : Int) :
    Byte.eqm z (Byte.unsigned (Byte.repr z)) := by
  change Zbits.eqmod Byte.modulus z (Z.modulo z Byte.modulus)
  exact Zbits.eqmod_mod Byte.modulus z

private theorem byte_to_unsigned_char (CRules : SeparationLogicSig)
    (p z : Int) (hvalid : isvalidptr_char p) :
    CRules.derivable1 (store_byte CRules p z)
      (store_uchar CRules p (Byte.unsigned (Byte.repr z))) := by
  intro state hstore
  have hr := Byte.unsigned_range (Byte.repr z)
  have hr' : 0 <= Byte.unsigned (Byte.repr z) ∧
      Byte.unsigned (Byte.repr z) <= Byte.max_unsigned := by
    constructor
    · exact hr.1
    · have hlt : Byte.unsigned (Byte.repr z) < 256 := by
        simpa [Byte.modulus, Byte.wordsize, Wordsize_8.wordsize] using hr.2
      change Byte.unsigned (Byte.repr z) <= 255
      omega
  exact ⟨⟨hvalid, hr'.1, hr'.2⟩,
    store_byte_eqm CRules p z _ (byte_eqm_unsigned_repr z) state hstore⟩

private theorem uchar_to_byte (CRules : SeparationLogicSig) (p z : Int) :
    CRules.derivable1 (store_uchar CRules p z) (store_byte CRules p z) := by
  intro _ h
  exact h.2

private theorem signed_chars8_valid_ends (CRules : SeparationLogicSig)
    (p z1 z2 z3 z4 z5 z6 z7 z8 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_char CRules p z1)
        (CRules.sepcon (store_char CRules (p + 1) z2)
          (CRules.sepcon (store_char CRules (p + 2) z3)
            (CRules.sepcon (store_char CRules (p + 3) z4)
              (CRules.sepcon (store_char CRules (p + 4) z5)
                (CRules.sepcon (store_char CRules (p + 5) z6)
                  (CRules.sepcon (store_char CRules (p + 6) z7)
                    (store_char CRules (p + 7) z8))))))))
      (CRules.coq_prop (isvalidptr_char p ∧ isvalidptr_char (p + 7))) := by
  intro _ h
  rcases h with ⟨_, _, _, h1, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h8⟩
  exact ⟨h1.1.1, h8.1.1⟩

private theorem unsigned_chars8_valid_ends (CRules : SeparationLogicSig)
    (p z1 z2 z3 z4 z5 z6 z7 z8 : Int) :
    CRules.derivable1
      (CRules.sepcon (store_uchar CRules p z1)
        (CRules.sepcon (store_uchar CRules (p + 1) z2)
          (CRules.sepcon (store_uchar CRules (p + 2) z3)
            (CRules.sepcon (store_uchar CRules (p + 3) z4)
              (CRules.sepcon (store_uchar CRules (p + 4) z5)
                (CRules.sepcon (store_uchar CRules (p + 5) z6)
                  (CRules.sepcon (store_uchar CRules (p + 6) z7)
                    (store_uchar CRules (p + 7) z8))))))))
      (CRules.coq_prop (isvalidptr_char p ∧ isvalidptr_char (p + 7))) := by
  intro _ h
  rcases h with ⟨_, _, _, h1, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h⟩
  rcases h with ⟨_, _, _, _, h8⟩
  exact ⟨h1.1.1, h8.1.1⟩

private theorem store_int64_store_char_core (CRules : SeparationLogicSig)
    (p v : Int) (Range : Prop) (hrange : Range) (hvalid : isvalidptr_int64 p) :
    CRules.derivable1 (store_8byte CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 => CRules.exp Int fun v3 =>
        CRules.exp Int fun v4 => CRules.exp Int fun v5 => CRules.exp Int fun v6 =>
        CRules.exp Int fun v7 => CRules.exp Int fun v8 =>
          CRules.andp (CRules.coq_prop (merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v))
            (CRules.andp (CRules.coq_prop Range)
              (CRules.andp (CRules.coq_prop (aligned_4 p))
                (CRules.sepcon (store_char CRules p v1)
                  (CRules.sepcon (store_char CRules (p + 1) v2)
                    (CRules.sepcon (store_char CRules (p + 2) v3)
                      (CRules.sepcon (store_char CRules (p + 3) v4)
                        (CRules.sepcon (store_char CRules (p + 4) v5)
                          (CRules.sepcon (store_char CRules (p + 5) v6)
                            (CRules.sepcon (store_char CRules (p + 6) v7)
                              (store_char CRules (p + 7) v8))))))))))) := by
  intro state h
  rcases h with ⟨z1, z2, z3, z4, z5, z6, z7, z8, hm, hs⟩
  have hv := int64_valid_chars p hvalid
  let s1 := Byte.signed (Byte.repr z1); let s2 := Byte.signed (Byte.repr z2)
  let s3 := Byte.signed (Byte.repr z3); let s4 := Byte.signed (Byte.repr z4)
  let s5 := Byte.signed (Byte.repr z5); let s6 := Byte.signed (Byte.repr z6)
  let s7 := Byte.signed (Byte.repr z7); let s8 := Byte.signed (Byte.repr z8)
  refine ⟨s1, s2, s3, s4, s5, s6, s7, s8, ?_, hrange, hv.1, ?_⟩
  · exact Endian.merge_int64_eqm z1 z2 z3 z4 z5 z6 z7 z8
      s1 s2 s3 s4 s5 s6 s7 s8 v
      (Byte.eqm_signed_repr z1) (Byte.eqm_signed_repr z2)
      (Byte.eqm_signed_repr z3) (Byte.eqm_signed_repr z4)
      (Byte.eqm_signed_repr z5) (Byte.eqm_signed_repr z6)
      (Byte.eqm_signed_repr z7) (Byte.eqm_signed_repr z8) hm
  · exact sepcon8_mono CRules
      (byte_to_signed_char CRules p z1 hv.2.1)
      (byte_to_signed_char CRules (p + 1) z2 hv.2.2.1)
      (byte_to_signed_char CRules (p + 2) z3 hv.2.2.2.1)
      (byte_to_signed_char CRules (p + 3) z4 hv.2.2.2.2.1)
      (byte_to_signed_char CRules (p + 4) z5 hv.2.2.2.2.2.1)
      (byte_to_signed_char CRules (p + 5) z6 hv.2.2.2.2.2.2.1)
      (byte_to_signed_char CRules (p + 6) z7 hv.2.2.2.2.2.2.2.1)
      (byte_to_signed_char CRules (p + 7) z8 hv.2.2.2.2.2.2.2.2) state hs

private theorem store_int64_store_uchar_core (CRules : SeparationLogicSig)
    (p v : Int) (Range : Prop) (hrange : Range) (hvalid : isvalidptr_int64 p) :
    CRules.derivable1 (store_8byte CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 => CRules.exp Int fun v3 =>
        CRules.exp Int fun v4 => CRules.exp Int fun v5 => CRules.exp Int fun v6 =>
        CRules.exp Int fun v7 => CRules.exp Int fun v8 =>
          CRules.andp (CRules.coq_prop (merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v))
            (CRules.andp (CRules.coq_prop Range)
              (CRules.andp (CRules.coq_prop (aligned_4 p))
                (CRules.sepcon (store_uchar CRules p v1)
                  (CRules.sepcon (store_uchar CRules (p + 1) v2)
                    (CRules.sepcon (store_uchar CRules (p + 2) v3)
                      (CRules.sepcon (store_uchar CRules (p + 3) v4)
                        (CRules.sepcon (store_uchar CRules (p + 4) v5)
                          (CRules.sepcon (store_uchar CRules (p + 5) v6)
                            (CRules.sepcon (store_uchar CRules (p + 6) v7)
                              (store_uchar CRules (p + 7) v8))))))))))) := by
  intro state h
  rcases h with ⟨z1, z2, z3, z4, z5, z6, z7, z8, hm, hs⟩
  have hv := int64_valid_chars p hvalid
  let u1 := Byte.unsigned (Byte.repr z1); let u2 := Byte.unsigned (Byte.repr z2)
  let u3 := Byte.unsigned (Byte.repr z3); let u4 := Byte.unsigned (Byte.repr z4)
  let u5 := Byte.unsigned (Byte.repr z5); let u6 := Byte.unsigned (Byte.repr z6)
  let u7 := Byte.unsigned (Byte.repr z7); let u8 := Byte.unsigned (Byte.repr z8)
  refine ⟨u1, u2, u3, u4, u5, u6, u7, u8, ?_, hrange, hv.1, ?_⟩
  · exact Endian.merge_int64_eqm z1 z2 z3 z4 z5 z6 z7 z8
      u1 u2 u3 u4 u5 u6 u7 u8 v
      (byte_eqm_unsigned_repr z1) (byte_eqm_unsigned_repr z2)
      (byte_eqm_unsigned_repr z3) (byte_eqm_unsigned_repr z4)
      (byte_eqm_unsigned_repr z5) (byte_eqm_unsigned_repr z6)
      (byte_eqm_unsigned_repr z7) (byte_eqm_unsigned_repr z8) hm
  · exact sepcon8_mono CRules
      (byte_to_unsigned_char CRules p z1 hv.2.1)
      (byte_to_unsigned_char CRules (p + 1) z2 hv.2.2.1)
      (byte_to_unsigned_char CRules (p + 2) z3 hv.2.2.2.1)
      (byte_to_unsigned_char CRules (p + 3) z4 hv.2.2.2.2.1)
      (byte_to_unsigned_char CRules (p + 4) z5 hv.2.2.2.2.2.1)
      (byte_to_unsigned_char CRules (p + 5) z6 hv.2.2.2.2.2.2.1)
      (byte_to_unsigned_char CRules (p + 6) z7 hv.2.2.2.2.2.2.2.1)
      (byte_to_unsigned_char CRules (p + 7) z8 hv.2.2.2.2.2.2.2.2) state hs

theorem store_int64_store_char (CRules : SeparationLogicSig) (p v : Int) :
    CRules.logic_equiv (store_int64 CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 => CRules.exp Int fun v3 =>
        CRules.exp Int fun v4 => CRules.exp Int fun v5 => CRules.exp Int fun v6 =>
        CRules.exp Int fun v7 => CRules.exp Int fun v8 =>
          CRules.andp (CRules.coq_prop (merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v))
            (CRules.andp
              (CRules.coq_prop (Int64.min_signed <= v ∧ v <= Int64.max_signed))
              (CRules.andp (CRules.coq_prop (aligned_4 p))
                (CRules.sepcon (store_char CRules p v1)
                  (CRules.sepcon (store_char CRules (p + 1) v2)
                    (CRules.sepcon (store_char CRules (p + 2) v3)
                      (CRules.sepcon (store_char CRules (p + 3) v4)
                        (CRules.sepcon (store_char CRules (p + 4) v5)
                          (CRules.sepcon (store_char CRules (p + 5) v6)
                            (CRules.sepcon (store_char CRules (p + 6) v7)
                              (store_char CRules (p + 7) v8))))))))))) := by
  constructor
  · intro state h
    exact store_int64_store_char_core CRules p v _
      ⟨h.1.2.2, h.1.2.1⟩ h.1.1 state h.2
  · intro state h
    rcases h with ⟨v1, v2, v3, v4, v5, v6, v7, v8,
      hmerge, hrange, halign, hchars⟩
    have hends := signed_chars8_valid_ends CRules p
      v1 v2 v3 v4 v5 v6 v7 v8 state hchars
    have hvalid := int64_valid_of_char_ends p halign hends.1 hends.2
    refine ⟨⟨hvalid, hrange.2, hrange.1⟩,
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, hmerge, ?_⟩⟩
    exact sepcon8_mono CRules
      (char_to_byte CRules p v1)
      (char_to_byte CRules (p + 1) v2)
      (char_to_byte CRules (p + 2) v3)
      (char_to_byte CRules (p + 3) v4)
      (char_to_byte CRules (p + 4) v5)
      (char_to_byte CRules (p + 5) v6)
      (char_to_byte CRules (p + 6) v7)
      (char_to_byte CRules (p + 7) v8) state hchars

theorem store_uint64_store_uchar (CRules : SeparationLogicSig) (p v : Int) :
    CRules.logic_equiv (store_uint64 CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 => CRules.exp Int fun v3 =>
        CRules.exp Int fun v4 => CRules.exp Int fun v5 => CRules.exp Int fun v6 =>
        CRules.exp Int fun v7 => CRules.exp Int fun v8 =>
          CRules.andp (CRules.coq_prop (merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v))
            (CRules.andp (CRules.coq_prop (0 <= v ∧ v <= Int64.max_unsigned))
              (CRules.andp (CRules.coq_prop (aligned_4 p))
                (CRules.sepcon (store_uchar CRules p v1)
                  (CRules.sepcon (store_uchar CRules (p + 1) v2)
                    (CRules.sepcon (store_uchar CRules (p + 2) v3)
                      (CRules.sepcon (store_uchar CRules (p + 3) v4)
                        (CRules.sepcon (store_uchar CRules (p + 4) v5)
                          (CRules.sepcon (store_uchar CRules (p + 5) v6)
                            (CRules.sepcon (store_uchar CRules (p + 6) v7)
                              (store_uchar CRules (p + 7) v8))))))))))) := by
  constructor
  · intro state h
    exact store_int64_store_uchar_core CRules p v _ h.1.2 h.1.1 state h.2
  · intro state h
    rcases h with ⟨v1, v2, v3, v4, v5, v6, v7, v8,
      hmerge, hrange, halign, hchars⟩
    have hends := unsigned_chars8_valid_ends CRules p
      v1 v2 v3 v4 v5 v6 v7 v8 state hchars
    have hvalid := int64_valid_of_char_ends p halign hends.1 hends.2
    refine ⟨⟨hvalid, hrange⟩,
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, hmerge, ?_⟩⟩
    exact sepcon8_mono CRules
      (uchar_to_byte CRules p v1)
      (uchar_to_byte CRules (p + 1) v2)
      (uchar_to_byte CRules (p + 2) v3)
      (uchar_to_byte CRules (p + 3) v4)
      (uchar_to_byte CRules (p + 4) v5)
      (uchar_to_byte CRules (p + 5) v6)
      (uchar_to_byte CRules (p + 6) v7)
      (uchar_to_byte CRules (p + 7) v8) state hchars

theorem store_int64_store_uchar (CRules : SeparationLogicSig) (p v : Int) :
    CRules.logic_equiv (store_int64 CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 => CRules.exp Int fun v3 =>
        CRules.exp Int fun v4 => CRules.exp Int fun v5 => CRules.exp Int fun v6 =>
        CRules.exp Int fun v7 => CRules.exp Int fun v8 =>
          CRules.andp (CRules.coq_prop (merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v))
            (CRules.andp
              (CRules.coq_prop (Int64.min_signed <= v ∧ v <= Int64.max_signed))
              (CRules.andp (CRules.coq_prop (aligned_4 p))
                (CRules.sepcon (store_uchar CRules p v1)
                  (CRules.sepcon (store_uchar CRules (p + 1) v2)
                    (CRules.sepcon (store_uchar CRules (p + 2) v3)
                      (CRules.sepcon (store_uchar CRules (p + 3) v4)
                        (CRules.sepcon (store_uchar CRules (p + 4) v5)
                          (CRules.sepcon (store_uchar CRules (p + 5) v6)
                            (CRules.sepcon (store_uchar CRules (p + 6) v7)
                              (store_uchar CRules (p + 7) v8))))))))))) := by
  constructor
  · intro state h
    exact store_int64_store_uchar_core CRules p v _
      ⟨h.1.2.2, h.1.2.1⟩ h.1.1 state h.2
  · intro state h
    rcases h with ⟨v1, v2, v3, v4, v5, v6, v7, v8,
      hmerge, hrange, halign, hchars⟩
    have hends := unsigned_chars8_valid_ends CRules p
      v1 v2 v3 v4 v5 v6 v7 v8 state hchars
    have hvalid := int64_valid_of_char_ends p halign hends.1 hends.2
    refine ⟨⟨hvalid, hrange.2, hrange.1⟩,
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, hmerge, ?_⟩⟩
    exact sepcon8_mono CRules
      (uchar_to_byte CRules p v1)
      (uchar_to_byte CRules (p + 1) v2)
      (uchar_to_byte CRules (p + 2) v3)
      (uchar_to_byte CRules (p + 3) v4)
      (uchar_to_byte CRules (p + 4) v5)
      (uchar_to_byte CRules (p + 5) v6)
      (uchar_to_byte CRules (p + 6) v7)
      (uchar_to_byte CRules (p + 7) v8) state hchars

theorem store_uint64_store_char (CRules : SeparationLogicSig) (p v : Int) :
    CRules.logic_equiv (store_uint64 CRules p v)
      (CRules.exp Int fun v1 => CRules.exp Int fun v2 => CRules.exp Int fun v3 =>
        CRules.exp Int fun v4 => CRules.exp Int fun v5 => CRules.exp Int fun v6 =>
        CRules.exp Int fun v7 => CRules.exp Int fun v8 =>
          CRules.andp (CRules.coq_prop (merge_int64 v1 v2 v3 v4 v5 v6 v7 v8 v))
            (CRules.andp (CRules.coq_prop (0 <= v ∧ v <= Int64.max_unsigned))
              (CRules.andp (CRules.coq_prop (aligned_4 p))
                (CRules.sepcon (store_char CRules p v1)
                  (CRules.sepcon (store_char CRules (p + 1) v2)
                    (CRules.sepcon (store_char CRules (p + 2) v3)
                      (CRules.sepcon (store_char CRules (p + 3) v4)
                        (CRules.sepcon (store_char CRules (p + 4) v5)
                          (CRules.sepcon (store_char CRules (p + 5) v6)
                            (CRules.sepcon (store_char CRules (p + 6) v7)
                              (store_char CRules (p + 7) v8))))))))))) := by
  constructor
  · intro state h
    exact store_int64_store_char_core CRules p v _ h.1.2 h.1.1 state h.2
  · intro state h
    rcases h with ⟨v1, v2, v3, v4, v5, v6, v7, v8,
      hmerge, hrange, halign, hchars⟩
    have hends := signed_chars8_valid_ends CRules p
      v1 v2 v3 v4 v5 v6 v7 v8 state hchars
    have hvalid := int64_valid_of_char_ends p halign hends.1 hends.2
    refine ⟨⟨hvalid, hrange⟩,
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, hmerge, ?_⟩⟩
    exact sepcon8_mono CRules
      (char_to_byte CRules p v1)
      (char_to_byte CRules (p + 1) v2)
      (char_to_byte CRules (p + 2) v3)
      (char_to_byte CRules (p + 3) v4)
      (char_to_byte CRules (p + 4) v5)
      (char_to_byte CRules (p + 5) v6)
      (char_to_byte CRules (p + 6) v7)
      (char_to_byte CRules (p + 7) v8) state hchars

end Canonical

end SimpleC.SL.StoreAux.StoreLibSig
