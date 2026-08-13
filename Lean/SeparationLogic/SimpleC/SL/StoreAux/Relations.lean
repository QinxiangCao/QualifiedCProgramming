import SimpleC.SL.StoreAux.Generic

namespace SimpleC.SL.StoreAux.StoreLibSig

open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.IntLib
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

theorem store_byte_store_byte_noinit (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_byte CRules p v) (store_byte_noninit CRules p) := by
  intro state h
  exact CRules.mstore_mstore_noninit p v state h

theorem store_2byte_store_2byte_noinit (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_2byte CRules p v) (store_2byte_noninit CRules p) := by
  unfold store_2byte store_2byte_noninit
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
  unfold store_4byte store_4byte_noninit
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
  unfold store_8byte store_8byte_noninit
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

theorem store_ptr_undef_store_ptr (CRules : SeparationLogicSig) (p v : Int) :
    CRules.derivable1 (store_ptr CRules p v) (undef_store_ptr CRules p) := by
  intro state h
  exact ⟨h.1.1, store_4byte_store_4byte_noinit CRules p v state h.2⟩

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
  | FET_ushort => exact store_ushort_undef_store_ushort CRules x v
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
  have herase :
      CRules.derivable1 (undef_store_ptr CRules x) (store_4byte_noninit CRules x) := by
    intro _ h
    exact h.2
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _ herase herase)
    (dup_store_4bytes_noninit CRules x)

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
  unfold store_2byte
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
  unfold store_4byte
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
  unfold store_8byte
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
  · exact dump_spatial_left CRules _ _ (hmerge z1 z2 z3 z4 z5 z6 z7 z8 hm)

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
  unfold merge_short at h ⊢
  rw [emod_unsigned_last_nbits v 16 ((2 : Int) ^ 16) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z1 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z2 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  exact h

private theorem merge_short_signed_cast (z1 z2 v : Int)
    (h : merge_short z1 z2 v) :
    merge_short (signed_last_nbits z1 8) (signed_last_nbits z2 8)
      (signed_last_nbits v 16) := by
  unfold merge_short at h ⊢
  rw [emod_signed_last_nbits v 16 ((2 : Int) ^ 16) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z1 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z2 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  exact h

private theorem merge_int_unsigned_cast (z1 z2 z3 z4 v : Int)
    (h : merge_int z1 z2 z3 z4 v) :
    merge_int (unsigned_last_nbits z1 8) (unsigned_last_nbits z2 8)
      (unsigned_last_nbits z3 8) (unsigned_last_nbits z4 8)
      (unsigned_last_nbits v 32) := by
  unfold merge_int at h ⊢
  rw [emod_unsigned_last_nbits v 32 ((2 : Int) ^ 32) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z1 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z2 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z3 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z4 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  exact h

private theorem merge_int_signed_cast (z1 z2 z3 z4 v : Int)
    (h : merge_int z1 z2 z3 z4 v) :
    merge_int (signed_last_nbits z1 8) (signed_last_nbits z2 8)
      (signed_last_nbits z3 8) (signed_last_nbits z4 8)
      (signed_last_nbits v 32) := by
  unfold merge_int at h ⊢
  rw [emod_signed_last_nbits v 32 ((2 : Int) ^ 32) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z1 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z2 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z3 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z4 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  exact h

private theorem merge_int64_unsigned_cast (z1 z2 z3 z4 z5 z6 z7 z8 v : Int)
    (h : merge_int64 z1 z2 z3 z4 z5 z6 z7 z8 v) :
    merge_int64 (unsigned_last_nbits z1 8) (unsigned_last_nbits z2 8)
      (unsigned_last_nbits z3 8) (unsigned_last_nbits z4 8)
      (unsigned_last_nbits z5 8) (unsigned_last_nbits z6 8)
      (unsigned_last_nbits z7 8) (unsigned_last_nbits z8 8)
      (unsigned_last_nbits v 64) := by
  unfold merge_int64 at h ⊢
  rw [emod_unsigned_last_nbits v 64 ((2 : Int) ^ 64) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z1 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z2 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z3 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z4 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z5 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z6 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z7 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_unsigned_last_nbits z8 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  exact h

private theorem merge_int64_signed_cast (z1 z2 z3 z4 z5 z6 z7 z8 v : Int)
    (h : merge_int64 z1 z2 z3 z4 z5 z6 z7 z8 v) :
    merge_int64 (signed_last_nbits z1 8) (signed_last_nbits z2 8)
      (signed_last_nbits z3 8) (signed_last_nbits z4 8)
      (signed_last_nbits z5 8) (signed_last_nbits z6 8)
      (signed_last_nbits z7 8) (signed_last_nbits z8 8)
      (signed_last_nbits v 64) := by
  unfold merge_int64 at h ⊢
  rw [emod_signed_last_nbits v 64 ((2 : Int) ^ 64) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z1 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z2 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z3 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z4 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z5 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z6 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z7 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  rw [emod_signed_last_nbits z8 8 ((2 : Int) ^ 8) (by omega) rfl (by decide)]
  exact h

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
  unfold isvalidptr_int at h
  unfold isvalidptr_char
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
  unfold isvalidptr_char at h0 h3
  unfold isvalidptr_int
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
  unfold merge_int at h ⊢
  rw [emod_signed_repr z1, emod_signed_repr z2,
    emod_signed_repr z3, emod_signed_repr z4]
  exact h

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
      ⟨z1, z2, z3, z4, hmerge,
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
      ⟨z1, z2, z3, z4, hmerge,
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
  simpa [undef_store_int, undef_store_uint] using
    undef_store_uint_undef_store_char CRules p

end SimpleC.SL.StoreAux.StoreLibSig
