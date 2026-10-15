import SimpleC.SL.StoreAux.Core

namespace SimpleC.SL.StoreAux.StoreLibSig

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CArch
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

private theorem sepcon_right_mono [SacContext]
    (P : SacContext.rules.expr) {Q R : SacContext.rules.expr}
    (h : SacContext.rules.derivable1 Q R) :
    SacContext.rules.derivable1
      (SacContext.rules.sepcon P Q) (SacContext.rules.sepcon P R) :=
  SacContext.rules.toContext.derivable1_sepcon_mono P P Q R
    (SacContext.rules.toContext.derivable1_refl P) h

private theorem store_byte_equiv_store_n_bytes_Z_proof [SacContext]
    (Arch : CArchSig) (Endian : CEndianSig) (a v : Int) :
    SacContext.rules.logic_equiv
      (store_byte SacContext.rules a v)
      (store_n_bytes_Z Arch Endian SacContext.rules a 1 v) := by
  constructor
  · Exists (vector_cons v #v[])
    simp only [store_n_bytes, vector_head_cons]
    apply split_pure_and_spatial_goals
    · exact SacContext.rules.toContext.derivable1_sepcon_emp_r _
    · apply dump_spatial_left
      exact (Endian.merge_byte_equiv_merge_n_bytes v v).mp (Byte.eqm_refl v)
  · Intros bytes
    rename_i hmerge
    rw [← vector_cons_eta bytes] at hmerge ⊢
    simp only [store_n_bytes, vector_head_cons] at ⊢
    exact SacContext.rules.toContext.derivable1_trans _ _ _
      (SacContext.rules.toContext.derivable1_sepcon_emp_l _)
      (store_byte_eqm SacContext.rules _ _ _ <|
        (Endian.merge_byte_equiv_merge_n_bytes _ _).mpr hmerge)

theorem store_byte_equiv_store_n_bytes_Z (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (a v : Int) :
    CRules.logic_equiv
      (store_byte CRules a v)
      (store_n_bytes_Z Arch Endian CRules a 1 v) := by
  letI : SacContext := ⟨CRules⟩
  exact store_byte_equiv_store_n_bytes_Z_proof Arch Endian a v

private theorem store_2byte_equiv_store_n_bytes_Z_proof [SacContext]
    (Arch : CArchSig) (Endian : CEndianSig) (a v : Int) :
    SacContext.rules.logic_equiv
      (store_2byte Endian SacContext.rules a v)
      (store_n_bytes_Z Arch Endian SacContext.rules a 2 v) := by
  constructor
  · Intros z1 z2
    rename_i hmerge
    Exists (vector_cons z1 (vector_cons z2 #v[]))
    simp only [store_n_bytes, vector_head_cons, vector_tail_cons]
    apply split_pure_and_spatial_goals
    · exact sepcon_right_mono (store_byte SacContext.rules a z1)
        (SacContext.rules.toContext.derivable1_sepcon_emp_r _)
    · apply dump_spatial_left
      exact (merge_short_equiv_merge_n_bytes Endian z1 z2 v).mp hmerge
  · Intros bytes
    rename_i hmerge
    rw [← vector_cons_eta bytes] at hmerge ⊢
    rw [← vector_cons_eta (vector_tail bytes)] at hmerge ⊢
    simp only [store_n_bytes, vector_head_cons, vector_tail_cons] at ⊢
    refine Automation.exp_right_rule (CRules := SacContext.rules) (vector_head bytes) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail bytes)) ?_
    apply split_pure_and_spatial_goals
    · exact sepcon_right_mono
        (store_byte SacContext.rules a (vector_head bytes))
        (SacContext.rules.toContext.derivable1_sepcon_emp_l _)
    · apply dump_spatial_left
      exact (merge_short_equiv_merge_n_bytes Endian
        (vector_head bytes) (vector_head (vector_tail bytes)) v).mpr hmerge

theorem store_2byte_equiv_store_n_bytes_Z (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (a v : Int) :
    CRules.logic_equiv
      (store_2byte Endian CRules a v)
      (store_n_bytes_Z Arch Endian CRules a 2 v) := by
  letI : SacContext := ⟨CRules⟩
  exact store_2byte_equiv_store_n_bytes_Z_proof Arch Endian a v

set_option maxHeartbeats 1000000 in
private theorem store_4byte_equiv_store_n_bytes_Z_proof [SacContext]
    (Arch : CArchSig) (Endian : CEndianSig) (a v : Int) :
    SacContext.rules.logic_equiv
      (store_4byte Endian SacContext.rules a v)
      (store_n_bytes_Z Arch Endian SacContext.rules a 4 v) := by
  constructor
  · Intros z1 z2 z3 z4
    rename_i hmerge
    Exists (vector_cons z1 (vector_cons z2 (vector_cons z3 (vector_cons z4 #v[]))))
    simp only [store_n_bytes, vector_head_cons, vector_tail_cons, Int.add_assoc]
    apply split_pure_and_spatial_goals
    · exact sepcon_right_mono (store_byte SacContext.rules a z1) <|
        sepcon_right_mono (store_byte SacContext.rules (a + 1) z2) <|
          sepcon_right_mono (store_byte SacContext.rules (a + 2) z3) <|
            SacContext.rules.toContext.derivable1_sepcon_emp_r _
    · apply dump_spatial_left
      exact (merge_int_equiv_merge_n_bytes Endian z1 z2 z3 z4 v).mp hmerge
  · Intros bytes
    rename_i hmerge
    rw [← vector_cons_eta bytes] at hmerge ⊢
    rw [← vector_cons_eta (vector_tail bytes)] at hmerge ⊢
    rw [← vector_cons_eta (vector_tail (vector_tail bytes))] at hmerge ⊢
    rw [← vector_cons_eta (vector_tail (vector_tail (vector_tail bytes)))] at hmerge ⊢
    simp only [store_n_bytes, vector_head_cons, vector_tail_cons, Int.add_assoc] at ⊢
    refine Automation.exp_right_rule (CRules := SacContext.rules) (vector_head bytes) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail bytes)) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail (vector_tail bytes))) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail (vector_tail (vector_tail bytes)))) ?_
    apply split_pure_and_spatial_goals
    · exact sepcon_right_mono
        (store_byte SacContext.rules a (vector_head bytes)) <|
        sepcon_right_mono
          (store_byte SacContext.rules (a + 1) (vector_head (vector_tail bytes))) <|
          sepcon_right_mono
            (store_byte SacContext.rules (a + 2)
              (vector_head (vector_tail (vector_tail bytes)))) <|
            SacContext.rules.toContext.derivable1_sepcon_emp_l _
    · apply dump_spatial_left
      exact (merge_int_equiv_merge_n_bytes Endian
        (vector_head bytes) (vector_head (vector_tail bytes))
        (vector_head (vector_tail (vector_tail bytes)))
        (vector_head (vector_tail (vector_tail (vector_tail bytes)))) v).mpr hmerge

theorem store_4byte_equiv_store_n_bytes_Z (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (a v : Int) :
    CRules.logic_equiv
      (store_4byte Endian CRules a v)
      (store_n_bytes_Z Arch Endian CRules a 4 v) := by
  letI : SacContext := ⟨CRules⟩
  exact store_4byte_equiv_store_n_bytes_Z_proof Arch Endian a v

private theorem vector8_eta (bytes : Vector Int 8) :
    bytes = DerivedPredSig.vec8 bytes[0] bytes[1] bytes[2] bytes[3]
      bytes[4] bytes[5] bytes[6] bytes[7] := by
  apply Vector.ext
  intro i hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h <;> subst i <;> rfl

set_option maxHeartbeats 2000000 in
private theorem store_8byte_equiv_store_n_bytes_Z_proof [SacContext]
    (Arch : CArchSig) (Endian : CEndianSig) (a v : Int) :
    SacContext.rules.logic_equiv
      (store_8byte Endian SacContext.rules a v)
      (store_n_bytes_Z Arch Endian SacContext.rules a 8 v) := by
  constructor
  · intro state h
    rcases h with ⟨z1, z2, z3, z4, z5, z6, z7, z8, hmerge, hstores⟩
    let bytes := DerivedPredSig.vec8 z1 z2 z3 z4 z5 z6 z7 z8
    refine ⟨bytes, ?_, ?_⟩
    · exact (merge_int64_equiv_merge_n_bytes Endian
        z1 z2 z3 z4 z5 z6 z7 z8 v).mp hmerge
    · have hspatial := sepcon_right_mono (store_byte SacContext.rules a z1) <|
        sepcon_right_mono (store_byte SacContext.rules (a + 1) z2) <|
          sepcon_right_mono (store_byte SacContext.rules (a + 2) z3) <|
            sepcon_right_mono (store_byte SacContext.rules (a + 3) z4) <|
              sepcon_right_mono (store_byte SacContext.rules (a + 4) z5) <|
                sepcon_right_mono (store_byte SacContext.rules (a + 5) z6) <|
                  sepcon_right_mono (store_byte SacContext.rules (a + 6) z7) <|
                    SacContext.rules.toContext.derivable1_sepcon_emp_r
                      (store_byte SacContext.rules (a + 7) z8)
      simpa only [bytes, store_n_bytes, DerivedPredSig.vec8,
        SimpleC.SL.CArch.vector_head, SimpleC.SL.CArch.vector_tail,
        Int.add_assoc] using hspatial state hstores
  · intro state h
    rcases h with ⟨bytes, hmerge, hstores⟩
    have heta := vector8_eta bytes
    rw [heta] at hmerge hstores
    let z1 := bytes[0]
    let z2 := bytes[1]
    let z3 := bytes[2]
    let z4 := bytes[3]
    let z5 := bytes[4]
    let z6 := bytes[5]
    let z7 := bytes[6]
    let z8 := bytes[7]
    refine ⟨z1, z2, z3, z4, z5, z6, z7, z8, ?_, ?_⟩
    · exact (merge_int64_equiv_merge_n_bytes Endian
        z1 z2 z3 z4 z5 z6 z7 z8 v).mpr hmerge
    · have hspatial := sepcon_right_mono (store_byte SacContext.rules a z1) <|
        sepcon_right_mono (store_byte SacContext.rules (a + 1) z2) <|
          sepcon_right_mono (store_byte SacContext.rules (a + 2) z3) <|
            sepcon_right_mono (store_byte SacContext.rules (a + 3) z4) <|
              sepcon_right_mono (store_byte SacContext.rules (a + 4) z5) <|
                sepcon_right_mono (store_byte SacContext.rules (a + 5) z6) <|
                  sepcon_right_mono (store_byte SacContext.rules (a + 6) z7) <|
                    SacContext.rules.toContext.derivable1_sepcon_emp_l
                      (store_byte SacContext.rules (a + 7) z8)
      have hstores' :
          SacContext.rules.sepcon (store_byte SacContext.rules a z1)
            (SacContext.rules.sepcon (store_byte SacContext.rules (a + 1) z2)
              (SacContext.rules.sepcon (store_byte SacContext.rules (a + 2) z3)
                (SacContext.rules.sepcon (store_byte SacContext.rules (a + 3) z4)
                  (SacContext.rules.sepcon (store_byte SacContext.rules (a + 4) z5)
                    (SacContext.rules.sepcon (store_byte SacContext.rules (a + 5) z6)
                      (SacContext.rules.sepcon (store_byte SacContext.rules (a + 6) z7)
                        (SacContext.rules.sepcon
                          (store_byte SacContext.rules (a + 7) z8)
                          SacContext.rules.emp))))))) state := by
        simpa only [z1, z2, z3, z4, z5, z6, z7, z8, store_n_bytes,
          DerivedPredSig.vec8, SimpleC.SL.CArch.vector_head,
          SimpleC.SL.CArch.vector_tail, Int.add_assoc] using hstores
      exact hspatial state hstores'

theorem store_8byte_equiv_store_n_bytes_Z (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig) (a v : Int) :
    CRules.logic_equiv
      (store_8byte Endian CRules a v)
      (store_n_bytes_Z Arch Endian CRules a 8 v) := by
  letI : SacContext := ⟨CRules⟩
  exact store_8byte_equiv_store_n_bytes_Z_proof Arch Endian a v

end SimpleC.SL.StoreAux.StoreLibSig
