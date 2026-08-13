import SimpleC.SL.StoreAux.Core

namespace SimpleC.SL.StoreAux.StoreLibSig

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

private theorem sepcon_right_mono [SacContext]
    (P : SacContext.rules.expr) {Q R : SacContext.rules.expr}
    (h : SacContext.rules.derivable1 Q R) :
    SacContext.rules.derivable1
      (SacContext.rules.sepcon P Q) (SacContext.rules.sepcon P R) :=
  SacContext.rules.toContext.derivable1_sepcon_mono P P Q R
    (SacContext.rules.toContext.derivable1_refl P) h

private theorem store_byte_equiv_store_n_bytes_Z_proof [SacContext] (a v : Int) :
    SacContext.rules.logic_equiv
      (store_byte SacContext.rules a v)
      (store_n_bytes_Z SacContext.rules a 1 v) := by
  constructor
  · Exists (vector_cons v #v[])
    simp only [store_n_bytes, vector_head_cons]
    apply split_pure_and_spatial_goals
    · exact SacContext.rules.toContext.derivable1_sepcon_emp_r _
    · apply dump_spatial_left
      simp [merge_n_bytes, n_bytes_to_Z, vector_head_cons, Z.pow, Z.modulo]
  · Intros bytes
    rename_i hmerge
    rw [← vector_cons_eta bytes] at hmerge ⊢
    simp only [store_n_bytes, vector_head_cons] at ⊢
    exact SacContext.rules.toContext.derivable1_trans _ _ _
      (SacContext.rules.toContext.derivable1_sepcon_emp_l _)
      (store_byte_eqm SacContext.rules _ _ _ <|
        (eqm_iff_mod_eq _ _).mpr <| by
          simpa [merge_n_bytes, n_bytes_to_Z, vector_head_cons, vector_tail_cons,
            Z.pow, Z.modulo] using hmerge.symm)

theorem store_byte_equiv_store_n_bytes_Z (CRules : SeparationLogicSig) (a v : Int) :
    CRules.logic_equiv
      (store_byte CRules a v)
      (store_n_bytes_Z CRules a 1 v) := by
  letI : SacContext := ⟨CRules⟩
  exact store_byte_equiv_store_n_bytes_Z_proof a v

private theorem store_2byte_equiv_store_n_bytes_Z_proof [SacContext] (a v : Int) :
    SacContext.rules.logic_equiv
      (store_2byte SacContext.rules a v)
      (store_n_bytes_Z SacContext.rules a 2 v) := by
  constructor
  · Intros z1 z2
    rename_i hmerge
    Exists (vector_cons z1 (vector_cons z2 #v[]))
    simp only [store_n_bytes, vector_head_cons, vector_tail_cons]
    apply split_pure_and_spatial_goals
    · exact sepcon_right_mono (store_byte SacContext.rules a z1)
        (SacContext.rules.toContext.derivable1_sepcon_emp_r _)
    · apply dump_spatial_left
      exact (merge_short_equiv_merge_n_bytes z1 z2 v).mp hmerge
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
      exact (merge_short_equiv_merge_n_bytes
        (vector_head bytes) (vector_head (vector_tail bytes)) v).mpr hmerge

theorem store_2byte_equiv_store_n_bytes_Z (CRules : SeparationLogicSig) (a v : Int) :
    CRules.logic_equiv
      (store_2byte CRules a v)
      (store_n_bytes_Z CRules a 2 v) := by
  letI : SacContext := ⟨CRules⟩
  exact store_2byte_equiv_store_n_bytes_Z_proof a v

private theorem store_4byte_equiv_store_n_bytes_Z_proof [SacContext] (a v : Int) :
    SacContext.rules.logic_equiv
      (store_4byte SacContext.rules a v)
      (store_n_bytes_Z SacContext.rules a 4 v) := by
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
      exact (merge_int_equiv_merge_n_bytes z1 z2 z3 z4 v).mp hmerge
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
      exact (merge_int_equiv_merge_n_bytes
        (vector_head bytes) (vector_head (vector_tail bytes))
        (vector_head (vector_tail (vector_tail bytes)))
        (vector_head (vector_tail (vector_tail (vector_tail bytes)))) v).mpr hmerge

theorem store_4byte_equiv_store_n_bytes_Z (CRules : SeparationLogicSig) (a v : Int) :
    CRules.logic_equiv
      (store_4byte CRules a v)
      (store_n_bytes_Z CRules a 4 v) := by
  letI : SacContext := ⟨CRules⟩
  exact store_4byte_equiv_store_n_bytes_Z_proof a v

private theorem store_8byte_equiv_store_n_bytes_Z_proof [SacContext] (a v : Int) :
    SacContext.rules.logic_equiv
      (store_8byte SacContext.rules a v)
      (store_n_bytes_Z SacContext.rules a 8 v) := by
  constructor
  · Intros z1 z2 z3 z4 z5 z6 z7 z8
    rename_i hmerge
    Exists (vector_cons z1 (vector_cons z2 (vector_cons z3 (vector_cons z4
      (vector_cons z5 (vector_cons z6 (vector_cons z7 (vector_cons z8 #v[]))))))))
    simp only [store_n_bytes, vector_head_cons, vector_tail_cons, Int.add_assoc]
    apply split_pure_and_spatial_goals
    · exact sepcon_right_mono (store_byte SacContext.rules a z1) <|
        sepcon_right_mono (store_byte SacContext.rules (a + 1) z2) <|
          sepcon_right_mono (store_byte SacContext.rules (a + 2) z3) <|
            sepcon_right_mono (store_byte SacContext.rules (a + 3) z4) <|
              sepcon_right_mono (store_byte SacContext.rules (a + 4) z5) <|
                sepcon_right_mono (store_byte SacContext.rules (a + 5) z6) <|
                  sepcon_right_mono (store_byte SacContext.rules (a + 6) z7) <|
                    SacContext.rules.toContext.derivable1_sepcon_emp_r _
    · apply dump_spatial_left
      exact (merge_int64_equiv_merge_n_bytes
        z1 z2 z3 z4 z5 z6 z7 z8 v).mp hmerge
  · Intros bytes
    rename_i hmerge
    rw [← vector_cons_eta bytes] at hmerge ⊢
    rw [← vector_cons_eta (vector_tail bytes)] at hmerge ⊢
    rw [← vector_cons_eta (vector_tail (vector_tail bytes))] at hmerge ⊢
    rw [← vector_cons_eta (vector_tail (vector_tail (vector_tail bytes)))] at hmerge ⊢
    rw [← vector_cons_eta (vector_tail (vector_tail (vector_tail (vector_tail bytes))))]
      at hmerge ⊢
    rw [← vector_cons_eta
      (vector_tail (vector_tail (vector_tail (vector_tail (vector_tail bytes)))))]
      at hmerge ⊢
    rw [← vector_cons_eta
      (vector_tail (vector_tail (vector_tail (vector_tail (vector_tail (vector_tail bytes))))))]
      at hmerge ⊢
    rw [← vector_cons_eta
      (vector_tail (vector_tail (vector_tail (vector_tail
        (vector_tail (vector_tail (vector_tail bytes)))))))] at hmerge ⊢
    simp only [store_n_bytes, vector_head_cons, vector_tail_cons, Int.add_assoc] at ⊢
    refine Automation.exp_right_rule (CRules := SacContext.rules) (vector_head bytes) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail bytes)) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail (vector_tail bytes))) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail (vector_tail (vector_tail bytes)))) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail (vector_tail (vector_tail (vector_tail bytes))))) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail (vector_tail (vector_tail
        (vector_tail (vector_tail bytes)))))) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail (vector_tail (vector_tail
        (vector_tail (vector_tail (vector_tail bytes))))))) ?_
    refine Automation.exp_right_rule (CRules := SacContext.rules)
      (vector_head (vector_tail (vector_tail (vector_tail
        (vector_tail (vector_tail (vector_tail (vector_tail bytes)))))))) ?_
    apply split_pure_and_spatial_goals
    · exact sepcon_right_mono
        (store_byte SacContext.rules a (vector_head bytes)) <|
        sepcon_right_mono
          (store_byte SacContext.rules (a + 1) (vector_head (vector_tail bytes))) <|
          sepcon_right_mono
            (store_byte SacContext.rules (a + 2)
              (vector_head (vector_tail (vector_tail bytes)))) <|
            sepcon_right_mono
              (store_byte SacContext.rules (a + 3)
                (vector_head (vector_tail (vector_tail (vector_tail bytes))))) <|
              sepcon_right_mono
                (store_byte SacContext.rules (a + 4)
                  (vector_head (vector_tail (vector_tail (vector_tail
                    (vector_tail bytes)))))) <|
                sepcon_right_mono
                  (store_byte SacContext.rules (a + 5)
                    (vector_head (vector_tail (vector_tail (vector_tail
                      (vector_tail (vector_tail bytes))))))) <|
                  sepcon_right_mono
                    (store_byte SacContext.rules (a + 6)
                      (vector_head (vector_tail (vector_tail (vector_tail
                        (vector_tail (vector_tail (vector_tail bytes)))))))) <|
                    SacContext.rules.toContext.derivable1_sepcon_emp_l _
    · apply dump_spatial_left
      exact (merge_int64_equiv_merge_n_bytes
        _ _ _ _ _ _ _ _ v).mpr hmerge

theorem store_8byte_equiv_store_n_bytes_Z (CRules : SeparationLogicSig) (a v : Int) :
    CRules.logic_equiv
      (store_8byte CRules a v)
      (store_n_bytes_Z CRules a 8 v) := by
  letI : SacContext := ⟨CRules⟩
  exact store_8byte_equiv_store_n_bytes_Z_proof a v

end SimpleC.SL.StoreAux.StoreLibSig
