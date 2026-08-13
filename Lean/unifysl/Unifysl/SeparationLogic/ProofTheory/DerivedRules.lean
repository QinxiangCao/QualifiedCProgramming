import Unifysl.SeparationLogic.ProofTheory.RewriteClass
import Unifysl.PropositionalLogic.ProofTheory.Classical

/-!
Coq inventory from `SeparationLogic/ProofTheory/DerivedRules.v`:
- `provable_andp_sepcon_derives`
- `provable_sepcon_andp_derives`
- `provable_truep_sepcon_truep`
- `provable_coq_prop_sepcon_andp1`
- `provable_coq_prop_sepcon_andp2`
- `provable_coq_prop_andp_sepcon2`
- `GC_Ext_Classical_collapse_aux`
- `GC_Ext_Classical_collapse`
- `derivable_emp`

The Coq source includes relocation notes for the GC collapse lemmas; those
notes are not active declarations.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Unifysl

open PropositionalLanguageNotation
open CoqPropInLogicNotation
open SeparationLogicNotation

section DerivedRules

variable {L : Language.{u}}
variable [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L]
variable [NegLanguage L] [IffLanguage L] [TrueLanguage L]
variable [SepconLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]
variable [SepconAxiomatization L Gamma]

private theorem andp_sepcon_derives_proof :
    forall x y z : @Language.expr L,
      |-- (((x && y) * z) ⟶ ((x * z) && (y * z))) := by
  intro x y z
  exact provables_impp_andp_fold ((x && y) * z) (x * z) (y * z)
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      (x && y) x z z
      (AndAxiomatization.provable_andp_elim1 x y)
      (provable_impp_refl z))
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      (x && y) y z z
      (AndAxiomatization.provable_andp_elim2 x y)
      (provable_impp_refl z))

theorem provable_andp_sepcon_derives :
    forall x y z : @Language.expr L,
      |-- (((x && y) * z) ⟶ ((x * z) && (y * z))) :=
  andp_sepcon_derives_proof (Gamma := Gamma)

private theorem sepcon_andp_derives_proof :
    forall x y z : @Language.expr L,
      |-- ((x * (y && z)) ⟶ ((x * y) && (x * z))) := by
  intro x y z
  exact provables_impp_andp_fold (x * (y && z)) (x * y) (x * z)
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      x x (y && z) y
      (provable_impp_refl x)
      (AndAxiomatization.provable_andp_elim1 y z))
    (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
      x x (y && z) z
      (provable_impp_refl x)
      (AndAxiomatization.provable_andp_elim2 y z))

theorem provable_sepcon_andp_derives :
    forall x y z : @Language.expr L,
      |-- ((x * (y && z)) ⟶ ((x * y) && (x * z))) :=
  sepcon_andp_derives_proof (Gamma := Gamma)

theorem provable_truep_sepcon_truep [ExtSeparationLogic L Gamma] :
    |-- (((TT : @Language.expr L) * TT) ⟷ TT) := by
  exact provables_iffp_intros ((TT : @Language.expr L) * TT) TT
    (provables_impp_elim ((TT : @Language.expr L) * TT) TT
      TrueAxiomatization.provable_truep_intros)
    (ExtSeparationLogic.sepcon_ext (Gamma := Gamma) TT)

section CoqProp

variable [CoqPropLanguage L]
variable [SepconCoqPropAxiomatization L Gamma]

private theorem prop_andp_sepcon1_impp :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- (((((!! P) && Q) * R) ⟶ (((!! P) && (Q * R))))) := by
  intro P Q R
  exact provables_iffp_elim1 (((!! P) && Q) * R) ((!! P) && (Q * R))
    (SepconCoqPropAxiomatization.prop_andp_sepcon1
      (Gamma := Gamma) P Q R)

private theorem prop_andp_sepcon1_rev :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- ((((!! P) && (Q * R)) ⟶ ((((!! P) && Q) * R)))) := by
  intro P Q R
  exact provables_iffp_elim2 (((!! P) && Q) * R) ((!! P) && (Q * R))
    (SepconCoqPropAxiomatization.prop_andp_sepcon1
      (Gamma := Gamma) P Q R)

private theorem andp_second_sepcon_comm :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- (((!! P) && (Q * R)) ⟶ ((!! P) && (R * Q))) := by
  intro P Q R
  exact provables_impp_andp_fold ((!! P) && (Q * R)) (!! P) (R * Q)
    (AndAxiomatization.provable_andp_elim1 (!! P) (Q * R))
    (solve_impp_trans ((!! P) && (Q * R)) (Q * R) (R * Q)
      (AndAxiomatization.provable_andp_elim2 (!! P) (Q * R))
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) Q R))

private theorem andp_second_sepcon_comm_rev :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- (((!! P) && (R * Q)) ⟶ ((!! P) && (Q * R))) := by
  intro P Q R
  exact provables_impp_andp_fold ((!! P) && (R * Q)) (!! P) (Q * R)
    (AndAxiomatization.provable_andp_elim1 (!! P) (R * Q))
    (solve_impp_trans ((!! P) && (R * Q)) (R * Q) (Q * R)
      (AndAxiomatization.provable_andp_elim2 (!! P) (R * Q))
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) R Q))

private theorem coq_prop_sepcon_andp2_proof :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- ((Q * ((!! P) && R)) ⟷ ((!! P) && (Q * R))) := by
  intro P Q R
  apply provables_iffp_intros
  · exact solve_impp_trans (Q * ((!! P) && R)) (((!! P) && R) * Q)
      (((!! P) && (Q * R)))
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) Q (((!! P) && R)))
      (solve_impp_trans (((!! P) && R) * Q) (((!! P) && (R * Q)))
        (((!! P) && (Q * R)))
        (prop_andp_sepcon1_impp P R Q)
        (andp_second_sepcon_comm_rev P Q R))
  · exact solve_impp_trans (((!! P) && (Q * R))) (((!! P) && (R * Q)))
      (Q * ((!! P) && R))
      (andp_second_sepcon_comm P Q R)
      (solve_impp_trans (((!! P) && (R * Q))) (((!! P) && R) * Q)
        (Q * ((!! P) && R))
        (prop_andp_sepcon1_rev P R Q)
        (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma)
          (((!! P) && R)) Q))

theorem provable_coq_prop_sepcon_andp2 :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- ((Q * ((!! P) && R)) ⟷ ((!! P) && (Q * R))) :=
  coq_prop_sepcon_andp2_proof (Gamma := Gamma)

private theorem coq_prop_sepcon_andp1_proof :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- ((Q * (R && (!! P))) ⟷ ((!! P) && (Q * R))) := by
  intro P Q R
  apply provables_iffp_intros
  · have hcomm : |-- ((R && (!! P)) ⟶ (((!! P) && R))) :=
      provable_andp_impp_comm R (!! P)
    exact solve_impp_trans (Q * (R && (!! P))) (Q * (((!! P) && R)))
      (((!! P) && (Q * R)))
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        Q Q (R && (!! P)) (((!! P) && R))
        (provable_impp_refl Q) hcomm)
      (provables_iffp_elim1 (Q * (((!! P) && R))) (((!! P) && (Q * R)))
        (coq_prop_sepcon_andp2_proof P Q R))
  · have hcomm : |-- ((((!! P) && R) ⟶ (R && (!! P)))) :=
      provable_andp_impp_comm (!! P) R
    exact solve_impp_trans (((!! P) && (Q * R))) (Q * (((!! P) && R)))
      (Q * (R && (!! P)))
      (provables_iffp_elim2 (Q * (((!! P) && R))) (((!! P) && (Q * R)))
        (coq_prop_sepcon_andp2_proof P Q R))
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        Q Q (((!! P) && R)) (R && (!! P))
        (provable_impp_refl Q) hcomm)

theorem provable_coq_prop_sepcon_andp1 :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- ((Q * (R && (!! P))) ⟷ ((!! P) && (Q * R))) :=
  coq_prop_sepcon_andp1_proof (Gamma := Gamma)

private theorem coq_prop_andp_sepcon2_proof :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- (((Q && (!! P)) * R) ⟷ ((!! P) && (Q * R))) := by
  intro P Q R
  apply provables_iffp_intros
  · have hcomm : |-- ((Q && (!! P)) ⟶ (((!! P) && Q))) :=
      provable_andp_impp_comm Q (!! P)
    exact solve_impp_trans ((Q && (!! P)) * R) ((((!! P) && Q) * R))
      (((!! P) && (Q * R)))
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        (Q && (!! P)) (((!! P) && Q) ) R R
        hcomm (provable_impp_refl R))
      (prop_andp_sepcon1_impp P Q R)
  · have hcomm : |-- ((((!! P) && Q) ⟶ (Q && (!! P)))) :=
      provable_andp_impp_comm (!! P) Q
    exact solve_impp_trans (((!! P) && (Q * R))) ((((!! P) && Q) * R))
      ((Q && (!! P)) * R)
      (prop_andp_sepcon1_rev P Q R)
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        (((!! P) && Q)) (Q && (!! P)) R R
        hcomm (provable_impp_refl R))

theorem provable_coq_prop_andp_sepcon2 :
    forall (P : Prop) (Q R : @Language.expr L),
      |-- (((Q && (!! P)) * R) ⟷ ((!! P) && (Q * R))) :=
  coq_prop_andp_sepcon2_proof (Gamma := Gamma)

end CoqProp

private theorem provable_same_antecedent_modus_ponens
    (A B C : @Language.expr L)
    (hAB : |-- (A ⟶ B)) (hABC : |-- (A ⟶ (B ⟶ C))) :
    |-- (A ⟶ C) := by
  have hmp : |-- ((A ⟶ B) ⟶ (A ⟶ (B ⟶ C)) ⟶ (A ⟶ C)) := by
    simpa [multi_imp] using
      (provable_multi_imp_modus_ponens [A] B C)
  have hstep : |-- ((A ⟶ (B ⟶ C)) ⟶ (A ⟶ C)) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (A ⟶ B) ((A ⟶ (B ⟶ C)) ⟶ (A ⟶ C))
      hmp hAB
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (A ⟶ (B ⟶ C)) (A ⟶ C) hstep hABC

private theorem sepcon_contradict_impp
    [GarbageCollectSeparationLogic L Gamma]
    (x : @Language.expr L) :
    |-- ((x * (~~ x)) ⟶ (x * x)) := by
  have hx : |-- ((x * (~~ x)) ⟶ x) :=
    GarbageCollectSeparationLogic.sepcon_elim1 (Gamma := Gamma) x (~~ x)
  have hnx : |-- ((x * (~~ x)) ⟶ (~~ x)) :=
    solve_impp_trans (x * (~~ x)) ((~~ x) * x) (~~ x)
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x (~~ x))
      (GarbageCollectSeparationLogic.sepcon_elim1 (Gamma := Gamma) (~~ x) x)
  have hcontr : |-- (x ⟶ ((~~ x) ⟶ (x * x))) :=
    provable_contradiction_elim2 x (x * x)
  have hstep : |-- ((x * (~~ x)) ⟶ ((~~ x) ⟶ (x * x))) :=
    solve_impp_trans (x * (~~ x)) x ((~~ x) ⟶ (x * x)) hx hcontr
  exact provable_same_antecedent_modus_ponens (x * (~~ x)) (~~ x) (x * x)
    hnx hstep

theorem GC_Ext_Classical_collapse_aux
    [SepconOrAxiomatization L Gamma]
    [ClassicalAxiomatization L Gamma]
    [GarbageCollectSeparationLogic L Gamma]
    [ExtSeparationLogic L Gamma] :
    forall x : @Language.expr L, |-- (x ⟶ (x * x)) := by
  intro x
  have hTTcase : |-- (((TT : @Language.expr L) ⟶ (x || (~~ x)))) :=
    provables_impp_elim (TT : @Language.expr L) (x || (~~ x))
      (provable_excluded_middle x)
  have htoSplit : |-- (x ⟶ (x * (x || (~~ x)))) :=
    solve_impp_trans x (x * (TT : @Language.expr L)) (x * (x || (~~ x)))
      (ExtSeparationLogic.sepcon_ext (Gamma := Gamma) x)
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        x x (TT : @Language.expr L) (x || (~~ x))
        (provable_impp_refl x) hTTcase)
  have hdist : |-- ((x * (x || (~~ x))) ⟶ ((x * x) || (x * (~~ x)))) := by
    have hcomm : |-- ((x * (x || (~~ x))) ⟶ ((x || (~~ x)) * x)) :=
      SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x (x || (~~ x))
    have hdistr : |-- (((x || (~~ x)) * x) ⟶ ((x * x) || ((~~ x) * x))) :=
      SepconOrAxiomatization.orp_sepcon_impp (Gamma := Gamma) x (~~ x) x
    have hright : |-- (((~~ x) * x) ⟶ ((x * x) || (x * (~~ x)))) :=
      solve_impp_trans ((~~ x) * x) (x * (~~ x)) ((x * x) || (x * (~~ x)))
        (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) (~~ x) x)
        (OrAxiomatization.provable_orp_intros2 (x * x) (x * (~~ x)))
    have hcases : |-- (((x * x) || ((~~ x) * x)) ⟶ ((x * x) || (x * (~~ x)))) :=
      provables_orp_impp_fold (x * x) ((~~ x) * x) ((x * x) || (x * (~~ x)))
        (OrAxiomatization.provable_orp_intros1 (x * x) (x * (~~ x)))
        hright
    exact solve_impp_trans (x * (x || (~~ x))) ((x || (~~ x)) * x)
      ((x * x) || (x * (~~ x)))
      hcomm
      (solve_impp_trans ((x || (~~ x)) * x) ((x * x) || ((~~ x) * x))
        ((x * x) || (x * (~~ x))) hdistr hcases)
  have hcases : |-- (((x * x) || (x * (~~ x))) ⟶ (x * x)) :=
    provables_orp_impp_fold (x * x) (x * (~~ x)) (x * x)
      (provable_impp_refl (x * x))
      (sepcon_contradict_impp x)
  exact solve_impp_trans x ((x * x) || (x * (~~ x))) (x * x)
    (solve_impp_trans x (x * (x || (~~ x)))
      ((x * x) || (x * (~~ x))) htoSplit hdist)
    hcases

theorem GC_Ext_Classical_collapse
    [SepconOrAxiomatization L Gamma]
    [ClassicalAxiomatization L Gamma]
    [GarbageCollectSeparationLogic L Gamma]
    [ExtSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- ((x * y) ⟷ (x && y)) := by
  intro x y
  apply provables_iffp_intros
  · exact provables_impp_andp_fold (x * y) x y
      (GarbageCollectSeparationLogic.sepcon_elim1 (Gamma := Gamma) x y)
      (solve_impp_trans (x * y) (y * x) y
        (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x y)
        (GarbageCollectSeparationLogic.sepcon_elim1 (Gamma := Gamma) y x))
  · have hdup : |-- ((x && y) ⟶ ((x && y) * (x && y))) :=
      GC_Ext_Classical_collapse_aux (x && y)
    have hmono : |-- (((x && y) * (x && y)) ⟶ (x * y)) :=
      SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        (x && y) x (x && y) y
        (AndAxiomatization.provable_andp_elim1 x y)
        (AndAxiomatization.provable_andp_elim2 x y)
    exact solve_impp_trans (x && y) ((x && y) * (x && y)) (x * y)
      hdup hmono

section Emp

variable [EmpLanguage L]
variable [EmpAxiomatization L Gamma]

theorem derivable_emp [GarbageCollectSeparationLogic L Gamma] :
    forall x y : @Language.expr L, |-- (emp : @Language.expr L) := by
  intro _x _y
  have hTTtoSep : |-- ((TT : @Language.expr L) ⟶ (TT * emp)) :=
    EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) TT
  have hSepToEmp : |-- (((TT : @Language.expr L) * emp) ⟶ emp) :=
    solve_impp_trans ((TT : @Language.expr L) * emp) (emp * (TT : @Language.expr L)) emp
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) TT emp)
      (GarbageCollectSeparationLogic.sepcon_elim1 (Gamma := Gamma) emp TT)
  have hTTtoEmp : |-- ((TT : @Language.expr L) ⟶ emp) :=
    solve_impp_trans (TT : @Language.expr L) (TT * emp) emp hTTtoSep hSepToEmp
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (TT : @Language.expr L) emp hTTtoEmp
    TrueAxiomatization.provable_truep_intros

end Emp

end DerivedRules

end Unifysl
