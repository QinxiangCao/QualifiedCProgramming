/- Coq inventory: unifysl-prp/MetaLogicInj/ProofTheory/ProofRules.v
   - Classes: CoqPropAxiomatization, CoqPropImpAxiomatization,
     CoqPropSequentCalculus, CoqPropDeduction, CoqPropImpDeduction
   - Derived rules for provability, derivable1, and logic equivalence
   - Register entries for D12P conversions at indices 8 and 9
-/

import Unifysl.PropositionalLogic.ProofTheory.Intuitionistic
import Unifysl.PropositionalLogic.ProofTheory.DeMorgan
import Unifysl.PropositionalLogic.ProofTheory.GodelDummett
import Unifysl.PropositionalLogic.ProofTheory.Classical
import Unifysl.PropositionalLogic.ProofTheory.RewriteClass
import Unifysl.PropositionalLogic.ProofTheory.ProofTheoryPatterns
import Unifysl.MetaLogicInj.Syntax

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Unifysl

open PropositionalLanguageNotation
open CoqPropInLogicNotation

class CoqPropAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [CoqPropLanguage L] (Gamma : Provable L) : Prop where
  provables_coq_prop_intros :
    forall P : Prop, P -> @Provable.provable L Gamma (!! P)
  provables_coq_prop_elim :
    forall (P : Prop) (x : @Language.expr L),
      (P -> @Provable.provable L Gamma x) ->
        @Provable.provable L Gamma ((!! P) ⟶ x)

namespace CoqPropAxiomatization

theorem coq_prop_intros {L : Language.{u}} [MinimumLanguage L]
    [CoqPropLanguage L] [Gamma : Provable L]
    [self : CoqPropAxiomatization L Gamma] :
    forall P : Prop, P -> @Provable.provable L Gamma (!! P) :=
  self.provables_coq_prop_intros

theorem coq_prop_elim {L : Language.{u}} [MinimumLanguage L]
    [CoqPropLanguage L] [Gamma : Provable L]
    [self : CoqPropAxiomatization L Gamma] :
    forall (P : Prop) (x : @Language.expr L),
      (P -> @Provable.provable L Gamma x) ->
        @Provable.provable L Gamma ((!! P) ⟶ x) :=
  self.provables_coq_prop_elim

end CoqPropAxiomatization

class CoqPropImpAxiomatization (L : Language.{u}) [MinimumLanguage L]
    [CoqPropLanguage L] (Gamma : Provable L) : Prop where
  provable_coq_prop_impp_derives :
    forall P Q : Prop,
      @Provable.provable L Gamma (((!! P) ⟶ (!! Q)) ⟶ (!! (P -> Q)))

namespace CoqPropImpAxiomatization

theorem coq_prop_impp {L : Language.{u}} [MinimumLanguage L]
    [CoqPropLanguage L] [Gamma : Provable L]
    [self : CoqPropImpAxiomatization L Gamma] :
    forall P Q : Prop,
      @Provable.provable L Gamma (((!! P) ⟶ (!! Q)) ⟶ (!! (P -> Q))) :=
  self.provable_coq_prop_impp_derives

end CoqPropImpAxiomatization

class CoqPropSequentCalculus (L : Language.{u}) [MinimumLanguage L]
    [CoqPropLanguage L] (Gamma : Derivable L) : Prop where
  derivables_coq_prop_intros :
    forall (P : Prop) (Phi : context (L := L)),
      P -> @Derivable.derivable L Gamma Phi (!! P)
  derivables_coq_prop_elim :
    forall (P : Prop) (Phi : context (L := L)) (x : @Language.expr L),
      (P -> @Derivable.derivable L Gamma Phi x) ->
        @Derivable.derivable L Gamma (Phi ;; (!! P)) x
  derivable_coq_prop_impp_l :
    forall (P Q : Prop) (Phi : context (L := L)),
      @Derivable.derivable L Gamma (Phi ;; ((!! P) ⟶ (!! Q))) (!! (P -> Q))

namespace CoqPropSequentCalculus

theorem derivable_coq_prop_intros {L : Language.{u}} [MinimumLanguage L]
    [CoqPropLanguage L] [Gamma : Derivable L]
    [self : CoqPropSequentCalculus L Gamma] :
    forall (P : Prop) (Phi : context (L := L)),
      P -> @Derivable.derivable L Gamma Phi (!! P) :=
  self.derivables_coq_prop_intros

theorem derivable_coq_prop_elim {L : Language.{u}} [MinimumLanguage L]
    [CoqPropLanguage L] [Gamma : Derivable L]
    [self : CoqPropSequentCalculus L Gamma] :
    forall (P : Prop) (Phi : context (L := L)) (x : @Language.expr L),
      (P -> @Derivable.derivable L Gamma Phi x) ->
        @Derivable.derivable L Gamma (Phi ;; (!! P)) x :=
  self.derivables_coq_prop_elim

theorem derivable_coq_prop_impp_left {L : Language.{u}} [MinimumLanguage L]
    [CoqPropLanguage L] [Gamma : Derivable L]
    [self : CoqPropSequentCalculus L Gamma] :
    forall (P Q : Prop) (Phi : context (L := L)),
      @Derivable.derivable L Gamma (Phi ;; ((!! P) ⟶ (!! Q))) (!! (P -> Q)) :=
  self.derivable_coq_prop_impp_l

end CoqPropSequentCalculus

class CoqPropDeduction (L : Language.{u}) [TrueLanguage L]
    [CoqPropLanguage L] (GammaD1 : Derivable1 L) : Prop where
  derivable1s_coq_prop_r :
    forall (P : Prop) (x : @Language.expr L),
      P -> @Derivable1.derivable1 L GammaD1 x (!! P)
  derivable1s_coq_prop_l :
    forall (P : Prop) (x : @Language.expr L),
      (P -> @Derivable1.derivable1 L GammaD1 TT x) ->
        @Derivable1.derivable1 L GammaD1 (!! P) x

namespace CoqPropDeduction

theorem coq_prop_right {L : Language.{u}} [TrueLanguage L]
    [CoqPropLanguage L] [GammaD1 : Derivable1 L]
    [self : CoqPropDeduction L GammaD1] :
    forall (P : Prop) (x : @Language.expr L),
      P -> @Derivable1.derivable1 L GammaD1 x (!! P) :=
  self.derivable1s_coq_prop_r

theorem coq_prop_left {L : Language.{u}} [TrueLanguage L]
    [CoqPropLanguage L] [GammaD1 : Derivable1 L]
    [self : CoqPropDeduction L GammaD1] :
    forall (P : Prop) (x : @Language.expr L),
      (P -> @Derivable1.derivable1 L GammaD1 TT x) ->
        @Derivable1.derivable1 L GammaD1 (!! P) x :=
  self.derivable1s_coq_prop_l

end CoqPropDeduction

class CoqPropImpDeduction (L : Language.{u}) [MinimumLanguage L]
    [CoqPropLanguage L] (GammaD1 : Derivable1 L) : Prop where
  derivable1_coq_prop_impp_derives :
    forall P Q : Prop,
      @Derivable1.derivable1 L GammaD1 ((!! P) ⟶ (!! Q)) (!! (P -> Q))

namespace CoqPropImpDeduction

theorem derivable1_coq_prop_impp {L : Language.{u}} [MinimumLanguage L]
    [CoqPropLanguage L] [GammaD1 : Derivable1 L]
    [self : CoqPropImpDeduction L GammaD1] :
    forall P Q : Prop,
      @Derivable1.derivable1 L GammaD1 ((!! P) ⟶ (!! Q)) (!! (P -> Q)) :=
  self.derivable1_coq_prop_impp_derives

end CoqPropImpDeduction

section DerivedRulesFromAxiomatization

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L] [CoqPropLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma] [AndAxiomatization L Gamma]
variable [OrAxiomatization L Gamma] [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma] [IffAxiomatization L Gamma]
variable [TrueAxiomatization L Gamma] [CoqPropAxiomatization L Gamma]

theorem provables_coq_prop_truep :
    forall P : Prop, P -> @Provable.provable L Gamma ((!! P) ⟷ TT) := by
  intro P hP
  exact provables_iffp_intros (!! P) TT
    (CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) P TT
      (fun _ => TrueAxiomatization.provable_truep_intros (Gamma := Gamma)))
    (aux_minimun_rule00 (!! P) TT
      (CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) P hP))

theorem provables_coq_prop_andp :
    forall (P : Prop) (Q : @Language.expr L),
      P -> @Provable.provable L Gamma (((!! P) && Q) ⟷ Q) := by
  intro P Q hP
  exact provables_iffp_intros (((!! P) && Q)) Q
    (AndAxiomatization.provable_andp_elim2 (!! P) Q)
    (provables_impp_andp_fold Q (!! P) Q
      (aux_minimun_rule00 (!! P) Q
        (CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) P hP))
      (provable_impp_refl Q))

theorem provables_andp_coq_prop :
    forall (P : Prop) (Q : @Language.expr L),
      P -> @Provable.provable L Gamma ((Q && (!! P)) ⟷ Q) := by
  intro P Q hP
  exact provables_iffp_intros (Q && (!! P)) Q
    (AndAxiomatization.provable_andp_elim1 Q (!! P))
    (provables_impp_andp_fold Q Q (!! P)
      (provable_impp_refl Q)
      (aux_minimun_rule00 (!! P) Q
        (CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) P hP)))

theorem provables_coq_prop_andp_derives :
    forall (P : Prop) (Q R : @Language.expr L),
      (P -> @Provable.provable L Gamma (Q ⟶ R)) ->
        @Provable.provable L Gamma (((!! P) && Q) ⟶ R) := by
  intro P Q R h
  have hcurried :
      @Provable.provable L Gamma (((!! P) ⟶ Q ⟶ R) ⟶ (((!! P) && Q) ⟶ R)) :=
    provable_impp_curry (!! P) Q R
  have hmeta : @Provable.provable L Gamma ((!! P) ⟶ Q ⟶ R) :=
    CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) P (Q ⟶ R) h
  exact MinimumAxiomatization.modus_ponens (Gamma := Gamma)
    ((!! P) ⟶ Q ⟶ R) (((!! P) && Q) ⟶ R) hcurried hmeta

theorem provables_andp_coq_prop_derives :
    forall (P : Prop) (Q R : @Language.expr L),
      (P -> @Provable.provable L Gamma (Q ⟶ R)) ->
        @Provable.provable L Gamma ((Q && (!! P)) ⟶ R) := by
  intro P Q R h
  exact solve_impp_trans (Q && (!! P)) (((!! P) && Q)) R
    (provable_andp_impp_comm Q (!! P))
    (provables_coq_prop_andp_derives P Q R h)

theorem provables_impp_coq_prop :
    forall (P : Prop) (Q : @Language.expr L),
      P -> @Provable.provable L Gamma (Q ⟶ (!! P)) := by
  intro P Q hP
  exact aux_minimun_rule00 (!! P) Q
    (CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) P hP)

theorem provable_coq_prop_and :
    forall P Q : Prop,
      @Provable.provable L Gamma ((!! (P ∧ Q)) ⟷ ((!! P) && (!! Q))) := by
  intro P Q
  exact provables_iffp_intros (!! (P ∧ Q)) ((!! P) && (!! Q))
    (CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) (P ∧ Q)
      ((!! P) && (!! Q))
      (fun hPQ =>
        provables_andp_intros (!! P) (!! Q)
          (CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) P hPQ.left)
          (CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) Q hPQ.right)))
    (provables_coq_prop_andp_derives P (!! Q) (!! (P ∧ Q))
      (fun hP =>
        CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) Q (!! (P ∧ Q))
          (fun hQ =>
            CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma)
              (P ∧ Q) ⟨hP, hQ⟩)))

theorem provable_coq_prop_or :
    forall P Q : Prop,
      @Provable.provable L Gamma ((!! (P ∨ Q)) ⟷ ((!! P) || (!! Q))) := by
  intro P Q
  exact provables_iffp_intros (!! (P ∨ Q)) ((!! P) || (!! Q))
    (CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) (P ∨ Q)
      ((!! P) || (!! Q))
      (fun hPQ =>
        hPQ.elim
          (fun hP =>
            provables_orp_intros1 (!! P) (!! Q)
              (CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) P hP))
          (fun hQ =>
            provables_orp_intros2 (!! P) (!! Q)
              (CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) Q hQ))))
    (provables_orp_impp_fold (!! P) (!! Q) (!! (P ∨ Q))
      (CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) P (!! (P ∨ Q))
        (fun hP =>
          CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma)
            (P ∨ Q) (Or.inl hP)))
      (CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) Q (!! (P ∨ Q))
        (fun hQ =>
          CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma)
            (P ∨ Q) (Or.inr hQ))))

theorem provable_coq_prop_imply [CoqPropImpAxiomatization L Gamma] :
    forall P Q : Prop,
      @Provable.provable L Gamma ((!! (P -> Q)) ⟷ (((!! P) ⟶ (!! Q)))) := by
  intro P Q
  exact provables_iffp_intros (!! (P -> Q)) (((!! P) ⟶ (!! Q)))
    (CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) (P -> Q)
      (((!! P) ⟶ (!! Q)))
      (fun hPQ =>
        CoqPropAxiomatization.coq_prop_elim (Gamma := Gamma) P (!! Q)
          (fun hP =>
            CoqPropAxiomatization.coq_prop_intros (Gamma := Gamma) Q (hPQ hP))))
    (CoqPropImpAxiomatization.coq_prop_impp (Gamma := Gamma) P Q)

end DerivedRulesFromAxiomatization

section Deduction2Axiomatization

variable {L : Language.{u}} [MinimumLanguage L] [AndLanguage L] [TrueLanguage L]
variable [CoqPropLanguage L]
variable [GammaD1 : Derivable1 L] [GammaP : Provable L]
variable [CoqPropDeduction L GammaD1]
variable [MinimumAxiomatization L GammaP] [BasicDeduction L GammaD1]
variable [TrueDeduction L GammaD1]
variable [Derivable1Provable L GammaP GammaD1]
variable [ProvableDerivable1 L GammaP GammaD1]

theorem Deduction2Axiomatization_coq_prop_AX :
    CoqPropAxiomatization L GammaP := by
  constructor
  · intro P hP
    exact (provable_derivable1_true (!! P)).mpr
      (CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) P TT hP)
  · intro P x h
    have hDer : @Derivable1.derivable1 L GammaD1 (!! P) x :=
      CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) P x
        (fun hP => (provable_derivable1_true x).mp (h hP))
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1) (!! P) x).mp hDer

theorem Deduction2Axiomatization_coq_prop_impp_AX
    [CoqPropImpDeduction L GammaD1] :
    CoqPropImpAxiomatization L GammaP := by
  constructor
  intro P Q
  exact (Derivable1Provable.derivable1_provable
    (L := L) (GammaP := GammaP) (GammaD := GammaD1)
    (((!! P) ⟶ (!! Q))) (!! (P -> Q))).mp
    (CoqPropImpDeduction.derivable1_coq_prop_impp
      (GammaD1 := GammaD1) P Q)

end Deduction2Axiomatization

instance reg_Deduction2Axiomatization_coq_prop_AX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `coq_prop_AX ``Deduction2Axiomatization_coq_prop_AX) 8 := {}

instance reg_Deduction2Axiomatization_coq_prop_impp_AX :
    RegisterClass D12P_reg
      (ProofRegistration.mk `coq_prop_impp_AX ``Deduction2Axiomatization_coq_prop_impp_AX) 9 := {}

section DeductionRules

variable {L : Language.{u}} [MinimumLanguage L] [CoqPropLanguage L]
variable [AndLanguage L] [OrLanguage L] [IffLanguage L] [TrueLanguage L]
variable [GammaD1 : Derivable1 L]
variable [AndDeduction L GammaD1] [ImpAndAdjointDeduction L GammaD1]
variable [OrDeduction L GammaD1] [IffDeduction L GammaD1]
variable [TrueDeduction L GammaD1] [CoqPropDeduction L GammaD1]
variable [BasicDeduction L GammaD1]

theorem derivable1s_coq_prop_andp_l :
    forall (P : Prop) (Q R : @Language.expr L),
      (P -> @Derivable1.derivable1 L GammaD1 Q R) ->
        @Derivable1.derivable1 L GammaD1 (((!! P) && Q)) R := by
  intro P Q R h
  refine (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) (!! P) Q R).mp ?_
  exact CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) P (Q ⟶ R)
    (fun hP =>
      (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
        (GammaD1 := GammaD1) TT Q R).mpr
        (derivable1_trans (TT && Q) Q R
          (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) TT Q)
          (h hP)))

theorem derivable1s_andp_coq_prop_l :
    forall (P : Prop) (Q R : @Language.expr L),
      (P -> @Derivable1.derivable1 L GammaD1 Q R) ->
        @Derivable1.derivable1 L GammaD1 (Q && (!! P)) R := by
  intro P Q R h
  exact derivable1_trans (Q && (!! P)) (((!! P) && Q)) R
    (derivable1_andp_comm Q (!! P))
    (derivable1s_coq_prop_andp_l P Q R h)

theorem derivable1s_coq_prop_andp_r :
    forall (P : Prop) (Q R : @Language.expr L),
      @Derivable1.derivable1 L GammaD1 R Q ->
        P -> @Derivable1.derivable1 L GammaD1 R ((!! P) && Q) := by
  intro P Q R hRQ hP
  exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) R (!! P) Q
    (CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) P R hP)
    hRQ

theorem derivables_coq_prop_imply :
    forall P Q : Prop, (P -> Q) ->
      @Derivable1.derivable1 L GammaD1 (!! P) (!! Q) := by
  intro P Q hPQ
  exact CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) P (!! Q)
    (fun hP =>
      CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) Q TT (hPQ hP))

theorem derivables_false_coq_prop :
    forall (P : Prop) (Q : @Language.expr L), (P -> False) ->
      @Derivable1.derivable1 L GammaD1 (!! P) Q := by
  intro P Q hfalse
  exact CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) P Q
    (fun hP => False.elim (hfalse hP))

section SLogicEquiv

variable [GammaE : LogicEquiv L]
variable [EquivDerivable1 L GammaD1 GammaE]

theorem logic_equiv_coq_prop_truep :
    forall P : Prop, P -> @LogicEquiv.logic_equiv L GammaE (!! P) TT := by
  intro P hP
  exact (__logic_equiv_derivable1 (!! P) TT).mpr
    ⟨TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) (!! P),
      CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) P TT hP⟩

theorem logic_equiv_coq_prop_andp1 :
    forall (P : @Language.expr L) (Q : Prop),
      @Derivable1.derivable1 L GammaD1 P (!! Q) ->
        @LogicEquiv.logic_equiv L GammaE P (((!! Q) && P)) := by
  intro P Q hPQ
  exact (__logic_equiv_derivable1 P (((!! Q) && P))).mpr
    ⟨AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) P (!! Q) P
        hPQ (derivable1_refl P),
      AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (!! Q) P⟩

theorem logic_equiv_coq_prop_andp2 :
    forall (P : Prop) (Q : @Language.expr L),
      P -> @LogicEquiv.logic_equiv L GammaE (((!! P) && Q)) Q := by
  intro P Q hP
  exact (__logic_equiv_derivable1 (((!! P) && Q)) Q).mpr
    ⟨AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (!! P) Q,
      AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
        Q (!! P) Q
        (CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) P Q hP)
        (derivable1_refl Q)⟩

theorem logic_equiv_andp_coq_prop :
    forall (P : Prop) (Q : @Language.expr L),
      P -> @LogicEquiv.logic_equiv L GammaE (Q && (!! P)) Q := by
  intro P Q hP
  exact (__logic_equiv_derivable1 (Q && (!! P)) Q).mpr
    ⟨AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) Q (!! P),
      AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
        Q Q (!! P)
        (derivable1_refl Q)
        (CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) P Q hP)⟩

theorem logic_equiv_coq_prop_and :
    forall P Q : Prop,
      @LogicEquiv.logic_equiv L GammaE (!! (P ∧ Q)) (((!! P) && (!! Q))) := by
  intro P Q
  refine (__logic_equiv_derivable1 (!! (P ∧ Q)) (((!! P) && (!! Q)))).mpr ?_
  constructor
  · exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
      (!! (P ∧ Q)) (!! P) (!! Q)
      (CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) (P ∧ Q) (!! P)
        (fun hPQ =>
          CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) P TT hPQ.left))
      (CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) (P ∧ Q) (!! Q)
        (fun hPQ =>
          CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) Q TT hPQ.right))
  · exact derivable1s_coq_prop_andp_l P (!! Q) (!! (P ∧ Q))
      (fun hP =>
        CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) Q (!! (P ∧ Q))
          (fun hQ =>
            CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1)
              (P ∧ Q) TT ⟨hP, hQ⟩))

theorem logic_equiv_coq_prop_or :
    forall P Q : Prop,
      @LogicEquiv.logic_equiv L GammaE (!! (P ∨ Q)) (((!! P) || (!! Q))) := by
  intro P Q
  refine (__logic_equiv_derivable1 (!! (P ∨ Q)) (((!! P) || (!! Q)))).mpr ?_
  constructor
  · exact CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1)
      (P ∨ Q) (((!! P) || (!! Q)))
      (fun hPQ =>
        hPQ.elim
          (fun hP =>
            derivable1_trans TT (!! P) (((!! P) || (!! Q)))
              (CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) P TT hP)
              (OrDeduction.derivable1_orp_intros1 (GammaD1 := GammaD1)
                (!! P) (!! Q)))
          (fun hQ =>
            derivable1_trans TT (!! Q) (((!! P) || (!! Q)))
              (CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) Q TT hQ)
              (OrDeduction.derivable1_orp_intros2 (GammaD1 := GammaD1)
                (!! P) (!! Q))))
  · exact OrDeduction.derivable1_orp_elim (GammaD1 := GammaD1)
      (!! P) (!! Q) (!! (P ∨ Q))
      (CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) P (!! (P ∨ Q))
        (fun hP =>
          CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1)
            (P ∨ Q) TT (Or.inl hP)))
      (CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) Q (!! (P ∨ Q))
        (fun hQ =>
          CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1)
            (P ∨ Q) TT (Or.inr hQ)))

theorem logic_equiv_coq_prop_imply [CoqPropImpDeduction L GammaD1] :
    forall P Q : Prop,
      @LogicEquiv.logic_equiv L GammaE (!! (P -> Q)) (((!! P) ⟶ (!! Q))) := by
  intro P Q
  refine (__logic_equiv_derivable1 (!! (P -> Q)) (((!! P) ⟶ (!! Q)))).mpr ?_
  constructor
  · exact CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1)
      (P -> Q) (((!! P) ⟶ (!! Q)))
      (fun hPQ =>
        (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
          (GammaD1 := GammaD1) TT (!! P) (!! Q)).mpr
          (derivable1_trans (TT && (!! P)) (!! P) (!! Q)
            (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) TT (!! P))
            (CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) P (!! Q)
              (fun hP =>
                CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1)
                  Q TT (hPQ hP)))))
  · exact CoqPropImpDeduction.derivable1_coq_prop_impp
      (GammaD1 := GammaD1) P Q

end SLogicEquiv

end DeductionRules

end Unifysl
