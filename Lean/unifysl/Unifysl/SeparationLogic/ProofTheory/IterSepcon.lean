import Lean
import Unifysl.SeparationLogic.ProofTheory.Deduction
import Unifysl.SeparationLogic.ProofTheory.RewriteClass
import Unifysl.PropositionalLogic.ProofTheory.ProofTheoryPatterns

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `SeparationLogic/ProofTheory/IterSepcon.v`:
- Classes:
  `IterSepconAxiomatization_left`, `IterSepconDeduction_left`,
  `IterSepconDefinition_left`, `IterSepconDefinition_right`,
  `NormalIterWand`.
- Conversions and registration:
  `IterSepconDeduction_leftToIterSepconAxiomatization_left`,
  `reg_IterSepconDeduction_left2IterSepconAxiomatization_left`.
- Provable-level rules:
  `provable_iter_sepcon_spec_left`, `provable_iter_sepcon_spec_right`,
  `provable_sepcon_iter_sepcon`, `provable_iter_sepcon_unfold_right_assoc`,
  `provable_iter_sepcon_unfold_left_assoc`, `proper_iter_sepcon_impp`,
  `proper_iter_sepcon_iffp`, `proper_iter_sepcon_Permutation`.
- Derivable1-level rules:
  `derivable1_sepcon_iter_sepcon1`, `derivable1_sepcon_iter_sepcon2`.
- Definition-based constructors, normality lemmas, and tactic:
  `FoldLeftSepcon2IterSepcon`, `FoldRightSepcon2IterSepcon`,
  `FoldLeftSepcon2IterSepcon_Normal`,
  `FoldRightSepcon2IterSepcon_Normal`,
  `IterSepconFromDefToAX_L2L`, `IterSepconFromDefToAX_R2L`,
  `AddConnective_iter_sepcon`, `Wand2IterWand`,
  `Wand2IterWand_Normal`, `IterSepconFromDefToD1_L2L`,
  `IterSepconAxiomatization_left2IterSepconDeduction_left`.
-/

universe u

namespace Unifysl

open Relation_ext
open PropositionalLanguageNotation
open SeparationLogicNotation

private theorem provable_iffp_trans_iter {L : Language.{u}}
    [MinimumLanguage L] [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    [NegLanguage L] [IffLanguage L] [TrueLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
    [FalseAxiomatization L Gamma] [IntuitionisticNegAxiomatization L Gamma]
    [TrueAxiomatization L Gamma]
    {x y z : @Language.expr L} :
    (|-- (x ⟷ y)) -> (|-- (y ⟷ z)) -> |-- (x ⟷ z) := by
  intro hxy hyz
  exact provables_iffp_intros x z
    (solve_impp_trans x y z
      (provables_iffp_elim1 x y hxy)
      (provables_iffp_elim1 y z hyz))
    (solve_impp_trans z y x
      (provables_iffp_elim2 y z hyz)
      (provables_iffp_elim2 x y hxy))

private theorem provable_iffp_symm_iter {L : Language.{u}}
    [MinimumLanguage L] [AndLanguage L] [OrLanguage L] [FalseLanguage L]
    [NegLanguage L] [IffLanguage L] [TrueLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
    [FalseAxiomatization L Gamma] [IntuitionisticNegAxiomatization L Gamma]
    [TrueAxiomatization L Gamma]
    {x y : @Language.expr L} :
    (|-- (x ⟷ y)) -> |-- (y ⟷ x) := by
  intro hxy
  exact provables_iffp_intros y x
    (provables_iffp_elim2 x y hxy)
    (provables_iffp_elim1 x y hxy)

private theorem sepcon_LU_iter {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [SepconAxiomatization L Gamma]
    [EmpAxiomatization L Gamma] :
    ProofTheoryPatternsP.LeftUnit L Gamma emp sepcon := by
  constructor
  · intro x
    exact solve_impp_trans (emp * x) (x * emp) x
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) emp x)
      (EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) x)
  · intro x
    exact solve_impp_trans x (x * emp) (emp * x)
      (EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) x)
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) x emp)

private theorem sepcon_RU_iter {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [EmpAxiomatization L Gamma] :
    ProofTheoryPatternsP.RightUnit L Gamma emp sepcon := by
  constructor
  · intro x
    exact EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) x
  · intro x
    exact EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) x

class IterSepconAxiomatization_left (L : Language.{u}) [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
    (Gamma : Provable L) : Prop where
  provable_iter_sepcon_derives :
    forall xs : List (@Language.expr L),
      |-- (iter_sepcon xs ⟶ List.foldl sepcon emp xs)
  provable_derives_iter_sepcon :
    forall xs : List (@Language.expr L),
      |-- (List.foldl sepcon emp xs ⟶ iter_sepcon xs)

class IterSepconDeduction_left (L : Language.{u}) [SepconLanguage L]
    [EmpLanguage L] [IterSepconLanguage L] (Gamma : Derivable1 L) : Prop where
  derivable1_iter_sepcon_l :
    forall xs : List (@Language.expr L),
      iter_sepcon xs |-- List.foldl sepcon emp xs
  derivable1_iter_sepcon_r :
    forall xs : List (@Language.expr L),
      List.foldl sepcon emp xs |-- iter_sepcon xs

namespace IterSepconAxiomatization_left

theorem iter_sepcon_spec_left1 {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
    [Gamma : Provable L] [self : IterSepconAxiomatization_left L Gamma] :
    forall xs : List (@Language.expr L),
      |-- (iter_sepcon xs ⟶ List.foldl sepcon emp xs) :=
  provable_iter_sepcon_derives (Gamma := Gamma)

theorem iter_sepcon_spec_left2 {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
    [Gamma : Provable L] [self : IterSepconAxiomatization_left L Gamma] :
    forall xs : List (@Language.expr L),
      |-- (List.foldl sepcon emp xs ⟶ iter_sepcon xs) :=
  provable_derives_iter_sepcon (Gamma := Gamma)

end IterSepconAxiomatization_left

namespace IterSepconDeduction_left

theorem iter_sepcon_d1_left1 {L : Language.{u}} [SepconLanguage L]
    [EmpLanguage L] [IterSepconLanguage L] [Gamma : Derivable1 L]
    [self : IterSepconDeduction_left L Gamma] :
    forall xs : List (@Language.expr L),
      iter_sepcon xs |-- List.foldl sepcon emp xs :=
  derivable1_iter_sepcon_l (Gamma := Gamma)

theorem iter_sepcon_d1_left2 {L : Language.{u}} [SepconLanguage L]
    [EmpLanguage L] [IterSepconLanguage L] [Gamma : Derivable1 L]
    [self : IterSepconDeduction_left L Gamma] :
    forall xs : List (@Language.expr L),
      List.foldl sepcon emp xs |-- iter_sepcon xs :=
  derivable1_iter_sepcon_r (Gamma := Gamma)

end IterSepconDeduction_left

section IterSepconDeductionLeftToAxiomatizationLeft

variable {L : Language.{u}} [MinimumLanguage L]
variable [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
variable [GammaD1 : Derivable1 L] [GammaP : Provable L]
variable [SepconDeduction_weak L GammaD1]
variable [IterSepconDeduction_left L GammaD1]
variable [Derivable1Provable L GammaP GammaD1]

theorem IterSepconDeduction_leftToIterSepconAxiomatization_left :
    IterSepconAxiomatization_left L GammaP := by
  constructor
  · intro xs
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (iter_sepcon xs) (List.foldl sepcon emp xs)).mp
        (IterSepconDeduction_left.iter_sepcon_d1_left1
          (Gamma := GammaD1) xs)
  · intro xs
    exact (Derivable1Provable.derivable1_provable
      (L := L) (GammaP := GammaP) (GammaD := GammaD1)
      (List.foldl sepcon emp xs) (iter_sepcon xs)).mp
        (IterSepconDeduction_left.iter_sepcon_d1_left2
          (Gamma := GammaD1) xs)

end IterSepconDeductionLeftToAxiomatizationLeft

instance reg_IterSepconDeduction_left2IterSepconAxiomatization_left :
    RegisterClass D12P_reg
      (ProofRegistration.mk `iter_sepcon_AXL
        ``IterSepconDeduction_leftToIterSepconAxiomatization_left) 20 := {}

section IterSepconAXRules

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L]
variable [SepconLanguage L] [WandLanguage L] [EmpLanguage L]
variable [IterSepconLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]
variable [SepconAxiomatization L Gamma] [WandAxiomatization L Gamma]
variable [EmpAxiomatization L Gamma]
variable [IterSepconAxiomatization_left L Gamma]

theorem provable_iter_sepcon_spec_left :
    forall xs : List (@Language.expr L),
      |-- (iter_sepcon xs ⟷ List.foldl sepcon emp xs) := by
  intro xs
  exact provables_iffp_intros (iter_sepcon xs) (List.foldl sepcon emp xs)
    (IterSepconAxiomatization_left.iter_sepcon_spec_left1
      (Gamma := Gamma) xs)
    (IterSepconAxiomatization_left.iter_sepcon_spec_left2
      (Gamma := Gamma) xs)

theorem provable_iter_sepcon_spec_right :
    forall xs : List (@Language.expr L),
      |-- (iter_sepcon xs ⟷ List.foldr sepcon emp xs) := by
  intro xs
  letI : ProofTheoryPatternsP.Monotonicity L Gamma sepcon := sepcon_Mono
  letI : ProofTheoryPatternsP.Associativity L Gamma sepcon := sepcon_Assoc
  letI : ProofTheoryPatternsP.LeftUnit L Gamma emp sepcon := sepcon_LU_iter
  letI : ProofTheoryPatternsP.RightUnit L Gamma emp sepcon := sepcon_RU_iter
  have hleft : |-- (iter_sepcon xs ⟷ List.foldl sepcon emp xs) :=
    provable_iter_sepcon_spec_left xs
  have hfold : |-- (List.foldl sepcon emp xs ⟷ List.foldr sepcon emp xs) :=
    PropositionalLogic.ProofTheoryPatterns.P.assoc_fold_left_fold_right_equiv
      (prodp := sepcon) (e := emp) xs
  exact provable_iffp_trans_iter hleft hfold

theorem provable_sepcon_iter_sepcon :
    forall xs ys : List (@Language.expr L),
      |-- ((iter_sepcon xs * iter_sepcon ys) ⟷ iter_sepcon (xs ++ ys)) := by
  intro xs ys
  letI : ProofTheoryPatternsP.Monotonicity L Gamma sepcon := sepcon_Mono
  letI : ProofTheoryPatternsP.Associativity L Gamma sepcon := sepcon_Assoc
  letI : ProofTheoryPatternsP.LeftUnit L Gamma emp sepcon := sepcon_LU_iter
  letI : ProofTheoryPatternsP.RightUnit L Gamma emp sepcon := sepcon_RU_iter
  have hxy :
      |-- ((iter_sepcon xs * iter_sepcon ys) ⟷
        (List.foldl sepcon emp xs * List.foldl sepcon emp ys)) :=
      (provables_sepcon_proper_iffp (L := L) (Gamma := Gamma)).proper
      (iter_sepcon xs) (List.foldl sepcon emp xs)
      (provable_iter_sepcon_spec_left xs)
      (iter_sepcon ys) (List.foldl sepcon emp ys)
      (provable_iter_sepcon_spec_left ys)
  have hfold :
      |-- ((List.foldl sepcon emp xs * List.foldl sepcon emp ys) ⟷
        List.foldl sepcon emp (xs ++ ys)) :=
    PropositionalLogic.ProofTheoryPatterns.P.assoc_prodp_fold_left_equiv
      (prodp := sepcon) (e := emp) xs ys
  have htarget :
      |-- (List.foldl sepcon emp (xs ++ ys) ⟷ iter_sepcon (xs ++ ys)) :=
    provable_iffp_symm_iter (provable_iter_sepcon_spec_left (xs ++ ys))
  exact provable_iffp_trans_iter hxy (provable_iffp_trans_iter hfold htarget)

theorem provable_iter_sepcon_unfold_right_assoc :
    forall xs : List (@Language.expr L),
      |-- (iter_sepcon xs ⟷
        fold_right_prodp_no_unit
          sepcon emp xs) := by
  intro xs
  letI : ProofTheoryPatternsP.Monotonicity L Gamma sepcon := sepcon_Mono
  letI : ProofTheoryPatternsP.Associativity L Gamma sepcon := sepcon_Assoc
  letI : ProofTheoryPatternsP.LeftUnit L Gamma emp sepcon := sepcon_LU_iter
  letI : ProofTheoryPatternsP.RightUnit L Gamma emp sepcon := sepcon_RU_iter
  have hspec : |-- (iter_sepcon xs ⟷ List.foldr sepcon emp xs) :=
    provable_iter_sepcon_spec_right xs
  have hunfold :
      |-- (List.foldr sepcon emp xs ⟷
        fold_right_prodp_no_unit
          sepcon emp xs) :=
    PropositionalLogic.ProofTheoryPatterns.P.fold_right_prodp_unfold
      (prodp := sepcon) (e := emp) xs
  exact provable_iffp_trans_iter hspec hunfold

theorem provable_iter_sepcon_unfold_left_assoc :
    forall xs : List (@Language.expr L),
      |-- (iter_sepcon xs ⟷
        match xs with
        | [] => emp
        | x :: xs0 => List.foldl sepcon x xs0) := by
  intro xs
  letI : ProofTheoryPatternsP.Monotonicity L Gamma sepcon := sepcon_Mono
  letI : ProofTheoryPatternsP.LeftUnit L Gamma emp sepcon := sepcon_LU_iter
  have hleft : |-- (iter_sepcon xs ⟷ List.foldl sepcon emp xs) :=
    provable_iter_sepcon_spec_left xs
  simpa using
    (provable_iffp_trans_iter hleft
      (PropositionalLogic.ProofTheoryPatterns.P.fold_left_prodp_unfold
        (prodp := sepcon) (e := emp) xs))

private def provableImppRelIter : @Language.expr L -> @Language.expr L -> Prop :=
  fun x y => @Provable.provable L Gamma (x ⟶ y)

private def provableIffpRelIter : @Language.expr L -> @Language.expr L -> Prop :=
  fun x y => @Provable.provable L Gamma (x ⟷ y)

instance proper_iter_sepcon_impp :
    Proper
      (List.Forall₂ (provableImppRelIter (L := L) (Gamma := Gamma)) ==>
        provableImppRelIter (L := L) (Gamma := Gamma))
      (iter_sepcon (L := L)) where
  proper := by
    intro xs ys hxy
    have hsrc : |-- (iter_sepcon xs ⟷ List.foldl sepcon emp xs) :=
      provable_iter_sepcon_spec_left xs
    have hdst : |-- (iter_sepcon ys ⟷ List.foldl sepcon emp ys) :=
      provable_iter_sepcon_spec_left ys
    have hfold :
        |-- (List.foldl sepcon emp xs ⟶ List.foldl sepcon emp ys) :=
      letI : Proper
          (provableImppRelIter (L := L) (Gamma := Gamma) ==>
            provableImppRelIter (L := L) (Gamma := Gamma) ==>
            provableImppRelIter (L := L) (Gamma := Gamma)) sepcon := {
        proper := by
          intro x1 x2 hx y1 y2 hy
          exact SepconAxiomatization.sepcon_mono (Gamma := Gamma)
            x1 x2 y1 y2 hx hy
      }
      (proper_fold_left' (RA := provableImppRelIter (L := L) (Gamma := Gamma))
        (RB := provableImppRelIter (L := L) (Gamma := Gamma)) sepcon).proper
          xs ys hxy emp emp (provable_impp_refl emp)
    exact solve_impp_trans (iter_sepcon xs) (List.foldl sepcon emp xs) (iter_sepcon ys)
      (provables_iffp_elim1 (iter_sepcon xs) (List.foldl sepcon emp xs) hsrc)
      (solve_impp_trans (List.foldl sepcon emp xs) (List.foldl sepcon emp ys)
        (iter_sepcon ys) hfold
        (provables_iffp_elim2 (iter_sepcon ys) (List.foldl sepcon emp ys) hdst))

instance proper_iter_sepcon_iffp :
    Proper
      (List.Forall₂ (provableIffpRelIter (L := L) (Gamma := Gamma)) ==>
        provableIffpRelIter (L := L) (Gamma := Gamma))
      (iter_sepcon (L := L)) where
  proper := by
    intro xs ys hxy
    have hsrc : |-- (iter_sepcon xs ⟷ List.foldl sepcon emp xs) :=
      provable_iter_sepcon_spec_left xs
    have hdst : |-- (iter_sepcon ys ⟷ List.foldl sepcon emp ys) :=
      provable_iter_sepcon_spec_left ys
    have hfold :
        |-- (List.foldl sepcon emp xs ⟷ List.foldl sepcon emp ys) :=
      letI : Proper
          (provableIffpRelIter (L := L) (Gamma := Gamma) ==>
            provableIffpRelIter (L := L) (Gamma := Gamma) ==>
            provableIffpRelIter (L := L) (Gamma := Gamma)) sepcon := {
        proper := by
          intro x1 x2 hx y1 y2 hy
          exact provables_iffp_intros (x1 * y1) (x2 * y2)
            (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
              x1 x2 y1 y2
              (provables_iffp_elim1 x1 x2 hx)
              (provables_iffp_elim1 y1 y2 hy))
            (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
              x2 x1 y2 y1
              (provables_iffp_elim2 x1 x2 hx)
              (provables_iffp_elim2 y1 y2 hy))
      }
      (proper_fold_left' (RA := provableIffpRelIter (L := L) (Gamma := Gamma))
        (RB := provableIffpRelIter (L := L) (Gamma := Gamma)) sepcon).proper
          xs ys hxy emp emp (provable_iffp_refl emp)
    exact provable_iffp_trans_iter hsrc
      (provable_iffp_trans_iter hfold (provable_iffp_symm_iter hdst))

instance proper_iter_sepcon_Permutation :
    Proper (List.Perm ==> provableIffpRelIter (L := L) (Gamma := Gamma))
      (iter_sepcon (L := L)) where
  proper := by
    intro xs ys hperm
    letI : ProofTheoryPatternsP.Monotonicity L Gamma sepcon := sepcon_Mono
    letI : ProofTheoryPatternsP.Commutativity L Gamma sepcon := sepcon_Comm
    letI : ProofTheoryPatternsP.Associativity L Gamma sepcon := sepcon_Assoc
    have hsrc : |-- (iter_sepcon xs ⟷ List.foldl sepcon emp xs) :=
      provable_iter_sepcon_spec_left xs
    have hdst : |-- (iter_sepcon ys ⟷ List.foldl sepcon emp ys) :=
      provable_iter_sepcon_spec_left ys
    have hfold :
        |-- (List.foldl sepcon emp xs ⟷ List.foldl sepcon emp ys) :=
      PropositionalLogic.ProofTheoryPatterns.P.assoc_fold_left_Permutation
        (prodp := sepcon) (e := emp) emp xs ys hperm
    exact provable_iffp_trans_iter hsrc
      (provable_iffp_trans_iter hfold (provable_iffp_symm_iter hdst))

end IterSepconAXRules

section IterSepconD1Rules

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [SepconLanguage L] [EmpLanguage L]
variable [IterSepconLanguage L]
variable [GammaD1 : Derivable1 L]
variable [AndDeduction L GammaD1]
variable [ImpAndAdjointDeduction L GammaD1]
variable [SepconDeduction L GammaD1]
variable [EmpDeduction L GammaD1]
variable [IterSepconDeduction_left L GammaD1]
variable [BasicDeduction L GammaD1]

theorem derivable1_sepcon_iter_sepcon1 :
    forall xs ys : List (@Language.expr L),
      (iter_sepcon xs * iter_sepcon ys) |-- iter_sepcon (xs ++ ys) := by
  intro xs ys
  have hxs : iter_sepcon xs |-- List.foldl sepcon emp xs :=
    IterSepconDeduction_left.iter_sepcon_d1_left1 (Gamma := GammaD1) xs
  have hys : iter_sepcon ys |-- List.foldl sepcon emp ys :=
    IterSepconDeduction_left.iter_sepcon_d1_left1 (Gamma := GammaD1) ys
  have hfold :
      (List.foldl sepcon emp xs * List.foldl sepcon emp ys)
        |-- List.foldl sepcon emp (xs ++ ys) := by
    letI : ProofTheoryPatterns.D1.Monotonicity L GammaD1 sepcon := derivable1_sepcon_Mono
    letI : ProofTheoryPatterns.D1.Associativity L GammaD1 sepcon := derivable1_sepcon_Assoc
    letI : ProofTheoryPatterns.D1.LeftUnit L GammaD1 emp sepcon := derivable1_sepcon_LU
    letI : ProofTheoryPatterns.D1.RightUnit L GammaD1 emp sepcon := derivable1_sepcon_RU
    exact ProofTheoryPatterns.D1.assoc_prodp_fold_left
      (prodp := sepcon) (e := emp) xs ys
  have htarget : List.foldl sepcon emp (xs ++ ys) |-- iter_sepcon (xs ++ ys) :=
    IterSepconDeduction_left.iter_sepcon_d1_left2 (Gamma := GammaD1) (xs ++ ys)
  exact derivable1_trans (iter_sepcon xs * iter_sepcon ys)
    (List.foldl sepcon emp xs * List.foldl sepcon emp ys)
    (iter_sepcon (xs ++ ys))
    (SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
      (iter_sepcon xs) (List.foldl sepcon emp xs)
      (iter_sepcon ys) (List.foldl sepcon emp ys) hxs hys)
    (derivable1_trans (List.foldl sepcon emp xs * List.foldl sepcon emp ys)
      (List.foldl sepcon emp (xs ++ ys)) (iter_sepcon (xs ++ ys))
      hfold htarget)

theorem derivable1_sepcon_iter_sepcon2 :
    forall xs ys : List (@Language.expr L),
      iter_sepcon (xs ++ ys) |-- (iter_sepcon xs * iter_sepcon ys) := by
  intro xs ys
  have hsrc : iter_sepcon (xs ++ ys) |-- List.foldl sepcon emp (xs ++ ys) :=
    IterSepconDeduction_left.iter_sepcon_d1_left1 (Gamma := GammaD1) (xs ++ ys)
  have hfold :
      List.foldl sepcon emp (xs ++ ys)
        |-- (List.foldl sepcon emp xs * List.foldl sepcon emp ys) := by
    letI : ProofTheoryPatterns.D1.Monotonicity L GammaD1 sepcon := derivable1_sepcon_Mono
    letI : ProofTheoryPatterns.D1.Associativity L GammaD1 sepcon := derivable1_sepcon_Assoc
    letI : ProofTheoryPatterns.D1.LeftUnit L GammaD1 emp sepcon := derivable1_sepcon_LU
    letI : ProofTheoryPatterns.D1.RightUnit L GammaD1 emp sepcon := derivable1_sepcon_RU
    exact ProofTheoryPatterns.D1.assoc_fold_left_app
      (prodp := sepcon) (e := emp) xs ys
  have hxs : List.foldl sepcon emp xs |-- iter_sepcon xs :=
    IterSepconDeduction_left.iter_sepcon_d1_left2 (Gamma := GammaD1) xs
  have hys : List.foldl sepcon emp ys |-- iter_sepcon ys :=
    IterSepconDeduction_left.iter_sepcon_d1_left2 (Gamma := GammaD1) ys
  exact derivable1_trans (iter_sepcon (xs ++ ys))
    (List.foldl sepcon emp (xs ++ ys)) (iter_sepcon xs * iter_sepcon ys)
    hsrc
    (derivable1_trans (List.foldl sepcon emp (xs ++ ys))
      (List.foldl sepcon emp xs * List.foldl sepcon emp ys)
      (iter_sepcon xs * iter_sepcon ys)
      hfold
      (SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
        (List.foldl sepcon emp xs) (iter_sepcon xs)
        (List.foldl sepcon emp ys) (iter_sepcon ys) hxs hys))

end IterSepconD1Rules

class IterSepconDefinition_left (L : Language.{u}) [SepconLanguage L]
    [EmpLanguage L] [IterSepconLanguage L] : Prop where
  iter_sepcon_def_l :
    forall xs : List (@Language.expr L),
      iter_sepcon xs = List.foldl sepcon emp xs

class IterSepconDefinition_right (L : Language.{u}) [SepconLanguage L]
    [EmpLanguage L] [IterSepconLanguage L] : Prop where
  iter_sepcon_def_r :
    forall xs : List (@Language.expr L),
      iter_sepcon xs = List.foldr sepcon emp xs

def FoldLeftSepcon2IterSepcon {L : Language.{u}} [SepconLanguage L]
    [EmpLanguage L] : IterSepconLanguage L where
  iter_sepcon := fun xs => List.foldl sepcon emp xs

def FoldRightSepcon2IterSepcon {L : Language.{u}} [SepconLanguage L]
    [EmpLanguage L] : IterSepconLanguage L where
  iter_sepcon := fun xs => List.foldr sepcon emp xs

theorem FoldLeftSepcon2IterSepcon_Normal {L : Language.{u}}
    [SepconLanguage L] [EmpLanguage L] :
    @IterSepconDefinition_left L _ _
      (FoldLeftSepcon2IterSepcon (L := L) : IterSepconLanguage L) := by
  exact @IterSepconDefinition_left.mk L
    (inferInstance : SepconLanguage L) (inferInstance : EmpLanguage L)
    (FoldLeftSepcon2IterSepcon (L := L)) (by intro xs; rfl)

theorem FoldRightSepcon2IterSepcon_Normal {L : Language.{u}}
    [SepconLanguage L] [EmpLanguage L] :
    @IterSepconDefinition_right L _ _
      (FoldRightSepcon2IterSepcon (L := L) : IterSepconLanguage L) := by
  exact @IterSepconDefinition_right.mk L
    (inferInstance : SepconLanguage L) (inferInstance : EmpLanguage L)
    (FoldRightSepcon2IterSepcon (L := L)) (by intro xs; rfl)

theorem IterSepconFromDefToAX_L2L {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
    [GammaP : Provable L] [MinimumAxiomatization L GammaP]
    [IterSepconDefinition_left L] :
    IterSepconAxiomatization_left L GammaP := by
  constructor
  · intro xs
    rw [IterSepconDefinition_left.iter_sepcon_def_l xs]
    exact provable_impp_refl (List.foldl sepcon emp xs)
  · intro xs
    rw [IterSepconDefinition_left.iter_sepcon_def_l xs]
    exact provable_impp_refl (List.foldl sepcon emp xs)

theorem IterSepconFromDefToAX_R2L {L : Language.{u}} [MinimumLanguage L]
    [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
    [GammaP : Provable L] [MinimumAxiomatization L GammaP]
    [SepconAxiomatization L GammaP] [EmpAxiomatization L GammaP]
    [IterSepconDefinition_right L] :
    IterSepconAxiomatization_left L GammaP := by
  constructor
  · intro xs
    rw [IterSepconDefinition_right.iter_sepcon_def_r xs]
    letI : ProofTheoryPatternsP.Monotonicity L GammaP sepcon := sepcon_Mono
    letI : ProofTheoryPatternsP.Associativity L GammaP sepcon := sepcon_Assoc
    letI : ProofTheoryPatternsP.LeftUnit L GammaP emp sepcon := sepcon_LU_iter
    letI : ProofTheoryPatternsP.RightUnit L GammaP emp sepcon := sepcon_RU_iter
    exact ProofTheoryPatternsP.assoc_fold_right_fold_left
      (prodp := sepcon) (e := emp) xs
  · intro xs
    rw [IterSepconDefinition_right.iter_sepcon_def_r xs]
    letI : ProofTheoryPatternsP.Monotonicity L GammaP sepcon := sepcon_Mono
    letI : ProofTheoryPatternsP.Associativity L GammaP sepcon := sepcon_Assoc
    letI : ProofTheoryPatternsP.LeftUnit L GammaP emp sepcon := sepcon_LU_iter
    letI : ProofTheoryPatternsP.RightUnit L GammaP emp sepcon := sepcon_RU_iter
    exact ProofTheoryPatternsP.assoc_fold_left_fold_right
      (prodp := sepcon) (e := emp) xs

open Lean Meta Elab Tactic

syntax "AddConnective_iter_sepcon" : tactic

private def iterSepconLocalLanguage? (type : Expr) : MetaM Bool := do
  pure <| (← whnf type).isConstOf ``Language

private def findIterSepconLocalLanguage : TacticM (Name × Expr) := withMainContext do
  let lctx ← getLCtx
  let mut found : Array (Name × Expr) := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      if ← iterSepconLocalLanguage? decl.type then
        found := found.push (decl.userName, mkFVar decl.fvarId)
  match found.size with
  | 1 => pure found[0]!
  | 0 => throwError "AddConnective_iter_sepcon could not find a local `Language`"
  | _ => throwError "AddConnective_iter_sepcon found more than one local `Language`"

private def findIterSepconLocalProvableName (L : Expr) : TacticM Name :=
  withMainContext do
  let lctx ← getLCtx
  let mut found : Array Name := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      let type ← whnf decl.type
      if type.isAppOf ``Provable then
        let args := type.getAppArgs
        if args.size == 1 then
          if ← isDefEq args[0]! L then
            found := found.push decl.userName
  match found.size with
  | 1 => pure found[0]!
  | 0 => throwError
      "AddConnective_iter_sepcon could not find a local `Provable` for the current language"
  | _ => throwError
      "AddConnective_iter_sepcon found more than one local `Provable` for the current language"

private def iterSepconAssertLocalInstance
    (baseName : Name) (type value : Expr) : TacticM FVarId :=
  withMainContext do
    let userName ← mkFreshUserName baseName
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    if type.hasExprMVar || value.hasExprMVar then
      throwError "local instance {userName} contains unresolved metavariables"
    let goal ← getMainGoal
    let (ids, goal) ← goal.assertHypotheses #[
      { userName := userName
        type := type
        value := value
        binderInfo := BinderInfo.instImplicit
        kind := LocalDeclKind.default }]
    replaceMainGoal [goal]
    withMainContext do
      discard <| synthInstance type
    pure ids[0]!

private def iterSepconAssertLocalInstanceFromSyntax
    (baseName : Name) (typeStx valueStx : TSyntax `term) : TacticM FVarId :=
  withMainContext do
  let userName ← mkFreshUserName baseName
  let type ← Term.elabType typeStx
  let value ← Term.elabTerm valueStx (some type)
  iterSepconAssertLocalInstance userName type value

private def addConnectiveIterSepcon : TacticM PUnit := withMainContext do
  let (LName, LExpr) ← findIterSepconLocalLanguage
  let GammaPName ← findIterSepconLocalProvableName LExpr
  let LId := mkIdent LName
  let GammaPId := mkIdent GammaPName
  discard <| iterSepconAssertLocalInstanceFromSyntax `iter_sepcon_L
    (← `(IterSepconLanguage $LId))
    (← `(FoldLeftSepcon2IterSepcon (L := $LId)))
  discard <| iterSepconAssertLocalInstanceFromSyntax `iter_sepcon_DL
    (← `(IterSepconDefinition_left $LId))
    (← `(FoldLeftSepcon2IterSepcon_Normal (L := $LId)))
  discard <| iterSepconAssertLocalInstanceFromSyntax `iter_sepcon_AXL
    (← `(IterSepconAxiomatization_left $LId $GammaPId))
    (← `(IterSepconFromDefToAX_L2L (L := $LId) (GammaP := $GammaPId)))

elab "AddConnective_iter_sepcon" : tactic => addConnectiveIterSepcon

class NormalIterWand (L : Language.{u}) [WandLanguage L]
    [IterWandLanguage L] : Prop where
  iter_wand_def :
    forall (xs : List (@Language.expr L)) (y : @Language.expr L),
      iter_wand xs y = List.foldr wand y xs

def Wand2IterWand {L : Language.{u}} [WandLanguage L] : IterWandLanguage L where
  iter_wand := fun xs y => List.foldr wand y xs

theorem Wand2IterWand_Normal {L : Language.{u}} [WandLanguage L] :
    @NormalIterWand L _ (Wand2IterWand (L := L) : IterWandLanguage L) := by
  exact @NormalIterWand.mk L (inferInstance : WandLanguage L)
    (Wand2IterWand (L := L)) (by intro xs y; rfl)

theorem IterSepconFromDefToD1_L2L {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [AndDeduction L GammaD1] [ImpAndAdjointDeduction L GammaD1]
    [IterSepconDefinition_left L] :
    IterSepconDeduction_left L GammaD1 := by
  constructor
  · intro xs
    rw [IterSepconDefinition_left.iter_sepcon_def_l xs]
    exact derivable1_refl (List.foldl sepcon emp xs)
  · intro xs
    rw [IterSepconDefinition_left.iter_sepcon_def_l xs]
    exact derivable1_refl (List.foldl sepcon emp xs)

theorem IterSepconAxiomatization_left2IterSepconDeduction_left
    {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
    [EmpLanguage L] [IterSepconLanguage L] [IterSepconDefinition_left L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [MinimumDeduction L GammaD1] [SepconDeduction L GammaD1] :
    IterSepconDeduction_left L GammaD1 := by
  letI GammaP : Provable L := Derivable12Provable (L := L)
  letI GammaPD1 : ProvableFromDerivable1 L GammaP GammaD1 :=
    Derivable12Provable_Normal (L := L)
  letI GammaD1P : Derivable1FromProvable L GammaP GammaD1 :=
    Deduction2Axiomatization_GammaD1P'
      (L := L) (GammaP := GammaP) (GammaD1 := GammaD1)
  letI minAX : MinimumAxiomatization L GammaP :=
    Deduction2Axiomatization_minAX'
      (L := L) (GammaP := GammaP) (GammaD1 := GammaD1)
  letI iterAX : IterSepconAxiomatization_left L GammaP :=
    IterSepconFromDefToAX_L2L (L := L) (GammaP := GammaP)
  constructor
  · intro xs
    exact (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1)
      (iter_sepcon xs) (List.foldl sepcon emp xs)).mpr
        (IterSepconAxiomatization_left.provable_iter_sepcon_derives
          (Gamma := GammaP) xs)
  · intro xs
    exact (__derivable1_provable (GammaP := GammaP) (GammaD := GammaD1)
      (List.foldl sepcon emp xs) (iter_sepcon xs)).mpr
        (IterSepconAxiomatization_left.provable_derives_iter_sepcon
          (Gamma := GammaP) xs)

end Unifysl
