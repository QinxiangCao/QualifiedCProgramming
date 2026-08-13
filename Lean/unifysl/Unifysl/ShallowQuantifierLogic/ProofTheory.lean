import Unifysl.ShallowQuantifierLogic.Syntax
import Unifysl.GeneralLogic.ProofTheory.BasicLogicEquiv
import Unifysl.SeparationLogic.ProofTheory.IterSepcon
import Unifysl.MetaLogicInj.ProofTheory.ProofRules

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `unifysl-prp/ShallowQuantifierLogic/ProofTheory.v`.

Active classes:
- `ShallowExistsDeduction`, 8.20 projection names
  `derivable1s_exp_r`, `derivable1s_exp_l`
- `ShallowForallDeduction`, 8.20 projection names
  `derivable1s_allp_r`, `derivable1s_allp_l`
- `deduction_exp_and`, 8.20 projection names
  `derivable1_exp_andp_l`, `derivable1_andp_exp_l`
- `deduction_exp_sepcon`, 8.20 projection names
  `derivable1_exp_sepcon_l`, `derivable1_sepcon_exp_l`
- `IterSepconFlatten`, 8.20 projection name
  `derivable1_iter_sepcon_flatten`
- `sepcon_andp_prop` and `sepcon_andp_prop_ext`, 8.20 projection names
  beginning with `derivable1_`
- `Iter_sepcon_andp_prop`, 8.20 projection name
  `derivable1_iter_sepcon_coq_prop_andp_l`

Active declarations:
- `ex_and0`, `ex_and1'`, `ex_and2'`, `ex_and1_`, `ex_and2_`,
  `ExpDeduction2ExsitsAnd`
- `ex_sepcon1_`, `ex_sepcon2_`, `ExpDeduction2ExsitsSepcon`
- `fold_left_prop`, `fold_left_sepcon_cong`, `derivable1_sepcon_assoc2`,
  `fold_left_prop_sepcon1`, `fold_left_prop_sepcon2`, `itersepcon_cons`,
  `itersepcon_cons1`, `itersepcon_cons2`, `itersepcon_app`,
  `itersepcon_app1`, `itersepcon_app2`, `itersepcon_flatten_`,
  `DeductionSepconFlatten`, `itersepcon_ex`
- `sepcon_andp_prop1_` through `sepcon_andp_prop8_`,
  `Derived_sepcon_andp_prop`, `Derived_sepcon_andp_prop_ext`
- `iter_sepcon_andp_prop_`, `Derived_iter_sepcon_andp_prop`
-/

universe u v

namespace Unifysl

open PropositionalLanguageNotation
open SeparationLogicNotation
open CoqPropInLogicNotation

class ShallowExistsDeduction (L : Language.{u}) [ShallowExistsLanguage L]
    (Gamma : Derivable1 L) : Prop where
  shallow_exp_right :
    forall {A : Type v} (P : @Language.expr L) (Q : A -> @Language.expr L)
      (x : A), P |-- Q x -> P |-- exp Q
  shallow_exp_left :
    forall {A : Type v} (P : A -> @Language.expr L) (Q : @Language.expr L),
      (forall x, P x |-- Q) -> exp P |-- Q

class ShallowForallDeduction (L : Language.{u}) [ShallowForallLanguage L]
    (Gamma : Derivable1 L) : Prop where
  shallow_all_right :
    forall {A : Type v} (P : @Language.expr L) (Q : A -> @Language.expr L),
      (forall x, P |-- Q x) -> P |-- allp Q
  shallow_all_left :
    forall {A : Type v} (P : A -> @Language.expr L)
      (Q : @Language.expr L) (x : A), P x |-- Q -> allp P |-- Q

theorem derivable1s_exp_r {L : Language.{u}} [ShallowExistsLanguage L]
    [Gamma : Derivable1 L] [ShallowExistsDeduction L Gamma] :
    forall {A : Type v} (P : @Language.expr L) (Q : A -> @Language.expr L)
      (x : A), P |-- Q x -> P |-- exp Q :=
  ShallowExistsDeduction.shallow_exp_right (Gamma := Gamma)

theorem derivable1s_exp_l {L : Language.{u}} [ShallowExistsLanguage L]
    [Gamma : Derivable1 L] [ShallowExistsDeduction L Gamma] :
    forall {A : Type v} (P : A -> @Language.expr L) (Q : @Language.expr L),
      (forall x, P x |-- Q) -> exp P |-- Q :=
  ShallowExistsDeduction.shallow_exp_left (Gamma := Gamma)

theorem derivable1s_allp_r {L : Language.{u}} [ShallowForallLanguage L]
    [Gamma : Derivable1 L] [ShallowForallDeduction L Gamma] :
    forall {A : Type v} (P : @Language.expr L) (Q : A -> @Language.expr L),
      (forall x, P |-- Q x) -> P |-- allp Q :=
  ShallowForallDeduction.shallow_all_right (Gamma := Gamma)

theorem derivable1s_allp_l {L : Language.{u}} [ShallowForallLanguage L]
    [Gamma : Derivable1 L] [ShallowForallDeduction L Gamma] :
    forall {A : Type v} (P : A -> @Language.expr L)
      (Q : @Language.expr L) (x : A), P x |-- Q -> allp P |-- Q :=
  ShallowForallDeduction.shallow_all_left (Gamma := Gamma)

section ExistsAllDeductionRules

variable {L : Language.{u}}
variable [ShallowExistsLanguage L] [ShallowForallLanguage L]
variable [Gamma : Derivable1 L] [BasicDeduction L Gamma]
variable [ShallowExistsDeduction L Gamma] [ShallowForallDeduction L Gamma]

theorem derivable1s_ex_l_unfold :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exists x, P x |-- Q) -> allp P |-- Q := by
  intro A P Q h
  rcases h with ⟨x, hx⟩
  exact derivable1s_allp_l (P := P) (Q := Q) x hx

theorem derivable1_allp_allp_swap :
    forall (A : Type v) (B : Type v) (P : A -> B -> @Language.expr L),
      allp (fun x => allp (fun y => P x y)) |--
        allp (fun y => allp (fun x => P x y)) := by
  intro A B P
  apply derivable1s_allp_r
  intro y
  apply derivable1s_allp_r
  intro x
  exact derivable1_trans
    (allp (fun x => allp (fun y => P x y)))
    (allp (fun y => P x y)) (P x y)
    (derivable1s_allp_l
      (P := fun x : A => allp (fun y : B => P x y))
      (Q := allp (fun y : B => P x y)) x
      (derivable1_refl (allp (fun y : B => P x y))))
    (derivable1s_allp_l
      (P := fun y : B => P x y) (Q := P x y) y
      (derivable1_refl (P x y)))

theorem derivable1_exp_allp_swap :
    forall (A : Type v) (B : Type v) (P : A -> B -> @Language.expr L),
      exp (fun x => allp (fun y => P x y)) |--
        allp (fun y => exp (fun x => P x y)) := by
  intro A B P
  apply derivable1s_allp_r
  intro y
  apply derivable1s_exp_l
  intro x
  exact derivable1s_exp_r
    (P := allp (fun y : B => P x y))
    (Q := fun x : A => P x y) x
    (derivable1s_allp_l
      (P := fun y : B => P x y) (Q := P x y) y
      (derivable1_refl (P x y)))

end ExistsAllDeductionRules

section ExistsDeductionRulesAnd

variable {L : Language.{u}}
variable [MinimumLanguage L] [AndLanguage L] [ShallowExistsLanguage L]
variable [Gamma : Derivable1 L]
variable [AndDeduction L Gamma] [BasicDeduction L Gamma]
variable [ShallowExistsDeduction L Gamma]
variable [ImpAndAdjointDeduction L Gamma]

theorem ex_and0 :
    forall {A : Type v} (P Q : A -> @Language.expr L),
      exp (fun a => P a && Q a) |-- (exp P && exp Q) := by
  intro A P Q
  apply AndDeduction.derivable1s_truep_intros
  · exact ShallowExistsDeduction.shallow_exp_left
      (Gamma := Gamma) (fun a : A => P a && Q a) (exp P)
      (fun a =>
        derivable1_trans (P a && Q a) (P a) (exp P)
          (AndDeduction.derivable1_andp_elim1 (GammaD1 := Gamma) (P a) (Q a))
          (ShallowExistsDeduction.shallow_exp_right
            (Gamma := Gamma) (P a) P a (derivable1_refl (P a))))
  · exact ShallowExistsDeduction.shallow_exp_left
      (Gamma := Gamma) (fun a : A => P a && Q a) (exp Q)
      (fun a =>
        derivable1_trans (P a && Q a) (Q a) (exp Q)
          (AndDeduction.derivable1_andp_elim2 (GammaD1 := Gamma) (P a) (Q a))
          (ShallowExistsDeduction.shallow_exp_right
            (Gamma := Gamma) (Q a) Q a (derivable1_refl (Q a))))

theorem ex_and1' :
    forall {A : Type v} (P : A -> @Language.expr L) (Q : @Language.expr L),
      exp (fun x => P x && Q) |-- (exp P && Q) := by
  intro A P Q
  apply AndDeduction.derivable1s_truep_intros
  · exact ShallowExistsDeduction.shallow_exp_left
      (Gamma := Gamma) (fun x : A => P x && Q) (exp P)
      (fun x =>
        derivable1_trans (P x && Q) (P x) (exp P)
          (AndDeduction.derivable1_andp_elim1 (GammaD1 := Gamma) (P x) Q)
          (ShallowExistsDeduction.shallow_exp_right
            (Gamma := Gamma) (P x) P x (derivable1_refl (P x))))
  · exact ShallowExistsDeduction.shallow_exp_left
      (Gamma := Gamma) (fun x : A => P x && Q) Q
      (fun x => AndDeduction.derivable1_andp_elim2
        (GammaD1 := Gamma) (P x) Q)

theorem ex_and2' :
    forall {A : Type v} (P : @Language.expr L) (Q : A -> @Language.expr L),
      exp (fun x => P && Q x) |-- (P && exp Q) := by
  intro A P Q
  apply AndDeduction.derivable1s_truep_intros
  · exact ShallowExistsDeduction.shallow_exp_left
      (Gamma := Gamma) (fun x : A => P && Q x) P
      (fun x => AndDeduction.derivable1_andp_elim1
        (GammaD1 := Gamma) P (Q x))
  · exact ShallowExistsDeduction.shallow_exp_left
      (Gamma := Gamma) (fun x : A => P && Q x) (exp Q)
      (fun x =>
        derivable1_trans (P && Q x) (Q x) (exp Q)
          (AndDeduction.derivable1_andp_elim2 (GammaD1 := Gamma) P (Q x))
          (ShallowExistsDeduction.shallow_exp_right
            (Gamma := Gamma) (Q x) Q x (derivable1_refl (Q x))))

theorem ex_and1_ :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exp P && Q) |-- exp (fun x => P x && Q) := by
  intro A P Q
  have h :
      exp P |-- (Q ⟶ exp (fun x => P x && Q)) := by
    exact ShallowExistsDeduction.shallow_exp_left
      (Gamma := Gamma) P (Q ⟶ exp (fun x => P x && Q))
      (fun x =>
        (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
          (GammaD1 := Gamma) (P x) Q (exp (fun x => P x && Q))).mpr
          (ShallowExistsDeduction.shallow_exp_right
            (Gamma := Gamma) (P x && Q) (fun x => P x && Q) x
            (AndDeduction.derivable1s_truep_intros
              (GammaD1 := Gamma) (P x && Q) (P x) Q
              (AndDeduction.derivable1_andp_elim1 (GammaD1 := Gamma) (P x) Q)
              (AndDeduction.derivable1_andp_elim2 (GammaD1 := Gamma) (P x) Q))))
  exact (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := Gamma) (exp P) Q (exp (fun x => P x && Q))).mp h

theorem ex_and2_ :
    forall (A : Type v) (P : @Language.expr L) (Q : A -> @Language.expr L),
      (P && exp Q) |-- exp (fun x => P && Q x) := by
  intro A P Q
  exact derivable1_trans (P && exp Q) (exp Q && P)
    (exp (fun x => P && Q x))
    (derivable1_andp_comm P (exp Q))
    (by
      have h :
          exp Q |-- (P ⟶ exp (fun x => P && Q x)) := by
        exact ShallowExistsDeduction.shallow_exp_left
          (Gamma := Gamma) Q (P ⟶ exp (fun x => P && Q x))
          (fun x =>
            (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
              (GammaD1 := Gamma) (Q x) P (exp (fun x => P && Q x))).mpr
              (ShallowExistsDeduction.shallow_exp_right
                (Gamma := Gamma) (Q x && P) (fun x => P && Q x) x
                (AndDeduction.derivable1s_truep_intros
                  (GammaD1 := Gamma) (Q x && P) P (Q x)
                  (AndDeduction.derivable1_andp_elim2
                    (GammaD1 := Gamma) (Q x) P)
                  (AndDeduction.derivable1_andp_elim1
                    (GammaD1 := Gamma) (Q x) P))))
      exact (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
        (GammaD1 := Gamma) (exp Q) P (exp (fun x => P && Q x))).mp h)

class deduction_exp_and : Prop where
  ex_and1 :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exp P && Q) |-- exp (fun x => P x && Q)
  ex_and2 :
    forall (A : Type v) (P : @Language.expr L) (Q : A -> @Language.expr L),
      (P && exp Q) |-- exp (fun x => P && Q x)

theorem ExpDeduction2ExsitsAnd : deduction_exp_and (L := L) := by
  constructor
  · exact ex_and1_
  · exact ex_and2_

theorem aux_ex_and0 :
    forall {A : Type v} (P Q : A -> @Language.expr L),
      exp (fun a => P a && Q a) |-- (exp P && exp Q) :=
  ex_and0 (Gamma := Gamma)

theorem aux_ex_and1' :
    forall {A : Type v} (P : A -> @Language.expr L) (Q : @Language.expr L),
      exp (fun x => P x && Q) |-- (exp P && Q) :=
  ex_and1' (Gamma := Gamma)

theorem aux_ex_and2' :
    forall {A : Type v} (P : @Language.expr L) (Q : A -> @Language.expr L),
      exp (fun x => P && Q x) |-- (P && exp Q) :=
  ex_and2' (Gamma := Gamma)

theorem aux_ex_and1_ :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exp P && Q) |-- exp (fun x => P x && Q) :=
  ex_and1_ (Gamma := Gamma)

theorem aux_ex_and2_ :
    forall (A : Type v) (P : @Language.expr L) (Q : A -> @Language.expr L),
      (P && exp Q) |-- exp (fun x => P && Q x) :=
  ex_and2_ (Gamma := Gamma)

theorem derivable1_exp_andp_l [deduction_exp_and (L := L)] :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exp P && Q) |-- exp (fun x => P x && Q) :=
  deduction_exp_and.ex_and1 (L := L)

theorem derivable1_andp_exp_l [deduction_exp_and (L := L)] :
    forall (A : Type v) (P : @Language.expr L) (Q : A -> @Language.expr L),
      (P && exp Q) |-- exp (fun x => P && Q x) :=
  deduction_exp_and.ex_and2 (L := L)

theorem logic_equiv_exp_andp {GammaE : LogicEquiv L}
    [EquivDerivable1 L Gamma GammaE] :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      logic_equiv (L := L) (exp P && Q) (exp (fun x => P x && Q)) := by
  intro A P Q
  exact (__logic_equiv_derivable1 (GammaD := Gamma) (GammaE := GammaE)
    (exp P && Q) (exp (fun x => P x && Q))).mpr
      ⟨ex_and1_ A P Q, ex_and1' P Q⟩

end ExistsDeductionRulesAnd

section ExistsDeductionRulesSepcon

variable {L : Language.{u}}
variable [SepconLanguage L] [WandLanguage L] [ShallowExistsLanguage L]
variable [Gamma : Derivable1 L]
variable [SepconDeduction L Gamma] [BasicDeduction L Gamma]
variable [ShallowExistsDeduction L Gamma] [WandDeduction L Gamma]

theorem ex_sepcon1_ :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exp P * Q) |-- exp (fun x => P x * Q) := by
  intro A P Q
  have h :
      exp P |-- (Q -* exp (fun x => P x * Q)) := by
    exact ShallowExistsDeduction.shallow_exp_left
      (Gamma := Gamma) P (Q -* exp (fun x => P x * Q))
      (fun x =>
        (WandDeduction.derivable1_wand_sepcon_adjoint
          (GammaD1 := Gamma) (P x) Q (exp (fun x => P x * Q))).mp
          (ShallowExistsDeduction.shallow_exp_right
            (Gamma := Gamma) (P x * Q) (fun x => P x * Q) x
            (SepconDeduction.derivable1_sepcon_mono
              (GammaD1 := Gamma) (P x) (P x) Q Q
              (derivable1_refl (P x)) (derivable1_refl Q))))
  exact (WandDeduction.derivable1_wand_sepcon_adjoint
    (GammaD1 := Gamma) (exp P) Q (exp (fun x => P x * Q))).mpr h

theorem ex_sepcon2_ :
    forall (A : Type v) (P : @Language.expr L) (Q : A -> @Language.expr L),
      (P * exp Q) |-- exp (fun x => P * Q x) := by
  intro A P Q
  exact derivable1_trans (P * exp Q) (exp Q * P)
    (exp (fun x => P * Q x))
    (SepconDeduction.derivable1_sepcon_comm (GammaD1 := Gamma) P (exp Q))
    (by
      have h :
          exp Q |-- (P -* exp (fun x => P * Q x)) := by
        exact ShallowExistsDeduction.shallow_exp_left
          (Gamma := Gamma) Q (P -* exp (fun x => P * Q x))
          (fun x =>
            (WandDeduction.derivable1_wand_sepcon_adjoint
              (GammaD1 := Gamma) (Q x) P (exp (fun x => P * Q x))).mp
              (ShallowExistsDeduction.shallow_exp_right
                (Gamma := Gamma) (Q x * P) (fun x => P * Q x) x
                (derivable1_trans (Q x * P) (P * Q x) (P * Q x)
                  (SepconDeduction.derivable1_sepcon_comm
                    (GammaD1 := Gamma) (Q x) P)
                  (SepconDeduction.derivable1_sepcon_mono
                    (GammaD1 := Gamma) P P (Q x) (Q x)
                    (derivable1_refl P) (derivable1_refl (Q x))))))
      exact (WandDeduction.derivable1_wand_sepcon_adjoint
        (GammaD1 := Gamma) (exp Q) P (exp (fun x => P * Q x))).mpr h)

class deduction_exp_sepcon : Prop where
  ex_sepcon1 :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exp P * Q) |-- exp (fun x => P x * Q)
  ex_sepcon2 :
    forall (A : Type v) (P : @Language.expr L) (Q : A -> @Language.expr L),
      (P * exp Q) |-- exp (fun x => P * Q x)

theorem ExpDeduction2ExsitsSepcon : deduction_exp_sepcon (L := L) := by
  constructor
  · exact ex_sepcon1_
  · exact ex_sepcon2_

theorem __derivable1_exp_sepcon_l :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exp P * Q) |-- exp (fun x => P x * Q) :=
  ex_sepcon1_ (Gamma := Gamma)

theorem __derivable1_sepcon_exp_l :
    forall (A : Type v) (P : @Language.expr L) (Q : A -> @Language.expr L),
      (P * exp Q) |-- exp (fun x => P * Q x) :=
  ex_sepcon2_ (Gamma := Gamma)

theorem derivable1_exp_sepcon_l [deduction_exp_sepcon (L := L)] :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      (exp P * Q) |-- exp (fun x => P x * Q) :=
  deduction_exp_sepcon.ex_sepcon1 (L := L)

theorem derivable1_sepcon_exp_l [deduction_exp_sepcon (L := L)] :
    forall (A : Type v) (P : @Language.expr L) (Q : A -> @Language.expr L),
      (P * exp Q) |-- exp (fun x => P * Q x) :=
  deduction_exp_sepcon.ex_sepcon2 (L := L)

theorem logic_equiv_exp_sepcon {GammaE : LogicEquiv L}
    [EquivDerivable1 L Gamma GammaE] :
    forall (A : Type v) (P : A -> @Language.expr L) (Q : @Language.expr L),
      logic_equiv (L := L) (exp P * Q) (exp (fun x => P x * Q)) := by
  intro A P Q
  have hrev : exp (fun x => P x * Q) |-- (exp P * Q) := by
    apply derivable1s_exp_l
    intro x
    exact SepconDeduction.derivable1_sepcon_mono
      (GammaD1 := Gamma) (P x) (exp P) Q Q
      (derivable1s_exp_r (P := P x) (Q := P) x
        (derivable1_refl (P x)))
      (derivable1_refl Q)
  exact (__logic_equiv_derivable1 (GammaD := Gamma) (GammaE := GammaE)
    (exp P * Q) (exp (fun x => P x * Q))).mpr
      ⟨ex_sepcon1_ A P Q, hrev⟩

end ExistsDeductionRulesSepcon

section IterSepconDerivedRules

variable {L : Language.{u}}
variable [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
variable [GammaD1 : Derivable1 L]
variable [BasicDeduction L GammaD1]
variable [SepconDeduction L GammaD1]
variable [EmpDeduction L GammaD1]
variable [IterSepconDeduction_left L GammaD1]

theorem fold_left_prop :
    forall {A : Type v} (f : A -> A -> A) (a b : A) (l : List A),
      (forall x y z, f (f x y) z = f x (f y z)) ->
        List.foldl f (f a b) l = f a (List.foldl f b l) := by
  intro A f a b l hassoc
  induction l generalizing a b with
  | nil => rfl
  | cons a' l ih =>
      simp [List.foldl]
      rw [ih (f a b) a']
      rw [hassoc]
      rw [ih b a']

theorem fold_left_sepcon_cong :
    forall (l : List (@Language.expr L)) (a b : @Language.expr L),
      a |-- b -> List.foldl sepcon a l |-- List.foldl sepcon b l := by
  intro l
  induction l with
  | nil =>
      intro a b h
      simpa using h
  | cons a' l ih =>
      intro a b h
      simpa [List.foldl] using
        ih (a * a') (b * a')
          (SepconDeduction.derivable1_sepcon_mono
            (GammaD1 := GammaD1) a b a' a' h (derivable1_refl a'))

private theorem derivable1_sepcon_assoc2_local :
    forall a b c : @Language.expr L, ((a * b) * c) |-- (a * (b * c)) := by
  exact Unifysl.derivable1_sepcon_assoc2

theorem fold_left_prop_sepcon1 :
    forall (a b : @Language.expr L) (l : List (@Language.expr L)),
      List.foldl sepcon (a * b) l |-- (a * List.foldl sepcon b l) := by
  intro a b l
  induction l generalizing a b with
  | nil => exact derivable1_refl (a * b)
  | cons a' l ih =>
      simpa [List.foldl] using
        derivable1_trans (List.foldl sepcon ((a * b) * a') l)
          (List.foldl sepcon (a * (b * a')) l)
          (a * List.foldl sepcon (b * a') l)
          (fold_left_sepcon_cong l ((a * b) * a') (a * (b * a'))
            (derivable1_sepcon_assoc2_local a b a'))
          (ih a (b * a'))

theorem fold_left_prop_sepcon2 :
    forall (a b : @Language.expr L) (l : List (@Language.expr L)),
      (a * List.foldl sepcon b l) |-- List.foldl sepcon (a * b) l := by
  intro a b l
  induction l generalizing a b with
  | nil => exact derivable1_refl (a * b)
  | cons a' l ih =>
      simpa [List.foldl] using
        derivable1_trans (a * List.foldl sepcon (b * a') l)
          (List.foldl sepcon (a * (b * a')) l)
          (List.foldl sepcon ((a * b) * a') l)
          (ih a (b * a'))
          (fold_left_sepcon_cong l (a * (b * a')) ((a * b) * a')
            (SepconDeduction.derivable1_sepcon_assoc1
              (GammaD1 := GammaD1) a b a'))

theorem itersepcon_cons :
    forall (a : @Language.expr L) (l : List (@Language.expr L)),
      iter_sepcon (a :: l) |-- (a * iter_sepcon l) ∧
      (a * iter_sepcon l) |-- iter_sepcon (a :: l) := by
  intro a l
  constructor
  · have h1 :
        iter_sepcon (a :: l) |-- List.foldl sepcon emp (a :: l) :=
      IterSepconDeduction_left.iter_sepcon_d1_left1
        (Gamma := GammaD1) (a :: l)
    have h2 :
        List.foldl sepcon emp (a :: l) |-- List.foldl sepcon (a * emp) l :=
      by
        simpa [List.foldl] using
          fold_left_sepcon_cong l (emp * a) (a * emp)
            (SepconDeduction.derivable1_sepcon_comm
              (GammaD1 := GammaD1) emp a)
    have h3 :
        List.foldl sepcon (a * emp) l |-- (a * List.foldl sepcon emp l) :=
      fold_left_prop_sepcon1 a emp l
    have h4 :
        (a * List.foldl sepcon emp l) |-- (a * iter_sepcon l) :=
      SepconDeduction.derivable1_sepcon_mono
        (GammaD1 := GammaD1) a a (List.foldl sepcon emp l) (iter_sepcon l)
        (derivable1_refl a)
        (IterSepconDeduction_left.iter_sepcon_d1_left2
          (Gamma := GammaD1) l)
    exact derivable1_trans (iter_sepcon (a :: l))
      (List.foldl sepcon emp (a :: l)) (a * iter_sepcon l) h1
      (derivable1_trans (List.foldl sepcon emp (a :: l))
        (List.foldl sepcon (a * emp) l) (a * iter_sepcon l) h2
        (derivable1_trans (List.foldl sepcon (a * emp) l)
          (a * List.foldl sepcon emp l) (a * iter_sepcon l) h3 h4))
  · have h1 :
        (a * iter_sepcon l) |-- (a * List.foldl sepcon emp l) :=
      SepconDeduction.derivable1_sepcon_mono
        (GammaD1 := GammaD1) a a (iter_sepcon l) (List.foldl sepcon emp l)
        (derivable1_refl a)
        (IterSepconDeduction_left.iter_sepcon_d1_left1
          (Gamma := GammaD1) l)
    have h2 :
        (a * List.foldl sepcon emp l) |-- List.foldl sepcon (a * emp) l :=
      fold_left_prop_sepcon2 a emp l
    have h3 :
        List.foldl sepcon (a * emp) l |-- List.foldl sepcon emp (a :: l) :=
      by
        simpa [List.foldl] using
          fold_left_sepcon_cong l (a * emp) (emp * a)
            (SepconDeduction.derivable1_sepcon_comm
              (GammaD1 := GammaD1) a emp)
    have h4 :
        List.foldl sepcon emp (a :: l) |-- iter_sepcon (a :: l) :=
      IterSepconDeduction_left.iter_sepcon_d1_left2
        (Gamma := GammaD1) (a :: l)
    exact derivable1_trans (a * iter_sepcon l)
      (a * List.foldl sepcon emp l) (iter_sepcon (a :: l)) h1
      (derivable1_trans (a * List.foldl sepcon emp l)
        (List.foldl sepcon (a * emp) l) (iter_sepcon (a :: l)) h2
        (derivable1_trans (List.foldl sepcon (a * emp) l)
          (List.foldl sepcon emp (a :: l)) (iter_sepcon (a :: l)) h3 h4))

def itersepcon_cons1 :=
  fun (a : @Language.expr L) (l : List (@Language.expr L)) =>
    (itersepcon_cons a l).left

def itersepcon_cons2 :=
  fun (a : @Language.expr L) (l : List (@Language.expr L)) =>
    (itersepcon_cons a l).right

theorem itersepcon_app :
    forall l1 l2 : List (@Language.expr L),
      (iter_sepcon l1 * iter_sepcon l2) |-- iter_sepcon (l1 ++ l2) ∧
      iter_sepcon (l1 ++ l2) |-- (iter_sepcon l1 * iter_sepcon l2) := by
  intro l1
  induction l1 with
  | nil =>
      intro l2
      constructor
      · have h :
            (iter_sepcon [] * iter_sepcon l2) |--
              (emp * iter_sepcon l2) :=
          SepconDeduction.derivable1_sepcon_mono
            (GammaD1 := GammaD1) (iter_sepcon []) emp
            (iter_sepcon l2) (iter_sepcon l2)
            (by
              simpa [List.foldl] using
                IterSepconDeduction_left.iter_sepcon_d1_left1
                  (Gamma := GammaD1) ([] : List (@Language.expr L)))
            (derivable1_refl (iter_sepcon l2))
        exact derivable1_trans (iter_sepcon [] * iter_sepcon l2)
          (emp * iter_sepcon l2) (iter_sepcon ([] ++ l2)) h
          (by
            simpa using
              derivable1_trans (emp * iter_sepcon l2)
                (iter_sepcon l2 * emp) (iter_sepcon l2)
                (SepconDeduction.derivable1_sepcon_comm
                  (GammaD1 := GammaD1) emp (iter_sepcon l2))
                (EmpDeduction.sepcon_emp_left
                  (GammaD1 := GammaD1) (iter_sepcon l2)))
      · have h :
            iter_sepcon ([] ++ l2) |-- (emp * iter_sepcon l2) := by
          simpa using
            derivable1_trans (iter_sepcon l2)
              (iter_sepcon l2 * emp) (emp * iter_sepcon l2)
              (EmpDeduction.sepcon_emp_right
                (GammaD1 := GammaD1) (iter_sepcon l2))
              (SepconDeduction.derivable1_sepcon_comm
                (GammaD1 := GammaD1) (iter_sepcon l2) emp)
        exact derivable1_trans (iter_sepcon ([] ++ l2))
          (emp * iter_sepcon l2) (iter_sepcon [] * iter_sepcon l2)
          h
          (SepconDeduction.derivable1_sepcon_mono
            (GammaD1 := GammaD1) emp (iter_sepcon [])
            (iter_sepcon l2) (iter_sepcon l2)
            (by
              simpa [List.foldl] using
                IterSepconDeduction_left.iter_sepcon_d1_left2
                  (Gamma := GammaD1) ([] : List (@Language.expr L)))
            (derivable1_refl (iter_sepcon l2)))
  | cons a l1 ih =>
      intro l2
      constructor
      · have h1 :
            (iter_sepcon (a :: l1) * iter_sepcon l2) |--
              ((a * iter_sepcon l1) * iter_sepcon l2) :=
          SepconDeduction.derivable1_sepcon_mono
            (GammaD1 := GammaD1) (iter_sepcon (a :: l1))
            (a * iter_sepcon l1) (iter_sepcon l2) (iter_sepcon l2)
            (itersepcon_cons1 a l1) (derivable1_refl (iter_sepcon l2))
        have h2 :
            ((a * iter_sepcon l1) * iter_sepcon l2) |--
              (a * (iter_sepcon l1 * iter_sepcon l2)) :=
          derivable1_sepcon_assoc2_local a (iter_sepcon l1) (iter_sepcon l2)
        have h3 :
            (a * (iter_sepcon l1 * iter_sepcon l2)) |--
              (a * iter_sepcon (l1 ++ l2)) :=
          SepconDeduction.derivable1_sepcon_mono
            (GammaD1 := GammaD1) a a
            (iter_sepcon l1 * iter_sepcon l2) (iter_sepcon (l1 ++ l2))
            (derivable1_refl a) (ih l2).left
        have h4 :
            (a * iter_sepcon (l1 ++ l2)) |--
              iter_sepcon (a :: (l1 ++ l2)) :=
          itersepcon_cons2 a (l1 ++ l2)
        exact derivable1_trans (iter_sepcon (a :: l1) * iter_sepcon l2)
          ((a * iter_sepcon l1) * iter_sepcon l2)
          (iter_sepcon ((a :: l1) ++ l2)) h1
          (by
            simpa [List.cons_append] using
              derivable1_trans ((a * iter_sepcon l1) * iter_sepcon l2)
                (a * (iter_sepcon l1 * iter_sepcon l2))
                (iter_sepcon (a :: (l1 ++ l2))) h2
                (derivable1_trans (a * (iter_sepcon l1 * iter_sepcon l2))
                  (a * iter_sepcon (l1 ++ l2))
                  (iter_sepcon (a :: (l1 ++ l2))) h3 h4))
      · have h1 :
          iter_sepcon ((a :: l1) ++ l2) |--
              (a * iter_sepcon (l1 ++ l2)) := by
          simpa [List.cons_append] using
            itersepcon_cons1 a (l1 ++ l2)
        have h2 :
            (a * iter_sepcon (l1 ++ l2)) |--
              (a * (iter_sepcon l1 * iter_sepcon l2)) :=
          SepconDeduction.derivable1_sepcon_mono
            (GammaD1 := GammaD1) a a
            (iter_sepcon (l1 ++ l2)) (iter_sepcon l1 * iter_sepcon l2)
            (derivable1_refl a) (ih l2).right
        have h3 :
            (a * (iter_sepcon l1 * iter_sepcon l2)) |--
              ((a * iter_sepcon l1) * iter_sepcon l2) :=
          SepconDeduction.derivable1_sepcon_assoc1
            (GammaD1 := GammaD1) a (iter_sepcon l1) (iter_sepcon l2)
        have h4 :
            ((a * iter_sepcon l1) * iter_sepcon l2) |--
              (iter_sepcon (a :: l1) * iter_sepcon l2) :=
          SepconDeduction.derivable1_sepcon_mono
            (GammaD1 := GammaD1) (a * iter_sepcon l1)
            (iter_sepcon (a :: l1)) (iter_sepcon l2) (iter_sepcon l2)
            (itersepcon_cons2 a l1) (derivable1_refl (iter_sepcon l2))
        exact derivable1_trans (iter_sepcon ((a :: l1) ++ l2))
          (a * iter_sepcon (l1 ++ l2))
          (iter_sepcon (a :: l1) * iter_sepcon l2) h1
          (derivable1_trans (a * iter_sepcon (l1 ++ l2))
            (a * (iter_sepcon l1 * iter_sepcon l2))
            (iter_sepcon (a :: l1) * iter_sepcon l2) h2
            (derivable1_trans (a * (iter_sepcon l1 * iter_sepcon l2))
              ((a * iter_sepcon l1) * iter_sepcon l2)
              (iter_sepcon (a :: l1) * iter_sepcon l2) h3 h4))

def itersepcon_app1 :=
  fun (l1 l2 : List (@Language.expr L)) => (itersepcon_app l1 l2).left

def itersepcon_app2 :=
  fun (l1 l2 : List (@Language.expr L)) => (itersepcon_app l1 l2).right

theorem itersepcon_flatten_ :
    forall xs1 xs2 xs3 : List (@Language.expr L),
      iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)) |--
      iter_sepcon (xs1 ++ xs2 ++ xs3) := by
  intro xs1
  induction xs1 with
  | nil =>
      intro xs2 xs3
      simpa using
        derivable1_trans
          (iter_sepcon (iter_sepcon xs2 :: xs3))
          (iter_sepcon xs2 * iter_sepcon xs3)
          (iter_sepcon (xs2 ++ xs3))
          (itersepcon_cons1 (iter_sepcon xs2) xs3)
          (itersepcon_app1 xs2 xs3)
  | cons a xs1 ih =>
      intro xs2 xs3
      have h1 :
          iter_sepcon ((a :: xs1) ++ (iter_sepcon xs2 :: xs3)) |--
            (a * iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3))) := by
        simpa [List.cons_append] using
          itersepcon_cons1 a (xs1 ++ (iter_sepcon xs2 :: xs3))
      have h2 :
          (a * iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3))) |--
            (a * iter_sepcon (xs1 ++ xs2 ++ xs3)) :=
        SepconDeduction.derivable1_sepcon_mono
          (GammaD1 := GammaD1) a a
          (iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)))
          (iter_sepcon (xs1 ++ xs2 ++ xs3))
          (derivable1_refl a) (ih xs2 xs3)
      have h3 :
          (a * iter_sepcon (xs1 ++ xs2 ++ xs3)) |--
            iter_sepcon (a :: (xs1 ++ xs2 ++ xs3)) :=
        itersepcon_cons2 a (xs1 ++ xs2 ++ xs3)
      exact derivable1_trans
        (iter_sepcon ((a :: xs1) ++ (iter_sepcon xs2 :: xs3)))
        (a * iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)))
        (iter_sepcon ((a :: xs1) ++ xs2 ++ xs3))
        h1
        (by
          simpa [List.cons_append, List.append_assoc] using
            derivable1_trans
              (a * iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)))
              (a * iter_sepcon (xs1 ++ xs2 ++ xs3))
              (iter_sepcon (a :: (xs1 ++ xs2 ++ xs3))) h2 h3)

class IterSepconFlatten : Prop where
  iter_sepcon_flatten :
    forall xs1 xs2 xs3 : List (@Language.expr L),
      iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)) |--
      iter_sepcon (xs1 ++ xs2 ++ xs3)

theorem derivable1_iter_sepcon_flatten [IterSepconFlatten (L := L)] :
    forall xs1 xs2 xs3 : List (@Language.expr L),
      iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)) |--
      iter_sepcon (xs1 ++ xs2 ++ xs3) :=
  IterSepconFlatten.iter_sepcon_flatten (L := L)

theorem DeductionSepconFlatten : IterSepconFlatten (L := L) := by
  constructor
  exact itersepcon_flatten_

section ExistsAndProp

variable [ShallowExistsLanguage L] [ShallowExistsDeduction L GammaD1]
variable [deduction_exp_sepcon (L := L)]

theorem itersepcon_ex {A : Type v} :
    forall (xs1 : List (@Language.expr L)) (x : A -> @Language.expr L)
      (xs3 : List (@Language.expr L)),
      iter_sepcon (xs1 ++ (exp x :: xs3)) |--
      exp (fun a => iter_sepcon (xs1 ++ (x a :: xs3))) := by
  intro xs1 x xs3
  have h1 :
      iter_sepcon (xs1 ++ (exp x :: xs3)) |--
        (iter_sepcon xs1 * iter_sepcon (exp x :: xs3)) :=
    itersepcon_app2 xs1 (exp x :: xs3)
  have h2 :
      (iter_sepcon xs1 * iter_sepcon (exp x :: xs3)) |--
        (iter_sepcon xs1 * (exp x * iter_sepcon xs3)) :=
    SepconDeduction.derivable1_sepcon_mono
      (GammaD1 := GammaD1) (iter_sepcon xs1) (iter_sepcon xs1)
      (iter_sepcon (exp x :: xs3)) (exp x * iter_sepcon xs3)
      (derivable1_refl (iter_sepcon xs1)) (itersepcon_cons1 (exp x) xs3)
  have h3 :
      (iter_sepcon xs1 * (exp x * iter_sepcon xs3)) |--
        ((iter_sepcon xs1 * exp x) * iter_sepcon xs3) :=
    SepconDeduction.derivable1_sepcon_assoc1
      (GammaD1 := GammaD1) (iter_sepcon xs1) (exp x) (iter_sepcon xs3)
  have h4' :
      ((iter_sepcon xs1 * exp x) * iter_sepcon xs3) |--
        exp (fun a => (iter_sepcon xs1 * x a) * iter_sepcon xs3) := by
    exact derivable1_trans
      ((iter_sepcon xs1 * exp x) * iter_sepcon xs3)
      (exp (fun a => iter_sepcon xs1 * x a) * iter_sepcon xs3)
      (exp (fun a => (iter_sepcon xs1 * x a) * iter_sepcon xs3))
      (SepconDeduction.derivable1_sepcon_mono
        (GammaD1 := GammaD1) (iter_sepcon xs1 * exp x)
        (exp (fun a => iter_sepcon xs1 * x a))
        (iter_sepcon xs3) (iter_sepcon xs3)
        (deduction_exp_sepcon.ex_sepcon2
          (A := A) (P := iter_sepcon xs1) (Q := x))
        (derivable1_refl (iter_sepcon xs3)))
      (deduction_exp_sepcon.ex_sepcon1
        (A := A) (P := fun a => iter_sepcon xs1 * x a)
        (Q := iter_sepcon xs3))
  have h5 :
      exp (fun a => (iter_sepcon xs1 * x a) * iter_sepcon xs3) |--
        exp (fun a => iter_sepcon (xs1 ++ (x a :: xs3))) := by
    apply ShallowExistsDeduction.shallow_exp_left
    intro a
    apply ShallowExistsDeduction.shallow_exp_right
    have hs1 :
        ((iter_sepcon xs1 * x a) * iter_sepcon xs3) |--
          (iter_sepcon xs1 * (x a * iter_sepcon xs3)) :=
      derivable1_sepcon_assoc2_local (iter_sepcon xs1) (x a) (iter_sepcon xs3)
    have hs2 :
        (iter_sepcon xs1 * (x a * iter_sepcon xs3)) |--
          (iter_sepcon xs1 * iter_sepcon (x a :: xs3)) :=
      SepconDeduction.derivable1_sepcon_mono
        (GammaD1 := GammaD1) (iter_sepcon xs1) (iter_sepcon xs1)
        (x a * iter_sepcon xs3) (iter_sepcon (x a :: xs3))
        (derivable1_refl (iter_sepcon xs1)) (itersepcon_cons2 (x a) xs3)
    have hs3 :
        (iter_sepcon xs1 * iter_sepcon (x a :: xs3)) |--
          iter_sepcon (xs1 ++ (x a :: xs3)) :=
      itersepcon_app1 xs1 (x a :: xs3)
    exact derivable1_trans ((iter_sepcon xs1 * x a) * iter_sepcon xs3)
      (iter_sepcon xs1 * (x a * iter_sepcon xs3))
      (iter_sepcon (xs1 ++ (x a :: xs3))) hs1
      (derivable1_trans (iter_sepcon xs1 * (x a * iter_sepcon xs3))
        (iter_sepcon xs1 * iter_sepcon (x a :: xs3))
        (iter_sepcon (xs1 ++ (x a :: xs3))) hs2 hs3)
  exact derivable1_trans (iter_sepcon (xs1 ++ (exp x :: xs3)))
    (iter_sepcon xs1 * iter_sepcon (exp x :: xs3))
    (exp (fun a => iter_sepcon (xs1 ++ (x a :: xs3)))) h1
    (derivable1_trans (iter_sepcon xs1 * iter_sepcon (exp x :: xs3))
      (iter_sepcon xs1 * (exp x * iter_sepcon xs3))
      (exp (fun a => iter_sepcon (xs1 ++ (x a :: xs3)))) h2
      (derivable1_trans (iter_sepcon xs1 * (exp x * iter_sepcon xs3))
        ((iter_sepcon xs1 * exp x) * iter_sepcon xs3)
        (exp (fun a => iter_sepcon (xs1 ++ (x a :: xs3)))) h3
        (derivable1_trans
          ((iter_sepcon xs1 * exp x) * iter_sepcon xs3)
          (exp (fun a => (iter_sepcon xs1 * x a) * iter_sepcon xs3))
          (exp (fun a => iter_sepcon (xs1 ++ (x a :: xs3)))) h4' h5)))

end ExistsAndProp

end IterSepconDerivedRules

section SepconAndpPropRules

variable {L : Language.{u}}
variable [SepconLanguage L] [TrueLanguage L] [CoqPropLanguage L]
variable [MinimumLanguage L] [AndLanguage L] [WandLanguage L]
variable [GammaD1 : Derivable1 L]
variable [BasicDeduction L GammaD1] [SepconDeduction L GammaD1]
variable [TrueDeduction L GammaD1] [CoqPropDeduction L GammaD1]
variable [AndDeduction L GammaD1] [ImpAndAdjointDeduction L GammaD1]
variable [WandDeduction L GammaD1]

theorem sepcon_andp_prop1_ :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      (P * ((!! Q) && R)) |-- ((!! Q) && (P * R)) := by
  intro P Q R
  apply AndDeduction.derivable1s_truep_intros
  · have hq_to_wand : (!! Q) |-- (P -* (!! Q)) :=
      CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) Q (P -* (!! Q))
        (fun hQ =>
          (WandDeduction.derivable1_wand_sepcon_adjoint
            (GammaD1 := GammaD1) TT P (!! Q)).mp
            (CoqPropDeduction.coq_prop_right
              (GammaD1 := GammaD1) Q (TT * P) hQ))
    have hand_to_wand : ((!! Q) && R) |-- (P -* (!! Q)) :=
      derivable1_trans (((!! Q) && R)) (!! Q) (P -* (!! Q))
        (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) (!! Q) R)
        hq_to_wand
    have hcomm : (P * ((!! Q) && R)) |-- (((!! Q) && R) * P) :=
      SepconDeduction.derivable1_sepcon_comm
        (GammaD1 := GammaD1) P (((!! Q) && R))
    exact derivable1_trans (P * ((!! Q) && R)) (((!! Q) && R) * P)
      (!! Q) hcomm
      ((WandDeduction.derivable1_wand_sepcon_adjoint
        (GammaD1 := GammaD1) (((!! Q) && R)) P (!! Q)).mpr
        hand_to_wand)
  · exact SepconDeduction.derivable1_sepcon_mono
      (GammaD1 := GammaD1) P P (((!! Q) && R)) R
      (derivable1_refl P)
      (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) (!! Q) R)

theorem sepcon_andp_prop2_ :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((!! Q) && (P * R)) |-- (P * ((!! Q) && R)) := by
  intro P Q R
  have hmeta :
      (!! Q) |-- ((P * R) ⟶ (P * ((!! Q) && R))) := by
    exact CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) Q
      ((P * R) ⟶ (P * ((!! Q) && R)))
      (fun hQ =>
        (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
          (GammaD1 := GammaD1) TT (P * R) (P * ((!! Q) && R))).mpr
          (derivable1_trans (TT && (P * R)) (P * R)
            (P * ((!! Q) && R))
            (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) TT (P * R))
            (SepconDeduction.derivable1_sepcon_mono
              (GammaD1 := GammaD1) P P R ((!! Q) && R)
              (derivable1_refl P)
              (AndDeduction.derivable1s_truep_intros
                (GammaD1 := GammaD1) R (!! Q) R
                (CoqPropDeduction.coq_prop_right
                  (GammaD1 := GammaD1) Q R hQ)
                (derivable1_refl R)))))
  exact (ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint
    (GammaD1 := GammaD1) (!! Q) (P * R) (P * ((!! Q) && R))).mp hmeta

class sepcon_andp_prop : Prop where
  sepcon_andp_prop1 :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      (P * ((!! Q) && R)) |-- ((!! Q) && (P * R))
  sepcon_andp_prop2 :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((!! Q) && (P * R)) |-- (P * ((!! Q) && R))

theorem derivable1_sepcon_coq_prop_andp_l [sepcon_andp_prop (L := L)] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      (P * ((!! Q) && R)) |-- ((!! Q) && (P * R)) :=
  sepcon_andp_prop.sepcon_andp_prop1 (L := L)

theorem derivable1_sepcon_coq_prop_andp_r [sepcon_andp_prop (L := L)] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((!! Q) && (P * R)) |-- (P * ((!! Q) && R)) :=
  sepcon_andp_prop.sepcon_andp_prop2 (L := L)

theorem sepcon_andp_prop3_ [sepcon_andp_prop (L := L)] :
    forall (P Q : @Language.expr L) (R : Prop),
      (P * (Q && (!! R))) |-- ((!! R) && (P * Q)) := by
  intro P Q R
  exact derivable1_trans (P * (Q && (!! R)))
    (P * ((!! R) && Q)) ((!! R) && (P * Q))
    (SepconDeduction.derivable1_sepcon_mono
      (GammaD1 := GammaD1) P P (Q && (!! R)) ((!! R) && Q)
      (derivable1_refl P) (derivable1_andp_comm Q (!! R)))
    (sepcon_andp_prop.sepcon_andp_prop1 (P := P) (Q := R) (R := Q))

theorem sepcon_andp_prop4_ [sepcon_andp_prop (L := L)] :
    forall (P Q : @Language.expr L) (R : Prop),
      ((!! R) && (P * Q)) |-- (P * (Q && (!! R))) := by
  intro P Q R
  exact derivable1_trans ((!! R) && (P * Q))
    (P * ((!! R) && Q)) (P * (Q && (!! R)))
    (sepcon_andp_prop.sepcon_andp_prop2 (P := P) (Q := R) (R := Q))
    (SepconDeduction.derivable1_sepcon_mono
      (GammaD1 := GammaD1) P P ((!! R) && Q) (Q && (!! R))
      (derivable1_refl P) (derivable1_andp_comm (!! R) Q))

theorem sepcon_andp_prop5_ [sepcon_andp_prop (L := L)] :
    forall (P : Prop) (Q R : @Language.expr L),
      (((!! P) && Q) * R) |-- ((!! P) && (Q * R)) := by
  intro P Q R
  exact derivable1_trans (((!! P) && Q) * R)
    (R * ((!! P) && Q)) ((!! P) && (Q * R))
    (SepconDeduction.derivable1_sepcon_comm
      (GammaD1 := GammaD1) (((!! P) && Q)) R)
    (derivable1_trans (R * ((!! P) && Q)) ((!! P) && (R * Q))
      ((!! P) && (Q * R))
      (sepcon_andp_prop.sepcon_andp_prop1 (P := R) (Q := P) (R := Q))
      (AndDeduction.derivable1s_truep_intros
        (GammaD1 := GammaD1) ((!! P) && (R * Q)) (!! P) (Q * R)
        (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1)
          (!! P) (R * Q))
        (derivable1_trans ((!! P) && (R * Q)) (R * Q) (Q * R)
          (AndDeduction.derivable1_andp_elim2
            (GammaD1 := GammaD1) (!! P) (R * Q))
          (SepconDeduction.derivable1_sepcon_comm
            (GammaD1 := GammaD1) R Q))))

theorem sepcon_andp_prop6_ [sepcon_andp_prop (L := L)] :
    forall (P : Prop) (Q R : @Language.expr L),
      ((!! P) && (Q * R)) |-- (((!! P) && Q) * R) := by
  intro P Q R
  exact derivable1_trans ((!! P) && (Q * R)) ((!! P) && (R * Q))
    (((!! P) && Q) * R)
    (AndDeduction.derivable1s_truep_intros
      (GammaD1 := GammaD1) ((!! P) && (Q * R)) (!! P) (R * Q)
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1)
        (!! P) (Q * R))
      (derivable1_trans ((!! P) && (Q * R)) (Q * R) (R * Q)
        (AndDeduction.derivable1_andp_elim2
          (GammaD1 := GammaD1) (!! P) (Q * R))
        (SepconDeduction.derivable1_sepcon_comm
          (GammaD1 := GammaD1) Q R)))
    (derivable1_trans ((!! P) && (R * Q)) (R * ((!! P) && Q))
      (((!! P) && Q) * R)
      (sepcon_andp_prop.sepcon_andp_prop2 (P := R) (Q := P) (R := Q))
      (SepconDeduction.derivable1_sepcon_comm
        (GammaD1 := GammaD1) R (((!! P) && Q))))

theorem sepcon_andp_prop7_ [sepcon_andp_prop (L := L)] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((P && (!! Q)) * R) |-- ((!! Q) && (P * R)) := by
  intro P Q R
  exact derivable1_trans ((P && (!! Q)) * R) (((!! Q) && P) * R)
    ((!! Q) && (P * R))
    (SepconDeduction.derivable1_sepcon_mono
      (GammaD1 := GammaD1) (P && (!! Q)) ((!! Q) && P) R R
      (derivable1_andp_comm P (!! Q)) (derivable1_refl R))
    (sepcon_andp_prop5_ (P := Q) (Q := P) (R := R))

theorem sepcon_andp_prop8_ [sepcon_andp_prop (L := L)] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((!! Q) && (P * R)) |-- ((P && (!! Q)) * R) := by
  intro P Q R
  exact derivable1_trans ((!! Q) && (P * R))
    (((!! Q) && P) * R) ((P && (!! Q)) * R)
    (sepcon_andp_prop6_ (P := Q) (Q := P) (R := R))
    (SepconDeduction.derivable1_sepcon_mono
      (GammaD1 := GammaD1) ((!! Q) && P) (P && (!! Q)) R R
      (derivable1_andp_comm (!! Q) P) (derivable1_refl R))

theorem aux_derivable1_sepcon_coq_prop_andp_l :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      (P * ((!! Q) && R)) |-- ((!! Q) && (P * R)) :=
  sepcon_andp_prop1_ (GammaD1 := GammaD1)

theorem aux_derivable1_sepcon_coq_prop_andp_r :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((!! Q) && (P * R)) |-- (P * ((!! Q) && R)) :=
  sepcon_andp_prop2_ (GammaD1 := GammaD1)

theorem aux_derivable1_sepcon_andp_coq_prop_l [sepcon_andp_prop (L := L)] :
    forall (P Q : @Language.expr L) (R : Prop),
      (P * (Q && (!! R))) |-- ((!! R) && (P * Q)) :=
  sepcon_andp_prop3_ (GammaD1 := GammaD1)

theorem aux_derivable1_sepcon_andp_coq_prop_r [sepcon_andp_prop (L := L)] :
    forall (P Q : @Language.expr L) (R : Prop),
      ((!! R) && (P * Q)) |-- (P * (Q && (!! R))) :=
  sepcon_andp_prop4_ (GammaD1 := GammaD1)

theorem aux_derivable1_coq_prop_andp_sepcon_l [sepcon_andp_prop (L := L)] :
    forall (P : Prop) (Q R : @Language.expr L),
      (((!! P) && Q) * R) |-- ((!! P) && (Q * R)) :=
  sepcon_andp_prop5_ (GammaD1 := GammaD1)

theorem aux_derivable1_coq_prop_andp_sepcon_r [sepcon_andp_prop (L := L)] :
    forall (P : Prop) (Q R : @Language.expr L),
      ((!! P) && (Q * R)) |-- (((!! P) && Q) * R) :=
  sepcon_andp_prop6_ (GammaD1 := GammaD1)

theorem aux_derivable1_andp_coq_prop_sepcon_l [sepcon_andp_prop (L := L)] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((P && (!! Q)) * R) |-- ((!! Q) && (P * R)) :=
  sepcon_andp_prop7_ (GammaD1 := GammaD1)

theorem aux_derivable1_andp_coq_prop_sepcon_r [sepcon_andp_prop (L := L)] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((!! Q) && (P * R)) |-- ((P && (!! Q)) * R) :=
  sepcon_andp_prop8_ (GammaD1 := GammaD1)

class sepcon_andp_prop_ext : Prop where
  sepcon_andp_prop3 :
    forall (P Q : @Language.expr L) (R : Prop),
      (P * (Q && (!! R))) |-- ((!! R) && (P * Q))
  sepcon_andp_prop4 :
    forall (P Q : @Language.expr L) (R : Prop),
      ((!! R) && (P * Q)) |-- (P * (Q && (!! R)))
  sepcon_andp_prop5 :
    forall (P : Prop) (Q R : @Language.expr L),
      (((!! P) && Q) * R) |-- ((!! P) && (Q * R))
  sepcon_andp_prop6 :
    forall (P : Prop) (Q R : @Language.expr L),
      ((!! P) && (Q * R)) |-- (((!! P) && Q) * R)
  sepcon_andp_prop7 :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((P && (!! Q)) * R) |-- ((!! Q) && (P * R))
  sepcon_andp_prop8 :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((!! Q) && (P * R)) |-- ((P && (!! Q)) * R)

theorem derivable1_sepcon_andp_coq_prop_l
    [sepcon_andp_prop_ext (L := L)] :
    forall (P Q : @Language.expr L) (R : Prop),
      (P * (Q && (!! R))) |-- ((!! R) && (P * Q)) :=
  sepcon_andp_prop_ext.sepcon_andp_prop3 (L := L)

theorem derivable1_sepcon_andp_coq_prop_r
    [sepcon_andp_prop_ext (L := L)] :
    forall (P Q : @Language.expr L) (R : Prop),
      ((!! R) && (P * Q)) |-- (P * (Q && (!! R))) :=
  sepcon_andp_prop_ext.sepcon_andp_prop4 (L := L)

theorem derivable1_coq_prop_andp_sepcon_l
    [sepcon_andp_prop_ext (L := L)] :
    forall (P : Prop) (Q R : @Language.expr L),
      (((!! P) && Q) * R) |-- ((!! P) && (Q * R)) :=
  sepcon_andp_prop_ext.sepcon_andp_prop5 (L := L)

theorem derivable1_coq_prop_andp_sepcon_r
    [sepcon_andp_prop_ext (L := L)] :
    forall (P : Prop) (Q R : @Language.expr L),
      ((!! P) && (Q * R)) |-- (((!! P) && Q) * R) :=
  sepcon_andp_prop_ext.sepcon_andp_prop6 (L := L)

theorem derivable1_andp_coq_prop_sepcon_l
    [sepcon_andp_prop_ext (L := L)] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((P && (!! Q)) * R) |-- ((!! Q) && (P * R)) :=
  sepcon_andp_prop_ext.sepcon_andp_prop7 (L := L)

theorem derivable1_andp_coq_prop_sepcon_r
    [sepcon_andp_prop_ext (L := L)] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      ((!! Q) && (P * R)) |-- ((P && (!! Q)) * R) :=
  sepcon_andp_prop_ext.sepcon_andp_prop8 (L := L)

theorem logic_equiv_sepcon_coq_prop_andp {GammaE : LogicEquiv L}
    [EquivDerivable1 L GammaD1 GammaE] :
    forall (P : @Language.expr L) (Q : Prop) (R : @Language.expr L),
      logic_equiv (L := L) (P * ((!! Q) && R)) ((!! Q) && (P * R)) := by
  intro P Q R
  exact (__logic_equiv_derivable1 (GammaD := GammaD1) (GammaE := GammaE)
    (P * ((!! Q) && R)) ((!! Q) && (P * R))).mpr
      ⟨sepcon_andp_prop1_ P Q R, sepcon_andp_prop2_ P Q R⟩

theorem logic_equiv_coq_prop_andp_sepcon {GammaE : LogicEquiv L}
    [EquivDerivable1 L GammaD1 GammaE] [sepcon_andp_prop (L := L)] :
    forall (P : Prop) (Q R : @Language.expr L),
      logic_equiv (L := L) (((!! P) && Q) * R) ((!! P) && (Q * R)) := by
  intro P Q R
  exact (__logic_equiv_derivable1 (GammaD := GammaD1) (GammaE := GammaE)
    (((!! P) && Q) * R) ((!! P) && (Q * R))).mpr
      ⟨sepcon_andp_prop5_ P Q R, sepcon_andp_prop6_ P Q R⟩

theorem logic_equiv_coq_prop_andp_sepcon_truep {GammaE : LogicEquiv L}
    [EquivDerivable1 L GammaD1 GammaE] :
  forall (P : @Language.expr L) (Q : Prop),
      logic_equiv (L := L) (P * (!! Q)) ((!! Q) && (P * TT)) := by
  intro P Q
  have htoAnd : (P * (!! Q)) |-- (P * ((!! Q) && TT)) :=
    SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
      P P (!! Q) ((!! Q) && TT)
      (derivable1_refl P)
      (AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1)
        (!! Q) (!! Q) TT
        (derivable1_refl (!! Q))
        (TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) (!! Q)))
  have hfromAnd : (P * ((!! Q) && TT)) |-- ((!! Q) && (P * TT)) :=
    sepcon_andp_prop1_ P Q TT
  have hbackAnd : ((!! Q) && (P * TT)) |-- (P * ((!! Q) && TT)) :=
    sepcon_andp_prop2_ P Q TT
  have hback : (P * ((!! Q) && TT)) |-- (P * (!! Q)) :=
    SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1)
      P P ((!! Q) && TT) (!! Q)
      (derivable1_refl P)
      (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) (!! Q) TT)
  exact (__logic_equiv_derivable1 (GammaD := GammaD1) (GammaE := GammaE)
    (P * (!! Q)) ((!! Q) && (P * TT))).mpr
      ⟨derivable1_trans (P * (!! Q)) (P * ((!! Q) && TT))
          ((!! Q) && (P * TT)) htoAnd hfromAnd,
        derivable1_trans ((!! Q) && (P * TT)) (P * ((!! Q) && TT))
          (P * (!! Q)) hbackAnd hback⟩

theorem Derived_sepcon_andp_prop : sepcon_andp_prop (L := L) := by
  constructor
  · exact sepcon_andp_prop1_
  · exact sepcon_andp_prop2_

theorem Derived_sepcon_andp_prop_ext [sepcon_andp_prop (L := L)] :
    sepcon_andp_prop_ext (L := L) := by
  constructor
  · exact sepcon_andp_prop3_
  · exact sepcon_andp_prop4_
  · exact sepcon_andp_prop5_
  · exact sepcon_andp_prop6_
  · exact sepcon_andp_prop7_
  · exact sepcon_andp_prop8_

end SepconAndpPropRules

section IterSepconAndpPropRules

variable {L : Language.{u}}
variable [SepconLanguage L] [EmpLanguage L] [IterSepconLanguage L]
variable [TrueLanguage L] [CoqPropLanguage L]
variable [MinimumLanguage L] [AndLanguage L] [WandLanguage L]
variable [GammaD1 : Derivable1 L]
variable [BasicDeduction L GammaD1] [SepconDeduction L GammaD1]
variable [EmpDeduction L GammaD1] [IterSepconDeduction_left L GammaD1]
variable [TrueDeduction L GammaD1] [CoqPropDeduction L GammaD1]
variable [AndDeduction L GammaD1] [ImpAndAdjointDeduction L GammaD1]
variable [WandDeduction L GammaD1]

theorem iter_sepcon_andp_prop_ :
    forall (xs1 : List (@Language.expr L)) (P : Prop)
      (x2 : @Language.expr L) (xs3 : List (@Language.expr L)),
      iter_sepcon (xs1 ++ (((!! P) && x2) :: xs3)) |--
      ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3))) := by
  intro xs1 P x2 xs3
  letI : sepcon_andp_prop (L := L) := Derived_sepcon_andp_prop
  have h1 :
      iter_sepcon (xs1 ++ (((!! P) && x2) :: xs3)) |--
        (iter_sepcon xs1 * iter_sepcon (((!! P) && x2) :: xs3)) :=
    itersepcon_app2 xs1 (((!! P) && x2) :: xs3)
  have h2 :
      (iter_sepcon xs1 * iter_sepcon (((!! P) && x2) :: xs3)) |--
        (iter_sepcon xs1 * (((!! P) && x2) * iter_sepcon xs3)) :=
    SepconDeduction.derivable1_sepcon_mono
      (GammaD1 := GammaD1) (iter_sepcon xs1) (iter_sepcon xs1)
      (iter_sepcon (((!! P) && x2) :: xs3))
      (((!! P) && x2) * iter_sepcon xs3)
      (derivable1_refl (iter_sepcon xs1))
      (itersepcon_cons1 (((!! P) && x2)) xs3)
  have h3 :
      (iter_sepcon xs1 * (((!! P) && x2) * iter_sepcon xs3)) |--
        ((iter_sepcon xs1 * ((!! P) && x2)) * iter_sepcon xs3) :=
    SepconDeduction.derivable1_sepcon_assoc1
      (GammaD1 := GammaD1) (iter_sepcon xs1) ((!! P) && x2)
      (iter_sepcon xs3)
  have h4 :
      ((iter_sepcon xs1 * ((!! P) && x2)) * iter_sepcon xs3) |--
        ((!! P) && ((iter_sepcon xs1 * x2) * iter_sepcon xs3)) :=
    sepcon_andp_prop5_ (P := P) (Q := iter_sepcon xs1 * x2)
      (R := iter_sepcon xs3)
      |> fun h =>
        derivable1_trans
          ((iter_sepcon xs1 * ((!! P) && x2)) * iter_sepcon xs3)
          (((!! P) && (iter_sepcon xs1 * x2)) * iter_sepcon xs3)
          ((!! P) && ((iter_sepcon xs1 * x2) * iter_sepcon xs3))
          (SepconDeduction.derivable1_sepcon_mono
            (GammaD1 := GammaD1)
            (iter_sepcon xs1 * ((!! P) && x2))
            ((!! P) && (iter_sepcon xs1 * x2))
            (iter_sepcon xs3) (iter_sepcon xs3)
            (sepcon_andp_prop1_ (P := iter_sepcon xs1) (Q := P) (R := x2))
            (derivable1_refl (iter_sepcon xs3)))
          h
  have h5 :
      ((!! P) && ((iter_sepcon xs1 * x2) * iter_sepcon xs3)) |--
        ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3))) :=
    AndDeduction.derivable1s_truep_intros
      (GammaD1 := GammaD1)
      ((!! P) && ((iter_sepcon xs1 * x2) * iter_sepcon xs3))
      (!! P) (iter_sepcon (xs1 ++ (x2 :: xs3)))
      (AndDeduction.derivable1_andp_elim1
        (GammaD1 := GammaD1) (!! P)
        ((iter_sepcon xs1 * x2) * iter_sepcon xs3))
      (derivable1_trans
        ((!! P) && ((iter_sepcon xs1 * x2) * iter_sepcon xs3))
        ((iter_sepcon xs1 * x2) * iter_sepcon xs3)
        (iter_sepcon (xs1 ++ (x2 :: xs3)))
          (AndDeduction.derivable1_andp_elim2
            (GammaD1 := GammaD1) (!! P)
            ((iter_sepcon xs1 * x2) * iter_sepcon xs3))
        (derivable1_trans ((iter_sepcon xs1 * x2) * iter_sepcon xs3)
          (iter_sepcon xs1 * (x2 * iter_sepcon xs3))
          (iter_sepcon (xs1 ++ (x2 :: xs3)))
          (derivable1_sepcon_assoc2_local (iter_sepcon xs1) x2 (iter_sepcon xs3))
          (derivable1_trans (iter_sepcon xs1 * (x2 * iter_sepcon xs3))
            (iter_sepcon xs1 * iter_sepcon (x2 :: xs3))
            (iter_sepcon (xs1 ++ (x2 :: xs3)))
            (SepconDeduction.derivable1_sepcon_mono
              (GammaD1 := GammaD1) (iter_sepcon xs1) (iter_sepcon xs1)
              (x2 * iter_sepcon xs3) (iter_sepcon (x2 :: xs3))
              (derivable1_refl (iter_sepcon xs1)) (itersepcon_cons2 x2 xs3))
            (itersepcon_app1 xs1 (x2 :: xs3)))))
  exact derivable1_trans
    (iter_sepcon (xs1 ++ (((!! P) && x2) :: xs3)))
    (iter_sepcon xs1 * iter_sepcon (((!! P) && x2) :: xs3))
    ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3))) h1
    (derivable1_trans
      (iter_sepcon xs1 * iter_sepcon (((!! P) && x2) :: xs3))
      (iter_sepcon xs1 * (((!! P) && x2) * iter_sepcon xs3))
      ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3))) h2
      (derivable1_trans
        (iter_sepcon xs1 * (((!! P) && x2) * iter_sepcon xs3))
        ((iter_sepcon xs1 * ((!! P) && x2)) * iter_sepcon xs3)
        ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3))) h3
        (derivable1_trans
          ((iter_sepcon xs1 * ((!! P) && x2)) * iter_sepcon xs3)
          ((!! P) && ((iter_sepcon xs1 * x2) * iter_sepcon xs3))
        ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3))) h4 h5)))

theorem derivable1_iter_sepcon_coq_prop_andp_l_ :
    forall (xs1 : List (@Language.expr L)) (P : Prop)
      (x2 : @Language.expr L) (xs3 : List (@Language.expr L)),
      iter_sepcon (xs1 ++ (((!! P) && x2) :: xs3)) |--
      ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3))) :=
  iter_sepcon_andp_prop_ (GammaD1 := GammaD1)

class Iter_sepcon_andp_prop : Prop where
  iter_sepcon_andp_prop :
    forall (xs1 : List (@Language.expr L)) (P : Prop)
      (x2 : @Language.expr L) (xs3 : List (@Language.expr L)),
      iter_sepcon (xs1 ++ (((!! P) && x2) :: xs3)) |--
      ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3)))

theorem derivable1_iter_sepcon_coq_prop_andp_l
    [Iter_sepcon_andp_prop (L := L)] :
    forall (xs1 : List (@Language.expr L)) (P : Prop)
      (x2 : @Language.expr L) (xs3 : List (@Language.expr L)),
      iter_sepcon (xs1 ++ (((!! P) && x2) :: xs3)) |--
      ((!! P) && iter_sepcon (xs1 ++ (x2 :: xs3))) :=
  Iter_sepcon_andp_prop.iter_sepcon_andp_prop (L := L)

theorem Derived_iter_sepcon_andp_prop :
    Iter_sepcon_andp_prop (L := L) := by
  constructor
  exact iter_sepcon_andp_prop_

theorem Derived_derivable1_iter_sepcon_coq_prop_andp_l :
    Iter_sepcon_andp_prop (L := L) :=
  Derived_iter_sepcon_andp_prop (GammaD1 := GammaD1)

end IterSepconAndpPropRules

namespace ShallowQuantifierLogic.ProofTheory

theorem derivable1_sepcon_assoc2 {L : Language.{u}} [SepconLanguage L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [SepconDeduction L GammaD1] :
    forall a b c : @Language.expr L, ((a * b) * c) |-- (a * (b * c)) :=
  Unifysl.derivable1_sepcon_assoc2

end ShallowQuantifierLogic.ProofTheory

end Unifysl
