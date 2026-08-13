import Unifysl.Lib.PTree
import Unifysl.SeparationLogic.ProofTheory.RewriteClass

/-!
Coq inventory from `unifysl-prp/SeparationLogic/ProofTheory/TheoryOfCancel.v`:
- Inductive `expr_deep` with constructors:
  `impp_deep`, `sepcon_deep`, `emp_deep`, `varp_deep`.
- Recursive Boolean equality `beq`.
- Inductive `tree_pos` with constructors:
  `var_pos`, `sepcon_pos`.
- Definitions/functions:
  `cancel_mark_context`, `cancel_mark'`, `cancel_mark`,
  `unmark_sort'`, `unmark_sort`, `cancel_different`,
  `mark_sort'`, `mark_sort`, `cancel_same`, `restore'`, `restore`.
- Proof lemmas:
  `provable_sepcon_assoc2`, `switch`, `build`, `build_cons`, `sepcon_build`,
  `add1`, `add2`, `L1_before1`, `L1_before2`, `L1_before3`, `L1`,
  `L2_before1`, `L2_before2`, `L2_before3`, `L2`, `L3`, `cancel_sound`.

Lean note: root `Unifysl.sepcon_assoc2` already exists from
`SeparationLogic.lean`, so this module's 8.20 Coq lemma is provided as
`Unifysl.SeparationLogic.ProofTheory.TheoryOfCancel.provable_sepcon_assoc2`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Unifysl

open PTree
open PropositionalLanguageNotation
open SeparationLogicNotation

inductive expr_deep : Type where
  | impp_deep : expr_deep -> expr_deep -> expr_deep
  | sepcon_deep : expr_deep -> expr_deep -> expr_deep
  | emp_deep : expr_deep
  | varp_deep : Nat -> expr_deep
deriving DecidableEq, Repr

export expr_deep (impp_deep sepcon_deep emp_deep varp_deep)

def beq : expr_deep -> expr_deep -> Bool
  | emp_deep, emp_deep => true
  | varp_deep x, varp_deep y => decide (x = y)
  | sepcon_deep p11 p12, sepcon_deep p21 p22 =>
      beq p11 p21 && beq p12 p22
  | impp_deep p11 p12, impp_deep p21 p22 =>
      beq p11 p21 && beq p12 p22
  | _, _ => false

private def positive_succ : PTree.positive -> PTree.positive
  | PTree.xH => PTree.xO PTree.xH
  | PTree.xO p => PTree.xI p
  | PTree.xI p => PTree.xO (positive_succ p)

inductive tree_pos (L : Language.{u}) : Type u where
  | var_pos : @Language.expr L -> Option PTree.positive -> tree_pos L
  | sepcon_pos : tree_pos L -> tree_pos L -> tree_pos L

export tree_pos (var_pos sepcon_pos)

def cancel_mark_context {L : Language.{u}} :
    expr_deep -> expr_deep -> tree_pos L -> PTree.positive -> tree_pos L × Bool
  | sepcon_deep dp dq, q, sepcon_pos tp tq, key =>
      match cancel_mark_context dp q tp key with
      | (tp', true) => (sepcon_pos tp' tq, true)
      | (tp', false) =>
          match cancel_mark_context dq q tq key with
          | (tq', true) => (sepcon_pos tp tq', true)
          | (_, false) => (sepcon_pos tp tq, false)
  | p, q, var_pos sp o, key =>
      if beq p q then
        match o with
        | none => (var_pos sp (some key), true)
        | some _ => (var_pos sp o, false)
      else
        (var_pos sp o, false)
  | _, _, tep, _ => (tep, false)

def cancel_mark' {L : Language.{u}} :
    expr_deep -> expr_deep -> tree_pos L -> tree_pos L -> PTree.positive ->
      tree_pos L × tree_pos L × PTree.positive
  | dep, sepcon_deep dp dq, tep, sepcon_pos tp tq, key =>
      match cancel_mark' dep dp tep tp key with
      | (tep', tp', key') =>
          match cancel_mark' dep dq tep' tq key' with
          | (tep'', tq', key'') => (tep'', sepcon_pos tp' tq', key'')
  | dep, q, tep, var_pos sq _, key =>
      match cancel_mark_context dep q tep key with
      | (tep', true) => (tep', var_pos sq (some key), positive_succ key)
      | (tep', false) => (tep', var_pos sq none, key)
  | _, _, tep, teq, key => (tep, teq, key)

def cancel_mark {L : Language.{u}} (dep deq : expr_deep)
    (tep teq : tree_pos L) : tree_pos L × tree_pos L :=
  match cancel_mark' dep deq tep teq PTree.xH with
  | (tep', teq', _) => (tep', teq')

def unmark_sort' {L : Language.{u}} [SepconLanguage L] :
    tree_pos L -> Option (@Language.expr L)
  | sepcon_pos tp tq =>
      match unmark_sort' tp with
      | none => unmark_sort' tq
      | some sp =>
          match unmark_sort' tq with
          | none => some sp
          | some sq => some (sp * sq)
  | var_pos sq o =>
      match o with
      | none => some sq
      | some _ => none

def unmark_sort {L : Language.{u}} [SepconLanguage L] [EmpLanguage L]
    (tep : tree_pos L) : @Language.expr L :=
  match unmark_sort' tep with
  | some sp => sp
  | none => emp

def cancel_different {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
    [EmpLanguage L] (tep teq : tree_pos L) : @Language.expr L :=
  unmark_sort tep ⟶ unmark_sort teq

def mark_sort' {L : Language.{u}} [SepconLanguage L] :
    tree_pos L -> PTree.tree (@Language.expr L) -> PTree.tree (@Language.expr L)
  | sepcon_pos tp tq, m => mark_sort' tq (mark_sort' tp m)
  | var_pos sq none, m => m
  | var_pos sq (some pos), m =>
      match PTree.get_rec (@Language.expr L) pos m with
      | none => PTree.set_rec (@Language.expr L) pos sq m
      | some sp => PTree.set_rec (@Language.expr L) pos (sp * sq) m

def mark_sort {L : Language.{u}} [SepconLanguage L] (tep : tree_pos L) :
    PTree.tree (@Language.expr L) :=
  mark_sort' tep PTree.empty

def cancel_same {L : Language.{u}} [SepconLanguage L]
    (tep teq : tree_pos L) : Prop :=
  mark_sort tep = mark_sort teq

def restore' {L : Language.{u}} [SepconLanguage L] : tree_pos L -> @Language.expr L
  | sepcon_pos tp tq => restore' tp * restore' tq
  | var_pos sp _ => sp

def restore {L : Language.{u}} [MinimumLanguage L] [SepconLanguage L]
    (tep teq : tree_pos L) : @Language.expr L :=
  restore' tep ⟶ restore' teq

section ProofOfLemma

variable {L : Language.{u}}
variable [MinimumLanguage L] [SepconLanguage L] [EmpLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [SepconAxiomatization L Gamma]
variable [EmpAxiomatization L Gamma]

namespace SeparationLogic.ProofTheory.TheoryOfCancel

theorem provable_sepcon_assoc2 :
    forall x y z : @Language.expr L,
      |-- (((x * y) * z) ⟶ (x * (y * z))) := by
  intro x y z
  exact Unifysl.sepcon_assoc2 (Gamma := Gamma) x y z

end SeparationLogic.ProofTheory.TheoryOfCancel

theorem switch :
    forall x y p q : @Language.expr L,
      |-- (((x * y) * (p * q)) ⟶ ((x * p) * (y * q))) := by
  intro x y p q
  have hinner :
      |-- ((y * (p * q)) ⟶ (p * (y * q))) := by
    exact solve_impp_trans (y * (p * q)) ((p * q) * y) (p * (y * q))
      (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) y (p * q))
      (solve_impp_trans ((p * q) * y) (p * (q * y)) (p * (y * q))
        (SeparationLogic.ProofTheory.TheoryOfCancel.provable_sepcon_assoc2 (Gamma := Gamma) p q y)
        (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
          p p (q * y) (y * q)
          (provable_impp_refl p)
          (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) q y)))
  exact solve_impp_trans ((x * y) * (p * q)) (x * (y * (p * q)))
    ((x * p) * (y * q))
    (SeparationLogic.ProofTheory.TheoryOfCancel.provable_sepcon_assoc2 (Gamma := Gamma) x y (p * q))
    (solve_impp_trans (x * (y * (p * q))) (x * (p * (y * q)))
      ((x * p) * (y * q))
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        x x (y * (p * q)) (p * (y * q))
        (provable_impp_refl x) hinner)
      (SepconAxiomatization.sepcon_assoc1 (Gamma := Gamma) x p (y * q)))

def build : List (@Language.expr L) -> @Language.expr L
  | [] => emp
  | p :: l' => p * build l'

theorem build_cons :
    forall (l1 l2 : List (@Language.expr L)) (e : @Language.expr L),
      |-- (build (l1 ++ e :: l2) ⟶ (build (l1 ++ l2) * e)) := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 e
      simp [build]
      exact SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) e (build l2)
  | cons a l1 ih =>
      intro l2 e
      simp [build]
      exact solve_impp_trans (a * build (l1 ++ e :: l2))
        (a * (build (l1 ++ l2) * e)) ((a * build (l1 ++ l2)) * e)
        (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
          a a (build (l1 ++ e :: l2)) (build (l1 ++ l2) * e)
          (provable_impp_refl a) (ih l2 e))
        (SepconAxiomatization.sepcon_assoc1 (Gamma := Gamma) a (build (l1 ++ l2)) e)

theorem sepcon_build :
    forall (l1 l2 : List (@Language.expr L)) (e : @Language.expr L),
      |-- ((build (l1 ++ l2) * e) ⟶ build (l1 ++ e :: l2)) := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 e
      simp [build]
      exact SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) (build l2) e
  | cons a l1 ih =>
      intro l2 e
      simp [build]
      exact solve_impp_trans ((a * build (l1 ++ l2)) * e)
        (a * (build (l1 ++ l2) * e)) (a * build (l1 ++ e :: l2))
        (SeparationLogic.ProofTheory.TheoryOfCancel.provable_sepcon_assoc2 (Gamma := Gamma)
          a (build (l1 ++ l2)) e)
        (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
          a a (build (l1 ++ l2) * e) (build (l1 ++ e :: l2))
          (provable_impp_refl a) (ih l2 e))

theorem add1 :
    forall (e' : @Language.expr L) (p : PTree.positive)
      (m : PTree.tree (@Language.expr L)),
      |-- (build (PTree.elements (@Language.expr L)
              (mark_sort' (var_pos e' (some p) : tree_pos L) m)) ⟶
            (build (PTree.elements (@Language.expr L) m) * e')) := by
  intro e' p m
  unfold mark_sort'
  cases hget : PTree.get_rec (@Language.expr L) p m with
  | some e =>
      rcases PTree.elements_set_some (@Language.expr L) p e (e * e') m hget with
        ⟨l1, l2, hm, hset⟩
      rw [hset, hm]
      exact solve_impp_trans (build (l1 ++ (e * e') :: l2))
        (build (l1 ++ l2) * (e * e')) (build (l1 ++ e :: l2) * e')
        (build_cons l1 l2 (e * e'))
        (solve_impp_trans (build (l1 ++ l2) * (e * e'))
          ((build (l1 ++ l2) * e) * e') (build (l1 ++ e :: l2) * e')
          (SepconAxiomatization.sepcon_assoc1 (Gamma := Gamma)
            (build (l1 ++ l2)) e e')
          (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
            (build (l1 ++ l2) * e) (build (l1 ++ e :: l2)) e' e'
            (sepcon_build l1 l2 e) (provable_impp_refl e')))
  | none =>
      rcases PTree.elements_set_none (@Language.expr L) p e' m hget with
        ⟨l1, l2, hm, hset⟩
      rw [hset, hm]
      exact build_cons l1 l2 e'

theorem add2 :
    forall (e' : @Language.expr L) (p : PTree.positive)
      (m : PTree.tree (@Language.expr L)),
      |-- ((build (PTree.elements (@Language.expr L) m) * e') ⟶
            build (PTree.elements (@Language.expr L)
              (mark_sort' (var_pos e' (some p) : tree_pos L) m))) := by
  intro e' p m
  unfold mark_sort'
  cases hget : PTree.get_rec (@Language.expr L) p m with
  | some e =>
      rcases PTree.elements_set_some (@Language.expr L) p e (e * e') m hget with
        ⟨l1, l2, hm, hset⟩
      rw [hset, hm]
      exact solve_impp_trans (build (l1 ++ e :: l2) * e')
        ((build (l1 ++ l2) * e) * e') (build (l1 ++ (e * e') :: l2))
        (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
          (build (l1 ++ e :: l2)) (build (l1 ++ l2) * e) e' e'
          (build_cons l1 l2 e) (provable_impp_refl e'))
        (solve_impp_trans ((build (l1 ++ l2) * e) * e')
          (build (l1 ++ l2) * (e * e')) (build (l1 ++ (e * e') :: l2))
          (SeparationLogic.ProofTheory.TheoryOfCancel.provable_sepcon_assoc2 (Gamma := Gamma)
            (build (l1 ++ l2)) e e')
          (sepcon_build l1 l2 (e * e')))
  | none =>
      rcases PTree.elements_set_none (@Language.expr L) p e' m hget with
        ⟨l1, l2, hm, hset⟩
      rw [hset, hm]
      exact sepcon_build l1 l2 e'

theorem L1_before1 :
    forall (sp : @Language.expr L) (p : PTree.positive),
      |-- (sp ⟶ build (PTree.elements (@Language.expr L)
          (mark_sort (var_pos sp (some p) : tree_pos L)))) := by
  intro sp p
  unfold mark_sort mark_sort'
  rw [PTree.get_empty, PTree.elements_set_empty]
  simp [build]
  exact EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) sp

theorem L1_before2 :
    forall p1 p2 : tree_pos L,
      |-- ((unmark_sort p1 * unmark_sort p2) ⟶ unmark_sort (sepcon_pos p1 p2)) := by
  intro p1 p2
  cases h1 : unmark_sort' p1 with
  | none =>
      cases h2 : unmark_sort' p2 with
      | none =>
          simp [unmark_sort, unmark_sort', h1, h2]
          exact EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) emp
      | some b =>
          simp [unmark_sort, unmark_sort', h1, h2]
          exact solve_impp_trans (emp * b) (b * emp) b
            (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) emp b)
            (EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) b)
  | some a =>
      cases h2 : unmark_sort' p2 with
      | none =>
          simp [unmark_sort, unmark_sort', h1, h2]
          exact EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) a
      | some b =>
          simp [unmark_sort, unmark_sort', h1, h2]
          exact provable_impp_refl (a * b)

private theorem L1_before3_aux :
    forall (p : tree_pos L) (m1 m2 m3 : PTree.tree (@Language.expr L)),
      (|-- ((build (PTree.elements (@Language.expr L) m1) *
              build (PTree.elements (@Language.expr L) m2)) ⟶
            build (PTree.elements (@Language.expr L) m3))) ->
        |-- ((build (PTree.elements (@Language.expr L) m1) *
                build (PTree.elements (@Language.expr L) (mark_sort' p m2))) ⟶
              build (PTree.elements (@Language.expr L) (mark_sort' p m3))) := by
  intro p
  induction p with
  | var_pos e o =>
      intro m1 m2 m3 h
      cases o with
      | none =>
          simpa [mark_sort'] using h
      | some pos =>
          exact solve_impp_trans
            (build (PTree.elements (@Language.expr L) m1) *
              build (PTree.elements (@Language.expr L)
                (mark_sort' (var_pos e (some pos) : tree_pos L) m2)))
            (build (PTree.elements (@Language.expr L) m1) *
              (build (PTree.elements (@Language.expr L) m2) * e))
            (build (PTree.elements (@Language.expr L)
              (mark_sort' (var_pos e (some pos) : tree_pos L) m3)))
            (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
              (build (PTree.elements (@Language.expr L) m1))
              (build (PTree.elements (@Language.expr L) m1))
              (build (PTree.elements (@Language.expr L)
                (mark_sort' (var_pos e (some pos) : tree_pos L) m2)))
              (build (PTree.elements (@Language.expr L) m2) * e)
              (provable_impp_refl (build (PTree.elements (@Language.expr L) m1)))
              (add1 e pos m2))
            (solve_impp_trans
              (build (PTree.elements (@Language.expr L) m1) *
                (build (PTree.elements (@Language.expr L) m2) * e))
              ((build (PTree.elements (@Language.expr L) m1) *
                  build (PTree.elements (@Language.expr L) m2)) * e)
              (build (PTree.elements (@Language.expr L)
                (mark_sort' (var_pos e (some pos) : tree_pos L) m3)))
              (SepconAxiomatization.sepcon_assoc1 (Gamma := Gamma)
                (build (PTree.elements (@Language.expr L) m1))
                (build (PTree.elements (@Language.expr L) m2)) e)
              (solve_impp_trans
                ((build (PTree.elements (@Language.expr L) m1) *
                    build (PTree.elements (@Language.expr L) m2)) * e)
                (build (PTree.elements (@Language.expr L) m3) * e)
                (build (PTree.elements (@Language.expr L)
                  (mark_sort' (var_pos e (some pos) : tree_pos L) m3)))
                (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
                  (build (PTree.elements (@Language.expr L) m1) *
                    build (PTree.elements (@Language.expr L) m2))
                  (build (PTree.elements (@Language.expr L) m3)) e e
                  h (provable_impp_refl e))
                (add2 e pos m3)))
  | sepcon_pos p1 p2 ih1 ih2 =>
      intro m1 m2 m3 h
      exact ih2 m1 (mark_sort' p1 m2) (mark_sort' p1 m3)
        (ih1 m1 m2 m3 h)

theorem L1_before3 :
    forall p1 p2 : tree_pos L,
      |-- ((build (PTree.elements (@Language.expr L) (mark_sort p1)) *
              build (PTree.elements (@Language.expr L) (mark_sort p2))) ⟶
            build (PTree.elements (@Language.expr L) (mark_sort (sepcon_pos p1 p2)))) := by
  intro p1 p2
  unfold mark_sort
  have hbase :
      |-- ((build (PTree.elements (@Language.expr L) (mark_sort' p1 PTree.empty)) *
              build (PTree.elements (@Language.expr L)
                (PTree.empty : PTree.tree (@Language.expr L)))) ⟶
            build (PTree.elements (@Language.expr L) (mark_sort' p1 PTree.empty))) := by
    simp [PTree.empty, PTree.elements, PTree.xelements, build]
    exact EmpAxiomatization.sepcon_emp1 (Gamma := Gamma)
      (build (PTree.elements (@Language.expr L) (mark_sort' p1 PTree.empty)))
  simpa [mark_sort'] using
    L1_before3_aux p2 (mark_sort' p1 PTree.empty)
      (PTree.empty : PTree.tree (@Language.expr L)) (mark_sort' p1 PTree.empty) hbase

theorem L1 :
    forall tep : tree_pos L,
      |-- (restore' tep ⟶
            (unmark_sort tep *
              build (PTree.elements (@Language.expr L) (mark_sort tep)))) := by
  intro tep
  induction tep with
  | var_pos sp op =>
      cases op with
      | none =>
          simp [restore', unmark_sort, unmark_sort', mark_sort, mark_sort', build,
            PTree.empty, PTree.elements, PTree.xelements]
          exact EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) sp
      | some p =>
          have hbuild := L1_before1 (L := L) (Gamma := Gamma) sp p
          simp [restore', unmark_sort, unmark_sort'] at hbuild ⊢
          exact solve_impp_trans sp
            (build (PTree.elements (@Language.expr L)
              (mark_sort (var_pos sp (some p) : tree_pos L))))
            (emp * build (PTree.elements (@Language.expr L)
              (mark_sort (var_pos sp (some p) : tree_pos L))))
            hbuild
            (solve_impp_trans
              (build (PTree.elements (@Language.expr L)
                (mark_sort (var_pos sp (some p) : tree_pos L))))
              (build (PTree.elements (@Language.expr L)
                (mark_sort (var_pos sp (some p) : tree_pos L))) * emp)
              (emp * build (PTree.elements (@Language.expr L)
                (mark_sort (var_pos sp (some p) : tree_pos L))))
              (EmpAxiomatization.sepcon_emp2 (Gamma := Gamma)
                (build (PTree.elements (@Language.expr L)
                  (mark_sort (var_pos sp (some p) : tree_pos L)))))
              (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma)
                (build (PTree.elements (@Language.expr L)
                  (mark_sort (var_pos sp (some p) : tree_pos L)))) emp))
  | sepcon_pos p1 p2 ih1 ih2 =>
      simp [restore', mark_sort]
      exact solve_impp_trans (restore' p1 * restore' p2)
        ((unmark_sort p1 *
            build (PTree.elements (@Language.expr L) (mark_sort p1))) *
          (unmark_sort p2 *
            build (PTree.elements (@Language.expr L) (mark_sort p2))))
        (unmark_sort (sepcon_pos p1 p2) *
          build (PTree.elements (@Language.expr L) (mark_sort (sepcon_pos p1 p2))))
        (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
          (restore' p1)
          (unmark_sort p1 * build (PTree.elements (@Language.expr L) (mark_sort p1)))
          (restore' p2)
          (unmark_sort p2 * build (PTree.elements (@Language.expr L) (mark_sort p2)))
          ih1 ih2)
        (solve_impp_trans
          ((unmark_sort p1 *
              build (PTree.elements (@Language.expr L) (mark_sort p1))) *
            (unmark_sort p2 *
              build (PTree.elements (@Language.expr L) (mark_sort p2))))
          ((unmark_sort p1 * unmark_sort p2) *
            (build (PTree.elements (@Language.expr L) (mark_sort p1)) *
              build (PTree.elements (@Language.expr L) (mark_sort p2))))
          (unmark_sort (sepcon_pos p1 p2) *
            build (PTree.elements (@Language.expr L) (mark_sort (sepcon_pos p1 p2))))
          (switch (unmark_sort p1)
            (build (PTree.elements (@Language.expr L) (mark_sort p1)))
            (unmark_sort p2)
            (build (PTree.elements (@Language.expr L) (mark_sort p2))))
          (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
            (unmark_sort p1 * unmark_sort p2) (unmark_sort (sepcon_pos p1 p2))
            (build (PTree.elements (@Language.expr L) (mark_sort p1)) *
              build (PTree.elements (@Language.expr L) (mark_sort p2)))
            (build (PTree.elements (@Language.expr L) (mark_sort (sepcon_pos p1 p2)))
            )
            (L1_before2 p1 p2) (L1_before3 p1 p2)))

theorem L2_before1 :
    forall (sq : @Language.expr L) (p : PTree.positive),
      |-- (build (PTree.elements (@Language.expr L)
          (mark_sort (var_pos sq (some p) : tree_pos L))) ⟶ sq) := by
  intro sq p
  unfold mark_sort mark_sort'
  rw [PTree.get_empty, PTree.elements_set_empty]
  simp [build]
  exact EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) sq

theorem L2_before2 :
    forall q1 q2 : tree_pos L,
      |-- (unmark_sort (sepcon_pos q1 q2) ⟶ (unmark_sort q1 * unmark_sort q2)) := by
  intro q1 q2
  cases h1 : unmark_sort' q1 with
  | none =>
      cases h2 : unmark_sort' q2 with
      | none =>
          simp [unmark_sort, unmark_sort', h1, h2]
          exact EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) emp
      | some b =>
          simp [unmark_sort, unmark_sort', h1, h2]
          exact solve_impp_trans b (b * emp) (emp * b)
            (EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) b)
            (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) b emp)
  | some a =>
      cases h2 : unmark_sort' q2 with
      | none =>
          simp [unmark_sort, unmark_sort', h1, h2]
          exact EmpAxiomatization.sepcon_emp2 (Gamma := Gamma) a
      | some b =>
          simp [unmark_sort, unmark_sort', h1, h2]
          exact provable_impp_refl (a * b)

private theorem L2_before3_aux :
    forall (p : tree_pos L) (m1 m2 m3 : PTree.tree (@Language.expr L)),
      (|-- (build (PTree.elements (@Language.expr L) m3) ⟶
            (build (PTree.elements (@Language.expr L) m1) *
              build (PTree.elements (@Language.expr L) m2)))) ->
        |-- (build (PTree.elements (@Language.expr L) (mark_sort' p m3)) ⟶
              (build (PTree.elements (@Language.expr L) m1) *
                build (PTree.elements (@Language.expr L) (mark_sort' p m2)))) := by
  intro p
  induction p with
  | var_pos e o =>
      intro m1 m2 m3 h
      cases o with
      | none =>
          simpa [mark_sort'] using h
      | some pos =>
          exact solve_impp_trans
            (build (PTree.elements (@Language.expr L)
              (mark_sort' (var_pos e (some pos) : tree_pos L) m3)))
            (build (PTree.elements (@Language.expr L) m3) * e)
            (build (PTree.elements (@Language.expr L) m1) *
              build (PTree.elements (@Language.expr L)
                (mark_sort' (var_pos e (some pos) : tree_pos L) m2)))
            (add1 e pos m3)
            (solve_impp_trans
              (build (PTree.elements (@Language.expr L) m3) * e)
              ((build (PTree.elements (@Language.expr L) m1) *
                  build (PTree.elements (@Language.expr L) m2)) * e)
              (build (PTree.elements (@Language.expr L) m1) *
                build (PTree.elements (@Language.expr L)
                  (mark_sort' (var_pos e (some pos) : tree_pos L) m2)))
              (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
                (build (PTree.elements (@Language.expr L) m3))
                (build (PTree.elements (@Language.expr L) m1) *
                  build (PTree.elements (@Language.expr L) m2))
                e e h (provable_impp_refl e))
              (solve_impp_trans
                ((build (PTree.elements (@Language.expr L) m1) *
                    build (PTree.elements (@Language.expr L) m2)) * e)
                (build (PTree.elements (@Language.expr L) m1) *
                  (build (PTree.elements (@Language.expr L) m2) * e))
                (build (PTree.elements (@Language.expr L) m1) *
                  build (PTree.elements (@Language.expr L)
                    (mark_sort' (var_pos e (some pos) : tree_pos L) m2)))
                (SeparationLogic.ProofTheory.TheoryOfCancel.provable_sepcon_assoc2 (Gamma := Gamma)
                  (build (PTree.elements (@Language.expr L) m1))
                  (build (PTree.elements (@Language.expr L) m2)) e)
                (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
                  (build (PTree.elements (@Language.expr L) m1))
                  (build (PTree.elements (@Language.expr L) m1))
                  (build (PTree.elements (@Language.expr L) m2) * e)
                  (build (PTree.elements (@Language.expr L)
                    (mark_sort' (var_pos e (some pos) : tree_pos L) m2))
                  )
                  (provable_impp_refl (build (PTree.elements (@Language.expr L) m1)))
                  (add2 e pos m2))))
  | sepcon_pos p1 p2 ih1 ih2 =>
      intro m1 m2 m3 h
      exact ih2 m1 (mark_sort' p1 m2) (mark_sort' p1 m3)
        (ih1 m1 m2 m3 h)

theorem L2_before3 :
    forall q1 q2 : tree_pos L,
      |-- (build (PTree.elements (@Language.expr L) (mark_sort (sepcon_pos q1 q2))) ⟶
            (build (PTree.elements (@Language.expr L) (mark_sort q1)) *
              build (PTree.elements (@Language.expr L) (mark_sort q2)))) := by
  intro q1 q2
  unfold mark_sort
  have hbase :
      |-- (build (PTree.elements (@Language.expr L) (mark_sort' q1 PTree.empty)) ⟶
            (build (PTree.elements (@Language.expr L) (mark_sort' q1 PTree.empty)) *
              build (PTree.elements (@Language.expr L)
                (PTree.empty : PTree.tree (@Language.expr L))))) := by
    simp [PTree.empty, PTree.elements, PTree.xelements, build]
    exact EmpAxiomatization.sepcon_emp2 (Gamma := Gamma)
      (build (PTree.elements (@Language.expr L) (mark_sort' q1 PTree.empty)))
  simpa [mark_sort'] using
    L2_before3_aux q2 (mark_sort' q1 PTree.empty)
      (PTree.empty : PTree.tree (@Language.expr L)) (mark_sort' q1 PTree.empty) hbase

theorem L2 :
    forall teq : tree_pos L,
      |-- ((unmark_sort teq *
              build (PTree.elements (@Language.expr L) (mark_sort teq))) ⟶
            restore' teq) := by
  intro teq
  induction teq with
  | var_pos sq oq =>
      cases oq with
      | none =>
          simp [restore', unmark_sort, unmark_sort', mark_sort, mark_sort', build,
            PTree.empty, PTree.elements, PTree.xelements]
          exact EmpAxiomatization.sepcon_emp1 (Gamma := Gamma) sq
      | some p =>
          simp [restore', unmark_sort, unmark_sort']
          exact solve_impp_trans
            (emp * build (PTree.elements (@Language.expr L)
              (mark_sort (var_pos sq (some p) : tree_pos L))))
            (build (PTree.elements (@Language.expr L)
              (mark_sort (var_pos sq (some p) : tree_pos L))) * emp)
            sq
            (SepconAxiomatization.sepcon_comm_impp (Gamma := Gamma) emp
              (build (PTree.elements (@Language.expr L)
                (mark_sort (var_pos sq (some p) : tree_pos L)))))
            (solve_impp_trans
              (build (PTree.elements (@Language.expr L)
                (mark_sort (var_pos sq (some p) : tree_pos L))) * emp)
              (build (PTree.elements (@Language.expr L)
                (mark_sort (var_pos sq (some p) : tree_pos L))))
              sq
              (EmpAxiomatization.sepcon_emp1 (Gamma := Gamma)
                (build (PTree.elements (@Language.expr L)
                  (mark_sort (var_pos sq (some p) : tree_pos L)))))
              (L2_before1 (L := L) (Gamma := Gamma) sq p))
  | sepcon_pos q1 q2 ih1 ih2 =>
      simp [restore', mark_sort]
      exact solve_impp_trans
        (unmark_sort (sepcon_pos q1 q2) *
          build (PTree.elements (@Language.expr L) (mark_sort (sepcon_pos q1 q2))))
        ((unmark_sort q1 * unmark_sort q2) *
          (build (PTree.elements (@Language.expr L) (mark_sort q1)) *
            build (PTree.elements (@Language.expr L) (mark_sort q2))))
        (restore' q1 * restore' q2)
        (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
          (unmark_sort (sepcon_pos q1 q2)) (unmark_sort q1 * unmark_sort q2)
          (build (PTree.elements (@Language.expr L) (mark_sort (sepcon_pos q1 q2))))
          (build (PTree.elements (@Language.expr L) (mark_sort q1)) *
            build (PTree.elements (@Language.expr L) (mark_sort q2)))
          (L2_before2 q1 q2) (L2_before3 q1 q2))
        (solve_impp_trans
          ((unmark_sort q1 * unmark_sort q2) *
            (build (PTree.elements (@Language.expr L) (mark_sort q1)) *
              build (PTree.elements (@Language.expr L) (mark_sort q2))))
          ((unmark_sort q1 *
              build (PTree.elements (@Language.expr L) (mark_sort q1))) *
            (unmark_sort q2 *
              build (PTree.elements (@Language.expr L) (mark_sort q2))))
          (restore' q1 * restore' q2)
          (switch (unmark_sort q1) (unmark_sort q2)
            (build (PTree.elements (@Language.expr L) (mark_sort q1)))
            (build (PTree.elements (@Language.expr L) (mark_sort q2))))
          (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
            (unmark_sort q1 *
              build (PTree.elements (@Language.expr L) (mark_sort q1)))
            (restore' q1)
            (unmark_sort q2 *
              build (PTree.elements (@Language.expr L) (mark_sort q2)))
            (restore' q2)
            ih1 ih2))

theorem L3 :
    forall m1 m2 : PTree.tree (@Language.expr L),
      m1 = m2 ->
      |-- (build (PTree.elements (@Language.expr L) m1) ⟶
            build (PTree.elements (@Language.expr L) m2)) := by
  intro m1 m2 h
  subst m2
  exact provable_impp_refl (build (PTree.elements (@Language.expr L) m1))

theorem cancel_sound :
    forall tep teq : tree_pos L,
      cancel_same tep teq ->
      @Provable.provable L Gamma (cancel_different tep teq) ->
      @Provable.provable L Gamma (restore tep teq) := by
  intro tep teq hsame hdif
  unfold cancel_same at hsame
  unfold cancel_different at hdif
  unfold restore
  exact solve_impp_trans (restore' tep)
    (unmark_sort tep * build (PTree.elements (@Language.expr L) (mark_sort tep)))
    (restore' teq)
    (L1 tep)
    (solve_impp_trans
      (unmark_sort tep * build (PTree.elements (@Language.expr L) (mark_sort tep)))
      (unmark_sort teq * build (PTree.elements (@Language.expr L) (mark_sort teq)))
      (restore' teq)
      (SepconAxiomatization.sepcon_mono (Gamma := Gamma)
        (unmark_sort tep) (unmark_sort teq)
        (build (PTree.elements (@Language.expr L) (mark_sort tep)))
        (build (PTree.elements (@Language.expr L) (mark_sort teq))
        )
        hdif (L3 (mark_sort tep) (mark_sort teq) hsame))
      (L2 teq))

end ProofOfLemma

end Unifysl
