import Unifysl.Lib.List_Func_ext
import Unifysl.MinimumLogic.ProofTheory.ProofTheoryPatterns
import Unifysl.PropositionalLogic.ProofTheory.Intuitionistic
import Unifysl.PropositionalLogic.ProofTheory.RewriteClass

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `PropositionalLogic/ProofTheory/ProofTheoryPatterns.v`:
- Module `P`: re-exports minimum provable-level proof patterns and adds
  pattern equivalence lemmas for commutativity, units, distributivity,
  adjointness, monotonicity, associativity, fold/permutation behavior, and
  `Build_LeftUnit'`, `Build_RightUnit'`, `Build_Associativity'`.
- Root derived rules: `falsep_andp`, `andp_falsep`,
  `andp_orp_distr_l`, `andp_orp_distr_r`,
  `provable_iter_andp_sepc_right`,
  `provable_iter_andp_unfold_right_assoc`,
  `provable_iter_andp_unfold_left_assoc`, `iter_andp_multi_imp`.
- Module `D1`: re-exports minimum derivable1-level proof patterns and adds the
  analogous logic-equivalence lemmas and builder lemmas.

Lean note: Coq source comments marking l/r naming concerns are preserved by
statement shape, not copied as migration markers. `fold_right_prodp_no_unit`
names the inline Coq `fix` used by fold-right unfold lemmas so public theorem
statements remain writable downstream.
-/

universe u

namespace Unifysl

open Relation_ext
open PropositionalLanguageNotation

private theorem provable_iffp_intro_of_local {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    (x y : @Language.expr L) :
    (|-- (x ⟶ y)) -> (|-- (y ⟶ x)) -> |-- (x ⟷ y) := by
  intro hxy hyx
  have h1 := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ y) ((y ⟶ x) ⟶ (x ⟷ y))
    (IffAxiomatization.provable_iffp_intros x y) hxy
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ x) (x ⟷ y) h1 hyx

private theorem provable_iffp_elim1_of_local {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    (x y : @Language.expr L) :
    (|-- (x ⟷ y)) -> |-- (x ⟶ y) := by
  intro h
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟷ y) (x ⟶ y)
    (IffAxiomatization.provable_iffp_elim1 x y) h

private theorem provable_iffp_elim2_of_local {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    (x y : @Language.expr L) :
    (|-- (x ⟷ y)) -> |-- (y ⟶ x) := by
  intro h
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟷ y) (y ⟶ x)
    (IffAxiomatization.provable_iffp_elim2 x y) h

private theorem provable_iffp_refl_of_local {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    (x : @Language.expr L) :
    |-- (x ⟷ x) :=
  provable_iffp_intro_of_local x x (provable_impp_refl x) (provable_impp_refl x)

private theorem provable_orp_impp_of_local {L : Language.{u}}
    [MinimumLanguage L] [OrLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [OrAxiomatization L Gamma]
    (x y z : @Language.expr L) :
    (|-- (x ⟶ z)) -> (|-- (y ⟶ z)) -> |-- ((x || y) ⟶ z) := by
  intro hx hy
  have h1 := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ z) ((y ⟶ z) ⟶ ((x || y) ⟶ z))
    (OrAxiomatization.provable_orp_elim x y z) hx
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ z) ((x || y) ⟶ z) h1 hy

private theorem provable_impp_andp_of_local {L : Language.{u}}
    [MinimumLanguage L] [AndLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [AndAxiomatization L Gamma]
    (x y z : @Language.expr L) :
    (|-- (x ⟶ y)) -> (|-- (x ⟶ z)) -> |-- (x ⟶ (y && z)) := by
  intro hxy hxz
  have hyz : |-- (y ⟶ z ⟶ (y && z)) :=
    AndAxiomatization.provable_andp_intros y z
  have hx_z_yz : |-- (x ⟶ z ⟶ (y && z)) :=
    aux_minimun_rule02 x y (z ⟶ (y && z)) hxy hyz
  have hmp :
      |-- ((x ⟶ z) ⟶ (x ⟶ z ⟶ (y && z)) ⟶ (x ⟶ (y && z))) := by
    simpa [multi_imp] using
      (provable_multi_imp_modus_ponens [x] z (y && z))
  have hstep := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ z)
    ((x ⟶ z ⟶ (y && z)) ⟶ x ⟶ (y && z))
    hmp hxz
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ z ⟶ (y && z)) (x ⟶ (y && z)) hstep hx_z_yz

private theorem provable_iffp_symm_of {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {x y : @Language.expr L} :
    (|-- (x ⟷ y)) -> |-- (y ⟷ x) := by
  intro hxy
  exact provable_iffp_intro_of_local y x
    (provable_iffp_elim2_of_local x y hxy)
    (provable_iffp_elim1_of_local x y hxy)

private theorem provable_iffp_trans_of {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {x y z : @Language.expr L} :
    (|-- (x ⟷ y)) -> (|-- (y ⟷ z)) -> |-- (x ⟷ z) := by
  intro hxy hyz
  exact provable_iffp_intro_of_local x z
    (solve_impp_trans x y z
      (provable_iffp_elim1_of_local x y hxy)
      (provable_iffp_elim1_of_local y z hyz))
    (solve_impp_trans z y x
      (provable_iffp_elim2_of_local y z hyz)
      (provable_iffp_elim2_of_local x y hxy))

private theorem logic_equiv_of_derivable1 {L : Language.{u}}
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE] {x y : @Language.expr L} :
    (x |-- y) -> (y |-- x) -> logic_equiv (L := L) x y := by
  intro hxy hyx
  exact (__logic_equiv_derivable1 x y).mpr ⟨hxy, hyx⟩

private theorem logic_equiv_forall2_left {L : Language.{u}}
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE] :
    forall {xs ys : List (@Language.expr L)},
      List.Forall₂ (fun x y => logic_equiv (L := L) x y) xs ys ->
        List.Forall₂ (fun x y => (x |-- y)) xs ys := by
  intro xs ys h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | cons hxy _ ih =>
      exact List.Forall₂.cons ((__logic_equiv_derivable1 _ _).mp hxy).left ih

private theorem logic_equiv_forall2_right {L : Language.{u}}
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE] :
    forall {xs ys : List (@Language.expr L)},
      List.Forall₂ (fun x y => logic_equiv (L := L) x y) xs ys ->
        List.Forall₂ (fun y x => (y |-- x)) ys xs := by
  intro xs ys h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | cons hxy _ ih =>
      exact List.Forall₂.cons ((__logic_equiv_derivable1 _ _).mp hxy).right ih

private theorem provable_iffp_forall2_left {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma] :
    forall {xs ys : List (@Language.expr L)},
      List.Forall₂ (fun x y => |-- (x ⟷ y)) xs ys ->
        List.Forall₂ (fun x y => |-- (x ⟶ y)) xs ys := by
  intro xs ys h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | cons hxy _ ih =>
      exact List.Forall₂.cons (provable_iffp_elim1_of_local _ _ hxy) ih

private theorem provable_iffp_forall2_right {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma] :
    forall {xs ys : List (@Language.expr L)},
      List.Forall₂ (fun x y => |-- (x ⟷ y)) xs ys ->
        List.Forall₂ (fun y x => |-- (y ⟶ x)) ys xs := by
  intro xs ys h
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | cons hxy _ ih =>
      exact List.Forall₂.cons (provable_iffp_elim2_of_local _ _ hxy) ih

private theorem provable_iffp_refl_forall2 {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma] :
    forall xs : List (@Language.expr L),
      List.Forall₂ (fun x y => |-- (x ⟷ y)) xs xs := by
  intro xs
  induction xs with
  | nil =>
      exact List.Forall₂.nil
  | cons x xs ih =>
      exact List.Forall₂.cons (provable_iffp_refl_of_local x) ih

private theorem logic_equiv_refl_forall2 {L : Language.{u}}
    [GammaE : LogicEquiv L] [BasicLogicEquiv L GammaE] :
    forall xs : List (@Language.expr L),
      List.Forall₂ (fun x y => logic_equiv (L := L) x y) xs xs := by
  intro xs
  induction xs with
  | nil =>
      exact List.Forall₂.nil
  | cons x xs ih =>
      exact List.Forall₂.cons (logic_equiv_refl x) ih

def fold_right_prodp_no_unit {L : Language.{u}}
    (prodp : @Language.expr L -> @Language.expr L -> @Language.expr L)
    (e : @Language.expr L) : List (@Language.expr L) -> @Language.expr L
  | [] => e
  | x :: [] => x
  | x :: xs => prodp x (fold_right_prodp_no_unit prodp e xs)

namespace PropositionalLogic.ProofTheoryPatterns.P

export Unifysl.ProofTheoryPatterns.P (
  Adjointness
  Commutativity
  Monotonicity
  Associativity
  LeftUnit
  RightUnit
  LeftDistr
  RightDistr
  adjoint
  prodp_comm_impp
  prodp_mono
  prodp_assoc1
  prodp_assoc2
  left_unit1
  left_unit2
  right_unit1
  right_unit2
  left_distr1
  left_distr2
  right_distr1
  right_distr2
  prodp_mono1
  funcp_mono2
  adjoint_modus_ponens
  adjoint_iter
  Adjoint2Mono
  funcp_mono
  fold_left_mono
  fold_right_mono
  fold_left_mono2
  fold_right_mono2
  assoc_fold_left_cons
  assoc_fold_right_cons
  assoc_fold_left_fold_right
  assoc_fold_right_fold_left
  assoc_prodp_fold_left
  assoc_fold_left_app
  LeftDistr2RightDistr
  RightDistr2LeftDistr
  Build_Associativity1
  Build_Associativity2
)


private theorem orp_Monotonicity_of_rules {L : Language.{u}}
    [MinimumLanguage L] [OrLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [OrAxiomatization L Gamma] :
    ProofTheoryPatternsP.Monotonicity L Gamma orp := by
  constructor
  intro x1 y1 x2 y2 hx hy
  exact provable_orp_impp_of_local x1 y1 (x2 || y2)
    (solve_impp_trans x1 x2 (x2 || y2) hx
      (OrAxiomatization.provable_orp_intros1 x2 y2))
    (solve_impp_trans y1 y2 (x2 || y2) hy
      (OrAxiomatization.provable_orp_intros2 x2 y2))

theorem prodp_comm {L : Language.{u}} [MinimumLanguage L] [IffLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Commutativity L Gamma prodp] :
    forall x y : @Language.expr L,
      |-- (prodp x y ⟷ prodp y x) := by
  intro x y
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.prodp_comm_impp x y)
    (ProofTheoryPatternsP.prodp_comm_impp y x)

theorem left_unit {L : Language.{u}} [MinimumLanguage L] [IffLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L} [ProofTheoryPatternsP.LeftUnit L Gamma e prodp] :
    forall x : @Language.expr L,
      |-- (prodp e x ⟷ x) := by
  intro x
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.left_unit1 (e := e) (prodp := prodp) x)
    (ProofTheoryPatternsP.left_unit2 (e := e) (prodp := prodp) x)

theorem right_unit {L : Language.{u}} [MinimumLanguage L] [IffLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L} [ProofTheoryPatternsP.RightUnit L Gamma e prodp] :
    forall x : @Language.expr L,
      |-- (prodp x e ⟷ x) := by
  intro x
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.right_unit1 (e := e) (prodp := prodp) x)
    (ProofTheoryPatternsP.right_unit2 (e := e) (prodp := prodp) x)

theorem prodp_sump_distr_l {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.LeftDistr L Gamma prodp sump] :
    forall x y z : @Language.expr L,
      |-- (prodp x (sump y z) ⟷ sump (prodp x y) (prodp x z)) := by
  intro x y z
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.left_distr1 (prodp := prodp) (sump := sump) x y z)
    (ProofTheoryPatternsP.left_distr2 (prodp := prodp) (sump := sump) x y z)

theorem prodp_sump_distr_r {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.RightDistr L Gamma prodp sump] :
    forall x y z : @Language.expr L,
      |-- (prodp (sump y z) x ⟷ sump (prodp y x) (prodp z x)) := by
  intro x y z
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.right_distr1 (prodp := prodp) (sump := sump) x y z)
    (ProofTheoryPatternsP.right_distr2 (prodp := prodp) (sump := sump) x y z)

theorem Adjoint2RDistr {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [OrAxiomatization L Gamma]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Adjointness L Gamma prodp funcp] :
    ProofTheoryPatternsP.RightDistr L Gamma prodp orp := by
  constructor
  · intro x y z
    let target : @Language.expr L := prodp y x || prodp z x
    have hy : |-- (y ⟶ funcp x target) :=
      (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
        y x target).mp (OrAxiomatization.provable_orp_intros1 (prodp y x) (prodp z x))
    have hz : |-- (z ⟶ funcp x target) :=
      (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
        z x target).mp (OrAxiomatization.provable_orp_intros2 (prodp y x) (prodp z x))
    exact (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
      (y || z) x target).mpr (provable_orp_impp_of_local y z (funcp x target) hy hz)
  · intro x y z
    exact provable_orp_impp_of_local (prodp y x) (prodp z x) (prodp (y || z) x)
      (ProofTheoryPatternsP.prodp_mono1 (prodp := prodp) (funcp := funcp)
        y (y || z) x (OrAxiomatization.provable_orp_intros1 y z))
      (ProofTheoryPatternsP.prodp_mono1 (prodp := prodp) (funcp := funcp)
        z (y || z) x (OrAxiomatization.provable_orp_intros2 y z))

theorem Adjoint2LDistr {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [OrAxiomatization L Gamma]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Adjointness L Gamma prodp funcp] [ProofTheoryPatternsP.Commutativity L Gamma prodp] :
    ProofTheoryPatternsP.LeftDistr L Gamma prodp orp := by
  letI : ProofTheoryPatternsP.Monotonicity L Gamma orp := orp_Monotonicity_of_rules
  letI : ProofTheoryPatternsP.RightDistr L Gamma prodp orp :=
    Adjoint2RDistr (prodp := prodp) (funcp := funcp)
  exact ProofTheoryPatternsP.RightDistr2LeftDistr (prodp := prodp) (sump := orp)

theorem prodp_orp_distr_l {L : Language.{u}} [MinimumLanguage L]
    [OrLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [OrAxiomatization L Gamma]
    [IffAxiomatization L Gamma]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Adjointness L Gamma prodp funcp] :
    forall x y z : @Language.expr L,
      |-- (prodp (x || y) z ⟷ (prodp x z || prodp y z)) := by
  intro x y z
  letI : ProofTheoryPatternsP.RightDistr L Gamma prodp orp :=
    Adjoint2RDistr (prodp := prodp) (funcp := funcp)
  exact prodp_sump_distr_r (prodp := prodp) (sump := orp) z x y

theorem prodp_orp_distr_r {L : Language.{u}} [MinimumLanguage L]
    [OrLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [OrAxiomatization L Gamma]
    [IffAxiomatization L Gamma]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Adjointness L Gamma prodp funcp] [ProofTheoryPatternsP.Commutativity L Gamma prodp] :
    forall x y z : @Language.expr L,
      |-- (prodp x (y || z) ⟷ (prodp x y || prodp x z)) := by
  intro x y z
  letI : ProofTheoryPatternsP.LeftDistr L Gamma prodp orp :=
    Adjoint2LDistr (prodp := prodp) (funcp := funcp)
  exact prodp_sump_distr_l (prodp := prodp) (sump := orp) x y z

theorem orp_funcp {L : Language.{u}} [MinimumLanguage L] [OrLanguage L]
    [IffLanguage L] [AndLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [OrAxiomatization L Gamma]
    [IffAxiomatization L Gamma] [AndAxiomatization L Gamma]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Adjointness L Gamma prodp funcp] [ProofTheoryPatternsP.Commutativity L Gamma prodp] :
    forall x y z : @Language.expr L,
      |-- (funcp (x || y) z ⟷ (funcp x z && funcp y z)) := by
  intro x y z
  letI : ProofTheoryPatternsP.Monotonicity L Gamma prodp :=
    ProofTheoryPatternsP.Adjoint2Mono (prodp := prodp) (funcp := funcp)
  let A : @Language.expr L := funcp x z && funcp y z
  have hleft : |-- (funcp (x || y) z ⟶ A) :=
    provable_impp_andp_of_local (funcp (x || y) z) (funcp x z) (funcp y z)
      (ProofTheoryPatternsP.funcp_mono (prodp := prodp) (funcp := funcp)
        (x || y) z x z (OrAxiomatization.provable_orp_intros1 x y)
        (provable_impp_refl z))
      (ProofTheoryPatternsP.funcp_mono (prodp := prodp) (funcp := funcp)
        (x || y) z y z (OrAxiomatization.provable_orp_intros2 x y)
        (provable_impp_refl z))
  have hright : |-- (A ⟶ funcp (x || y) z) := by
    letI : ProofTheoryPatternsP.LeftDistr L Gamma prodp orp :=
      Adjoint2LDistr (prodp := prodp) (funcp := funcp)
    have htoOr : |-- (prodp A (x || y) ⟶ (prodp A x || prodp A y)) :=
      ProofTheoryPatternsP.left_distr1 (prodp := prodp) (sump := orp) A x y
    have hxcase : |-- (prodp A x ⟶ z) :=
      (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
        A x z).mpr (AndAxiomatization.provable_andp_elim1 (funcp x z) (funcp y z))
    have hycase : |-- (prodp A y ⟶ z) :=
      (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
        A y z).mpr (AndAxiomatization.provable_andp_elim2 (funcp x z) (funcp y z))
    have hprod : |-- (prodp A (x || y) ⟶ z) :=
      solve_impp_trans (prodp A (x || y)) (prodp A x || prodp A y) z
        htoOr (provable_orp_impp_of_local (prodp A x) (prodp A y) z hxcase hycase)
    exact (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
      A (x || y) z).mp hprod
  exact provable_iffp_intro_of_local _ _ hleft hright

theorem funcp_andp_distr_r {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [AndLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    [AndAxiomatization L Gamma]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Adjointness L Gamma prodp funcp] :
    forall x y z : @Language.expr L,
      |-- (funcp x (y && z) ⟷ (funcp x y && funcp x z)) := by
  intro x y z
  let A : @Language.expr L := funcp x y && funcp x z
  have hleft : |-- (funcp x (y && z) ⟶ A) :=
    provable_impp_andp_of_local (funcp x (y && z)) (funcp x y) (funcp x z)
      (ProofTheoryPatternsP.funcp_mono2 (prodp := prodp) (funcp := funcp)
        x (y && z) y (AndAxiomatization.provable_andp_elim1 y z))
      (ProofTheoryPatternsP.funcp_mono2 (prodp := prodp) (funcp := funcp)
        x (y && z) z (AndAxiomatization.provable_andp_elim2 y z))
  have hright : |-- (A ⟶ funcp x (y && z)) := by
    have hycase : |-- (prodp A x ⟶ y) :=
      (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
        A x y).mpr (AndAxiomatization.provable_andp_elim1 (funcp x y) (funcp x z))
    have hzcase : |-- (prodp A x ⟶ z) :=
      (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
        A x z).mpr (AndAxiomatization.provable_andp_elim2 (funcp x y) (funcp x z))
    have hprod : |-- (prodp A x ⟶ (y && z)) :=
      provable_impp_andp_of_local (prodp A x) y z hycase hzcase
    exact (ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
      A x (y && z)).mp hprod
  exact provable_iffp_intro_of_local _ _ hleft hright

theorem falsep_prodp {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [FalseLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    [FalseAxiomatization L Gamma]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Adjointness L Gamma prodp funcp] :
    forall x : @Language.expr L,
      |-- (prodp FF x ⟷ FF) := by
  intro x
  exact provable_iffp_intro_of_local _ _
    ((ProofTheoryPatternsP.adjoint (prodp := prodp) (funcp := funcp)
      FF x FF).mpr (FalseAxiomatization.provable_falsep_elim (funcp x FF)))
    (FalseAxiomatization.provable_falsep_elim (prodp FF x))

theorem prodp_falsep {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [FalseLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    [FalseAxiomatization L Gamma]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Adjointness L Gamma prodp funcp] [ProofTheoryPatternsP.Commutativity L Gamma prodp] :
    forall x : @Language.expr L,
      |-- (prodp x FF ⟷ FF) := by
  intro x
  exact provable_iffp_trans_of
    (prodp_comm (prodp := prodp) x FF)
    (falsep_prodp (prodp := prodp) (funcp := funcp) x)

theorem prodp_iffp {L : Language.{u}} [MinimumLanguage L] [IffLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Monotonicity L Gamma prodp] :
    forall x1 x2 y1 y2 : @Language.expr L,
      (|-- (x1 ⟷ x2)) -> (|-- (y1 ⟷ y2)) ->
        |-- (prodp x1 y1 ⟷ prodp x2 y2) := by
  intro x1 x2 y1 y2 hx hy
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.prodp_mono (prodp := prodp) x1 y1 x2 y2
      (provable_iffp_elim1_of_local x1 x2 hx)
      (provable_iffp_elim1_of_local y1 y2 hy))
    (ProofTheoryPatternsP.prodp_mono (prodp := prodp) x2 y2 x1 y1
      (provable_iffp_elim2_of_local x1 x2 hx)
      (provable_iffp_elim2_of_local y1 y2 hy))

theorem fold_left_iffp {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Monotonicity L Gamma prodp] :
    forall (x1 x2 : @Language.expr L)
      (xs1 xs2 : List (@Language.expr L)),
      List.Forall₂ (fun x1 x2 => |-- (x1 ⟷ x2)) xs1 xs2 ->
      (|-- (x1 ⟷ x2)) ->
        |-- (List.foldl prodp x1 xs1 ⟷ List.foldl prodp x2 xs2) := by
  intro x1 x2 xs1 xs2 hxs hx
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.fold_left_mono (prodp := prodp) x1 x2 xs1 xs2
      (provable_iffp_forall2_left hxs)
      (provable_iffp_elim1_of_local x1 x2 hx))
    (ProofTheoryPatternsP.fold_left_mono (prodp := prodp) x2 x1 xs2 xs1
      (provable_iffp_forall2_right hxs)
      (provable_iffp_elim2_of_local x1 x2 hx))

theorem fold_left_prodp_unfold {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Monotonicity L Gamma prodp]
    {e : @Language.expr L} [ProofTheoryPatternsP.LeftUnit L Gamma e prodp] :
    forall xs : List (@Language.expr L),
      |-- (List.foldl prodp e xs ⟷
        match xs with
        | [] => e
        | x :: xs0 => List.foldl prodp x xs0) := by
  intro xs
  cases xs with
  | nil =>
      simp
      exact provable_iffp_refl_of_local e
  | cons x xs =>
      simp [List.foldl]
      exact fold_left_iffp (prodp := prodp) (prodp e x) x xs xs
        (provable_iffp_refl_forall2 xs)
        (left_unit (prodp := prodp) (e := e) x)

theorem fold_right_prodp_unfold {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Monotonicity L Gamma prodp]
    {e : @Language.expr L} [ProofTheoryPatternsP.RightUnit L Gamma e prodp] :
    forall xs : List (@Language.expr L),
      |-- (List.foldr prodp e xs ⟷ fold_right_prodp_no_unit prodp e xs) := by
  intro xs
  cases xs with
  | nil =>
      simp [fold_right_prodp_no_unit]
      exact provable_iffp_refl_of_local e
  | cons x xs =>
      induction xs generalizing x with
      | nil =>
          simp [fold_right_prodp_no_unit, List.foldr]
          exact right_unit (prodp := prodp) (e := e) x
      | cons y ys ih =>
          simp [fold_right_prodp_no_unit, List.foldr]
          exact prodp_iffp (prodp := prodp)
            x x (List.foldr prodp e (y :: ys))
            (fold_right_prodp_no_unit prodp e (y :: ys))
            (provable_iffp_refl_of_local x) (ih y)

theorem prodp_assoc {L : Language.{u}} [MinimumLanguage L] [IffLanguage L]
    [Gamma : Provable L] [MinimumAxiomatization L Gamma]
    [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [ProofTheoryPatternsP.Associativity L Gamma prodp] :
    forall x y z : @Language.expr L,
      |-- (prodp x (prodp y z) ⟷ prodp (prodp x y) z) := by
  intro x y z
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.prodp_assoc1 (prodp := prodp) x y z)
    (ProofTheoryPatternsP.prodp_assoc2 (prodp := prodp) x y z)

theorem assoc_fold_left_fold_right_equiv {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L}
    [ProofTheoryPatternsP.Monotonicity L Gamma prodp] [ProofTheoryPatternsP.Associativity L Gamma prodp]
    [ProofTheoryPatternsP.LeftUnit L Gamma e prodp] [ProofTheoryPatternsP.RightUnit L Gamma e prodp] :
    forall xs : List (@Language.expr L),
      |-- (List.foldl prodp e xs ⟷ List.foldr prodp e xs) := by
  intro xs
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.assoc_fold_left_fold_right
      (prodp := prodp) (e := e) xs)
    (ProofTheoryPatternsP.assoc_fold_right_fold_left
      (prodp := prodp) (e := e) xs)

theorem assoc_prodp_fold_left_equiv {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L}
    [ProofTheoryPatternsP.Monotonicity L Gamma prodp] [ProofTheoryPatternsP.Associativity L Gamma prodp]
    [ProofTheoryPatternsP.LeftUnit L Gamma e prodp] [ProofTheoryPatternsP.RightUnit L Gamma e prodp] :
    forall xs1 xs2 : List (@Language.expr L),
      |-- (prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2) ⟷
        List.foldl prodp e (xs1 ++ xs2)) := by
  intro xs1 xs2
  exact provable_iffp_intro_of_local _ _
    (ProofTheoryPatternsP.assoc_prodp_fold_left
      (prodp := prodp) (e := e) xs1 xs2)
    (ProofTheoryPatternsP.assoc_fold_left_app
      (prodp := prodp) (e := e) xs1 xs2)

theorem assoc_fold_left_Permutation {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L}
    [ProofTheoryPatternsP.Monotonicity L Gamma prodp] [ProofTheoryPatternsP.Commutativity L Gamma prodp]
    [ProofTheoryPatternsP.Associativity L Gamma prodp] :
    forall (x : @Language.expr L) (ys1 ys2 : List (@Language.expr L)),
      ys1.Perm ys2 ->
        |-- (List.foldl prodp x ys1 ⟷ List.foldl prodp x ys2) := by
  intro x ys1 ys2 hperm
  let R : @Language.expr L -> @Language.expr L -> Prop :=
    fun a b => |-- (a ⟷ b)
  let Req : Equivalence R := {
    refl := by
      intro a
      exact provable_iffp_refl_of_local a
    symm := by
      intro a b hab
      exact provable_iffp_symm_of hab
    trans := by
      intro a b c hab hbc
      exact provable_iffp_trans_of hab hbc
  }
  letI : Proper (R ==> Eq ==> R) prodp := {
    proper := by
      intro x1 x2 hx z1 z2 hz
      cases hz
      exact prodp_iffp (prodp := prodp) x1 x2 z1 z1 hx
        (provable_iffp_refl_of_local z1)
  }
  have hswap :
      forall x1 x2 y z : @Language.expr L,
        R x1 x2 -> R (prodp (prodp x1 y) z) (prodp (prodp x2 z) y) := by
    intro x1 x2 y z hx
    have h1 : R (prodp (prodp x1 y) z) (prodp x1 (prodp y z)) :=
      Req.symm
        (prodp_assoc (prodp := prodp) x1 y z)
    have h2 : R (prodp x1 (prodp y z)) (prodp x2 (prodp z y)) :=
      prodp_iffp (prodp := prodp) x1 x2 (prodp y z) (prodp z y)
        hx (prodp_comm (prodp := prodp) y z)
    have h3 : R (prodp x2 (prodp z y)) (prodp (prodp x2 z) y) :=
      prodp_assoc (prodp := prodp) x2 z y
    exact Req.trans h1 (Req.trans h2 h3)
  exact (proper_permutation_fold_left (RA := R) (EqRA := Req)
    (f := prodp) hswap).proper ys1 ys2 hperm x x (Req.refl x)

theorem Build_LeftUnit' {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {e : @Language.expr L}
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L} :
    (forall x : @Language.expr L, |-- (prodp e x ⟷ x)) ->
      ProofTheoryPatternsP.LeftUnit L Gamma e prodp := by
  intro h
  constructor
  · intro x
    exact provable_iffp_elim1_of_local (prodp e x) x (h x)
  · intro x
    exact provable_iffp_elim2_of_local (prodp e x) x (h x)

theorem Build_RightUnit' {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {e : @Language.expr L}
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L} :
    (forall x : @Language.expr L, |-- (prodp x e ⟷ x)) ->
      ProofTheoryPatternsP.RightUnit L Gamma e prodp := by
  intro h
  constructor
  · intro x
    exact provable_iffp_elim1_of_local (prodp x e) x (h x)
  · intro x
    exact provable_iffp_elim2_of_local (prodp x e) x (h x)

theorem Build_Associativity' {L : Language.{u}} [MinimumLanguage L]
    [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L} :
    (forall x y z : @Language.expr L,
      |-- (prodp (prodp x y) z ⟷ prodp x (prodp y z))) ->
      ProofTheoryPatternsP.Associativity L Gamma prodp := by
  intro h
  constructor
  · intro x y z
    exact provable_iffp_elim2_of_local (prodp (prodp x y) z) (prodp x (prodp y z))
      (h x y z)
  · intro x y z
    exact provable_iffp_elim1_of_local (prodp (prodp x y) z) (prodp x (prodp y z))
      (h x y z)

end PropositionalLogic.ProofTheoryPatterns.P

section DerivableRules

variable {L : Language.{u}} [MinimumLanguage L]
variable [AndLanguage L] [OrLanguage L] [FalseLanguage L] [NegLanguage L]
variable [IffLanguage L] [TrueLanguage L]
variable [Gamma : Provable L]
variable [MinimumAxiomatization L Gamma]
variable [AndAxiomatization L Gamma] [OrAxiomatization L Gamma]
variable [FalseAxiomatization L Gamma]
variable [IntuitionisticNegAxiomatization L Gamma]
variable [IffAxiomatization L Gamma] [TrueAxiomatization L Gamma]

theorem falsep_andp :
    forall x : @Language.expr L,
      |-- ((FF && x) ⟷ FF) := by
  intro x
  letI : ProofTheoryPatternsP.Adjointness L Gamma andp impp := impp_andp_Adjoint
  exact PropositionalLogic.ProofTheoryPatterns.P.falsep_prodp
    (prodp := andp) (funcp := impp) x

theorem andp_falsep :
    forall x : @Language.expr L,
      |-- ((x && FF) ⟷ FF) := by
  intro x
  letI : ProofTheoryPatternsP.Adjointness L Gamma andp impp := impp_andp_Adjoint
  letI : ProofTheoryPatternsP.Commutativity L Gamma andp := andp_Comm
  exact PropositionalLogic.ProofTheoryPatterns.P.prodp_falsep
    (prodp := andp) (funcp := impp) x

theorem andp_orp_distr_l :
    forall x y z : @Language.expr L,
      |-- (((x || y) && z) ⟷ ((x && z) || (y && z))) := by
  intro x y z
  letI : ProofTheoryPatternsP.Adjointness L Gamma andp impp := impp_andp_Adjoint
  exact PropositionalLogic.ProofTheoryPatterns.P.prodp_orp_distr_l
    (prodp := andp) (funcp := impp) x y z

theorem andp_orp_distr_r :
    forall x y z : @Language.expr L,
      |-- ((x && (y || z)) ⟷ ((x && y) || (x && z))) := by
  intro x y z
  letI : ProofTheoryPatternsP.Adjointness L Gamma andp impp := impp_andp_Adjoint
  letI : ProofTheoryPatternsP.Commutativity L Gamma andp := andp_Comm
  exact PropositionalLogic.ProofTheoryPatterns.P.prodp_orp_distr_r
    (prodp := andp) (funcp := impp) x y z

variable [IterAndLanguage L]
variable [IterAndAxiomatization_left L Gamma]

theorem provable_iter_andp_sepc_right :
    forall xs : List (@Language.expr L),
      |-- (iter_andp xs ⟷ List.foldr andp TT xs) := by
  intro xs
  letI : ProofTheoryPatternsP.Monotonicity L Gamma andp := andp_Mono
  letI : ProofTheoryPatternsP.Associativity L Gamma andp := andp_Assoc
  letI : ProofTheoryPatternsP.LeftUnit L Gamma TT andp := andp_LU
  letI : ProofTheoryPatternsP.RightUnit L Gamma TT andp := andp_RU
  have hleft : |-- (iter_andp xs ⟷ List.foldl andp TT xs) :=
    IterAndAxiomatization_left.provable_iter_andp_spec_left (Gamma := Gamma) xs
  have hfold : |-- (List.foldl andp TT xs ⟷ List.foldr andp TT xs) :=
    PropositionalLogic.ProofTheoryPatterns.P.assoc_fold_left_fold_right_equiv
      (prodp := andp) (e := TT) xs
  exact provable_iffp_trans_of hleft hfold

theorem provable_iter_andp_unfold_right_assoc :
    forall xs : List (@Language.expr L),
      |-- (iter_andp xs ⟷ fold_right_prodp_no_unit andp TT xs) := by
  intro xs
  letI : ProofTheoryPatternsP.Monotonicity L Gamma andp := andp_Mono
  letI : ProofTheoryPatternsP.RightUnit L Gamma TT andp := andp_RU
  have hspec : |-- (iter_andp xs ⟷ List.foldr andp TT xs) :=
    provable_iter_andp_sepc_right xs
  have hunfold : |-- (List.foldr andp TT xs ⟷ fold_right_prodp_no_unit andp TT xs) :=
    PropositionalLogic.ProofTheoryPatterns.P.fold_right_prodp_unfold
      (prodp := andp) (e := TT) xs
  exact provable_iffp_trans_of hspec hunfold

theorem provable_iter_andp_unfold_left_assoc :
    forall xs : List (@Language.expr L),
      |-- (iter_andp xs ⟷
        match xs with
        | [] => TT
        | x :: xs0 => List.foldl andp x xs0) := by
  intro xs
  letI : ProofTheoryPatternsP.Monotonicity L Gamma andp := andp_Mono
  letI : ProofTheoryPatternsP.LeftUnit L Gamma TT andp := andp_LU
  have hleft : |-- (iter_andp xs ⟷ List.foldl andp TT xs) :=
    IterAndAxiomatization_left.provable_iter_andp_spec_left (Gamma := Gamma) xs
  have hunfold :=
    PropositionalLogic.ProofTheoryPatterns.P.fold_left_prodp_unfold
      (prodp := andp) (e := TT) xs
  simpa using provable_iffp_trans_of hleft hunfold

theorem iter_andp_multi_imp :
    forall (xs : List (@Language.expr L)) (y : @Language.expr L),
      |-- ((iter_andp xs ⟶ y) ⟷ multi_imp xs y) := by
  intro xs y
  have hspec : |-- (iter_andp xs ⟷ List.foldr andp TT xs) :=
    provable_iter_andp_sepc_right xs
  have himpSpec :
      |-- ((iter_andp xs ⟶ y) ⟷ (List.foldr andp TT xs ⟶ y)) :=
    (provables_impp_proper_iffp (L := L) (GammaP := Gamma)).proper
      (iter_andp xs) (List.foldr andp TT xs) hspec
      y y (provable_iffp_refl_of_local y)
  have hfold :
      forall xs : List (@Language.expr L),
        |-- ((List.foldr andp TT xs ⟶ y) ⟷ multi_imp xs y) := by
    intro xs
    induction xs with
    | nil =>
        simpa [multi_imp] using provable_truep_impp y
    | cons x xs ih =>
        have hcur :
            |-- (((x && List.foldr andp TT xs) ⟶ y) ⟷
              (x ⟶ List.foldr andp TT xs ⟶ y)) :=
          provable_iffp_symm_of
            (Unifysl.provable_andp_impp (L := L) (Gamma := Gamma)
              x (List.foldr andp TT xs) y)
        have hcongr :
            |-- ((x ⟶ List.foldr andp TT xs ⟶ y) ⟷
              (x ⟶ multi_imp xs y)) :=
          (provables_impp_proper_iffp (L := L) (GammaP := Gamma)).proper
            x x (provable_iffp_refl_of_local x)
            (List.foldr andp TT xs ⟶ y) (multi_imp xs y) ih
        simpa [List.foldr, multi_imp] using
          provable_iffp_trans_of hcur hcongr
  exact provable_iffp_trans_of himpSpec (hfold xs)

end DerivableRules

namespace PropositionalLogic.ProofTheoryPatterns.D1

export Unifysl.ProofTheoryPatterns.D1 (
  Adjointness
  Commutativity
  Monotonicity
  Associativity
  LeftUnit
  RightUnit
  LeftDistr
  RightDistr
  adjoint
  derivable1_prodp_comm
  prodp_mono
  prodp_assoc1
  prodp_assoc2
  left_unit1
  left_unit2
  right_unit1
  right_unit2
  left_distr1
  left_distr2
  right_distr1
  right_distr2
  prodp_mono1
  funcp_mono2
  adjoint_modus_ponens
  adjoint_iter
  Adjoint2Mono
  funcp_mono
  fold_left_mono
  fold_right_mono
  fold_left_mono2
  fold_right_mono2
  assoc_fold_left_cons
  assoc_fold_right_cons
  assoc_fold_left_fold_right
  assoc_fold_right_fold_left
  assoc_prodp_fold_left
  assoc_fold_left_app
  LeftDistr2RightDistr
  RightDistr2LeftDistr
  Build_Associativity1
  Build_Associativity2
)


private theorem derivable1_orp_Monotonicity_of_deduction {L : Language.{u}}
    [OrLanguage L] [GammaD1 : Derivable1 L]
    [BasicDeduction L GammaD1] [OrDeduction L GammaD1] :
    Unifysl.Monotonicity L GammaD1 orp := by
  constructor
  intro x1 y1 x2 y2 hx hy
  exact derivable1_orp_mono x1 x2 y1 y2 hx hy

theorem prodp_comm {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Commutativity L GammaD1 prodp] :
    forall x y : @Language.expr L,
      logic_equiv (L := L) (prodp x y) (prodp y x) := by
  intro x y
  exact logic_equiv_of_derivable1
    (Unifysl.derivable1_prodp_comm (prodp := prodp) x y)
    (Unifysl.derivable1_prodp_comm (prodp := prodp) y x)

theorem left_unit {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L} [Unifysl.LeftUnit L GammaD1 e prodp] :
    forall x : @Language.expr L,
      logic_equiv (L := L) (prodp e x) x := by
  intro x
  exact logic_equiv_of_derivable1
    (Unifysl.left_unit1 (e := e) (prodp := prodp) x)
    (Unifysl.left_unit2 (e := e) (prodp := prodp) x)

theorem right_unit {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L} [Unifysl.RightUnit L GammaD1 e prodp] :
    forall x : @Language.expr L,
      logic_equiv (L := L) (prodp x e) x := by
  intro x
  exact logic_equiv_of_derivable1
    (Unifysl.right_unit1 (e := e) (prodp := prodp) x)
    (Unifysl.right_unit2 (e := e) (prodp := prodp) x)

theorem prodp_sump_distr_l {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.LeftDistr L GammaD1 prodp sump] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (prodp x (sump y z))
        (sump (prodp x y) (prodp x z)) := by
  intro x y z
  exact logic_equiv_of_derivable1
    (Unifysl.left_distr1 (prodp := prodp) (sump := sump) x y z)
    (Unifysl.left_distr2 (prodp := prodp) (sump := sump) x y z)

theorem prodp_sump_distr_r {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp sump : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.RightDistr L GammaD1 prodp sump] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (prodp (sump y z) x)
        (sump (prodp y x) (prodp z x)) := by
  intro x y z
  exact logic_equiv_of_derivable1
    (Unifysl.right_distr1 (prodp := prodp) (sump := sump) x y z)
    (Unifysl.right_distr2 (prodp := prodp) (sump := sump) x y z)

theorem Adjoint2RDistr {L : Language.{u}} [OrLanguage L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [OrDeduction L GammaD1]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Adjointness L GammaD1 prodp funcp] :
    Unifysl.RightDistr L GammaD1 prodp orp := by
  constructor
  · intro x y z
    let target : @Language.expr L := prodp y x || prodp z x
    have hy : y |-- funcp x target :=
      (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
        y x target).mp
        (OrDeduction.derivable1_orp_intros1 (prodp y x) (prodp z x))
    have hz : z |-- funcp x target :=
      (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
        z x target).mp
        (OrDeduction.derivable1_orp_intros2 (prodp y x) (prodp z x))
    exact (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
      (y || z) x target).mpr
        (OrDeduction.derivable1_orp_elim y z (funcp x target) hy hz)
  · intro x y z
    exact OrDeduction.derivable1_orp_elim (prodp y x) (prodp z x)
      (prodp (y || z) x)
      (Unifysl.prodp_mono1 (prodp := prodp) (funcp := funcp)
        y (y || z) x (OrDeduction.derivable1_orp_intros1 y z))
      (Unifysl.prodp_mono1 (prodp := prodp) (funcp := funcp)
        z (y || z) x (OrDeduction.derivable1_orp_intros2 y z))

theorem Adjoint2LDistr {L : Language.{u}} [OrLanguage L]
    [GammaD1 : Derivable1 L] [BasicDeduction L GammaD1]
    [OrDeduction L GammaD1]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Adjointness L GammaD1 prodp funcp] [Unifysl.Commutativity L GammaD1 prodp] :
    Unifysl.LeftDistr L GammaD1 prodp orp := by
  letI : Unifysl.Monotonicity L GammaD1 orp := derivable1_orp_Monotonicity_of_deduction
  letI : Unifysl.RightDistr L GammaD1 prodp orp :=
    Adjoint2RDistr (prodp := prodp) (funcp := funcp)
  exact Unifysl.RightDistr2LeftDistr (prodp := prodp) (sump := orp)

theorem prodp_orp_distr_l {L : Language.{u}} [OrLanguage L]
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    [OrDeduction L GammaD1]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Adjointness L GammaD1 prodp funcp] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (prodp (x || y) z)
        (prodp x z || prodp y z) := by
  intro x y z
  letI : Unifysl.RightDistr L GammaD1 prodp orp :=
    Adjoint2RDistr (prodp := prodp) (funcp := funcp)
  exact prodp_sump_distr_r (prodp := prodp) (sump := orp) z x y

theorem prodp_orp_distr_r {L : Language.{u}} [OrLanguage L]
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    [OrDeduction L GammaD1]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Adjointness L GammaD1 prodp funcp] [Unifysl.Commutativity L GammaD1 prodp] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (prodp x (y || z))
        (prodp x y || prodp x z) := by
  intro x y z
  letI : Unifysl.LeftDistr L GammaD1 prodp orp :=
    Adjoint2LDistr (prodp := prodp) (funcp := funcp)
  exact prodp_sump_distr_l (prodp := prodp) (sump := orp) x y z

theorem orp_funcp {L : Language.{u}} [OrLanguage L] [AndLanguage L]
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    [OrDeduction L GammaD1] [AndDeduction L GammaD1]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Adjointness L GammaD1 prodp funcp] [Unifysl.Commutativity L GammaD1 prodp] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (funcp (x || y) z)
        (funcp x z && funcp y z) := by
  intro x y z
  letI : Unifysl.Monotonicity L GammaD1 prodp :=
    Unifysl.Adjoint2Mono (prodp := prodp) (funcp := funcp)
  let A : @Language.expr L := funcp x z && funcp y z
  have hleft : funcp (x || y) z |-- A :=
    AndDeduction.derivable1s_truep_intros
      (GammaD1 := GammaD1) (funcp (x || y) z) (funcp x z) (funcp y z)
      (Unifysl.funcp_mono (prodp := prodp) (funcp := funcp)
        (x || y) z x z (OrDeduction.derivable1_orp_intros1 x y)
        (derivable1_refl z))
      (Unifysl.funcp_mono (prodp := prodp) (funcp := funcp)
        (x || y) z y z (OrDeduction.derivable1_orp_intros2 x y)
        (derivable1_refl z))
  have hright : A |-- funcp (x || y) z := by
    letI : Unifysl.LeftDistr L GammaD1 prodp orp :=
      Adjoint2LDistr (prodp := prodp) (funcp := funcp)
    have htoOr : prodp A (x || y) |-- (prodp A x || prodp A y) :=
      Unifysl.left_distr1 (prodp := prodp) (sump := orp) A x y
    have hxcase : prodp A x |-- z :=
      (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
        A x z).mpr
        (AndDeduction.derivable1_andp_elim1
          (GammaD1 := GammaD1) (funcp x z) (funcp y z))
    have hycase : prodp A y |-- z :=
      (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
        A y z).mpr
        (AndDeduction.derivable1_andp_elim2
          (GammaD1 := GammaD1) (funcp x z) (funcp y z))
    have hprod : prodp A (x || y) |-- z :=
      derivable1_trans (prodp A (x || y)) (prodp A x || prodp A y) z
        htoOr (OrDeduction.derivable1_orp_elim (prodp A x) (prodp A y) z hxcase hycase)
    exact (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
      A (x || y) z).mp hprod
  exact logic_equiv_of_derivable1 hleft hright

theorem funcp_andp_distr_r {L : Language.{u}} [AndLanguage L]
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    [AndDeduction L GammaD1]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Adjointness L GammaD1 prodp funcp] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (funcp x (y && z))
        (funcp x y && funcp x z) := by
  intro x y z
  let A : @Language.expr L := funcp x y && funcp x z
  have hleft : funcp x (y && z) |-- A :=
    AndDeduction.derivable1s_truep_intros
      (GammaD1 := GammaD1) (funcp x (y && z)) (funcp x y) (funcp x z)
      (Unifysl.funcp_mono2 (prodp := prodp) (funcp := funcp)
        x (y && z) y
        (AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) y z))
      (Unifysl.funcp_mono2 (prodp := prodp) (funcp := funcp)
        x (y && z) z
        (AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) y z))
  have hright : A |-- funcp x (y && z) := by
    have hycase : prodp A x |-- y :=
      (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
        A x y).mpr
        (AndDeduction.derivable1_andp_elim1
          (GammaD1 := GammaD1) (funcp x y) (funcp x z))
    have hzcase : prodp A x |-- z :=
      (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
        A x z).mpr
        (AndDeduction.derivable1_andp_elim2
          (GammaD1 := GammaD1) (funcp x y) (funcp x z))
    have hprod : prodp A x |-- (y && z) :=
      AndDeduction.derivable1s_truep_intros
        (GammaD1 := GammaD1) (prodp A x) y z hycase hzcase
    exact (Unifysl.adjoint (prodp := prodp) (funcp := funcp)
      A x (y && z)).mp hprod
  exact logic_equiv_of_derivable1 hleft hright

theorem falsep_prodp {L : Language.{u}} [FalseLanguage L]
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    [FalseDeduction L GammaD1]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Adjointness L GammaD1 prodp funcp] :
    forall x : @Language.expr L,
      logic_equiv (L := L) (prodp FF x) FF := by
  intro x
  exact logic_equiv_of_derivable1
    ((Unifysl.adjoint (prodp := prodp) (funcp := funcp)
      FF x FF).mpr (FalseDeduction.derivable1_falsep_elim
        (GammaD1 := GammaD1) (funcp x FF)))
    (FalseDeduction.derivable1_falsep_elim (GammaD1 := GammaD1) (prodp FF x))

theorem prodp_falsep {L : Language.{u}} [FalseLanguage L]
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    [FalseDeduction L GammaD1]
    {prodp funcp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Adjointness L GammaD1 prodp funcp] [Unifysl.Commutativity L GammaD1 prodp] :
    forall x : @Language.expr L,
      logic_equiv (L := L) (prodp x FF) FF := by
  intro x
  have hfalse := (__logic_equiv_derivable1 (prodp FF x) FF).mp
    (falsep_prodp (prodp := prodp) (funcp := funcp) x)
  exact logic_equiv_of_derivable1
    (derivable1_trans (prodp x FF) (prodp FF x) FF
      (Unifysl.derivable1_prodp_comm (prodp := prodp) x FF) hfalse.left)
    (FalseDeduction.derivable1_falsep_elim (GammaD1 := GammaD1) (prodp x FF))

theorem prodp_iffp {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Monotonicity L GammaD1 prodp] :
    forall x1 x2 y1 y2 : @Language.expr L,
      logic_equiv (L := L) x1 x2 ->
      logic_equiv (L := L) y1 y2 ->
        logic_equiv (L := L) (prodp x1 y1) (prodp x2 y2) := by
  intro x1 x2 y1 y2 hx hy
  have hxD := (__logic_equiv_derivable1 x1 x2).mp hx
  have hyD := (__logic_equiv_derivable1 y1 y2).mp hy
  exact logic_equiv_of_derivable1
    (Unifysl.prodp_mono (prodp := prodp) x1 y1 x2 y2 hxD.left hyD.left)
    (Unifysl.prodp_mono (prodp := prodp) x2 y2 x1 y1 hxD.right hyD.right)

theorem fold_left_iffp {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Monotonicity L GammaD1 prodp] :
    forall (x1 x2 : @Language.expr L)
      (xs1 xs2 : List (@Language.expr L)),
      List.Forall₂ (fun x1 x2 => logic_equiv (L := L) x1 x2) xs1 xs2 ->
      logic_equiv (L := L) x1 x2 ->
        logic_equiv (L := L)
          (List.foldl prodp x1 xs1) (List.foldl prodp x2 xs2) := by
  intro x1 x2 xs1 xs2 hxs hx
  have hxD := (__logic_equiv_derivable1 x1 x2).mp hx
  exact logic_equiv_of_derivable1
    (Unifysl.fold_left_mono (prodp := prodp) x1 x2 xs1 xs2
      (logic_equiv_forall2_left hxs) hxD.left)
    (Unifysl.fold_left_mono (prodp := prodp) x2 x1 xs2 xs1
      (logic_equiv_forall2_right hxs) hxD.right)

theorem fold_left_prodp_unfold {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Monotonicity L GammaD1 prodp]
    {e : @Language.expr L} [Unifysl.LeftUnit L GammaD1 e prodp] :
    forall xs : List (@Language.expr L),
      logic_equiv (L := L) (List.foldl prodp e xs)
        (match xs with
        | [] => e
        | x :: xs0 => List.foldl prodp x xs0) := by
  intro xs
  cases xs with
  | nil =>
      simp
      exact logic_equiv_refl e
  | cons x xs =>
      simp [List.foldl]
      exact fold_left_iffp (prodp := prodp) (prodp e x) x xs xs
        (logic_equiv_refl_forall2 xs)
        (left_unit (prodp := prodp) (e := e) x)

theorem fold_right_prodp_unfold {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Monotonicity L GammaD1 prodp]
    {e : @Language.expr L} [Unifysl.RightUnit L GammaD1 e prodp] :
    forall xs : List (@Language.expr L),
      logic_equiv (L := L) (List.foldr prodp e xs)
        (fold_right_prodp_no_unit prodp e xs) := by
  intro xs
  cases xs with
  | nil =>
      simp [fold_right_prodp_no_unit]
      exact logic_equiv_refl e
  | cons x xs =>
      induction xs generalizing x with
      | nil =>
          simp [fold_right_prodp_no_unit, List.foldr]
          exact right_unit (prodp := prodp) (e := e) x
      | cons y ys ih =>
          simp [fold_right_prodp_no_unit, List.foldr]
          exact prodp_iffp (prodp := prodp)
            x x (List.foldr prodp e (y :: ys))
            (fold_right_prodp_no_unit prodp e (y :: ys))
            (logic_equiv_refl x) (ih y)

theorem prodp_assoc {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    [Unifysl.Associativity L GammaD1 prodp] :
    forall x y z : @Language.expr L,
      logic_equiv (L := L) (prodp x (prodp y z)) (prodp (prodp x y) z) := by
  intro x y z
  exact logic_equiv_of_derivable1
    (Unifysl.prodp_assoc1 (prodp := prodp) x y z)
    (Unifysl.prodp_assoc2 (prodp := prodp) x y z)

theorem assoc_fold_left_fold_right_equiv {L : Language.{u}}
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L}
    [Unifysl.Monotonicity L GammaD1 prodp] [Unifysl.Associativity L GammaD1 prodp]
    [Unifysl.LeftUnit L GammaD1 e prodp] [Unifysl.RightUnit L GammaD1 e prodp] :
    forall xs : List (@Language.expr L),
      logic_equiv (L := L) (List.foldl prodp e xs) (List.foldr prodp e xs) := by
  intro xs
  exact logic_equiv_of_derivable1
    (Unifysl.assoc_fold_left_fold_right (prodp := prodp) (e := e) xs)
    (Unifysl.assoc_fold_right_fold_left (prodp := prodp) (e := e) xs)

theorem assoc_prodp_fold_left_equiv {L : Language.{u}}
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L}
    [Unifysl.Monotonicity L GammaD1 prodp] [Unifysl.Associativity L GammaD1 prodp]
    [Unifysl.LeftUnit L GammaD1 e prodp] [Unifysl.RightUnit L GammaD1 e prodp] :
    forall xs1 xs2 : List (@Language.expr L),
      logic_equiv (L := L)
        (prodp (List.foldl prodp e xs1) (List.foldl prodp e xs2))
        (List.foldl prodp e (xs1 ++ xs2)) := by
  intro xs1 xs2
  exact logic_equiv_of_derivable1
    (Unifysl.assoc_prodp_fold_left (prodp := prodp) (e := e) xs1 xs2)
    (Unifysl.assoc_fold_left_app (prodp := prodp) (e := e) xs1 xs2)

theorem assoc_fold_left_Permutation {L : Language.{u}}
    [GammaD1 : Derivable1 L] [GammaE : LogicEquiv L]
    [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L}
    {e : @Language.expr L}
    [Unifysl.Monotonicity L GammaD1 prodp] [Unifysl.Commutativity L GammaD1 prodp]
    [Unifysl.Associativity L GammaD1 prodp] :
    forall (x : @Language.expr L) (ys1 ys2 : List (@Language.expr L)),
      ys1.Perm ys2 ->
        logic_equiv (L := L) (List.foldl prodp x ys1) (List.foldl prodp x ys2) := by
  intro x ys1 ys2 hperm
  let R : @Language.expr L -> @Language.expr L -> Prop := logic_equiv (L := L)
  let Req : Equivalence R := {
    refl := by
      intro a
      exact logic_equiv_refl a
    symm := by
      intro a b hab
      exact logic_equiv_symm a b hab
    trans := by
      intro a b c hab hbc
      exact logic_equiv_trans a b c hab hbc
  }
  letI : Proper (R ==> Eq ==> R) prodp := {
    proper := by
      intro x1 x2 hx z1 z2 hz
      cases hz
      exact prodp_iffp (prodp := prodp) x1 x2 z1 z1 hx (logic_equiv_refl z1)
  }
  have hswap :
      forall x1 x2 y z : @Language.expr L,
        R x1 x2 -> R (prodp (prodp x1 y) z) (prodp (prodp x2 z) y) := by
    intro x1 x2 y z hx
    have h1 : R (prodp (prodp x1 y) z) (prodp x1 (prodp y z)) :=
      Req.symm (prodp_assoc (prodp := prodp) x1 y z)
    have h2 : R (prodp x1 (prodp y z)) (prodp x2 (prodp z y)) :=
      prodp_iffp (prodp := prodp) x1 x2 (prodp y z) (prodp z y)
        hx (prodp_comm (prodp := prodp) y z)
    have h3 : R (prodp x2 (prodp z y)) (prodp (prodp x2 z) y) :=
      prodp_assoc (prodp := prodp) x2 z y
    exact Req.trans h1 (Req.trans h2 h3)
  exact (proper_permutation_fold_left (RA := R) (EqRA := Req)
    (f := prodp) hswap).proper ys1 ys2 hperm x x (Req.refl x)

theorem Build_LeftUnit' {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {e : @Language.expr L}
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L} :
    (forall x : @Language.expr L, logic_equiv (L := L) (prodp e x) x) ->
      Unifysl.LeftUnit L GammaD1 e prodp := by
  intro h
  constructor
  · intro x
    exact ((__logic_equiv_derivable1 (prodp e x) x).mp (h x)).left
  · intro x
    exact ((__logic_equiv_derivable1 (prodp e x) x).mp (h x)).right

theorem Build_RightUnit' {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {e : @Language.expr L}
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L} :
    (forall x : @Language.expr L, logic_equiv (L := L) (prodp x e) x) ->
      Unifysl.RightUnit L GammaD1 e prodp := by
  intro h
  constructor
  · intro x
    exact ((__logic_equiv_derivable1 (prodp x e) x).mp (h x)).left
  · intro x
    exact ((__logic_equiv_derivable1 (prodp x e) x).mp (h x)).right

theorem Build_Associativity' {L : Language.{u}} [GammaD1 : Derivable1 L]
    [GammaE : LogicEquiv L] [EquivDerivable1 L GammaD1 GammaE]
    [BasicDeduction L GammaD1] [BasicLogicEquiv L GammaE]
    {prodp : @Language.expr L -> @Language.expr L -> @Language.expr L} :
    (forall x y z : @Language.expr L,
      logic_equiv (L := L) (prodp (prodp x y) z) (prodp x (prodp y z))) ->
      Unifysl.Associativity L GammaD1 prodp := by
  intro h
  constructor
  · intro x y z
    exact ((__logic_equiv_derivable1 (prodp (prodp x y) z)
      (prodp x (prodp y z))).mp (h x y z)).right
  · intro x y z
    exact ((__logic_equiv_derivable1 (prodp (prodp x y) z)
      (prodp x (prodp y z))).mp (h x y z)).left

end PropositionalLogic.ProofTheoryPatterns.D1

end Unifysl
