/-
Coq inventory from `unifysl-prp/SeparationLogic/Model/OSAGenerators.v`.

Active declarations migrated here:
- trivial_Join, trivial_SA, trivial_uSA, trivial_incrSA
- unit_Join, unit_SA, unit_uSA, unit_dSA, unit_incrSA,
  unit_residual, unit_unital
- equiv_Join, equiv_SA, identity_uSA, equiv_incrSA, ikiM_uSA,
  ikiM_dSA, equiv_Unit, equiv_UJR
- option_join, option_Join, option_SA, option_ord_uSA,
  option_ord_dSA, option_ord_incr_None, option_ord_res_None,
  option_ord_USA, option_disj_uSA, option_disj_dSA,
  option_disj_incr_None, option_disj_res_None, option_disj_USA,
  option_disj_USA', option_Unit, option_UJR
- fun_Join, fun_SA, fun_uSA, fun_dSA, fun_incrSA, fun_unitSA,
  fun_unitSA', fun_Unit, fun_UJR
- sum_join, sum_Join, sum_SA
- prod_Join, prod_SA, prod_uSA, prod_dSA, prod_incr, prod_incrSA,
  prod_residualSA, prod_unitalSA, prod_Unit, prod_UJR
- SeparationAlgebra_unit.unit, SeparationAlgebra_unit.unit_join,
  SeparationAlgebra_unit.unit_spec

Legacy/example declarations inside Coq comment blocks are intentionally omitted,
including trivial_UJR, sum_UJR, nat_le_kiM, SAu_kiM, Heap, Stack, and
StepIndex_* examples.
-/

import Unifysl.SeparationLogic.Model.OrderedSA

universe u v w

namespace Unifysl

set_option linter.unusedVariables false

open Relation_ext

section trivialSA

def trivial_Join (worlds : Type u) : Join worlds where
  join := fun _ _ _ => False

def trivial_SA (worlds : Type u) :
    @SeparationAlgebra worlds (trivial_Join worlds) := by
  letI : Join worlds := trivial_Join worlds
  exact
    { join_comm := by
        intro m1 m2 m h
        cases h
      join_assoc := by
        intro mx my mz mxy mxyz h _
        cases h }

def trivial_uSA {worlds : Type u} [Relation worlds] :
    @UpwardsClosedSeparationAlgebra worlds _ (trivial_Join worlds) := by
  letI : Join worlds := trivial_Join worlds
  exact
    { join_Korder_up := by
        intro m n m1 m2 h _
        cases h }

def trivial_incrSA (worlds : Type u) :
    @IncreasingSeparationAlgebra worlds
      { Krelation := fun x y => x = y } (trivial_Join worlds) := by
  letI : Relation worlds := { Krelation := fun x y => x = y }
  letI : Join worlds := trivial_Join worlds
  exact
    { all_increasing := by
        intro x n n' h
        cases h }

end trivialSA

section unitSA

def unit_Join : Join PUnit where
  join := fun _ _ _ => True

def unit_SA : @SeparationAlgebra PUnit unit_Join := by
  letI : Join PUnit := unit_Join
  exact
    { join_comm := by
        intro _ _ _ _
        trivial
      join_assoc := by
        intro _ _ _ _ _ _ _
        exact ⟨PUnit.unit, True.intro, True.intro⟩ }

def unit_uSA :
    @UpwardsClosedSeparationAlgebra PUnit
      { Krelation := fun x y => x = y } unit_Join := by
  letI : Relation PUnit := { Krelation := fun x y => x = y }
  letI : Join PUnit := unit_Join
  exact
    { join_Korder_up := by
        intro m n m1 m2 _ hmn
        cases m
        cases n
        cases m1
        cases m2
        exact ⟨PUnit.unit, PUnit.unit, True.intro, rfl, rfl⟩ }

def unit_dSA :
    @DownwardsClosedSeparationAlgebra PUnit
      { Krelation := fun x y => x = y } unit_Join := by
  letI : Relation PUnit := { Krelation := fun x y => x = y }
  letI : Join PUnit := unit_Join
  exact
    { join_Korder_down := by
        intro m1 m2 m n1 n2 _ _ _
        cases m1
        cases m2
        cases m
        cases n1
        cases n2
        exact ⟨PUnit.unit, True.intro, rfl⟩ }

instance unit_incrSA :
    @IncreasingSeparationAlgebra PUnit
      { Krelation := fun x y => x = y } unit_Join := by
  letI : Relation PUnit := { Krelation := fun x y => x = y }
  letI : Join PUnit := unit_Join
  exact
    { all_increasing := by
        intro x n n' _
        cases n
        cases n'
        rfl }

instance unit_residual :
    @ResidualSeparationAlgebra PUnit
      { Krelation := fun x y => x = y } unit_Join := by
  letI : Relation PUnit := { Krelation := fun x y => x = y }
  letI : Join PUnit := unit_Join
  exact
    { residue_exists := by
        intro n
        cases n
        exact ⟨PUnit.unit, PUnit.unit, True.intro, rfl⟩ }

def unit_unital :
    @UnitalSeparationAlgebra PUnit
      { Krelation := fun x y => x = y } unit_Join := by
  letI : Relation PUnit := { Krelation := fun x y => x = y }
  letI : Join PUnit := unit_Join
  letI : PreOrder (@Krelation PUnit _) := eq_preorder PUnit
  have hI :
      @IncreasingSeparationAlgebra PUnit
        { Krelation := fun x y => x = y } unit_Join := unit_incrSA
  have hR :
      @ResidualSeparationAlgebra PUnit
        { Krelation := fun x y => x = y } unit_Join := unit_residual
  exact ((incr_unital_iff_residual (worlds := PUnit) hI).mpr hR)

end unitSA

section equivSA

def equiv_Join (worlds : Type u) : Join worlds where
  join := fun a b c => a = c /\ b = c

def equiv_SA (worlds : Type u) :
    @SeparationAlgebra worlds (equiv_Join worlds) := by
  letI : Join worlds := equiv_Join worlds
  exact
    { join_comm := by
        intro m1 m2 m h
        exact ⟨h.right, h.left⟩
      join_assoc := by
        intro mx my mz mxy mxyz hxy hxyz
        rcases hxy with ⟨hmx, hmy⟩
        rcases hxyz with ⟨hmxy, hmz⟩
        subst mx
        subst my
        subst mxy
        subst mz
        exact ⟨mxyz, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ }

def identity_uSA {worlds : Type u} [Relation worlds] :
    @UpwardsClosedSeparationAlgebra worlds _ (equiv_Join worlds) := by
  letI : Join worlds := equiv_Join worlds
  exact
    { join_Korder_up := by
        intro m n m1 m2 hj hmn
        rcases hj with ⟨hm1, hm2⟩
        subst m1
        subst m2
        exact ⟨n, n, ⟨rfl, rfl⟩, hmn, hmn⟩ }

def equiv_incrSA (worlds : Type u) :
    @IncreasingSeparationAlgebra worlds
      { Krelation := fun x y => x = y } (equiv_Join worlds) := by
  letI : Relation worlds := { Krelation := fun x y => x = y }
  letI : Join worlds := equiv_Join worlds
  exact
    { all_increasing := by
        intro x n n' h
        exact h.right }

def ikiM_uSA {worlds : Type u} [Relation worlds]
    [po_R : PreOrder (@Krelation worlds _)]
    [IdentityKripkeIntuitionisticModel worlds] [J : Join worlds] :
    UpwardsClosedSeparationAlgebra worlds where
  join_Korder_up := by
    intro m n m1 m2 hj hmn
    have hmn' : m = n := Korder_identity m n hmn
    subst n
    exact ⟨m1, m2, hj, po_R.refl m1, po_R.refl m2⟩

def ikiM_dSA {worlds : Type u} [Relation worlds]
    [po_R : PreOrder (@Krelation worlds _)]
    [IdentityKripkeIntuitionisticModel worlds] [J : Join worlds] :
    DownwardsClosedSeparationAlgebra worlds where
  join_Korder_down := by
    intro m1 m2 m n1 n2 hj hn1 hn2
    have h1 : n1 = m1 := Korder_identity n1 m1 hn1
    have h2 : n2 = m2 := Korder_identity n2 m2 hn2
    subst n1
    subst n2
    exact ⟨m, hj, po_R.refl m⟩

def equiv_Unit (worlds : Type u) : Unit worlds where
  is_unit := fun _ => True

def equiv_UJR (worlds : Type u) :
    @UnitJoinRelation worlds (equiv_Unit worlds) (equiv_Join worlds) := by
  letI : Unit worlds := equiv_Unit worlds
  letI : Join worlds := equiv_Join worlds
  exact
    { unit_join := by
        intro n
        exact ⟨n, True.intro, rfl, rfl⟩
      unit_spec := by
        intro n m u _ hj
        exact hj.left }

end equivSA

section optionSA

inductive option_join {worlds : Type u} [J : Join worlds] :
    Option worlds -> Option worlds -> Option worlds -> Prop where
  | None_None_join : option_join none none none
  | None_Some_join (a : worlds) : option_join none (some a) (some a)
  | Some_None_join (a : worlds) : option_join (some a) none (some a)
  | Some_Some_join (a b c : worlds) :
      join a b c -> option_join (some a) (some b) (some c)

export option_join
  (None_None_join None_Some_join Some_None_join Some_Some_join)

def option_Join {worlds : Type u} [J : Join worlds] : Join (Option worlds) where
  join := option_join

def option_SA (worlds : Type u) [J : Join worlds]
    [SA : SeparationAlgebra worlds] :
    @SeparationAlgebra (Option worlds) option_Join := by
  letI : Join (Option worlds) := option_Join
  exact
    { join_comm := by
        intro m1 m2 m h
        cases h with
        | None_None_join =>
            exact None_None_join
        | None_Some_join a =>
            exact Some_None_join a
        | Some_None_join a =>
            exact None_Some_join a
        | Some_Some_join a b c hj =>
            exact Some_Some_join b a c (join_comm a b c hj)
      join_assoc := by
        intro mx my mz mxy mxyz hxy hxyz
        cases hxy with
        | None_None_join =>
            cases hxyz with
            | None_None_join =>
                exact ⟨none, None_None_join, None_None_join⟩
            | None_Some_join a =>
                exact ⟨some a, None_Some_join a, None_Some_join a⟩
        | None_Some_join a =>
            cases hxyz with
            | Some_None_join _ =>
                exact ⟨some a, Some_None_join a, None_Some_join a⟩
            | Some_Some_join _ b c hj =>
                exact ⟨some c, Some_Some_join a b c hj, None_Some_join c⟩
        | Some_None_join a =>
            cases hxyz with
            | Some_None_join _ =>
                exact ⟨none, None_None_join, Some_None_join a⟩
            | Some_Some_join _ b c hj =>
                exact ⟨some b, None_Some_join b, Some_Some_join a b c hj⟩
        | Some_Some_join a b c hj1 =>
            cases hxyz with
            | Some_None_join _ =>
                exact ⟨some b, Some_None_join b, Some_Some_join a b c hj1⟩
            | Some_Some_join _ d e hj2 =>
                rcases join_assoc a b d c e hj1 hj2 with ⟨bd, hbd, ha⟩
                exact ⟨some bd, Some_Some_join b d bd hbd,
                  Some_Some_join a bd e ha⟩ }

def option_ord_uSA {worlds : Type u} [R : Relation worlds] [J : Join worlds]
    (uSA : UpwardsClosedSeparationAlgebra worlds) :
    @UpwardsClosedSeparationAlgebra (Option worlds)
      { Krelation := option01_relation (@Krelation worlds R) } option_Join := by
  letI : Relation (Option worlds) :=
    { Krelation := option01_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  exact
    { join_Korder_up := by
        intro m n m1 m2 hj hmn
        cases hj with
        | None_None_join =>
            cases hmn with
            | None_None_option01 =>
                exact ⟨none, none, None_None_join, None_None_option01, None_None_option01⟩
            | None_Some_option01 a =>
                exact ⟨none, some a, None_Some_join a, None_None_option01,
                  None_Some_option01 a⟩
        | None_Some_join b =>
            cases hmn with
            | Some_Some_option01 _ c hbc =>
                exact ⟨none, some c, None_Some_join c, None_None_option01,
                  Some_Some_option01 b c hbc⟩
        | Some_None_join b =>
            cases hmn with
            | Some_Some_option01 _ c hbc =>
                exact ⟨some c, none, Some_None_join c,
                  Some_Some_option01 b c hbc, None_None_option01⟩
        | Some_Some_join a b c hjc =>
            cases hmn with
            | Some_Some_option01 _ d hcd =>
                rcases join_Korder_up c d a b hjc hcd with
                  ⟨n1, n2, hn, ha, hb⟩
                exact ⟨some n1, some n2, Some_Some_join n1 n2 d hn,
                  Some_Some_option01 a n1 ha, Some_Some_option01 b n2 hb⟩ }

def option_ord_dSA {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] [J : Join worlds]
    [SA : SeparationAlgebra worlds]
    (dSA : DownwardsClosedSeparationAlgebra worlds)
    [incrSA : IncreasingSeparationAlgebra worlds] :
    @DownwardsClosedSeparationAlgebra (Option worlds)
      { Krelation := option01_relation (@Krelation worlds R) } option_Join := by
  letI : Relation (Option worlds) :=
    { Krelation := option01_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  exact
    { join_Korder_down := by
        intro m1 m2 m n1 n2 hj hn1 hn2
        cases hj with
        | None_None_join =>
            cases hn1 with
            | None_None_option01 =>
                cases hn2 with
                | None_None_option01 =>
                    exact ⟨none, None_None_join, None_None_option01⟩
        | None_Some_join a =>
            cases hn1 with
            | None_None_option01 =>
                cases hn2 with
                | None_Some_option01 _ =>
                    exact ⟨none, None_None_join, None_Some_option01 a⟩
                | Some_Some_option01 b _ hba =>
                    exact ⟨some b, None_Some_join b, Some_Some_option01 b a hba⟩
        | Some_None_join a =>
            cases hn1 with
            | None_Some_option01 _ =>
                cases hn2 with
                | None_None_option01 =>
                    exact ⟨none, None_None_join, None_Some_option01 a⟩
            | Some_Some_option01 b _ hba =>
                cases hn2 with
                | None_None_option01 =>
                    exact ⟨some b, Some_None_join b, Some_Some_option01 b a hba⟩
        | Some_Some_join a b c hjc =>
            cases hn1 with
            | None_Some_option01 _ =>
                cases hn2 with
                | None_Some_option01 _ =>
                    exact ⟨none, None_None_join, None_Some_option01 c⟩
                | Some_Some_option01 b' _ hb'b =>
                    have hbc : Krelation b c := all_increasing a b c hjc
                    exact ⟨some b', None_Some_join b',
                      Some_Some_option01 b' c (po_R.trans b' b c hb'b hbc)⟩
            | Some_Some_option01 a' _ ha'a =>
                cases hn2 with
                | None_Some_option01 _ =>
                    have hac : Krelation a c :=
                      all_increasing b a c (join_comm a b c hjc)
                    exact ⟨some a', Some_None_join a',
                      Some_Some_option01 a' c (po_R.trans a' a c ha'a hac)⟩
                | Some_Some_option01 b' _ hb'b =>
                    rcases join_Korder_down a b c a' b' hjc ha'a hb'b with
                      ⟨n, hn, hnc⟩
                    exact ⟨some n, Some_Some_join a' b' n hn,
                      Some_Some_option01 n c hnc⟩ }

def option_ord_incr_None {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] [J : Join worlds]
    [SeparationAlgebra worlds] :
    @increasing (Option worlds)
      { Krelation := option01_relation (@Krelation worlds R) } option_Join none := by
  letI : Relation (Option worlds) :=
    { Krelation := option01_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  intro n n' hj
  cases hj with
  | None_None_join =>
      exact None_None_option01
  | None_Some_join a =>
      exact Some_Some_option01 a a (po_R.refl a)

def option_ord_res_None {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] [J : Join worlds]
    [SeparationAlgebra worlds] :
    forall n,
      @residue (Option worlds)
        { Krelation := option01_relation (@Krelation worlds R) } option_Join n none := by
  letI : Relation (Option worlds) :=
    { Krelation := option01_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  intro n
  exists n
  constructor
  · cases n with
    | none => exact None_None_join
    | some a => exact None_Some_join a
  · cases n with
    | none => exact None_None_option01
    | some a => exact Some_Some_option01 a a (po_R.refl a)

def option_ord_USA {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] [J : Join worlds]
    [SA : SeparationAlgebra worlds] :
    @UnitalSeparationAlgebra (Option worlds)
      { Krelation := option01_relation (@Krelation worlds R) } option_Join := by
  letI : Relation (Option worlds) :=
    { Krelation := option01_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  exact
    { incr_exists := by
        intro n
        exact ⟨none, option_ord_res_None n, option_ord_incr_None⟩ }

def option_disj_uSA {worlds : Type u} [R : Relation worlds] [J : Join worlds]
    (uSA : UpwardsClosedSeparationAlgebra worlds) :
    @UpwardsClosedSeparationAlgebra (Option worlds)
      { Krelation := option00_relation (@Krelation worlds R) } option_Join := by
  letI : Relation (Option worlds) :=
    { Krelation := option00_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  exact
    { join_Korder_up := by
        intro m n m1 m2 hj hmn
        cases hj with
        | None_None_join =>
            cases hmn with
            | None_None_option00 =>
                exact ⟨none, none, None_None_join, None_None_option00, None_None_option00⟩
        | None_Some_join b =>
            cases hmn with
            | Some_Some_option00 _ c hbc =>
                exact ⟨none, some c, None_Some_join c, None_None_option00,
                  Some_Some_option00 b c hbc⟩
        | Some_None_join b =>
            cases hmn with
            | Some_Some_option00 _ c hbc =>
                exact ⟨some c, none, Some_None_join c,
                  Some_Some_option00 b c hbc, None_None_option00⟩
        | Some_Some_join a b c hjc =>
            cases hmn with
            | Some_Some_option00 _ d hcd =>
                rcases join_Korder_up c d a b hjc hcd with
                  ⟨n1, n2, hn, ha, hb⟩
                exact ⟨some n1, some n2, Some_Some_join n1 n2 d hn,
                  Some_Some_option00 a n1 ha, Some_Some_option00 b n2 hb⟩ }

def option_disj_dSA {worlds : Type u} [R : Relation worlds]
    [J : Join worlds] [SeparationAlgebra worlds]
    (dSA : DownwardsClosedSeparationAlgebra worlds) :
    @DownwardsClosedSeparationAlgebra (Option worlds)
      { Krelation := option00_relation (@Krelation worlds R) } option_Join := by
  letI : Relation (Option worlds) :=
    { Krelation := option00_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  exact
    { join_Korder_down := by
        intro m1 m2 m n1 n2 hj hn1 hn2
        cases hj with
        | None_None_join =>
            cases hn1 with
            | None_None_option00 =>
                cases hn2 with
                | None_None_option00 =>
                    exact ⟨none, None_None_join, None_None_option00⟩
        | None_Some_join a =>
            cases hn1 with
            | None_None_option00 =>
                cases hn2 with
                | Some_Some_option00 b _ hba =>
                    exact ⟨some b, None_Some_join b, Some_Some_option00 b a hba⟩
        | Some_None_join a =>
            cases hn1 with
            | Some_Some_option00 b _ hba =>
                cases hn2 with
                | None_None_option00 =>
                    exact ⟨some b, Some_None_join b, Some_Some_option00 b a hba⟩
        | Some_Some_join a b c hjc =>
            cases hn1 with
            | Some_Some_option00 a' _ ha'a =>
                cases hn2 with
                | Some_Some_option00 b' _ hb'b =>
                    rcases join_Korder_down a b c a' b' hjc ha'a hb'b with
                      ⟨n, hn, hnc⟩
                    exact ⟨some n, Some_Some_join a' b' n hn,
                      Some_Some_option00 n c hnc⟩ }

def option_disj_incr_None {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] [J : Join worlds]
    [SeparationAlgebra worlds] :
    @increasing (Option worlds)
      { Krelation := option00_relation (@Krelation worlds R) } option_Join none := by
  letI : Relation (Option worlds) :=
    { Krelation := option00_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  intro n n' hj
  cases hj with
  | None_None_join =>
      exact None_None_option00
  | None_Some_join a =>
      exact Some_Some_option00 a a (po_R.refl a)

def option_disj_res_None {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] [J : Join worlds]
    [SeparationAlgebra worlds] :
    forall n,
      @residue (Option worlds)
        { Krelation := option00_relation (@Krelation worlds R) } option_Join n none := by
  letI : Relation (Option worlds) :=
    { Krelation := option00_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  intro n
  exists n
  constructor
  · cases n with
    | none => exact None_None_join
    | some a => exact None_Some_join a
  · cases n with
    | none => exact None_None_option00
    | some a => exact Some_Some_option00 a a (po_R.refl a)

def option_disj_USA {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] [J : Join worlds]
    [SA : SeparationAlgebra worlds] :
    @UnitalSeparationAlgebra (Option worlds)
      { Krelation := option00_relation (@Krelation worlds R) } option_Join := by
  letI : Relation (Option worlds) :=
    { Krelation := option00_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  exact
    { incr_exists := by
        intro n
        exact ⟨none, option_disj_res_None n, option_disj_incr_None⟩ }

def option_disj_USA' {worlds : Type u} [R : Relation worlds]
    [po_R : PreOrder (@Krelation worlds R)] [J : Join worlds]
    [SA : SeparationAlgebra worlds] :
    @UnitalSeparationAlgebra' (Option worlds)
      { Krelation := option00_relation (@Krelation worlds R) } option_Join := by
  letI : Relation (Option worlds) :=
    { Krelation := option00_relation (@Krelation worlds R) }
  letI : Join (Option worlds) := option_Join
  exact
    { incr'_exists := by
        intro n
        refine ⟨none, option_disj_res_None n, ?_⟩
        intro n' hn'
        cases hn' with
        | None_None_option00 =>
            exact option_disj_incr_None }

def option_Unit (worlds : Type u) : Unit (Option worlds) where
  is_unit := fun m => m = none

def option_UJR (worlds : Type u) [J : Join worlds] :
    @UnitJoinRelation (Option worlds) (option_Unit worlds) option_Join := by
  letI : Unit (Option worlds) := option_Unit worlds
  letI : Join (Option worlds) := option_Join
  exact
    { unit_join := by
        intro n
        refine ⟨none, rfl, ?_⟩
        cases n with
        | none => exact None_None_join
        | some a => exact Some_None_join a
      unit_spec := by
        intro n m u hu hj
        cases hj with
        | None_None_join => rfl
        | Some_None_join a => rfl
        | None_Some_join a =>
            cases hu
        | Some_Some_join a b c _ =>
            cases hu }

end optionSA

section exponentialSA

def fun_Join (A : Type u) (B : Type v) [J_B : Join B] : Join (A -> B) where
  join := fun a b c => forall x, join (a x) (b x) (c x)

def fun_SA (A : Type u) (B : Type v) [J_B : Join B]
    [SA_B : SeparationAlgebra B] :
    @SeparationAlgebra (A -> B) (fun_Join A B) := by
  letI : Join (A -> B) := fun_Join A B
  exact {
  join_comm := by
    intro a b c h x
    exact join_comm (a x) (b x) (c x) (h x)
  join_assoc := by
    classical
    intro mx my mz mxy mxyz hxy hxyz
    let myz : A -> B := fun x =>
      Classical.choose (join_assoc (mx := mx x) (my := my x) (mz := mz x)
        (mxy := mxy x) (mxyz := mxyz x) (hxy x) (hxyz x))
    refine ⟨myz, ?_, ?_⟩
    · intro x
      exact (Classical.choose_spec (join_assoc (mx := mx x) (my := my x)
        (mz := mz x) (mxy := mxy x) (mxyz := mxyz x) (hxy x) (hxyz x))).left
    · intro x
      exact (Classical.choose_spec (join_assoc (mx := mx x) (my := my x)
        (mz := mz x) (mxy := mxy x) (mxyz := mxyz x) (hxy x) (hxyz x))).right }

def fun_uSA (A : Type u) (B : Type v) [R_B : Relation B]
    [J_B : Join B] (uSA_B : UpwardsClosedSeparationAlgebra B) :
    @UpwardsClosedSeparationAlgebra (A -> B)
      { Krelation := pointwise_relation A (@Krelation B R_B) } (fun_Join A B) := by
  letI : Relation (A -> B) :=
    { Krelation := pointwise_relation A (@Krelation B R_B) }
  letI : Join (A -> B) := fun_Join A B
  exact
    { join_Korder_up := by
        classical
        intro m n m1 m2 hj hmn
        let h : forall x : A, exists n1 n2,
            join n1 n2 (n x) /\ Krelation (m1 x) n1 /\ Krelation (m2 x) n2 :=
          fun x => join_Korder_up (m x) (n x) (m1 x) (m2 x) (hj x) (hmn x)
        let n1 : A -> B := fun x => Classical.choose (h x)
        let n2 : A -> B := fun x => Classical.choose (Classical.choose_spec (h x))
        refine ⟨n1, n2, ?_, ?_, ?_⟩
        · intro x
          exact (Classical.choose_spec (Classical.choose_spec (h x))).left
        · intro x
          exact (Classical.choose_spec (Classical.choose_spec (h x))).right.left
        · intro x
          exact (Classical.choose_spec (Classical.choose_spec (h x))).right.right }

def fun_dSA (A : Type u) (B : Type v) [R_B : Relation B]
    [J_B : Join B] (dSA_B : DownwardsClosedSeparationAlgebra B) :
    @DownwardsClosedSeparationAlgebra (A -> B)
      { Krelation := pointwise_relation A (@Krelation B R_B) } (fun_Join A B) := by
  letI : Relation (A -> B) :=
    { Krelation := pointwise_relation A (@Krelation B R_B) }
  letI : Join (A -> B) := fun_Join A B
  exact
    { join_Korder_down := by
        classical
        intro m1 m2 m n1 n2 hj hn1 hn2
        let n : A -> B := fun x =>
          Classical.choose (join_Korder_down (m1 x) (m2 x) (m x)
            (n1 x) (n2 x) (hj x) (hn1 x) (hn2 x))
        refine ⟨n, ?_, ?_⟩
        · intro x
          exact (Classical.choose_spec (join_Korder_down (m1 x) (m2 x) (m x)
            (n1 x) (n2 x) (hj x) (hn1 x) (hn2 x))).left
        · intro x
          exact (Classical.choose_spec (join_Korder_down (m1 x) (m2 x) (m x)
            (n1 x) (n2 x) (hj x) (hn1 x) (hn2 x))).right }

def fun_incrSA (A : Type u) (B : Type v) [R_B : Relation B]
    [J_B : Join B] (incr_B : IncreasingSeparationAlgebra B) :
    @IncreasingSeparationAlgebra (A -> B)
      { Krelation := pointwise_relation A (@Krelation B R_B) } (fun_Join A B) := by
  letI : Relation (A -> B) :=
    { Krelation := pointwise_relation A (@Krelation B R_B) }
  letI : Join (A -> B) := fun_Join A B
  exact
    { all_increasing := by
        intro f n n' hj x
        exact all_increasing (f x) (n x) (n' x) (hj x) }

def fun_unitSA (A : Type u) (B : Type v) [R_B : Relation B]
    [J_B : Join B] (USA_B : UnitalSeparationAlgebra B) :
    @UnitalSeparationAlgebra (A -> B)
      { Krelation := pointwise_relation A (@Krelation B R_B) } (fun_Join A B) := by
  letI : Relation (A -> B) :=
    { Krelation := pointwise_relation A (@Krelation B R_B) }
  letI : Join (A -> B) := fun_Join A B
  exact
    { incr_exists := by
        classical
        intro n
        let M : A -> B := fun x => Classical.choose (incr_exists (n x))
        refine ⟨M, ?_, ?_⟩
        · let N' : A -> B := fun x =>
            Classical.choose (Classical.choose_spec (incr_exists (n x))).left
          refine ⟨N', ?_, ?_⟩
          · intro x
            exact (Classical.choose_spec
              (Classical.choose_spec (incr_exists (n x))).left).left
          · intro x
            exact (Classical.choose_spec
              (Classical.choose_spec (incr_exists (n x))).left).right
        · intro n1 n2 hj x
          exact (Classical.choose_spec (incr_exists (n x))).right (n1 x) (n2 x) (hj x) }

def fun_unitSA' (A : Type u) (B : Type v) [R_B : Relation B]
    [J_B : Join B] (USA'_B : UnitalSeparationAlgebra' B) :
    @UnitalSeparationAlgebra' (A -> B)
      { Krelation := pointwise_relation A (@Krelation B R_B) } (fun_Join A B) := by
  letI : Relation (A -> B) :=
    { Krelation := pointwise_relation A (@Krelation B R_B) }
  letI : Join (A -> B) := fun_Join A B
  exact
    { incr'_exists := by
        classical
        intro n
        let M : A -> B := fun x => Classical.choose (incr'_exists (n x))
        refine ⟨M, ?_, ?_⟩
        · let N' : A -> B := fun x =>
            Classical.choose (Classical.choose_spec (incr'_exists (n x))).left
          refine ⟨N', ?_, ?_⟩
          · intro x
            exact (Classical.choose_spec
              (Classical.choose_spec (incr'_exists (n x))).left).left
          · intro x
            exact (Classical.choose_spec
              (Classical.choose_spec (incr'_exists (n x))).left).right
        · intro n' hn' n1 n2 hj x
          exact (Classical.choose_spec (incr'_exists (n x))).right
            (n' x) (hn' x) (n1 x) (n2 x) (hj x) }

def fun_Unit (A : Type u) (B : Type v) [U_B : Unit B] :
    Unit (A -> B) where
  is_unit := fun v => forall x, is_unit (v x)

def fun_UJR (A : Type u) (B : Type v) [U_B : Unit B] [J_B : Join B]
    [UJR_B : UnitJoinRelation B] :
    @UnitJoinRelation (A -> B) (fun_Unit A B) (fun_Join A B) := by
  letI : Unit (A -> B) := fun_Unit A B
  letI : Join (A -> B) := fun_Join A B
  exact {
  unit_join := by
    classical
    intro n
    let u : A -> B := fun x => Classical.choose (unit_join (n x))
    refine ⟨u, ?_, ?_⟩
    · intro x
      exact (Classical.choose_spec (unit_join (n x))).left
    · intro x
      exact (Classical.choose_spec (unit_join (n x))).right
  unit_spec := by
    intro n m u hu hj
    funext x
    exact unit_spec (n x) (m x) (u x) (hu x) (hj x) }

end exponentialSA

section sumSA

inductive sum_join {A : Type u} {B : Type v} [J1 : Join A] [J2 : Join B] :
    Sum A B -> Sum A B -> Sum A B -> Prop where
  | left_join (a b c : A) :
      join a b c -> sum_join (Sum.inl a) (Sum.inl b) (Sum.inl c)
  | right_join (a b c : B) :
      join a b c -> sum_join (Sum.inr a) (Sum.inr b) (Sum.inr c)

export sum_join (left_join right_join)

def sum_Join (A : Type u) (B : Type v) [Join_A : Join A] [Join_B : Join B] :
    Join (Sum A B) where
  join := sum_join

def sum_SA (A : Type u) (B : Type v) [Join_A : Join A] [Join_B : Join B]
    [SA_A : SeparationAlgebra A] [SA_B : SeparationAlgebra B] :
    @SeparationAlgebra (Sum A B) (sum_Join A B) := by
  letI : Join (Sum A B) := sum_Join A B
  exact {
  join_comm := by
    intro m1 m2 m h
    cases h with
    | left_join a b c hj =>
        exact left_join b a c (join_comm a b c hj)
    | right_join a b c hj =>
        exact right_join b a c (join_comm a b c hj)
  join_assoc := by
    intro mx my mz mxy mxyz hxy hxyz
    cases hxy with
    | left_join a b c hj1 =>
        cases hxyz with
        | left_join _ d e hj2 =>
            rcases join_assoc a b d c e hj1 hj2 with ⟨bd, hbd, ha⟩
            exact ⟨Sum.inl bd, left_join b d bd hbd, left_join a bd e ha⟩
    | right_join a b c hj1 =>
        cases hxyz with
        | right_join _ d e hj2 =>
            rcases join_assoc a b d c e hj1 hj2 with ⟨bd, hbd, ha⟩
            exact ⟨Sum.inr bd, right_join b d bd hbd, right_join a bd e ha⟩ }

end sumSA

section productSA

def prod_Join (A : Type u) (B : Type v) [Join_A : Join A] [Join_B : Join B] :
    Join (A × B) where
  join := fun a b c => join a.1 b.1 c.1 /\ join a.2 b.2 c.2

def prod_SA (A : Type u) (B : Type v) [Join_A : Join A] [Join_B : Join B]
    [SA_A : SeparationAlgebra A] [SA_B : SeparationAlgebra B] :
    @SeparationAlgebra (A × B) (prod_Join A B) := by
  letI : Join (A × B) := prod_Join A B
  exact {
  join_comm := by
    intro a b c h
    exact ⟨join_comm a.1 b.1 c.1 h.left,
      join_comm a.2 b.2 c.2 h.right⟩
  join_assoc := by
    intro mx my mz mxy mxyz hxy hxyz
    rcases hxy with ⟨hxy1, hxy2⟩
    rcases hxyz with ⟨hxyz1, hxyz2⟩
    rcases join_assoc mx.1 my.1 mz.1 mxy.1 mxyz.1 hxy1 hxyz1 with
      ⟨myz1, h1, h2⟩
    rcases join_assoc mx.2 my.2 mz.2 mxy.2 mxyz.2 hxy2 hxyz2 with
      ⟨myz2, h3, h4⟩
    exact ⟨(myz1, myz2), ⟨h1, h3⟩, ⟨h2, h4⟩⟩ }

def prod_uSA (A : Type u) (B : Type v) [R_A : Relation A] [R_B : Relation B]
    [Join_A : Join A] [Join_B : Join B]
    [uSA_A : UpwardsClosedSeparationAlgebra A]
    [uSA_B : UpwardsClosedSeparationAlgebra B] :
    @UpwardsClosedSeparationAlgebra (A × B)
      { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
      (prod_Join A B) := by
  letI : Relation (A × B) :=
    { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
  letI : Join (A × B) := prod_Join A B
  exact
    { join_Korder_up := by
        intro m n m1 m2 hj hmn
        rcases hj with ⟨hj1, hj2⟩
        rcases hmn with ⟨hmn1, hmn2⟩
        rcases join_Korder_up m.1 n.1 m1.1 m2.1 hj1 hmn1 with
          ⟨fst_n1, fst_n2, hfstj, hfst1, hfst2⟩
        rcases join_Korder_up m.2 n.2 m1.2 m2.2 hj2 hmn2 with
          ⟨snd_n1, snd_n2, hsndj, hsnd1, hsnd2⟩
        exact ⟨(fst_n1, snd_n1), (fst_n2, snd_n2),
          ⟨hfstj, hsndj⟩, ⟨hfst1, hsnd1⟩, ⟨hfst2, hsnd2⟩⟩ }

def prod_dSA (A : Type u) (B : Type v) [R_A : Relation A] [R_B : Relation B]
    [Join_A : Join A] [Join_B : Join B]
    [dSA_A : DownwardsClosedSeparationAlgebra A]
    [dSA_B : DownwardsClosedSeparationAlgebra B] :
    @DownwardsClosedSeparationAlgebra (A × B)
      { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
      (prod_Join A B) := by
  letI : Relation (A × B) :=
    { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
  letI : Join (A × B) := prod_Join A B
  exact
    { join_Korder_down := by
        intro m1 m2 m n1 n2 hj hn1 hn2
        rcases hj with ⟨hj1, hj2⟩
        rcases hn1 with ⟨hn11, hn12⟩
        rcases hn2 with ⟨hn21, hn22⟩
        rcases join_Korder_down m1.1 m2.1 m.1 n1.1 n2.1 hj1 hn11 hn21 with
          ⟨fst_n, hfstj, hfst⟩
        rcases join_Korder_down m1.2 m2.2 m.2 n1.2 n2.2 hj2 hn12 hn22 with
          ⟨snd_n, hsndj, hsnd⟩
        exact ⟨(fst_n, snd_n), ⟨hfstj, hsndj⟩, ⟨hfst, hsnd⟩⟩ }

def prod_incr (A : Type u) (B : Type v) [R_A : Relation A] [R_B : Relation B]
    [Join_A : Join A] [Join_B : Join B] :
    forall (a : A) (b : B),
      increasing a -> increasing b ->
      @increasing (A × B)
        { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
        (prod_Join A B) (a, b) := by
  letI : Relation (A × B) :=
    { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
  letI : Join (A × B) := prod_Join A B
  intro a b ha hb n n' hj
  exact ⟨ha n.1 n'.1 hj.left, hb n.2 n'.2 hj.right⟩

def prod_incrSA (A : Type u) (B : Type v) [R_A : Relation A] [R_B : Relation B]
    [Join_A : Join A] [Join_B : Join B]
    [incrSA_A : IncreasingSeparationAlgebra A]
    [incrSA_B : IncreasingSeparationAlgebra B] :
    @IncreasingSeparationAlgebra (A × B)
      { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
      (prod_Join A B) := by
  letI : Relation (A × B) :=
    { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
  letI : Join (A × B) := prod_Join A B
  exact
    { all_increasing := by
        intro x
        cases x with
        | mk a b =>
            exact prod_incr A B a b (all_increasing a) (all_increasing b) }

def prod_residualSA (A : Type u) (B : Type v) [R_A : Relation A] [R_B : Relation B]
    [Join_A : Join A] [Join_B : Join B]
    [residualSA_A : ResidualSeparationAlgebra A]
    [residualSA_B : ResidualSeparationAlgebra B] :
    @ResidualSeparationAlgebra (A × B)
      { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
      (prod_Join A B) := by
  letI : Relation (A × B) :=
    { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
  letI : Join (A × B) := prod_Join A B
  exact
    { residue_exists := by
        intro n
        rcases n with ⟨a, b⟩
        rcases residue_exists a with ⟨a', a'', ha1, ha2⟩
        rcases residue_exists b with ⟨b', b'', hb1, hb2⟩
        exact ⟨(a', b'), (a'', b''), ⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩ }

def prod_unitalSA (A : Type u) (B : Type v) [R_A : Relation A] [R_B : Relation B]
    [Join_A : Join A] [Join_B : Join B]
    [unitalSA_A : UnitalSeparationAlgebra A]
    [unitalSA_B : UnitalSeparationAlgebra B] :
    @UnitalSeparationAlgebra (A × B)
      { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
      (prod_Join A B) := by
  letI : Relation (A × B) :=
    { Krelation := RelProd (@Krelation A R_A) (@Krelation B R_B) }
  letI : Join (A × B) := prod_Join A B
  exact
    { incr_exists := by
        intro n
        rcases n with ⟨a, b⟩
        rcases incr_exists a with ⟨a', hares, hainc⟩
        rcases incr_exists b with ⟨b', hbres, hbinc⟩
        refine ⟨(a', b'), ?_, ?_⟩
        · rcases hares with ⟨a'', ha1, ha2⟩
          rcases hbres with ⟨b'', hb1, hb2⟩
          exact ⟨(a'', b''), ⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩
        · intro n1 n2 hj
          exact ⟨hainc n1.1 n2.1 hj.left, hbinc n1.2 n2.2 hj.right⟩ }

def prod_Unit (A : Type u) (B : Type v) [U_A : Unit A] [U_B : Unit B] :
    Unit (A × B) where
  is_unit := fun m => is_unit m.1 /\ is_unit m.2

def prod_UJR (A : Type u) (B : Type v) [U_A : Unit A] [U_B : Unit B]
    [J_A : Join A] [J_B : Join B]
    [USR_A : UnitJoinRelation A] [USR_B : UnitJoinRelation B] :
    @UnitJoinRelation (A × B) (prod_Unit A B) (prod_Join A B) := by
  letI : Unit (A × B) := prod_Unit A B
  letI : Join (A × B) := prod_Join A B
  exact {
  unit_join := by
    intro n
    rcases n with ⟨na, nb⟩
    rcases unit_join na with ⟨ua, hua, hja⟩
    rcases unit_join nb with ⟨ub, hub, hjb⟩
    exact ⟨(ua, ub), ⟨hua, hub⟩, ⟨hja, hjb⟩⟩
  unit_spec := by
    intro n m u hu hj
    rcases n with ⟨na, nb⟩
    rcases m with ⟨ma, mb⟩
    rcases u with ⟨ua, ub⟩
    rcases hu with ⟨hua, hub⟩
    rcases hj with ⟨hja, hjb⟩
    have ha : na = ma := unit_spec na ma ua hua hja
    have hb : nb = mb := unit_spec nb mb ub hub hjb
    exact Prod.ext ha hb }

end productSA

class SeparationAlgebra_unit (worlds : Type u) [J : Join worlds] : Type u where
  unit : worlds
  unit_join : forall n, join n unit n
  unit_spec : forall n m, join n unit m -> n = m

export SeparationAlgebra_unit (unit unit_join unit_spec)

end Unifysl
