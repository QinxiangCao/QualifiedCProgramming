import SimpleC.SL.CommonAssertion
import CommonAssertionBinderFixture

namespace CommonAssertionTests

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.DerivedPredSigCompat
open SimpleC.SL.CNotation
open SimpleC.SL.FloatLib
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

def TestRules : SeparationLogicSig where
  toContext := Facade.Smoke.Ctx
  mstore := fun _ _ _ => False
  mstore_noninit := fun _ _ => False
  mstore_mstore_noninit := by
    intro _ _ _ h
    exact False.elim h
  mstore_eqm := by
    intro _ _ _ _ state h
    exact False.elim h
  dup_mstore_noninit := by
    intro _ state h
    rcases h with ⟨_, _, _, hFalse, _⟩
    exact False.elim hFalse

-- Same assertion carrier, but a definitionally different finite-store model.
-- sep_apply must treat the SeparationLogicSig argument as part of the atom.
def OtherRules : SeparationLogicSig where
  toContext := Facade.Smoke.Ctx
  mstore := fun p _ _ => False ∧ p = p
  mstore_noninit := fun _ _ => False
  mstore_mstore_noninit := by
    intro _ _ _ h
    exact False.elim h.1
  mstore_eqm := by
    intro _ _ _ _ _ h
    exact False.elim h.1
  dup_mstore_noninit := by
    intro _ state h
    rcases h with ⟨_, _, _, hFalse, _⟩
    exact False.elim hFalse

local instance : SacContext := ⟨TestRules⟩

def nestedExp : Nat -> Assertion -> Assertion
  | 0, P => P
  | n + 1, P => SacContext.rules.exp Int (fun _ => nestedExp n P)

def nestedAll : Nat -> Assertion -> Assertion
  | 0, P => P
  | n + 1, P => SacContext.rules.allp Int (fun _ => nestedAll n P)

#check fun (P : Int -> Int -> Assertion) => (EX x, EX y, P x y)
#check fun (P : Int -> Int -> Assertion) => (ALL x, ALL y, P x y)

-- The three module-type counterparts and flattened facade/BasePred surface.
#check BasePredSig
#check BasePredSig.mstore
#check BasePredSig.mstore_noninit
#check BasePredSig.mstore_mstore_noninit
#check BasePredSig.mstore_eqm
#check BasePredSig.dup_mstore_noninit
#check SeparationLogicSig
#check SeparationLogicSig.toBasePredSig
#check DerivedPredSig
#check DerivedPredSig.canonical
#check TestRules.expr
#check TestRules.sepcon
#check TestRules.derivable1
#check TestRules.mstore

def acceptsDerivedPredModule (CRules : SeparationLogicSig)
    (_DePredSig : DerivedPredSigCompat.Sig CRules) : Type := CRules.expr

#check acceptsDerivedPredModule TestRules
  (DerivedPredSig.canonical SimpleC.SL.CArch.Arch32
    SimpleC.SL.CArch.BigEndian TestRules)

-- File-level semantic declarations.
#check aligned_2
#check aligned_4
#check aligned_8
#check SimpleC.SL.CommonAssertion.isvalidptr_char
#check SimpleC.SL.CommonAssertion.isvalidptr_short
#check SimpleC.SL.CommonAssertion.isvalidptr_int
#check SimpleC.SL.CommonAssertion.isvalidptr_int64
#check SimpleC.SL.CommonAssertion.isvalidptr_int128
#check SimpleC.SL.CommonAssertion.isvalidptr_float
#check SimpleC.SL.CommonAssertion.isvalidptr_double
#check SimpleC.SL.CommonAssertion.isvalidptr_long_double
#check SimpleC.SL.CommonAssertion.isvalidptr
#check merge_short
#check merge_short_255_255_neg_1
#check merge_short_255_neg1_neg_1
#check merge_int
#check merge_int64
#check merge_int_equiv
#check merge_uint_equiv

-- All definitions in DerivedPredSig.
#check store_byte
#check store_2byte
#check store_4byte
#check store_8byte
#check store_bytes
#check store_16byte
#check store_byte_noninit
#check store_2byte_noninit
#check store_4byte_noninit
#check store_8byte_noninit
#check store_bytes_noninit
#check store_16byte_noninit
#check store_char
#check undef_store_char
#check store_uchar
#check undef_store_uchar
#check store_short
#check undef_store_short
#check store_ushort
#check undef_store_ushort
#check store_int
#check undef_store_int
#check store_uint
#check undef_store_uint
#check store_int64
#check undef_store_int64
#check store_uint64
#check undef_store_uint64
#check store_int128
#check undef_store_int128
#check store_uint128
#check undef_store_uint128
#check store_float
#check store_double
#check store_long_double
#check store_finite_float
#check store_finite_double
#check store_finite_long_double
#check undef_store_float
#check undef_store_double
#check undef_store_long_double
#check undef_store_finite_float
#check undef_store_finite_double
#check undef_store_finite_long_double
#check store_ptr
#check undef_store_ptr
#check Invalid_store
#check Invalid_undef_store
#check dup_data_at_error
#check dup_data_at_error_prop
#check store_array_rec
#check store_array_missing_i_rec
#check store_array
#check store_undef_array_rec
#check store_undef_array_missing_i_rec
#check store_undef_array
#check store_align4_list
#check store_align4_n
#check store_align_list
#check store_align_n
#check front_end_type_value
#check typed_poly_store
#check poly_store
#check poly_undef_store
#check struct_padding
#check union_padding
#check derivable1_wand_sepcon_adjoint
#check all_list

-- All 34 active lemmas.
#check coq_prop_andp_left
#check coq_prop_andp_right
#check coq_prop_imply
#check coq_prop_False_left
#check orp_sepcon_left
#check orp_sepcon_right
#check orp_sepcon_left'
#check orp_sepcon_right'
#check orp_sepcon_left_equiv
#check orp_sepcon_right_equiv
#check exp_right_exists
#check derivable1_imp
#check derivable1_andp_mono
#check ex_logic_equiv_andp
#check wand_equiv
#check ex_logic_equiv_sepcon
#check prop_add_left
#check truep_andp_left_equiv
#check truep_andp_right_equiv
#check sepcon_emp_equiv
#check sepcon_cancel_res_emp
#check sepcon_cancel_end
#check sepcon_prop_equiv
#check exp_exp_right
#check exp_allp_left
#check exp_allp_swap
#check allp_allp_swap
#check sepcon_emp_logic_equiv'
#check elim_wand_emp_emp
#check dump_spatial_left
#check split_pure_and_spatial_goals
#check _derivable1_andp_intros
#check add_pure_split
#check sepcon_cancel_lhs_emp

-- Scope and notation surface.
#check (emp : Assertion)
#check fun (P Q : Assertion) => P |-- Q
#check fun (P Q : Assertion) => P ⊣⊢ Q
#check fun (P Q : Assertion) => P -* Q
#check fun (P Q : Assertion) => P ⟶ₗ Q
#check fun (P Q : Assertion) => P || Q
#check fun (P Q : Assertion) => P && Q
#check fun (P Q : Assertion) => P ** Q
#check fun (P : Prop) => (“ P ” : Assertion)
#check (TT : Assertion)
#check fun (P : Int -> Assertion) => (EX x, P x)
#check fun (P : Int -> Assertion) => (ALL x, P x)
#check fun (P : Int -> Assertion) => (EX x : Int, P x)
#check fun (P : Int -> Assertion) => (ALL x : Int, P x)
#check fun (x value : Int) => x # INT |-> value
#check fun (x : Int) => x # INT |->_
#check fun (x value : Int) => x # INT128 |-> value
#check fun (x value : Int) => x # UINT128 |-> value
#check fun (x : Int) => x # INT128 |->_
#check fun (x : Int) => x # UINT128 |->_
#check fun (x value : Int) => x # Int |-> value
#check fun (x value : Int) => x # Ptr |-> value
#check fun (x : Int) => x # Int |->_
#check fun (x : Int) => x # Ptr |->_
#check fun (x value : Int) (ty : front_end_type) => x # ty |-> value
#check fun (x : Int) (ty : front_end_type) => x # ty |->_
#check fun (x : lvalue_expr) => Padding(x, "S")
#check fun (xs : List Int) (x : Int) => xs +:: x

-- Source edge behavior: negative lengths produce zero cells.
example (storeA : addr -> Int -> TestRules.expr) (x : addr) :
    store_undef_array TestRules storeA x (-3) =
      store_undef_array_rec TestRules storeA x 0 (-3) 0 := by
  rfl

example : merge_short 255 255 (-1) := merge_short_255_255_neg_1
example : merge_short 255 (-1) (-1) := merge_short_255_neg1_neg_1

-- Core tactic behavior on the same goal shapes as the Coq rules.
example (P : Assertion) : P |-- P := by
  exact SacContext.rules.toContext.derivable1_refl P

example (P : Assertion) : P |-- P := by
  simpl_auto

example {A : Type} (P : A -> Assertion) (Q : Assertion)
    (h : forall x, P x |-- Q) : (EX x, P x) |-- Q := by
  Intros x
  exact h x

example {A : Type} (P : Assertion) (Q : A -> Assertion)
    (h : forall x, P |-- Q x) : P |-- (ALL x, Q x) := by
  Intros_r x
  exact h x

example {A : Type} (P : A -> Assertion) (Q : Assertion)
    (h : forall x, P x |-- Q) : (EX x, P x) |-- Q := by
  Intro_any
  exact h _

example {A : Type} (R : A -> Prop) (P : A -> Assertion) (Q : Assertion)
    (h : forall x, R x -> (P x |-- Q)) :
    (EX x, “ R x ” && P x) |-- Q := by
  Intro_any
  exact h _ (by assumption)

example {A : Type} (P : Assertion) (Q : A -> Assertion)
    (h : forall x, P |-- Q x) : P |-- (ALL x, Q x) := by
  Intros_r_any
  exact h _

example {A : Type} (P : Assertion) (Q : A -> Assertion) (x : A)
    (h : P |-- Q x) : P |-- (EX y, Q y) := by
  Exists x
  exact h

example {A : Type} (P : Assertion) (Q : A -> Assertion) (x : A)
    (h : P |-- Q x) : P |-- (EX y, Q y) := by
  eExists
  exact h

example {A : Type} (P : A -> Assertion) (Q : Assertion) (x : A)
    (h : P x |-- Q) : (ALL y, P y) |-- Q := by
  Exists_l x
  exact h

example : Exists fun x : Nat => x = 0 := by
  Exists_l 0
  rfl

example (P : Prop) (Q : Assertion) : (“ P ” && Q) |-- Q := by
  Intros_p hP
  entailer!

example (P : Prop) (Q : Assertion) : (Q && “ P ”) |-- Q := by
  Intros_p hP
  entailer!

-- A spatial-only antecedent with a pure conjunction conclusion takes the
-- structural pure branch before store normalization. This is the shape used
-- by the two large exgcd safety witnesses.
example (x value : Int) (hlo : Int.min_signed <= value)
    (hhi : value <= Int.max_signed) :
    store_4byte TestRules x value |--
      “ Int.min_signed <= value ” && “ value <= Int.max_signed ” := by
  entailer!

example (P Q : Assertion) : P |-- P || Q := by
  Left
  entailer!

example (P Q : Assertion) : Q |-- P || Q := by
  Right
  entailer!

-- `Left` and `Right` retain Coq's setoid-rewrite behavior below `sepcon`.
example (P Q R : Assertion) : P ** Q |-- P ** (Q || R) := by
  Left
  entailer!

example (P Q R : Assertion) : P ** R |-- P ** (Q || R) := by
  Right
  entailer!

example (P Q R : Assertion) (hP : P |-- R) (hQ : Q |-- R) : P || Q |-- R := by
  Split
  · exact hP
  · exact hQ

-- Coq-style scripts perform top-level disjunction elimination explicitly.
example (P Q R : Assertion) (hP : P |-- R) (hQ : Q |-- R) : P || Q |-- R := by
  Split
  · exact hP
  · exact hQ

-- Existential branches are introduced by `Split`/`Intros`, not by `entailer!`.
example (P : Int -> Assertion) (Q R : Assertion)
    (hP : forall x, P x |-- R) (hQ : Q |-- R) :
    (EX x : Int, P x) || Q |-- R := by
  Split
  · Intros x
    exact hP x
  · exact hQ

-- Larger existential disjunctions use the same explicit route and name their
-- witnesses immediately afterwards.
example (P Q : Int -> Assertion) (S R : Assertion)
    (hP : forall x, P x |-- R) (hQ : forall x, Q x |-- R) (hS : S |-- R) :
    (EX x : Int, P x) || (EX x : Int, Q x) || S |-- R := by
  Split
  · Intros x
    exact hP x
  · Split
    · Intros x
      exact hQ x
    · exact hS

-- RHS disjunction and existential witnesses are explicit in the Coq route.
example (P : Int -> Assertion) (x : Int) : P x |-- (EX y : Int, P y) || emp := by
  Left
  Exists x
  entailer!

-- `Split` first distributes disjunctions nested under either sepcon argument.
example (P Q R S : Assertion) (hP : P ** R |-- S) (hQ : Q ** R |-- S) :
    (P || Q) ** R |-- S := by
  Split
  · exact hP
  · exact hQ

example (P Q R S : Assertion) (hQ : P ** Q |-- S) (hR : P ** R |-- S) :
    P ** (Q || R) |-- S := by
  Split
  · exact hQ
  · exact hR

example : emp |-- emp -* emp := by
  wand_elim
  entailer!

example (P Q R : Assertion) (h : P ** Q |-- R) : P |-- Q -* R := by
  wand_elim
  exact h

example (P Q R S : Assertion) (h : (P ** Q) ** R |-- S) :
    P |-- Q -* (R -* S) := by
  wand_elim
  exact h

example (P Q : Assertion) : P && Q |-- P := by
  entailer_pure

example (P Q : Assertion) : P && Q |-- Q && P := by
  entailer_pure

example (P Q R : Assertion) : (P && Q) && R |-- R && P := by
  andp_cancel

example (P : Assertion) : P |-- TT && P := by
  andp_cancel

example (A : Prop) (P : Assertion) (hA : A) : P |-- “ A ” && P := by
  andp_cancel

example (P Q : Assertion) : P ** Q |-- Q ** P := by
  andp_cancel

example (P Q : Assertion) : P ** Q |-- Q ** P := by
  entailer_pure

example (P : Assertion) : P |-- P := by
  pre_process_default

example (P Q R : Assertion) (h : Q |-- R) : P ** Q |-- P ** R := by
  pre_process

-- `pre_process` unfolds transparent local assertion wrappers when they expose
-- a spatial product, matching Coq's simpl/cancel pipeline.
def wrappedSepcon (P Q : Assertion) : Assertion := P ** Q

attribute [sac_unfold] wrappedSepcon

example (P Q : Assertion) : P ** Q |-- wrappedSepcon P Q := by
  pre_process

-- The bounded arithmetic compatibility branch covers the source `lia`/`nia`
-- shapes reached by the migrated abs and multiplication examples.
example (x : Int) (hx : 0 <= x) :
    TT && emp |-- “ x = SimpleC.SL.IntLib.Zabs x ” && emp := by
  pre_process

example (x : Int) (hx : x < 0) :
    TT && emp |-- “ -x = SimpleC.SL.IntLib.Zabs x ” && emp := by
  pre_process

example (x y : Int) :
    TT && emp |-- “ (0 + y) + (x - 1) * y = x * y ” && emp := by
  pre_process

example (x y i j ans : Int) (hi : i + 1 > x) (hix : i <= x)
    (hj : j + 1 > y) (hjy : j <= y)
    (hans : ans = (i - 1) * y + j) :
    TT && emp |-- “ ans = x * y ” && emp := by
  pre_process

example (x : Int) (hx : 0 <= x ∧ x < 100) :
    TT && emp |--
      “ SimpleC.SL.IntLib.INT_MIN <= 0 + x ∧
        0 + x <= SimpleC.SL.IntLib.INT_MAX ” && emp := by
  pre_process
  entailer!

example (A B : Prop) (hA : A) : A \/ B := by
  pre_process_default

example (A B : Prop) (hB : B) : A \/ B := by
  aggressive_pre_process

example (A B : Prop) (P : Assertion) (hA : A) (hB : B) :
    P |-- ((“ A ” && “ B ”) && P) := by
  aggressive_pre_process <;> assumption

example (A B : Prop) (P : Assertion) (hA : A) (hB : B) :
    P |-- (“ A ” && (“ B ” && P)) := by
  aggressive_pre_process <;> assumption

-- All four bounded variadic tactics accept the source zero-argument form.
example (P : Assertion) : P |-- P := by
  Intros
  exact SacContext.rules.toContext.derivable1_refl P

example (P Q R S : Assertion) (h : P ** (Q ** R) |-- S) :
    (P ** Q) ** R |-- S := by
  Intros
  exact h

example (P : Assertion) : P |-- P := by
  Intros_r
  exact SacContext.rules.toContext.derivable1_refl P

example (P : Assertion) : P ** emp |-- P := by
  Exists
  exact SacContext.rules.toContext.derivable1_refl P

example (P : Assertion) : P ** emp |-- P := by
  Exists_l
  exact SacContext.rules.toContext.derivable1_refl P

example (P : Assertion) : nestedExp 20 P |-- P := by
  Intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
  entailer!

example (P : Assertion) : P |-- nestedAll 20 P := by
  Intros_r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
  entailer!

example (P : Type -> Assertion) (h : forall A : Type, emp |-- P A) :
    emp |-- (ALL A : Type, P A) := by
  Intros_r A
  exact h A

example (P : Assertion) (Q : Int -> Int -> Assertion)
    (h : forall x y, Q x y |-- P) :
    (EX x : Int, (EX y : Int, Q x y) ** emp) |-- P := by
  Intros x y
  exact h x y

example (P : Int -> Assertion) (Q R S : Assertion)
    (h : forall x, P x ** (Q ** R) |-- S) :
    ((EX x : Int, P x) ** Q) ** R |-- S := by
  Intros x
  exact h x

example (P Q : Assertion) (h : P |-- Q) :
    (EX _x : Int, P) |-- Q := by
  Intros _
  exact h

example (P : Int -> Int -> Assertion) (Q : Assertion)
    (h : forall x y, P x y |-- Q) :
    (EX p : (Int × Int), P p.1 p.2) |-- Q := by
  Intros ⟨x, y⟩
  exact h x y

example (P : Assertion) (Q : Int -> Int -> Assertion)
    (h : forall x y, P |-- Q x y) :
    P |-- (ALL x : Int, (ALL y : Int, Q x y) ** emp) := by
  Intros_r x y
  exact h x y

example (P Q : Assertion) (h : P |-- Q) :
    P |-- (ALL _x : Int, Q) := by
  Intros_r _
  exact h

example (P : Assertion) (Q : Int -> Int -> Assertion)
    (h : forall x y, P |-- Q x y) :
    P |-- (ALL p : (Int × Int), Q p.1 p.2) := by
  Intros_r ⟨x, y⟩
  exact h x y

example (P : Assertion) : P |-- nestedExp 20 P := by
  Exists (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)
    (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)
    (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)
    (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)
  entailer!

-- `Exists` normalizes before each witness, as in the source tactic.
example (A : Prop) (P : Assertion) (Q : Int -> Int -> Assertion)
    (hA : A) (h : P |-- Q 0 1) :
    P |-- (EX x : Int, “ A ” && (EX y : Int, Q x y)) := by
  Exists (0 : Int) (1 : Int)
  apply split_pure_and_spatial_goals
  · exact h
  · exact dump_spatial_left SacContext.rules P A hA

example (P : Assertion) (Q : Int -> Assertion) (h : P |-- Q 0) :
    P |-- (EX x : Int, Q x) ** emp := by
  Exists (0 : Int)
  exact h

example (P : Assertion) (Q : Int -> Int -> Assertion)
    (h : Q 0 1 |-- P) :
    (ALL x, ALL y, Q x y) ** emp |-- P := by
  Exists_l (0 : Int) (1 : Int)
  exact h

example (P : Assertion) : nestedAll 20 P |-- P := by
  Exists_l (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)
    (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)
    (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)
    (0 : Int) (0 : Int) (0 : Int) (0 : Int) (0 : Int)
  entailer!

example : True := by
  fail_if_success
    Intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  trivial

example : True := by
  fail_if_success
    Intros_r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  trivial

example : True := by
  fail_if_success
    Exists 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  trivial

example : True := by
  fail_if_success
    Exists_l 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  trivial

-- Cancellation is proof-producing and works modulo sepcon association/commutation.
example (P Q R : Assertion) : (P ** Q) ** R |-- P ** (Q ** R) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

-- The public tactic traverses the complete entailment, including its RHS.
example (P Q R : Assertion) : P ** (Q ** R) |-- (P ** Q) ** R := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q R S : Assertion) :
    S && ((P ** Q) ** R) |-- S && (P ** (Q ** R)) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q R : Int -> Assertion) :
    (EX x : Int, (P x ** Q x) ** R x) |--
      (EX x : Int, P x ** (Q x ** R x)) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q R : Assertion) :
    (P ** Q) ** R ⊣⊢ P ** (Q ** R) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.logic_equiv_refl _

example (P Q R : Int -> Assertion) :
    (ALL x : Int, (P x ** Q x) ** R x) |--
      (ALL x : Int, P x ** (Q x ** R x)) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q R S : Assertion) :
    S || ((P ** Q) ** R) |-- S || (P ** (Q ** R)) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q R S : Assertion) :
    S -* ((P ** Q) ** R) |-- S -* (P ** (Q ** R)) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q R S : Assertion) :
    S ⟶ₗ ((P ** Q) ** R) |-- S ⟶ₗ (P ** (Q ** R)) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q R S : Assertion) :
    SacContext.rules.toContext.iffp S ((P ** Q) ** R) |--
      SacContext.rules.toContext.iffp S (P ** (Q ** R)) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q R : Assertion) : P ** (Q ** R) |-- P ** (Q ** R) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

set_option maxHeartbeats 500000 in
example (A B C D E F G H I J : Assertion) :
    (((((((((A ** B) ** C) ** D) ** E) ** F) ** G) ** H) ** I) ** J) |--
      A ** (B ** (C ** (D ** (E ** (F ** (G ** (H ** (I ** J)))))))) := by
  sepcon_assoc_change
  exact SacContext.rules.toContext.derivable1_refl _

example (P Q : Assertion) : P ** Q |-- Q ** P := by
  cancel

example (P Q R : Assertion) : (P ** Q) ** R |-- R ** (Q ** P) := by
  cancel

example (P Q R : Assertion) (h : Q |-- R) : P ** Q |-- P ** R := by
  cancel
  exact h

example (P Q R : Assertion) : P ** (Q ** R) |-- R ** (Q ** P) := by
  cancel Q
  cancel

example (P Q R : Assertion) : (R ** P) ** Q |-- Q ** (R ** P) := by
  sepcon_lift P
  change P ** (R ** Q) |-- P ** (Q ** R)
  cancel

example (P Q R S T : Assertion)
    (h : (Q ** P) && R |-- (Q ** S) && T) :
    (P ** Q) && R |-- (S ** Q) && T := by
  sepcon_lift Q
  exact h

-- A one-sided hit must not make the exp-bound conclusion a rewrite target.
example (P Q : Assertion) (h : P ** Q |-- EX _x : Int, Q) :
    Q ** P |-- EX _x : Int, Q := by
  sepcon_lift P
  exact h

set_option linter.unusedVariables false in
example (P Q R : Assertion) : True := by
  fail_if_success
    have : P ** Q |-- P ** Q := by
      sepcon_lift R
  trivial

example (P Q : Assertion) (h : emp |-- Q) : P |-- P ** Q := by
  cancel P
  exact h

example (P Q : Assertion) (h : Q |-- emp) : P ** Q |-- P := by
  cancel P
  exact h

example (P Q R : Assertion) (h : P |-- Q) : P ** R |-- Q ** R := by
  sep_apply_l_atomic h
  entailer!

example (P Q R S : Assertion) (h : P |-- Q)
    (rest : R |-- P ** S) : R |-- Q ** S := by
  sep_apply_r_atomic h
  exact rest

example (P Q R : Assertion) (h : P |-- Q && R) : P |-- Q && R := by
  sep_apply_right h
  entailer!

example (P Q R : Assertion) (h : P |-- Q && R) : P |-- Q && R := by
  sep_apply_r_atomic h
  entailer!

example (P Q R S : Assertion) (h : P ** Q |-- S) :
    (R ** Q) ** P |-- S ** R := by
  sep_apply_l_atomic h
  entailer!

example (P Q R S T : Assertion) (h : P ** Q |-- S)
    (rest : R |-- (P ** Q) ** T) : R |-- T ** S := by
  sep_apply_r_atomic h
  exact rest

example (P Q R : Assertion) (h : P ⊣⊢ Q) : R ** P |-- Q ** R := by
  sep_apply_l_atomic h
  entailer!

example (P Q : Int -> Assertion) (h : forall x, P x |-- Q x) :
    P 7 |-- Q 7 := by
  sep_apply h
  entailer!

example (P Q : Int -> Assertion) (h : forall x, P x |-- Q x) :
    P 7 |-- Q 7 := by
  sep_apply_left h
  entailer!

example (P Q R : Assertion) (h : P |-- Q)
    (rest : R |-- P) : R |-- Q := by
  sep_apply_right h
  exact rest

example (P Q R S : Assertion) (h : P |-- Q)
    (rest : S |-- P && R) : S |-- Q && R := by
  sep_apply_right h
  exact rest

example (P Q R S : Assertion) (h : P |-- Q)
    (rest : S |-- P && R) : S |-- Q && R := by
  sep_apply_r_atomic h
  exact rest

example (A : Prop) (P Q : Assertion) (h : A -> (P |-- Q))
    (hPure : P |-- “ A ”) : P |-- Q := by
  sep_apply_l_atomic h
  · exact hPure
  · entailer!

example (P Q : Assertion) (h : forall n : Nat, P |-- Q) : P |-- Q := by
  fail_if_success sep_apply_l_atomic h
  exact h 0

-- Legacy application keeps Coq's `cut` ordering: spatial residual first,
-- then ordinary proposition premises from the last binder back to the first.
example (A B : Prop) (P Q : Assertion) (h : A -> B -> (P |-- Q))
    (hA : A) (hB : B) : P |-- Q := by
  sep_apply h
  · entailer!
  · exact hB
  · exact hA

example (A : Prop) (P R : Assertion) (h : P |-- “ A ”) :
    P ** R |-- P ** R := by
  prop_apply h
  entailer!

private def hiddenSepcon (P Q : Assertion) : Assertion := P ** Q

-- The source-style exposed-atom path deliberately does not unfold
-- hiddenSepcon; the compatibility normalizer must still handle it.
example (A : Prop) (P Q R : Assertion) (h : P ** Q |-- “ A ”) :
    hiddenSepcon P Q ** R |-- hiddenSepcon P Q ** R := by
  prop_apply h
  entailer!

example (A B : Prop) (P R : Assertion) (h : A -> (P |-- “ B ”))
    (hA : A) : P ** R |-- P ** R := by
  prop_apply h
  · entailer!
  · exact hA

example (A B : Prop) (P R : Assertion) (h : P |-- (“ A ” && “ B ”)) :
    P ** R |-- P ** R := by
  prop_apply h
  entailer!

example (A : Prop) (P R : Assertion) (h : P |-- “ A ”) :
    P ** R |-- P ** R := by
  prop_apply_p h
  entailer!

example (A B : Prop) (P : Assertion) (h : A -> (P |-- “ B ”))
    (hA : A) : P |-- P := by
  fail_if_success prop_apply_p h
  exact SacContext.rules.toContext.derivable1_refl P

example (A : Prop) (P : Assertion) (h : P |-- “ A ”) : P |-- P := by
  add_pure A as hA
  · exact h
  · entailer!

example (P : Assertion) : P |-- P := by
  Goal_apply SacContext.rules.toContext.derivable1_refl P

example (P Q R : Assertion) (h : P |-- Q) : P ** R |-- Q ** R := by
  Goal_apply h

def goalApplyAggressiveSpatialRule : Prop :=
  forall (P : Assertion) (A B C D : Prop)
    (_hA : A) (_hB : B) (_hC : C) (_hD : D),
    P |-- TT && emp

theorem goal_apply_aggressive_spatial_rule : goalApplyAggressiveSpatialRule := by
  unfold goalApplyAggressiveSpatialRule
  intros
  entailer!

def goalApplyAggressivePureRuleA : Prop :=
  forall (P : Assertion) (A B C D : Prop)
    (_hA : A) (_hB : B) (_hC : C) (_hD : D),
    P |-- “ A ∧ True ”

def goalApplyAggressivePureRuleB : Prop :=
  forall (P : Assertion) (A B C D : Prop)
    (_hA : A) (_hB : B) (_hC : C) (_hD : D),
    P |-- “ B ∧ True ”

def goalApplyAggressivePureRuleC : Prop :=
  forall (P : Assertion) (A B C D : Prop)
    (_hA : A) (_hB : B) (_hC : C) (_hD : D),
    P |-- “ C ∧ True ”

def goalApplyAggressivePureRuleD : Prop :=
  forall (P : Assertion) (A B C D : Prop)
    (_hA : A) (_hB : B) (_hC : C) (_hD : D),
    P |-- “ D ∧ True ”

theorem goal_apply_aggressive_pure_rule_a : goalApplyAggressivePureRuleA := by
  unfold goalApplyAggressivePureRuleA
  intros
  dump_pre_spatial
  exact ⟨by assumption, trivial⟩

theorem goal_apply_aggressive_pure_rule_b : goalApplyAggressivePureRuleB := by
  unfold goalApplyAggressivePureRuleB
  intros
  dump_pre_spatial
  exact ⟨by assumption, trivial⟩

theorem goal_apply_aggressive_pure_rule_c : goalApplyAggressivePureRuleC := by
  unfold goalApplyAggressivePureRuleC
  intros
  dump_pre_spatial
  exact ⟨by assumption, trivial⟩

theorem goal_apply_aggressive_pure_rule_d : goalApplyAggressivePureRuleD := by
  unfold goalApplyAggressivePureRuleD
  intros
  dump_pre_spatial
  exact ⟨by assumption, trivial⟩

def goalApplyAggressiveFixture : Prop :=
  True \/ (forall (P : Assertion) (A B C D : Prop)
    (_hA : A) (_hB : B) (_hC : C) (_hD : D),
    P |-- “ A ∧ True ” && “ B ∧ True ” &&
      “ C ∧ True ” && “ D ∧ True ” && emp)

example : goalApplyAggressiveFixture := by
  aggressive_pre_process
  · Goal_apply goal_apply_aggressive_spatial_rule
  · Goal_apply goal_apply_aggressive_pure_rule_a
  · Goal_apply goal_apply_aggressive_pure_rule_b
  · Goal_apply goal_apply_aggressive_pure_rule_c
  · Goal_apply goal_apply_aggressive_pure_rule_d

theorem goal_apply_context_rule {A : Type} (x y : A) (h : x = y) : x = y := h

example {A : Type} (a b : A) (h : a = b) : a = b := by
  Goal_apply goal_apply_context_rule

theorem goal_apply_needs_two (x y : Nat) : True := by
  trivial

example (x : Nat) : True := by
  fail_if_success Goal_apply goal_apply_needs_two
  trivial

example (P Q : Assertion) (h : TT && P |-- Q) : P |-- Q := by
  Goal_apply h

example (P Q : Assertion) (h : P |-- Q && TT) : P |-- Q := by
  Goal_apply h

example (P Q : Assertion) (h : TT && P ⊣⊢ Q) : P |-- Q := by
  Goal_apply h

example (P Q : Assertion) (h : TT && P ⊣⊢ Q) : P ⊣⊢ Q := by
  Goal_apply h

example (P Q R : Assertion) (h : (TT && P) ** R |-- Q) :
    P ** R |-- Q := by
  Goal_apply h

example (P Q : Int -> Assertion)
    (h : (EX x : Int, TT && P x) |-- (EX x : Int, Q x)) :
    (EX x : Int, P x) |-- (EX x : Int, Q x) := by
  Goal_apply h

example (P : Assertion) (Q : Int -> Assertion)
    (h : P |-- (ALL x : Int, TT && Q x)) :
    P |-- (ALL x : Int, Q x) := by
  Goal_apply h

example (P Q R : Assertion) (h : (TT && P) || R |-- Q) :
    P || R |-- Q := by
  Goal_apply h

example (P Q R : Assertion) (h : P |-- (TT && Q) -* R) :
    P |-- Q -* R := by
  Goal_apply h

example (P Q R : Assertion) (h : P |-- (TT && Q) ⟶ₗ R) :
    P |-- Q ⟶ₗ R := by
  Goal_apply h

example (P Q R : Assertion)
    (h : P |-- SacContext.rules.toContext.iffp (TT && Q) R) :
    P |-- SacContext.rules.toContext.iffp Q R := by
  Goal_apply h

example (P Q : Assertion) (h : P |-- Q) : P |-- Q := by
  cancel
  exact h

-- Normalization follows the one-way Coq rewrite set.
example (P : Assertion) : P ** emp |-- P := by
  normalize
  entailer!

example (P : Assertion) : emp ** P |-- P := by
  normalize
  entailer!

example (P : Assertion) : TT && P |-- P := by
  normalize
  entailer!

example (P Q R : Assertion) : (P || Q) ** R |-- (P ** R) || (Q ** R) := by
  normalize
  entailer!

example (A B : Prop) : (“ A ” || “ B ”) |-- “ A ∨ B ” := by
  normalize
  entailer!

example (x value : Int) :
    poly_store TestRules FET_int x value |-- store_int TestRules x value := by
  entailer!

-- Phase-four A: the integer-128 branches now reduce to real 16-byte stores.
example (x value : Int) :
    poly_store TestRules FET_int128 x value = store_int128 TestRules x value := by
  poly_store_unfold
example (x value : Int) :
    poly_store TestRules FET_uint128 x value = store_uint128 TestRules x value := rfl
example (x : Int) :
    poly_undef_store TestRules FET_int128 x = undef_store_int128 TestRules x := by
  poly_store_unfold
example (x : Int) :
    poly_undef_store TestRules FET_uint128 x = undef_store_uint128 TestRules x := rfl

example (x value : Int) :
    store_16byte TestRules x value =
      TestRules.exp (Vector Int 16) (fun bytes =>
        TestRules.andp
          (TestRules.coq_prop
            (SimpleC.SL.CArch.BigEndian.merge_n_bytes 16 bytes value))
          (store_bytes TestRules x 16 bytes)) := rfl

example : SimpleC.SL.CommonAssertion.isvalidptr_int128 (Int.max_unsigned - 15) := by
  unfold SimpleC.SL.CommonAssertion.isvalidptr_int128 aligned_4
  native_decide
example : ¬SimpleC.SL.CommonAssertion.isvalidptr_int128 (Int.max_unsigned - 14) := by
  unfold SimpleC.SL.CommonAssertion.isvalidptr_int128 aligned_4
  native_decide

-- Phase-four B: untyped bit-pattern stores and dependent typed stores both
-- reduce to the same concrete floating store definitions.
example (x value : Int) :
    poly_store TestRules FET_float x value =
      store_float TestRules x (fp32_of_bits value) := by
  poly_store_unfold
-- Freeze Coq split_bits semantics through the actual untyped-store path.  The
-- sign, exponent, and fraction fields are decoded separately for inputs that
-- are outside the target unsigned range.
section PolyStoreSplitBitsTests

set_option maxRecDepth 100000

theorem poly_store_float_neg_one (x : Int) :
    poly_store TestRules FET_float x (-1) =
      store_float TestRules x (fp32_of_bits 2147483647) := by
  change store_float TestRules x (fp32_of_bits (-1)) = _
  exact congrArg (store_float TestRules x) (by decide)
theorem poly_store_float_width (x : Int) :
    poly_store TestRules FET_float x 4294967296 =
      store_float TestRules x (fp32_of_bits 2147483648) := by
  change store_float TestRules x (fp32_of_bits 4294967296) = _
  exact congrArg (store_float TestRules x) (by decide)
theorem poly_store_float_double_width_pred (x : Int) :
    poly_store TestRules FET_float x 8589934591 =
      store_float TestRules x (fp32_of_bits 4294967295) := by
  change store_float TestRules x (fp32_of_bits 8589934591) = _
  exact congrArg (store_float TestRules x) (by decide)
theorem poly_store_double_neg_one (x : Int) :
    poly_store TestRules FET_double x (-1) =
      store_double TestRules x (fp64_of_bits 9223372036854775807) := by
  change store_double TestRules x (fp64_of_bits (-1)) = _
  exact congrArg (store_double TestRules x) (by decide)
theorem poly_store_double_width (x : Int) :
    poly_store TestRules FET_double x 18446744073709551616 =
      store_double TestRules x (fp64_of_bits 9223372036854775808) := by
  change store_double TestRules x (fp64_of_bits 18446744073709551616) = _
  exact congrArg (store_double TestRules x) (by decide)
theorem poly_store_double_double_width_pred (x : Int) :
    poly_store TestRules FET_double x 36893488147419103231 =
      store_double TestRules x (fp64_of_bits 18446744073709551615) := by
  change store_double TestRules x (fp64_of_bits 36893488147419103231) = _
  exact congrArg (store_double TestRules x) (by decide)
theorem poly_store_long_double_neg_one (x : Int) :
    poly_store TestRules FET_long_double x (-1) =
      store_long_double TestRules x (fp128_of_bits (Z.pow 2 127 - 1)) := by
  change store_long_double TestRules x (fp128_of_bits (-1)) = _
  exact congrArg (store_long_double TestRules x) (by decide)
theorem poly_store_long_double_width (x : Int) :
    poly_store TestRules FET_long_double x (Z.pow 2 128) =
      store_long_double TestRules x (fp128_of_bits (Z.pow 2 127)) := by
  change store_long_double TestRules x (fp128_of_bits (Z.pow 2 128)) = _
  exact congrArg (store_long_double TestRules x) (by decide)
theorem poly_store_long_double_double_width_pred (x : Int) :
    poly_store TestRules FET_long_double x (Z.pow 2 129 - 1) =
      store_long_double TestRules x (fp128_of_bits (Z.pow 2 128 - 1)) := by
  change store_long_double TestRules x (fp128_of_bits (Z.pow 2 129 - 1)) = _
  exact congrArg (store_long_double TestRules x) (by decide)

#print axioms poly_store_float_neg_one
#print axioms poly_store_double_width
#print axioms poly_store_long_double_double_width_pred

end PolyStoreSplitBitsTests

example (x value : Int) :
    poly_store TestRules FET_double x value =
      store_double TestRules x (fp64_of_bits value) := by
  poly_store_unfold
example (x value : Int) :
    poly_store TestRules FET_long_double x value =
      store_long_double TestRules x (fp128_of_bits value) := by
  poly_store_unfold
example (x : Int) :
    poly_undef_store TestRules FET_float x = undef_store_float TestRules x := by
  poly_store_unfold
example (x : Int) :
    poly_undef_store TestRules FET_double x = undef_store_double TestRules x := by
  poly_store_unfold
example (x : Int) :
    poly_undef_store TestRules FET_long_double x = undef_store_long_double TestRules x := by
  poly_store_unfold

example (x : Int) (value : fp32) :
    typed_poly_store TestRules FET_float x value = store_float TestRules x value := by
  poly_store_unfold
example (x : Int) (value : fp64) :
    typed_poly_store TestRules FET_double x value = store_double TestRules x value := by
  poly_store_unfold
example (x : Int) (value : fp128) :
    typed_poly_store TestRules FET_long_double x value =
      store_long_double TestRules x value := by
  poly_store_unfold
example (x value : Int) :
    typed_poly_store TestRules FET_int128 x value = store_int128 TestRules x value := by
  poly_store_unfold

example : front_end_type_value FET_float = fp32 := rfl
example : front_end_type_value FET_double = fp64 := rfl
example : front_end_type_value FET_long_double = fp128 := rfl
example : front_end_type_value FET_uint128 = Int := rfl

example (x : Int) (value : fp32) :
    store_float TestRules x value =
      TestRules.andp
        (TestRules.coq_prop
          (SimpleC.SL.CommonAssertion.isvalidptr_float x ∧ 0 <= bits_of_fp32 value ∧
            bits_of_fp32 value <= Int.max_unsigned))
        (store_4byte TestRules x (bits_of_fp32 value)) := rfl

example (x : Int) (value : fp64) :
    store_finite_double TestRules x value =
      TestRules.andp (TestRules.coq_prop (fp64_isFinite value))
        (store_double TestRules x value) := rfl

example (x : Int) (value : fp32) :
    (x # Float |-> value) = store_float TestRules x value := rfl
example (x : Int) (value : fp128) :
    (x # FiniteLongDouble |-> value) =
      store_finite_long_double TestRules x value := rfl
example (x : Int) :
    (x # Double |->_) = undef_store_double TestRules x := rfl

-- Store notation binds tighter than the separation connectives, as in Coq's
-- source expressions used by generated verification conditions.
example (x y : Int) (vx vy : fp32) :
    (x # Float |-> vx ** y # Float |-> vy) =
      TestRules.sepcon (store_float TestRules x vx) (store_float TestRules y vy) := rfl
example (P : Prop) (x : Int) (value : fp64) :
    (“ P ” && x # Double |-> value) =
      TestRules.andp (TestRules.coq_prop P) (store_double TestRules x value) := rfl

example (x value : Int)
    (hRange : SimpleC.SL.CommonAssertion.isvalidptr_int x ∧ value <= Int.max_signed ∧
      value >= Int.min_signed) :
    store_4byte TestRules x value |-- store_int TestRules x value := by
  entailer!

example (ty : front_end_type) (x : Int) :
    poly_undef_store TestRules ty x |-- poly_undef_store TestRules ty x := by
  poly_store_unfold
  cancel

example (A : Prop) (P R : Assertion) :
    (P && “ A ”) ** R |-- (“ A ” && P) ** R := by
  rel_rw [SimpleC.SL.CommonAssertion.DerivedPredSig.AutomationHelpers.coq_prop_andp_right_equiv]
  simpl_auto

example (A : Prop) (P : Assertion) :
    “ A ” ** P |-- P ** “ A ” := by
  rel_rw [SimpleC.SL.CommonAssertion.DerivedPredSig.AutomationHelpers.coq_prop_sepcon_left_equiv]
  simpl_auto

example {A : Type} (P : Assertion) (Q : A -> Assertion) :
    P && SacContext.rules.exp A Q |--
      SacContext.rules.exp A (fun x => Q x && P) := by
  normalize
  entailer!

example {A : Type} (P : Assertion) (Q : A -> Assertion) :
    P ** SacContext.rules.exp A Q |--
      SacContext.rules.exp A (fun x => Q x ** P) := by
  normalize
  entailer!

example (P Q R : Assertion) : (P ** Q) && R |-- R && (P ** Q) := by
  normalize
  entailer!

example (P Q : Assertion) (h : P |-- Q) : P |-- Q := by
  normalize
  exact h

example (A : Prop) (P : Assertion) (hA : P |-- “ A ”) :
    P |-- “ A ” && P := by
  split_pure_spatial
  · entailer!
  · exact hA

example (A : Prop) (P : Assertion) (hA : P |-- “ A ”) :
    P |-- P && “ A ” := by
  split_pure_spatial
  · entailer!
  · exact hA

set_option linter.unusedVariables false in
example (P Q R : Assertion) : True := by
  fail_if_success
    have : P |-- Q && R := by
      split_pure_spatial
  trivial

example (A B : Prop) (P : Assertion)
    (hA : P |-- “ A ”) (hB : P |-- “ B ”) :
    P |-- “ A ” && “ B ” := by
  split_pures
  · exact hA
  · exact hB

example (P Q R : Assertion) (h : P |-- Q && R) : P |-- Q && R := by
  split_pures
  exact h

example (A : Prop) (P : Assertion) (hA : A) : P |-- “ A ” := by
  dump_pre_spatial
  exact hA

example (A B C : Prop) (P : Assertion) (hA : A) (hB : B) (hC : C) :
    P |-- “ A ” && “ B ” && “ C ” && P := by
  entailer!

private structure TacticOptionCell where
  result : Option Int

example (a : TacticOptionCell) (result : Int)
    (hresult : a.result = some result)
    (hRange :
      (match a.result with | none => 0 | some r => r) <= Int.max_signed ∧
      (match a.result with | none => 0 | some r => r) >= Int.min_signed) :
    result <= Int.max_signed ∧ result >= Int.min_signed := by
  constructor <;> simpl_auto

example (result : Int) (P : Assertion)
    (hRange : result <= Int.max_signed ∧ result >= Int.min_signed) :
    P |-- “ result <= Int.max_signed ” &&
      “ result >= Int.min_signed ” && P := by
  entailer!

example (v z : Int) (h : v = z)
    (hvalid : DerivedPredSig.valid_ptr_value SimpleC.SL.CArch.Arch32 z) :
    DerivedPredSig.valid_ptr_value SimpleC.SL.CArch.Arch32 v := by
  simpl_auto

example (P : Assertion) : P |-- P := by
  aggressive_pre_process

-- The shared pipeline reaches the same product-sign and absolute-value
-- boundary branches used by the arithmetic examples.
example (q n : Int) (hq : q <= 0) (hn : 0 <= n) : q * n <= 0 := by
  simpl_auto

example (x : Int) (hx : Z.abs x <= 2147483647) :
    -2147483648 < x ∧ x <= 2147483647 := by
  constructor <;> simpl_auto

example (x y : Int) (hxy : Z.abs x < Z.abs y)
    (hyLower : -2147483648 < y) (hyUpper : y <= 2147483647) :
    -2147483648 < x ∧ x <= 2147483647 := by
  constructor <;> simpl_auto

-- The compatibility tactic is intentionally not a general polynomial solver.
set_option linter.unusedVariables false in
example (x y : Int) : True := by
  fail_if_success
    have : 2 * x * y <= x * x + y * y := by
      simpl_auto
  trivial

example {A : Type} (a b : A) (xs ys : List A)
    (h : a :: xs = b :: ys) : a = b /\ xs = ys := by
  subst_eqs
  exact ⟨rfl, rfl⟩

example {A B : Type} (a a' : A) (b b' : B)
    (h : (a, b) = (a', b')) : a = a' /\ b = b' := by
  subst_eqs
  exact ⟨rfl, rfl⟩

example {A : Type} (a b : A) (h : some a = some b) : a = b := by
  subst_eqs
  rfl

example {A : Type} (a : A) (h : (none : Option A) = some a) : False := by
  subst_eqs

-- Imported proposition binders keep their source names after pre_process.
-- Its leading existential also exercises the no-witness fast path.
example : CommonAssertionBinderFixture.namedBinderGoal TestRules := by
  pre_process
  Exists (0 : Int)
  exact TestRules.toContext.derivable1_refl sourceAssertion

-- The low-level splitter preserves the Coq cancellation branch order.
example (P : Assertion) :
    P |-- “ exists n : Nat, n = 37 ” && “ exists n : Nat, n = 41 ” := by
  _andp_split_right
  · dump_pre_spatial
    exact ⟨41, rfl⟩
  · dump_pre_spatial
    exact ⟨37, rfl⟩

-- pre_process exports store guards, while sep_apply still matches a rule
-- stated with the original canonical store wrappers.
example (x value ptrAddr ptrValue : Int) (P : Assertion)
    (hInt : SimpleC.SL.CommonAssertion.isvalidptr_int x ∧ value <= Int.max_signed ∧
      value >= Int.min_signed)
    (hPtr : SimpleC.SL.CommonAssertion.isvalidptr ptrAddr ∧ ptrValue >= 0 ∧
      ptrValue <= Int.max_unsigned)
    (hRule : DerivedPredSig.store_int SimpleC.SL.CArch.Arch32
      SimpleC.SL.CArch.BigEndian TestRules x value **
      DerivedPredSig.store_ptr SimpleC.SL.CArch.Arch32
        SimpleC.SL.CArch.BigEndian TestRules ptrAddr ptrValue |-- P) :
    DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian TestRules x value **
      DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian TestRules
        ptrAddr ptrValue |-- P := by
  sep_apply hRule
  simpl_auto

-- sep_apply keeps a normalized store's complete pure-guard chain attached to
-- the matched spatial prefix, even when an unrelated frame follows it.
example (data value next nextValue prev prevValue : Int) (P Q : Assertion)
    (hRule :
      DerivedPredSig.store_int SimpleC.SL.CArch.Arch32
          SimpleC.SL.CArch.BigEndian TestRules data value **
      DerivedPredSig.store_ptr SimpleC.SL.CArch.Arch32
          SimpleC.SL.CArch.BigEndian TestRules next nextValue **
      DerivedPredSig.store_ptr SimpleC.SL.CArch.Arch32
          SimpleC.SL.CArch.BigEndian TestRules prev prevValue |-- Q) :
    DerivedPredSig.store_int SimpleC.SL.CArch.Arch32
        SimpleC.SL.CArch.BigEndian TestRules data value **
      DerivedPredSig.store_ptr SimpleC.SL.CArch.Arch32
        SimpleC.SL.CArch.BigEndian TestRules next nextValue **
      DerivedPredSig.store_ptr SimpleC.SL.CArch.Arch32
        SimpleC.SL.CArch.BigEndian TestRules prev prevValue ** P |-- Q ** P := by
  asrt_simpl
  sep_apply hRule
  entailer!

noncomputable abbrev wrappedStoreInt (x value : Int) : Assertion :=
  DerivedPredSig.store_int SimpleC.SL.CArch.Arch32
    SimpleC.SL.CArch.BigEndian TestRules x value

noncomputable abbrev wrappedStorePtr (x value : Int) : Assertion :=
  DerivedPredSig.store_ptr SimpleC.SL.CArch.Arch32
    SimpleC.SL.CArch.BigEndian TestRules x value

noncomputable abbrev wrappedStoreInt2 (x value : Int) : Assertion :=
  wrappedStoreInt x value

noncomputable abbrev wrappedStoreInt3 (x value : Int) : Assertion :=
  wrappedStoreInt2 x value

noncomputable abbrev wrappedStoreInt4 (x value : Int) : Assertion :=
  wrappedStoreInt3 x value

noncomputable abbrev wrappedStoreInt5 (x value : Int) : Assertion :=
  wrappedStoreInt4 x value

noncomputable def wrappedStorePair
    (x value ptrAddr ptrValue : Int) : Assertion :=
  wrappedStoreInt x value ** wrappedStorePtr ptrAddr ptrValue

example (x value ptrAddr ptrValue : Int) (P : Assertion)
    (hInt : SimpleC.SL.CommonAssertion.isvalidptr_int x ∧ value <= Int.max_signed ∧
      value >= Int.min_signed)
    (hPtr : SimpleC.SL.CommonAssertion.isvalidptr ptrAddr ∧ ptrValue >= 0 ∧
      ptrValue <= Int.max_unsigned)
    (hRule : wrappedStoreInt x value ** wrappedStorePtr ptrAddr ptrValue |-- P) :
    DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian TestRules x value **
      DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian TestRules
        ptrAddr ptrValue |-- P := by
  sep_apply hRule
  simpl_auto

-- Guard removal runs after a transparent composite predicate is normalized.
example (x value ptrAddr ptrValue : Int) (P : Assertion)
    (hInt : SimpleC.SL.CommonAssertion.isvalidptr_int x ∧ value <= Int.max_signed ∧
      value >= Int.min_signed)
    (hPtr : SimpleC.SL.CommonAssertion.isvalidptr ptrAddr ∧ ptrValue >= 0 ∧
      ptrValue <= Int.max_unsigned)
    (hRule : wrappedStorePair x value ptrAddr ptrValue |-- P) :
    DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian TestRules x value **
      DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian TestRules
        ptrAddr ptrValue |-- P := by
  sep_apply hRule
  simpl_auto

-- Coq unification follows transparent aliases without a small fixed depth.
-- Cover both four- and five-link alias chains.
example (x value : Int) (P : Assertion)
    (hInt : SimpleC.SL.CommonAssertion.isvalidptr_int x ∧ value <= Int.max_signed ∧
      value >= Int.min_signed)
    (hRule : wrappedStoreInt4 x value |-- P) :
    DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian TestRules x value |-- P := by
  sep_apply hRule
  simpl_auto

example (x value : Int) (P : Assertion)
    (hInt : SimpleC.SL.CommonAssertion.isvalidptr_int x ∧ value <= Int.max_signed ∧
      value >= Int.min_signed)
    (hRule : wrappedStoreInt5 x value |-- P) :
    DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian TestRules x value |-- P := by
  sep_apply hRule
  simpl_auto

-- The selected SAC rule projection and its concrete value denote the same
-- finite store atom.
example (x value : Int) (P : Assertion)
    (hRule : store_4byte SacContext.rules x value |-- P) :
    store_4byte TestRules x value |-- P := by
  sep_apply hRule
  entailer!

-- Full definitional equality for finite stores must not identify distinct
-- addresses, values, or store widths.
set_option linter.unusedVariables false in
example (x y value : Int) (hxy : x ≠ y)
    (hRule : store_4byte TestRules x value |-- emp) :
    store_4byte TestRules y value |-- store_4byte TestRules y value := by
  fail_if_success sep_apply hRule
  exact TestRules.toContext.derivable1_refl _

set_option linter.unusedVariables false in
example (x value other : Int) (hvalue : value ≠ other)
    (hRule : store_4byte TestRules x value |-- emp) :
    store_4byte TestRules x other |-- store_4byte TestRules x other := by
  fail_if_success sep_apply hRule
  exact TestRules.toContext.derivable1_refl _

set_option linter.unusedVariables false in
example (x value : Int)
    (hRule : store_2byte TestRules x value |-- emp) :
    store_4byte TestRules x value |-- store_4byte TestRules x value := by
  fail_if_success sep_apply hRule
  exact TestRules.toContext.derivable1_refl _

set_option linter.unusedVariables false in
example (x value : Int)
    (hRule : DerivedPredSig.store_4byte SimpleC.SL.CArch.LittleEndian
      TestRules x value |-- emp) :
    DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian
      TestRules x value |--
        DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian
          TestRules x value := by
  fail_if_success sep_apply hRule
  exact TestRules.toContext.derivable1_refl _

set_option linter.unusedVariables false in
example (x value : Int)
    (hRule : store_4byte_noninit TestRules x |-- emp) :
    store_4byte TestRules x value |-- store_4byte TestRules x value := by
  fail_if_success sep_apply hRule
  exact TestRules.toContext.derivable1_refl _

set_option linter.unusedVariables false in
example (x value : Int)
    (hRule : DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian
      OtherRules x value |-- emp) :
    DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian
      TestRules x value |--
        DerivedPredSig.store_4byte SimpleC.SL.CArch.BigEndian
          TestRules x value := by
  fail_if_success sep_apply hRule
  exact TestRules.toContext.derivable1_refl _

-- Although int and pointer wrappers share a four-byte spatial atom, the int
-- wrapper cannot be stripped when only the pointer guard is available.
set_option linter.unusedVariables false in
example (x value : Int)
    (hPtr : SimpleC.SL.CommonAssertion.isvalidptr x ∧ value >= 0 ∧ value <= Int.max_unsigned)
    (hRule : store_int TestRules x value |-- emp) :
    store_ptr TestRules x value |-- store_ptr TestRules x value := by
  fail_if_success sep_apply hRule
  exact TestRules.toContext.derivable1_refl _

#print axioms merge_int_equiv
#print axioms store_16byte
#print axioms store_int128
#print axioms sepcon_prop_equiv
#print axioms elim_wand_emp_emp

end CommonAssertionTests
