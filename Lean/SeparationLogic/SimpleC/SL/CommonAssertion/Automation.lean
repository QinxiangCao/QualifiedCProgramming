import SimpleC.SL.CommonAssertion.Derived
import AUXLib.NiaCompat
import Lean.Attributes
import Lean.Elab.Tactic
import Lean.Elab.Tactic.Injection
import Lean.Meta.Tactic.Rename
import Lean.ReducibilityAttrs

register_simp_attr sac_unfold

namespace SimpleC.SL.CommonAssertion

open Unifysl.LogicGenerator.demo932

universe u

class SacContext where
  CRules : SeparationLogicSig

class SacArchContext where
  Arch : SimpleC.SL.CArch.CArchSig

class SacEndianContext where
  Endian : SimpleC.SL.CArch.CEndianSig

instance (priority := low) defaultSacArchContext : SacArchContext :=
  ⟨SimpleC.SL.CArch.Arch32⟩

instance (priority := low) defaultSacEndianContext : SacEndianContext :=
  ⟨SimpleC.SL.CArch.BigEndian⟩

namespace SacContext

abbrev rules [ctx : SacContext] : SeparationLogicSig := ctx.CRules
abbrev arch [ctx : SacArchContext] : SimpleC.SL.CArch.CArchSig := ctx.Arch
abbrev endian [ctx : SacEndianContext] : SimpleC.SL.CArch.CEndianSig := ctx.Endian
abbrev Assertion [SacContext] : Type := rules.expr

abbrev exp [SacContext] {A : Type u} (P : A -> Assertion) : Assertion :=
  Unifysl.LogicGenerator.demo932.DerivedNamesSig.exp rules.DerivedNames A P

abbrev allp [SacContext] {A : Type u} (P : A -> Assertion) : Assertion :=
  Unifysl.LogicGenerator.demo932.DerivedNamesSig.allp rules.DerivedNames A P

end SacContext

instance (priority := high) sacCNotationContext [ctx : SacArchContext] :
    SimpleC.SL.CNotation.CNotationContext :=
  ⟨ctx.Arch⟩

namespace DerivedPredSig

open SacContext

variable (CRules : SeparationLogicSig)

inductive all_list : Type 1 where
  | norm_asrt : CRules.expr -> all_list
  | dependent_asrt : forall A : Type, (A -> CRules.expr) -> all_list

theorem sepcon_emp_logic_equiv' (P : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon CRules.emp P) P := by
  exact CRules.toContext.logic_equiv_trans
    (CRules.sepcon CRules.emp P) (CRules.sepcon P CRules.emp) P
    (CRules.toContext.logic_equiv_sepcon_comm CRules.emp P)
    (CRules.toContext.logic_equiv_sepcon_emp P)

theorem elim_wand_emp_emp :
    CRules.logic_equiv CRules.emp (CRules.wand CRules.emp CRules.emp) := by
  constructor
  · exact (CRules.toContext.derivable1s_wand_sepcon_adjoint
      CRules.emp CRules.emp CRules.emp).mp
      (CRules.toContext.derivable1_sepcon_emp_l CRules.emp)
  · exact CRules.toContext.derivable1_trans
      (CRules.wand CRules.emp CRules.emp)
      (CRules.sepcon (CRules.wand CRules.emp CRules.emp) CRules.emp)
      CRules.emp
      (CRules.toContext.derivable1_sepcon_emp_r
        (CRules.wand CRules.emp CRules.emp))
      (CRules.toContext.derivable1_wand_elim1 CRules.emp CRules.emp)

theorem dump_spatial_left (P : CRules.expr) (Q : Prop) (hQ : Q) :
    CRules.derivable1 P (CRules.coq_prop Q) := by
  intro _ _
  exact hQ

theorem split_pure_and_spatial_goals
    (P pure spatial : CRules.expr)
    (hSpatial : CRules.derivable1 P spatial)
    (hPure : CRules.derivable1 P pure) :
    CRules.derivable1 P (CRules.andp pure spatial) := by
  intro state hP
  exact ⟨hPure state hP, hSpatial state hP⟩

theorem split_spatial_and_pure_goals
    (P spatial pure : CRules.expr)
    (hSpatial : CRules.derivable1 P spatial)
    (hPure : CRules.derivable1 P pure) :
    CRules.derivable1 P (CRules.andp spatial pure) := by
  intro state hP
  exact ⟨hSpatial state hP, hPure state hP⟩

theorem _derivable1_andp_intros (P A B : CRules.expr)
    (hA : CRules.derivable1 P A) (hB : CRules.derivable1 P B) :
    CRules.derivable1 P (CRules.andp A B) := by
  intro state hP
  exact ⟨hA state hP, hB state hP⟩

theorem add_pure_split (P : Prop) (C F : CRules.expr)
    (hPure : CRules.derivable1 C (CRules.coq_prop P))
    (hRest : CRules.derivable1 (CRules.andp (CRules.coq_prop P) C) F) :
    CRules.derivable1 C F := by
  intro state hC
  exact hRest state ⟨hPure state hC, hC⟩

theorem sepcon_cancel_lhs_emp (P Q : CRules.expr)
    (hQ : CRules.derivable1 Q CRules.emp) :
    CRules.derivable1 (CRules.sepcon P Q) P := by
  exact CRules.toContext.derivable1_trans
    (CRules.sepcon P Q) (CRules.sepcon P CRules.emp) P
    (CRules.toContext.derivable1_sepcon_mono P P Q CRules.emp
      (CRules.toContext.derivable1_refl P) hQ)
    (CRules.toContext.derivable1_sepcon_emp_l P)

namespace AutomationHelpers

theorem fold_addr_max_unsigned (Arch : SimpleC.SL.CArch.CArchSig) :
    Arch.addr_max_unsigned = DerivedPredSig.addr_max_unsigned Arch := rfl

theorem fold_ptr_size (Arch : SimpleC.SL.CArch.CArchSig) :
    Arch.ptr_size = DerivedPredSig.ptr_size Arch := rfl

theorem fold_ptr_align (Arch : SimpleC.SL.CArch.CArchSig) :
    Arch.ptr_align = DerivedPredSig.ptr_align Arch := rfl

theorem fold_ptr_size_Z (Arch : SimpleC.SL.CArch.CArchSig) :
    Arch.ptr_size_Z = DerivedPredSig.ptr_size_Z Arch := rfl

theorem fold_ptr_width_Z (Arch : SimpleC.SL.CArch.CArchSig) :
    Arch.ptr_width_Z = DerivedPredSig.ptr_width_Z Arch := rfl

theorem fold_aligned (Arch : SimpleC.SL.CArch.CArchSig) (align p : Int) :
    Arch.aligned align p = DerivedPredSig.aligned Arch align p := rfl

open SimpleC.SL.CNotation

theorem zabs_of_nonneg (x : Int) (h : 0 <= x) :
    Z.abs x = x :=
  Int.natAbs_of_nonneg h

theorem zabs_of_neg (x : Int) (h : x < 0) :
    Z.abs x = -x := by
  cases x with
  | ofNat n =>
      exact False.elim ((Int.not_lt_of_ge (Int.natCast_nonneg n)) h)
  | negSucc n => rfl

theorem self_eq_zabs_iff (x : Int) : x = Z.abs x ↔ 0 <= x := by
  constructor
  · intro h
    exact (Z.abs_eq_iff x).1 h.symm
  · intro h
    exact ((Z.abs_eq_iff x).2 h).symm

theorem neg_eq_zabs_iff (x : Int) : -x = Z.abs x ↔ x <= 0 := by
  constructor
  · intro h
    have hz : 0 <= Z.abs x := Z.abs_nonneg x
    omega
  · intro hx
    cases x with
    | ofNat n =>
        have hz : Int.ofNat n = 0 :=
          Int.le_antisymm hx (Int.ofNat_zero_le n)
        have hn : n = 0 := Int.ofNat_inj.mp (by simpa using hz)
        subst n
        rfl
    | negSucc n => rfl

theorem sub_rev_eq_zabs_sub_iff (x y : Int) :
    y - x = Z.abs (x - y) ↔ x <= y := by
  rw [show y - x = -(x - y) by omega, neg_eq_zabs_iff]
  omega

theorem upper_of_abs_le {x bound : Int} (habs : Z.abs x <= bound) :
    x <= bound := by
  exact (Z.abs_le_iff x bound).1 habs |>.2

theorem lower_of_abs_le {x lower bound : Int} (habs : Z.abs x <= bound)
    (hlower : lower <= -bound) :
    lower <= x := by
  have hx := (Z.abs_le_iff x bound).1 habs |>.1
  omega

theorem upper_of_abs_lt_abs {x y upper : Int}
    (habs : Z.abs x < Z.abs y) (hyUpper : y <= upper)
    (hyLower : -upper <= y) :
    x <= upper := by
  have hyAbs : Z.abs y <= upper :=
    (Z.abs_le_iff y upper).2 ⟨hyLower, hyUpper⟩
  have hxUpper : x <= Z.abs x :=
    (Z.abs_le_iff x (Z.abs x)).1 (Int.le_refl _) |>.2
  omega

theorem lower_of_abs_lt_abs {x y lower upper : Int}
    (habs : Z.abs x < Z.abs y) (hyUpper : y <= upper)
    (hyLower : -upper <= y) (hlower : lower < -upper) :
    lower < x := by
  have hyAbs : Z.abs y <= upper :=
    (Z.abs_le_iff y upper).2 ⟨hyLower, hyUpper⟩
  have hxLower : -Z.abs x <= x :=
    (Z.abs_le_iff x (Z.abs x)).1 (Int.le_refl _) |>.1
  omega

theorem int32_upper_of_abs_lt_abs {x y : Int}
    (habs : Z.abs x < Z.abs y) (hyUpper : y <= SimpleC.SL.IntLib.INT_MAX)
    (hyLower : SimpleC.SL.IntLib.INT_MIN < y) :
    x <= SimpleC.SL.IntLib.INT_MAX := by
  apply upper_of_abs_lt_abs habs hyUpper
  simp only [SimpleC.SL.IntLib.INT_MIN, SimpleC.SL.IntLib.INT_MAX] at *
  omega

theorem int32_lower_of_abs_lt_abs {x y : Int}
    (habs : Z.abs x < Z.abs y) (hyUpper : y <= SimpleC.SL.IntLib.INT_MAX)
    (hyLower : SimpleC.SL.IntLib.INT_MIN < y) :
    SimpleC.SL.IntLib.INT_MIN < x := by
  apply lower_of_abs_lt_abs habs hyUpper
  · simp only [SimpleC.SL.IntLib.INT_MIN, SimpleC.SL.IntLib.INT_MAX] at *
    omega
  · simp only [SimpleC.SL.IntLib.INT_MIN, SimpleC.SL.IntLib.INT_MAX]
    omega

variable (Arch : SimpleC.SL.CArch.CArchSig)
  (Endian : SimpleC.SL.CArch.CEndianSig)

theorem poly_store_unfold_int :
    poly_store Arch Endian CRules FET_int = store_int Arch Endian CRules := rfl

theorem poly_store_unfold_char :
    poly_store Arch Endian CRules FET_char = store_char Arch CRules := rfl

theorem poly_store_unfold_int64 :
    poly_store Arch Endian CRules FET_int64 = store_int64 Arch Endian CRules := rfl

theorem poly_store_unfold_short :
    poly_store Arch Endian CRules FET_short = store_short Arch Endian CRules := rfl

theorem poly_store_unfold_uint :
    poly_store Arch Endian CRules FET_uint = store_uint Arch Endian CRules := rfl

theorem poly_store_unfold_uchar :
    poly_store Arch Endian CRules FET_uchar = store_uchar Arch CRules := rfl

theorem poly_store_unfold_uint64 :
    poly_store Arch Endian CRules FET_uint64 = store_uint64 Arch Endian CRules := rfl

theorem poly_store_unfold_int128 :
    poly_store Arch Endian CRules FET_int128 = store_int128 Arch Endian CRules := rfl

theorem poly_store_unfold_uint128 :
    poly_store Arch Endian CRules FET_uint128 = store_uint128 Arch Endian CRules := rfl

theorem poly_store_unfold_ushort :
    poly_store Arch Endian CRules FET_ushort = store_ushort Arch Endian CRules := rfl

theorem poly_store_unfold_ptr :
    poly_store Arch Endian CRules FET_ptr = store_ptr Arch Endian CRules := rfl

theorem poly_store_unfold_float :
    poly_store Arch Endian CRules FET_float =
      fun x z => store_float Arch Endian CRules x (SimpleC.SL.FloatLib.fp32_of_bits z) := rfl

theorem poly_store_unfold_double :
    poly_store Arch Endian CRules FET_double =
      fun x z => store_double Arch Endian CRules x (SimpleC.SL.FloatLib.fp64_of_bits z) := rfl

theorem poly_store_unfold_long_double :
    poly_store Arch Endian CRules FET_long_double =
      fun x z => store_long_double Arch Endian CRules x (SimpleC.SL.FloatLib.fp128_of_bits z) := rfl

theorem typed_poly_store_unfold_int :
    typed_poly_store Arch Endian CRules FET_int = store_int Arch Endian CRules := rfl

theorem typed_poly_store_unfold_char :
    typed_poly_store Arch Endian CRules FET_char = store_char Arch CRules := rfl

theorem typed_poly_store_unfold_int64 :
    typed_poly_store Arch Endian CRules FET_int64 = store_int64 Arch Endian CRules := rfl

theorem typed_poly_store_unfold_short :
    typed_poly_store Arch Endian CRules FET_short = store_short Arch Endian CRules := rfl

theorem typed_poly_store_unfold_uint :
    typed_poly_store Arch Endian CRules FET_uint = store_uint Arch Endian CRules := rfl

theorem typed_poly_store_unfold_uchar :
    typed_poly_store Arch Endian CRules FET_uchar = store_uchar Arch CRules := rfl

theorem typed_poly_store_unfold_uint64 :
    typed_poly_store Arch Endian CRules FET_uint64 = store_uint64 Arch Endian CRules := rfl

theorem typed_poly_store_unfold_int128 :
    typed_poly_store Arch Endian CRules FET_int128 = store_int128 Arch Endian CRules := rfl

theorem typed_poly_store_unfold_uint128 :
    typed_poly_store Arch Endian CRules FET_uint128 = store_uint128 Arch Endian CRules := rfl

theorem typed_poly_store_unfold_ushort :
    typed_poly_store Arch Endian CRules FET_ushort = store_ushort Arch Endian CRules := rfl

theorem typed_poly_store_unfold_float :
    typed_poly_store Arch Endian CRules FET_float = store_float Arch Endian CRules := rfl

theorem typed_poly_store_unfold_double :
    typed_poly_store Arch Endian CRules FET_double = store_double Arch Endian CRules := rfl

theorem typed_poly_store_unfold_long_double :
    typed_poly_store Arch Endian CRules FET_long_double = store_long_double Arch Endian CRules := rfl

theorem typed_poly_store_unfold_ptr :
    typed_poly_store Arch Endian CRules FET_ptr = store_ptr Arch Endian CRules := rfl

theorem poly_undef_store_unfold_int :
    poly_undef_store Arch CRules FET_int = undef_store_int Arch CRules := rfl

theorem poly_undef_store_unfold_char :
    poly_undef_store Arch CRules FET_char = undef_store_char Arch CRules := rfl

theorem poly_undef_store_unfold_int64 :
    poly_undef_store Arch CRules FET_int64 = undef_store_int64 Arch CRules := rfl

theorem poly_undef_store_unfold_short :
    poly_undef_store Arch CRules FET_short = undef_store_short Arch CRules := rfl

theorem poly_undef_store_unfold_uint :
    poly_undef_store Arch CRules FET_uint = undef_store_uint Arch CRules := rfl

theorem poly_undef_store_unfold_uchar :
    poly_undef_store Arch CRules FET_uchar = undef_store_uchar Arch CRules := rfl

theorem poly_undef_store_unfold_uint64 :
    poly_undef_store Arch CRules FET_uint64 = undef_store_uint64 Arch CRules := rfl

theorem poly_undef_store_unfold_int128 :
    poly_undef_store Arch CRules FET_int128 = undef_store_int128 Arch CRules := rfl

theorem poly_undef_store_unfold_uint128 :
    poly_undef_store Arch CRules FET_uint128 = undef_store_uint128 Arch CRules := rfl

theorem poly_undef_store_unfold_ushort :
    poly_undef_store Arch CRules FET_ushort = undef_store_ushort Arch CRules := rfl

theorem poly_undef_store_unfold_ptr :
    poly_undef_store Arch CRules FET_ptr = undef_store_ptr Arch CRules := rfl

theorem poly_undef_store_unfold_float :
    poly_undef_store Arch CRules FET_float = undef_store_float Arch CRules := rfl

theorem poly_undef_store_unfold_double :
    poly_undef_store Arch CRules FET_double = undef_store_double Arch CRules := rfl

theorem poly_undef_store_unfold_long_double :
    poly_undef_store Arch CRules FET_long_double = undef_store_long_double Arch CRules := rfl

theorem coq_prop_andp_right_equiv (P : CRules.expr) (Q : Prop) :
    CRules.logic_equiv (CRules.andp P (CRules.coq_prop Q))
      (CRules.andp (CRules.coq_prop Q) P) :=
  CRules.toContext.logic_equiv_andp_comm P (CRules.coq_prop Q)

theorem coq_prop_sepcon_left_equiv (P : Prop) (Q : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon (CRules.coq_prop P) Q)
      (CRules.sepcon Q (CRules.coq_prop P)) :=
  CRules.toContext.logic_equiv_sepcon_comm (CRules.coq_prop P) Q

theorem spatial_andp_right_equiv (P Q R : CRules.expr) :
    CRules.logic_equiv (CRules.andp (CRules.sepcon P Q) R)
      (CRules.andp R (CRules.sepcon P Q)) :=
  CRules.toContext.logic_equiv_andp_comm (CRules.sepcon P Q) R

theorem exp_andp_right_equiv {A : Type}
    (P : CRules.expr) (Q : A -> CRules.expr) :
    CRules.logic_equiv (CRules.andp P (CRules.exp A Q))
      (CRules.andp (CRules.exp A Q) P) :=
  CRules.toContext.logic_equiv_andp_comm P (CRules.exp A Q)

theorem exp_sepcon_right_equiv {A : Type}
    (P : CRules.expr) (Q : A -> CRules.expr) :
    CRules.logic_equiv (CRules.sepcon P (CRules.exp A Q))
      (CRules.sepcon (CRules.exp A Q) P) :=
  CRules.toContext.logic_equiv_sepcon_comm P (CRules.exp A Q)

end AutomationHelpers

namespace Automation

universe v

theorem exp_left_rule {CRules : SeparationLogicSig} {A : Type v}
    {P : A -> CRules.expr} {Q : CRules.expr}
    (h : forall x, CRules.derivable1 (P x) Q) :
    CRules.derivable1
      (Unifysl.LogicGenerator.demo932.DerivedNamesSig.exp
        CRules.DerivedNames A P) Q := by
  intro state hP
  rcases hP with ⟨x, hx⟩
  exact h x state hx

theorem allp_right_rule {CRules : SeparationLogicSig} {A : Type v}
    {P : CRules.expr} {Q : A -> CRules.expr}
    (h : forall x, CRules.derivable1 P (Q x)) :
    CRules.derivable1 P
      (Unifysl.LogicGenerator.demo932.DerivedNamesSig.allp
        CRules.DerivedNames A Q) := by
  intro state hP x
  exact h x state hP

theorem exp_right_rule {CRules : SeparationLogicSig} {A : Type v}
    {P : CRules.expr} {Q : A -> CRules.expr} (x : A)
    (h : CRules.derivable1 P (Q x)) :
    CRules.derivable1 P
      (Unifysl.LogicGenerator.demo932.DerivedNamesSig.exp
        CRules.DerivedNames A Q) := by
  intro state hP
  exact ⟨x, h state hP⟩

theorem allp_left_rule {CRules : SeparationLogicSig} {A : Type v}
    {P : A -> CRules.expr} {Q : CRules.expr} (x : A)
    (h : CRules.derivable1 (P x) Q) :
    CRules.derivable1
      (Unifysl.LogicGenerator.demo932.DerivedNamesSig.allp
        CRules.DerivedNames A P) Q := by
  intro state hP
  exact h state (hP x)

theorem logic_equiv_exp_rule {CRules : SeparationLogicSig} {A : Type v}
    (P Q : A → CRules.expr) (h : ∀ x, CRules.logic_equiv (P x) (Q x)) :
    CRules.logic_equiv
      (Unifysl.LogicGenerator.demo932.DerivedNamesSig.exp
        CRules.DerivedNames A P)
      (Unifysl.LogicGenerator.demo932.DerivedNamesSig.exp
        CRules.DerivedNames A Q) := by
  constructor
  · apply exp_left_rule
    intro x
    exact exp_right_rule x (h x).left
  · apply exp_left_rule
    intro x
    exact exp_right_rule x (h x).right

theorem logic_equiv_allp_rule {CRules : SeparationLogicSig} {A : Type v}
    (P Q : A → CRules.expr) (h : ∀ x, CRules.logic_equiv (P x) (Q x)) :
    CRules.logic_equiv
      (Unifysl.LogicGenerator.demo932.DerivedNamesSig.allp
        CRules.DerivedNames A P)
      (Unifysl.LogicGenerator.demo932.DerivedNamesSig.allp
        CRules.DerivedNames A Q) := by
  constructor
  · apply allp_right_rule
    intro x
    exact allp_left_rule x (h x).left
  · apply allp_right_rule
    intro x
    exact allp_left_rule x (h x).right

theorem logic_equiv_orp_mono_rule (CRules : SeparationLogicSig)
    (P P' Q Q' : CRules.expr) (hP : CRules.logic_equiv P P')
    (hQ : CRules.logic_equiv Q Q') :
    CRules.logic_equiv (CRules.orp P Q) (CRules.orp P' Q') :=
  CRules.toContext.logic_equiv_orp_congr P P' Q Q' hP hQ

theorem logic_equiv_wand_mono_rule (CRules : SeparationLogicSig)
    (P P' Q Q' : CRules.expr) (hP : CRules.logic_equiv P P')
    (hQ : CRules.logic_equiv Q Q') :
    CRules.logic_equiv (CRules.wand P Q) (CRules.wand P' Q') :=
  wand_equiv CRules P Q P' Q' hP hQ

theorem logic_equiv_impp_mono_rule (CRules : SeparationLogicSig)
    (P P' Q Q' : CRules.expr) (hP : CRules.logic_equiv P P')
    (hQ : CRules.logic_equiv Q Q') :
    CRules.logic_equiv (CRules.impp P Q) (CRules.impp P' Q') := by
  constructor
  · intro state hImp hP'
    exact hQ.left state (hImp (hP.right state hP'))
  · intro state hImp hp
    exact hQ.right state (hImp (hP.left state hp))

theorem logic_equiv_iffp_mono_rule (CRules : SeparationLogicSig)
    (P P' Q Q' : CRules.expr) (hP : CRules.logic_equiv P P')
    (hQ : CRules.logic_equiv Q Q') :
    CRules.logic_equiv (CRules.toContext.iffp P Q)
      (CRules.toContext.iffp P' Q') := by
  change CRules.logic_equiv
    (CRules.andp (CRules.impp P Q) (CRules.impp Q P))
    (CRules.andp (CRules.impp P' Q') (CRules.impp Q' P'))
  let hForward := logic_equiv_impp_mono_rule CRules P P' Q Q' hP hQ
  let hBackward := logic_equiv_impp_mono_rule CRules Q Q' P P' hQ hP
  constructor
  · intro state h
    exact ⟨hForward.left state h.left, hBackward.left state h.right⟩
  · intro state h
    exact ⟨hForward.right state h.left, hBackward.right state h.right⟩

theorem apply_sepcon_adjoint_rule {CRules : SeparationLogicSig}
    {P Q R : CRules.expr}
    (h : CRules.derivable1 (CRules.sepcon P Q) R) :
    CRules.derivable1 P (CRules.wand Q R) :=
  (CRules.toContext.derivable1s_wand_sepcon_adjoint P Q R).mp h

theorem andp_left_rule {CRules : SeparationLogicSig} {P Q R : CRules.expr}
    (h : CRules.derivable1 P R) :
    CRules.derivable1 (CRules.andp P Q) R := by
  intro state hPQ
  exact h state hPQ.left

theorem andp_right_rule {CRules : SeparationLogicSig} {P Q R : CRules.expr}
    (h : CRules.derivable1 Q R) :
    CRules.derivable1 (CRules.andp P Q) R := by
  intro state hPQ
  exact h state hPQ.right

theorem orp_intros_left {CRules : SeparationLogicSig} {P Q R : CRules.expr}
    (h : CRules.derivable1 P Q) :
    CRules.derivable1 P (CRules.orp Q R) := by
  intro state hP
  exact Or.inl (h state hP)

theorem orp_intros_right {CRules : SeparationLogicSig} {P Q R : CRules.expr}
    (h : CRules.derivable1 P R) :
    CRules.derivable1 P (CRules.orp Q R) := by
  intro state hP
  exact Or.inr (h state hP)

theorem orp_elim {CRules : SeparationLogicSig} {P Q R : CRules.expr}
    (hP : CRules.derivable1 P R) (hQ : CRules.derivable1 Q R) :
    CRules.derivable1 (CRules.orp P Q) R := by
  intro state h
  rcases h with h | h
  · exact hP state h
  · exact hQ state h

theorem derivable_refl {CRules : SeparationLogicSig} {P : CRules.expr} :
    CRules.derivable1 P P := by
  intro _ hP
  exact hP

theorem logic_equiv_refl_rule (CRules : SeparationLogicSig) (P : CRules.expr) :
    CRules.logic_equiv P P :=
  CRules.toContext.logic_equiv_refl P

theorem logic_equiv_symm_rule (CRules : SeparationLogicSig) (P Q : CRules.expr)
    (h : CRules.logic_equiv P Q) : CRules.logic_equiv Q P :=
  CRules.toContext.logic_equiv_symm P Q h

theorem logic_equiv_trans_rule (CRules : SeparationLogicSig)
    (P Q R : CRules.expr) (hPQ : CRules.logic_equiv P Q)
    (hQR : CRules.logic_equiv Q R) : CRules.logic_equiv P R :=
  CRules.toContext.logic_equiv_trans P Q R hPQ hQR

theorem logic_equiv_sepcon_mono_rule (CRules : SeparationLogicSig)
    (P P' Q Q' : CRules.expr) (hP : CRules.logic_equiv P P')
    (hQ : CRules.logic_equiv Q Q') :
    CRules.logic_equiv (CRules.sepcon P Q) (CRules.sepcon P' Q') :=
  CRules.toContext.logic_equiv_sepcon_proper.proper P P' hP Q Q' hQ

theorem logic_equiv_andp_mono_rule (CRules : SeparationLogicSig)
    (P P' Q Q' : CRules.expr) (hP : CRules.logic_equiv P P')
    (hQ : CRules.logic_equiv Q Q') :
    CRules.logic_equiv (CRules.andp P Q) (CRules.andp P' Q') :=
  CRules.toContext.logic_equiv_andp_congr P P' Q Q' hP hQ

theorem logic_equiv_andp_assoc_rule (CRules : SeparationLogicSig)
    (P Q R : CRules.expr) :
    CRules.logic_equiv (CRules.andp (CRules.andp P Q) R)
      (CRules.andp P (CRules.andp Q R)) :=
  CRules.toContext.logic_equiv_andp_assoc P Q R

theorem derivable_andp_mono_rule (CRules : SeparationLogicSig)
    (P P' Q Q' : CRules.expr) (hP : CRules.derivable1 P P')
    (hQ : CRules.derivable1 Q Q') :
    CRules.derivable1 (CRules.andp P Q) (CRules.andp P' Q') :=
  CRules.toContext.derivable1s_andp_mono P P' Q Q' hP hQ

theorem logic_equiv_coq_prop_and_rule (CRules : SeparationLogicSig)
    (P Q : Prop) :
    CRules.logic_equiv (CRules.coq_prop (P /\ Q))
      (CRules.andp (CRules.coq_prop P) (CRules.coq_prop Q)) :=
  CRules.toContext.logic_equiv_coq_prop_and P Q

theorem logic_equiv_coq_prop_or_rule (CRules : SeparationLogicSig)
    (P Q : Prop) :
    CRules.logic_equiv (CRules.coq_prop (P \/ Q))
      (CRules.orp (CRules.coq_prop P) (CRules.coq_prop Q)) :=
  CRules.toContext.logic_equiv_coq_prop_or P Q

theorem logic_equiv_sepcon_comm_rule (CRules : SeparationLogicSig)
    (P Q : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon P Q) (CRules.sepcon Q P) :=
  CRules.toContext.logic_equiv_sepcon_comm P Q

theorem logic_equiv_sepcon_assoc_rule (CRules : SeparationLogicSig)
    (P Q R : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon P (CRules.sepcon Q R))
      (CRules.sepcon (CRules.sepcon P Q) R) :=
  CRules.toContext.logic_equiv_sepcon_assoc P Q R

theorem logic_equiv_sepcon_swap_rule (CRules : SeparationLogicSig)
    (P Q R : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon P (CRules.sepcon Q R))
      (CRules.sepcon Q (CRules.sepcon P R)) :=
  CRules.toContext.logic_equiv_sepcon_swap P Q R

theorem logic_equiv_coq_prop_andp_sepcon_rule (CRules : SeparationLogicSig)
    (P : Prop) (Q R : CRules.expr) :
    CRules.logic_equiv
      (CRules.sepcon (CRules.andp (CRules.coq_prop P) Q) R)
      (CRules.andp (CRules.coq_prop P) (CRules.sepcon Q R)) :=
  CRules.toContext.logic_equiv_coq_prop_andp_sepcon P Q R

theorem logic_equiv_sepcon_coq_prop_andp_rule (CRules : SeparationLogicSig)
    (P : CRules.expr) (Q : Prop) (R : CRules.expr) :
    CRules.logic_equiv
      (CRules.sepcon P (CRules.andp (CRules.coq_prop Q) R))
      (CRules.sepcon (CRules.andp (CRules.coq_prop Q) P) R) :=
  CRules.toContext.logic_equiv_sepcon_coq_prop_andp P Q R

theorem logic_equiv_coq_prop_sepcon_rule (CRules : SeparationLogicSig)
    (P : Prop) (Q : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon (CRules.coq_prop P) Q)
      (CRules.sepcon Q (CRules.coq_prop P)) :=
  CRules.toContext.logic_equiv_sepcon_comm (CRules.coq_prop P) Q

theorem logic_equiv_andp_comm_rule (CRules : SeparationLogicSig)
    (P Q : CRules.expr) :
    CRules.logic_equiv (CRules.andp P Q) (CRules.andp Q P) :=
  CRules.toContext.logic_equiv_andp_comm P Q

theorem logic_equiv_forward_rule (CRules : SeparationLogicSig)
    (P Q : CRules.expr) (h : CRules.logic_equiv P Q) :
    CRules.derivable1 P Q :=
  h.left

theorem logic_equiv_backward_rule (CRules : SeparationLogicSig)
    (P Q : CRules.expr) (h : CRules.logic_equiv P Q) :
    CRules.derivable1 Q P :=
  h.right

theorem derivable_trans_rule (CRules : SeparationLogicSig) (P Q R : CRules.expr)
    (hPQ : CRules.derivable1 P Q) (hQR : CRules.derivable1 Q R) :
    CRules.derivable1 P R :=
  CRules.toContext.derivable1_trans P Q R hPQ hQR

theorem derivable_refl_rule (CRules : SeparationLogicSig) (P : CRules.expr) :
    CRules.derivable1 P P :=
  CRules.toContext.derivable1_refl P

theorem derivable_sepcon_mono_rule (CRules : SeparationLogicSig)
    (P P' Q Q' : CRules.expr) (hP : CRules.derivable1 P P')
    (hQ : CRules.derivable1 Q Q') :
    CRules.derivable1 (CRules.sepcon P Q) (CRules.sepcon P' Q') :=
  CRules.toContext.derivable1_sepcon_mono P P' Q Q' hP hQ

end Automation

end DerivedPredSig
end SimpleC.SL.CommonAssertion

namespace SimpleC.SL.SAC

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CNotation

scoped notation "emp" => SacContext.rules.emp
scoped infix:20 " |-- " => SacContext.rules.derivable1
scoped infix:20 " ⊣⊢ " => SacContext.rules.logic_equiv
scoped infixr:55 " -* " => SacContext.rules.wand
scoped infixr:40 " ⟶ₗ " => SacContext.rules.impp
scoped infixr:35 " || " => SacContext.rules.orp
scoped infixr:40 " && " => SacContext.rules.andp
scoped infixl:50 " ** " => SacContext.rules.sepcon
scoped notation:100 "“" P "”" => SacContext.rules.coq_prop P
scoped notation "TT" => SacContext.rules.truep

scoped syntax:45 "EX " ident ":" term:50 "," term:0 : term
scoped syntax:45 "EX " ident "," term:0 : term
scoped macro_rules
  | `(EX $x:ident : $type:term, $body:term) =>
      `(SacContext.exp (A := $type) (fun $x : $type => $body))
  | `(EX $x:ident, $body:term) =>
      `(SacContext.exp (fun $x => $body))

scoped syntax:45 "ALL " ident ":" term:50 "," term:0 : term
scoped syntax:45 "ALL " ident "," term:0 : term
scoped macro_rules
  | `(ALL $x:ident : $type:term, $body:term) =>
      `(SacContext.allp (A := $type) (fun $x : $type => $body))
  | `(ALL $x:ident, $body:term) =>
      `(SacContext.allp (fun $x => $body))

scoped notation "Assertion" => SacContext.Assertion

scoped notation:60 x:61 " # " "CHAR" " |-> " value:60 =>
  store_char SacContext.arch SacContext.rules x value
scoped notation:60 x:61 " # " "UCHAR" " |-> " value:60 =>
  store_uchar SacContext.arch SacContext.rules x value
scoped notation:60 x:61 " # " "SHORT" " |-> " value:60 =>
  store_short SacContext.arch SacContext.endian SacContext.rules x value
scoped notation:60 x:61 " # " "USHORT" " |-> " value:60 =>
  store_ushort SacContext.arch SacContext.endian SacContext.rules x value
scoped notation:60 x:61 " # " "INT" " |-> " value:60 =>
  store_int SacContext.arch SacContext.endian SacContext.rules x value
scoped notation:60 x:61 " # " "UINT" " |-> " value:60 =>
  store_uint SacContext.arch SacContext.endian SacContext.rules x value
scoped notation:60 x:61 " # " "INT64" " |-> " value:60 =>
  store_int64 SacContext.arch SacContext.endian SacContext.rules x value
scoped notation:60 x:61 " # " "UINT64" " |-> " value:60 =>
  store_uint64 SacContext.arch SacContext.endian SacContext.rules x value
scoped notation:60 x:61 " # " "INT128" " |-> " value:60 =>
  store_int128 SacContext.arch SacContext.endian SacContext.rules x value
scoped notation:60 x:61 " # " "UINT128" " |-> " value:60 =>
  store_uint128 SacContext.arch SacContext.endian SacContext.rules x value
scoped notation:60 x:61 " # " "PTR" " |-> " value:60 =>
  store_ptr SacContext.arch SacContext.endian SacContext.rules x value

scoped syntax:60 (name := rocqDataAt) (priority := high)
  term:61 " # " ident " |-> " term:60 : term
scoped macro_rules (kind := rocqDataAt)
  | `($x:term # Char |-> $value:term) =>
      `(store_char SacContext.arch SacContext.rules $x $value)
  | `($x:term # UChar |-> $value:term) =>
      `(store_uchar SacContext.arch SacContext.rules $x $value)
  | `($x:term # Short |-> $value:term) =>
      `(store_short SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # UShort |-> $value:term) =>
      `(store_ushort SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # Int |-> $value:term) =>
      `(store_int SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # UInt |-> $value:term) =>
      `(store_uint SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # Int64 |-> $value:term) =>
      `(store_int64 SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # UInt64 |-> $value:term) =>
      `(store_uint64 SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # Int128 |-> $value:term) =>
      `(store_int128 SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # UInt128 |-> $value:term) =>
      `(store_uint128 SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # Float |-> $value:term) =>
      `(store_float SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # Double |-> $value:term) =>
      `(store_double SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # LongDouble |-> $value:term) =>
      `(store_long_double SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # FiniteFloat |-> $value:term) =>
      `(store_finite_float SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # FiniteDouble |-> $value:term) =>
      `(store_finite_double SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # FiniteLongDouble |-> $value:term) =>
      `(store_finite_long_double SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # Ptr |-> $value:term) =>
      `(store_ptr SacContext.arch SacContext.endian SacContext.rules $x $value)
  | `($x:term # $type:ident |-> $value:term) => do
      match type.getId with
      | `Float => `(store_float SacContext.arch SacContext.endian SacContext.rules $x $value)
      | `Double => `(store_double SacContext.arch SacContext.endian SacContext.rules $x $value)
      | `LongDouble => `(store_long_double SacContext.arch SacContext.endian SacContext.rules $x $value)
      | `FiniteFloat => `(store_finite_float SacContext.arch SacContext.endian SacContext.rules $x $value)
      | `FiniteDouble => `(store_finite_double SacContext.arch SacContext.endian SacContext.rules $x $value)
      | `FiniteLongDouble => `(store_finite_long_double SacContext.arch SacContext.endian SacContext.rules $x $value)
      | _ => `(poly_store SacContext.arch SacContext.endian SacContext.rules $type $x $value)

scoped notation:60 x:61 " # " "CHAR" " |->_" => undef_store_char SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "UCHAR" " |->_" => undef_store_uchar SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "SHORT" " |->_" => undef_store_short SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "USHORT" " |->_" => undef_store_ushort SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "INT" " |->_" => undef_store_int SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "UINT" " |->_" => undef_store_uint SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "INT64" " |->_" => undef_store_int64 SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "UINT64" " |->_" => undef_store_uint64 SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "INT128" " |->_" => undef_store_int128 SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "UINT128" " |->_" => undef_store_uint128 SacContext.arch SacContext.rules x
scoped notation:60 x:61 " # " "PTR" " |->_" => undef_store_ptr SacContext.arch SacContext.rules x

scoped syntax:60 (name := rocqUndefDataAt) (priority := high)
  term:61 " # " ident " |->_" : term
scoped macro_rules (kind := rocqUndefDataAt)
  | `($x:term # Char |->_) => `(undef_store_char SacContext.arch SacContext.rules $x)
  | `($x:term # UChar |->_) => `(undef_store_uchar SacContext.arch SacContext.rules $x)
  | `($x:term # Short |->_) => `(undef_store_short SacContext.arch SacContext.rules $x)
  | `($x:term # UShort |->_) => `(undef_store_ushort SacContext.arch SacContext.rules $x)
  | `($x:term # Int |->_) => `(undef_store_int SacContext.arch SacContext.rules $x)
  | `($x:term # UInt |->_) => `(undef_store_uint SacContext.arch SacContext.rules $x)
  | `($x:term # Int64 |->_) => `(undef_store_int64 SacContext.arch SacContext.rules $x)
  | `($x:term # UInt64 |->_) => `(undef_store_uint64 SacContext.arch SacContext.rules $x)
  | `($x:term # Int128 |->_) => `(undef_store_int128 SacContext.arch SacContext.rules $x)
  | `($x:term # UInt128 |->_) => `(undef_store_uint128 SacContext.arch SacContext.rules $x)
  | `($x:term # Float |->_) => `(undef_store_float SacContext.arch SacContext.rules $x)
  | `($x:term # Double |->_) => `(undef_store_double SacContext.arch SacContext.rules $x)
  | `($x:term # LongDouble |->_) => `(undef_store_long_double SacContext.arch SacContext.rules $x)
  | `($x:term # FiniteFloat |->_) => `(undef_store_finite_float SacContext.arch SacContext.rules $x)
  | `($x:term # FiniteDouble |->_) => `(undef_store_finite_double SacContext.arch SacContext.rules $x)
  | `($x:term # FiniteLongDouble |->_) =>
      `(undef_store_finite_long_double SacContext.arch SacContext.rules $x)
  | `($x:term # Ptr |->_) => `(undef_store_ptr SacContext.arch SacContext.rules $x)
  | `($x:term # $type:ident |->_) => do
      match type.getId with
      | `Float => `(undef_store_float SacContext.arch SacContext.rules $x)
      | `Double => `(undef_store_double SacContext.arch SacContext.rules $x)
      | `LongDouble => `(undef_store_long_double SacContext.arch SacContext.rules $x)
      | `FiniteFloat => `(undef_store_finite_float SacContext.arch SacContext.rules $x)
      | `FiniteDouble => `(undef_store_finite_double SacContext.arch SacContext.rules $x)
      | `FiniteLongDouble => `(undef_store_finite_long_double SacContext.arch SacContext.rules $x)
      | _ => `(poly_undef_store SacContext.arch SacContext.rules $type $x)

scoped notation:60 x:61 " # " type:61 " |-> " value:60 =>
  poly_store SacContext.arch SacContext.endian SacContext.rules type x value
scoped notation:60 x:61 " # " type:61 " |->_" =>
  poly_undef_store SacContext.arch SacContext.rules type x

scoped notation:25 "Padding(" x ", " name ")" =>
  struct_padding SacContext.rules x name
scoped notation:25 "Padding(" x ", " unionName ", " fieldName ")" =>
  union_padding SacContext.rules x unionName fieldName

scoped infixr:19 " +:: " => fun xs x => xs ++ [x]

end SimpleC.SL.SAC

namespace SimpleC.SL.CommonAssertion.DerivedPredSig

open Lean Elab Tactic

syntax "pureIntros_without_rename" : tactic

namespace SpatialAutomation

open Lean Meta Elab Tactic

structure Ops where
  rules : Expr
  derivable : Expr
  logicEquiv : Expr
  sepcon : Expr
  andp : Expr
  orp : Expr
  wand : Expr
  impp : Expr
  iffp : Expr
  exp : Expr
  allp : Expr
  coqProp : Expr
  emp : Expr
  truep : Expr

structure Normalized where
  atoms : List Expr
  expression : Expr
  proof : Expr

private partial def shallowUnfoldAtom (expression : Expr) : Nat → MetaM Expr
  | 0 => pure expression
  | fuel + 1 => do
      match expression.getAppFn.consumeMData with
      | .const name _ =>
          if ← Lean.isIrreducible name then
            return expression
      | _ => return expression
      let some unfolded ← unfoldDefinition? expression | return expression
      if unfolded == expression then
        return expression
      shallowUnfoldAtom unfolded fuel

private def finiteStoreAtomName? (expression : Expr) : Option Name :=
  match expression.getAppFn.consumeMData with
  | .const name _ =>
      if [``store_byte, ``store_2byte, ``store_4byte, ``store_8byte, ``store_16byte,
          ``store_byte_noninit, ``store_2byte_noninit,
          ``store_4byte_noninit, ``store_8byte_noninit,
          ``store_16byte_noninit].contains name then
        some name
      else
        none
  | _ => none

private def unfoldFiniteStoreCompat? (expression : Expr) : MetaM Expr := do
  match expression.getAppFn.consumeMData with
  | .const name _ =>
      if [``DerivedPredSigCompat.store_2byte,
          ``DerivedPredSigCompat.store_4byte,
          ``DerivedPredSigCompat.store_8byte,
          ``DerivedPredSigCompat.store_16byte].contains name then
        return (← unfoldDefinition? expression).getD expression
      return expression
  | _ => return expression

private def isDefEqFiniteStoreAtom (lhs rhs : Expr) : MetaM Bool := do
  let lhs ← unfoldFiniteStoreCompat? lhs
  let rhs ← unfoldFiniteStoreCompat? rhs
  let some lhsName := finiteStoreAtomName? lhs | return false
  let some rhsName := finiteStoreAtomName? rhs | return false
  if lhsName != rhsName then
    return false
  let lhsArgs := lhs.getAppArgs.toList
  let rhsArgs := rhs.getAppArgs.toList
  if lhsArgs.length != rhsArgs.length then
    return false
  let environmentArgCount :=
    if [``store_2byte, ``store_4byte, ``store_8byte,
        ``store_16byte].contains lhsName then 2 else 1
  for (lhsArg, rhsArg) in
      (lhsArgs.take environmentArgCount).zip (rhsArgs.take environmentArgCount) do
    let saved <- saveState
    if !(<- withTransparency .all <| isDefEq lhsArg rhsArg) then
      restoreState saved
      return false
  for (lhsArg, rhsArg) in
      (lhsArgs.drop environmentArgCount).zip (rhsArgs.drop environmentArgCount) do
    let saved <- saveState
    if !(<- withTransparency .all <| isDefEq lhsArg rhsArg) then
      restoreState saved
      return false
  return true

private partial def containsConst (target : Name) : Expr -> Bool
  | .const name _ => name == target
  | .app fn argument => containsConst target fn || containsConst target argument
  | .lam _ type body _ => containsConst target type || containsConst target body
  | .forallE _ type body _ => containsConst target type || containsConst target body
  | .letE _ type value body _ =>
      containsConst target type || containsConst target value ||
        containsConst target body
  | .mdata _ expression => containsConst target expression
  | .proj _ _ expression => containsConst target expression
  | _ => false

private def isArchitectureStoreBranch (expression : Expr) : Bool :=
  containsConst ``ptr_size expression

private def storeFacadeBaseName? (expression : Expr) : Option String :=
  match expression.getAppFn.consumeMData with
  | .const name _ =>
      let baseName :=
        match name with
        | .str _ base => base
        | _ => ""
      if #["storeA", "undefstoreA",
       "store_char", "undef_store_char",
       "store_uchar", "undef_store_uchar",
       "store_short", "undef_store_short",
       "store_ushort", "undef_store_ushort",
       "store_int", "undef_store_int",
       "store_uint", "undef_store_uint",
       "store_int64", "undef_store_int64",
       "store_uint64", "undef_store_uint64",
       "store_int128", "undef_store_int128",
       "store_uint128", "undef_store_uint128",
       "store_float", "undef_store_float",
       "store_double", "undef_store_double",
       "store_long_double", "undef_store_long_double",
       "store_finite_float", "undef_store_finite_float",
       "store_finite_double", "undef_store_finite_double",
       "store_finite_long_double", "undef_store_finite_long_double",
       "store_ptr", "undef_store_ptr"].contains baseName then
        some baseName
      else
        none
  | _ => none

private def isStoreFacadeAtom (expression : Expr) : Bool :=
  (storeFacadeBaseName? expression).isSome

private def isDynamicStoreWrapper (expression : Expr) : Bool :=
  match expression.getAppFn.consumeMData with
  | .const name _ =>
      [``store_char, ``undef_store_char,
       ``store_uchar, ``undef_store_uchar,
       ``store_short, ``undef_store_short,
       ``store_ushort, ``undef_store_ushort,
       ``store_int, ``undef_store_int,
       ``store_uint, ``undef_store_uint,
       ``store_int64, ``undef_store_int64,
       ``store_uint64, ``undef_store_uint64,
       ``store_int128, ``undef_store_int128,
       ``store_uint128, ``undef_store_uint128,
       ``store_float, ``undef_store_float,
       ``store_double, ``undef_store_double,
       ``store_long_double, ``undef_store_long_double,
       ``store_finite_float, ``undef_store_finite_float,
       ``store_finite_double, ``undef_store_finite_double,
       ``store_finite_long_double, ``undef_store_finite_long_double,
       ``store_ptr, ``undef_store_ptr].contains name
  | _ => false

private partial def unfoldToDynamicStoreWrapper? (expression : Expr)
    (visited : List Name := []) : MetaM (Option Expr) := do
  let expression := expression.headBeta
  if isDynamicStoreWrapper expression then
    return some expression
  match expression.getAppFn.consumeMData with
  | .const name _ =>
      if visited.contains name || !isStoreFacadeAtom expression ||
          (← Lean.isIrreducible name) then
        return none
      let some unfolded ← unfoldDefinition? expression | return none
      if unfolded == expression then
        return none
      unfoldToDynamicStoreWrapper? unfolded (name :: visited)
  | .proj .. =>
      let some reducedFn ←
          withTransparency .all <| reduceProj? expression.getAppFn.consumeMData
        | return none
      unfoldToDynamicStoreWrapper?
        ((mkAppN reducedFn expression.getAppArgs).headBeta) visited
  | _ => return none

private def isDefEqStoreWrapperAtom (lhs rhs : Expr) : MetaM (Option Bool) := do
  let some lhs ← unfoldToDynamicStoreWrapper? lhs | return none
  let some rhs ← unfoldToDynamicStoreWrapper? rhs | return none
  if lhs.getAppFn.consumeMData != rhs.getAppFn.consumeMData then
    return some false
  let lhsArgs := lhs.getAppArgs.toList
  let rhsArgs := rhs.getAppArgs.toList
  if lhsArgs.length != rhsArgs.length then
    return some false
  let saved ← saveState
  for (lhsArg, rhsArg) in lhsArgs.zip rhsArgs do
    unless ← withTransparency .reducible <| isDefEq lhsArg rhsArg do
      restoreState saved
      return some false
  return some true

private def isLowLevelStoreAtom (expression : Expr) : Bool :=
  match expression.getAppFn.consumeMData with
  | .const name _ =>
      [``store_2byte, ``store_4byte, ``store_8byte, ``store_16byte,
       ``store_2byte_noninit, ``store_4byte_noninit,
       ``store_8byte_noninit, ``store_16byte_noninit,
       ``DerivedPredSigCompat.store_2byte,
       ``DerivedPredSigCompat.store_4byte,
       ``DerivedPredSigCompat.store_8byte,
       ``DerivedPredSigCompat.store_16byte].contains name
  | _ => false

private def isDefEqAtom (lhs rhs : Expr) : MetaM Bool := do
  if lhs == rhs then
    return true
  let saved <- saveState
  if <- withTransparency .instances <| isDefEq lhs rhs then
    return true
  restoreState saved
  let saved <- saveState
  if <- withTransparency .reducible <| isDefEq lhs rhs then
    return true
  restoreState saved
  if <- isDefEqFiniteStoreAtom lhs rhs then
    return true
  match ← isDefEqStoreWrapperAtom lhs rhs with
  | some true => return true
  | some false | none => pure ()
  match storeFacadeBaseName? lhs, storeFacadeBaseName? rhs with
  | some lhsName, some rhsName =>
      if lhsName != rhsName then
        return false
      let saved <- saveState
      if <- withTransparency .all <| isDefEq lhs rhs then
        return true
      restoreState saved
  | some _, none =>
      unless isLowLevelStoreAtom rhs || isArchitectureStoreBranch rhs do
        return false
      let saved <- saveState
      if <- withTransparency .all <| isDefEq lhs rhs then
        return true
      restoreState saved
  | none, some _ =>
      unless isLowLevelStoreAtom lhs || isArchitectureStoreBranch lhs do
        return false
      let saved <- saveState
      if <- withTransparency .all <| isDefEq lhs rhs then
        return true
      restoreState saved
  | none, none => pure ()
  if isArchitectureStoreBranch lhs || isArchitectureStoreBranch rhs then
    let saved <- saveState
    if <- withTransparency .all <| isDefEq lhs rhs then
      return true
    restoreState saved
  if isLowLevelStoreAtom lhs != isLowLevelStoreAtom rhs then
    let saved <- saveState
    if <- withTransparency .all <| isDefEq lhs rhs then
      return true
    restoreState saved
  if lhs.hasMVar || rhs.hasMVar then
    return ← isDefEq lhs rhs
  let reducedLhs ← shallowUnfoldAtom lhs 4
  let reducedRhs ← shallowUnfoldAtom rhs 4
  if reducedLhs == lhs && reducedRhs == rhs then
    return false
  withTransparency .instances <| isDefEq reducedLhs reducedRhs

private def defEqNoCommit (lhs rhs : Expr) : MetaM Bool := do
  let saved <- saveState
  let result <- isDefEqAtom lhs rhs
  restoreState saved
  pure result

private def operatorBaseName? (expression : Expr) : Option String :=
  match expression.getAppFn.consumeMData with
  | .const (.str _ name) _ => some name
  | _ => none

private def defEqLogicalConstantNoCommit (lhs rhs : Expr) : MetaM Bool := do
  if lhs == rhs then
    return true
  if operatorBaseName? lhs != operatorBaseName? rhs then
    return false
  defEqNoCommit lhs rhs

private def defEqOperatorNoCommit (lhs rhs : Expr) : MetaM Bool := do
  if lhs == rhs then
    return true
  if operatorBaseName? lhs != operatorBaseName? rhs then
    return false
  if ← defEqNoCommit lhs rhs then
    return true
  let saved ← saveState
  let result ← withTransparency .all <| isDefEq lhs rhs
  restoreState saved
  return result

private def isDefEqProofType (lhs rhs : Expr) : MetaM Bool :=
  withTransparency .instances <| isDefEq lhs rhs

private def matchBinary (op expression : Expr) : MetaM (Option (Expr × Expr)) := do
  match expression.consumeMData with
  | .app (.app fn lhs) rhs =>
      if <- defEqOperatorNoCommit fn op then
        pure (some (lhs, rhs))
      else
        pure none
  | _ => pure none

private def matchUnary (op expression : Expr) : MetaM (Option Expr) := do
  match expression.consumeMData with
  | .app fn argument =>
      if <- defEqOperatorNoCommit fn op then
        pure (some argument)
      else
        pure none
  | _ => pure none

private def matchBinarySyntactic (op expression : Expr) : Option (Expr × Expr) :=
  match expression.consumeMData with
  | .app (.app fn lhs) rhs =>
      if fn == op then some (lhs, rhs) else none
  | _ => none

private def matchUnarySyntactic (op expression : Expr) : Option Expr :=
  match expression.consumeMData with
  | .app fn argument => if fn == op then some argument else none
  | _ => none

private def getOps : TacticM Ops := do
  let rules <- Lean.Elab.Term.elabTerm (← `(SacContext.rules))
    (some (mkConst ``SeparationLogicSig))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let rules <- instantiateMVars rules
  let derivable <- mkAppM ``SeparationLogicSig.derivable1 #[rules]
  let logicEquiv <- mkAppM ``SeparationLogicSig.logic_equiv #[rules]
  let sepcon <- mkAppM ``SeparationLogicSig.sepcon #[rules]
  let andp <- mkAppM ``SeparationLogicSig.andp #[rules]
  let orp <- mkAppM ``SeparationLogicSig.orp #[rules]
  let wand <- mkAppM ``SeparationLogicSig.wand #[rules]
  let impp <- mkAppM ``SeparationLogicSig.impp #[rules]
  let context <- mkAppM ``SeparationLogicSig.toContext #[rules]
  let iffp <- mkAppM
    ``Unifysl.LogicGenerator.demo932.Facade.Context.iffp #[context]
  let exp <- mkAppM ``SeparationLogicSig.exp #[rules]
  let allp <- mkAppM ``SeparationLogicSig.allp #[rules]
  let coqProp <- mkAppM ``SeparationLogicSig.coq_prop #[rules]
  let emp <- mkAppM ``SeparationLogicSig.emp #[rules]
  let truep <- mkAppM ``SeparationLogicSig.truep #[rules]
  pure ⟨rules, derivable, logicEquiv, sepcon, andp, orp, wand, impp, iffp,
    exp, allp, coqProp, emp, truep⟩

private def isCanonicalStoreWrapper (expression : Expr) : Bool :=
  match expression.getAppFn.consumeMData with
  | .const name _ =>
      [``store_char, ``undef_store_char,
       ``store_uchar, ``undef_store_uchar,
       ``store_short, ``undef_store_short,
       ``store_ushort, ``undef_store_ushort,
       ``store_int, ``undef_store_int,
       ``store_uint, ``undef_store_uint,
       ``store_int64, ``undef_store_int64,
       ``store_uint64, ``undef_store_uint64,
       ``store_int128, ``undef_store_int128,
       ``store_uint128, ``undef_store_uint128,
       ``store_float, ``undef_store_float,
       ``store_double, ``undef_store_double,
       ``store_long_double, ``undef_store_long_double,
       ``store_finite_float, ``undef_store_finite_float,
       ``store_finite_double, ``undef_store_finite_double,
       ``store_finite_long_double, ``undef_store_finite_long_double,
       ``store_ptr, ``undef_store_ptr,
       ``DerivedPredSigCompat.store_char, ``DerivedPredSigCompat.undef_store_char,
       ``DerivedPredSigCompat.store_uchar, ``DerivedPredSigCompat.undef_store_uchar,
       ``DerivedPredSigCompat.store_short, ``DerivedPredSigCompat.undef_store_short,
       ``DerivedPredSigCompat.store_ushort, ``DerivedPredSigCompat.undef_store_ushort,
       ``DerivedPredSigCompat.store_int, ``DerivedPredSigCompat.undef_store_int,
       ``DerivedPredSigCompat.store_uint, ``DerivedPredSigCompat.undef_store_uint,
       ``DerivedPredSigCompat.store_int64, ``DerivedPredSigCompat.undef_store_int64,
       ``DerivedPredSigCompat.store_uint64, ``DerivedPredSigCompat.undef_store_uint64,
       ``DerivedPredSigCompat.store_int128, ``DerivedPredSigCompat.undef_store_int128,
       ``DerivedPredSigCompat.store_uint128, ``DerivedPredSigCompat.undef_store_uint128,
       ``DerivedPredSigCompat.store_float, ``DerivedPredSigCompat.undef_store_float,
       ``DerivedPredSigCompat.store_double, ``DerivedPredSigCompat.undef_store_double,
       ``DerivedPredSigCompat.store_long_double,
       ``DerivedPredSigCompat.undef_store_long_double,
       ``DerivedPredSigCompat.store_finite_float,
       ``DerivedPredSigCompat.undef_store_finite_float,
       ``DerivedPredSigCompat.store_finite_double,
       ``DerivedPredSigCompat.undef_store_finite_double,
       ``DerivedPredSigCompat.store_finite_long_double,
       ``DerivedPredSigCompat.undef_store_finite_long_double,
       ``DerivedPredSigCompat.store_ptr, ``DerivedPredSigCompat.undef_store_ptr].contains name
  | _ => false

private partial def unfoldStoreForInspection? (ops : Ops) (expression : Expr)
    (seenStoreWrapper : Bool := false) (visited : List Name := []) :
    MetaM (Option Expr) := do
  if let some wrapper ← unfoldToDynamicStoreWrapper? expression then
    let unfolded ← withTransparency .all <| whnf wrapper
    if unfolded != expression then
      if (← matchBinary ops.andp unfolded).isSome then
        return some unfolded
      if let some inspected ← unfoldStoreForInspection? ops unfolded true visited then
        return some inspected
  let seenStoreWrapper := seenStoreWrapper || isStoreFacadeAtom expression ||
    isCanonicalStoreWrapper expression
  if (← matchBinary ops.andp expression).isSome then
    return if seenStoreWrapper then some expression else none
  if !seenStoreWrapper && (finiteStoreAtomName? expression).isSome then
    return none
  let unfoldOpaqueFacade : MetaM (Option Expr) := do
    unless isStoreFacadeAtom expression do
      return none
    let unfolded ← withTransparency .all <| whnf expression
    if unfolded == expression then
      return none
    unfoldStoreForInspection? ops unfolded true visited
  let name <-
    match expression.getAppFn.consumeMData with
    | .const name _ => pure name
    | .proj .. =>
        let some reducedFn ←
            withTransparency .all <| reduceProj? expression.getAppFn.consumeMData
          | return ← unfoldOpaqueFacade
        let unfolded := (mkAppN reducedFn expression.getAppArgs).headBeta
        if unfolded != expression then
          return ← unfoldStoreForInspection? ops unfolded seenStoreWrapper visited
        return ← unfoldOpaqueFacade
    | _ => return ← unfoldOpaqueFacade
  if visited.contains name || (← Lean.isIrreducible name) then
    return ← unfoldOpaqueFacade
  let some unfolded ← unfoldDefinition? expression
    | return ← unfoldOpaqueFacade
  if unfolded == expression then
    return none
  unfoldStoreForInspection? ops unfolded seenStoreWrapper (name :: visited)

private def foldAtoms (ops : Ops) : List Expr -> Expr
  | [] => ops.emp
  | [atom] => atom
  | atom :: rest => mkApp2 ops.sepcon atom (foldAtoms ops rest)

private def equivRefl (ops : Ops) (p : Expr) : MetaM Expr :=
  mkAppM ``Automation.logic_equiv_refl_rule #[ops.rules, p]

private def equivSymm (ops : Ops) (p q proof : Expr) : MetaM Expr :=
  mkAppM ``Automation.logic_equiv_symm_rule #[ops.rules, p, q, proof]

private def equivTrans (ops : Ops) (p q r first second : Expr) : MetaM Expr :=
  mkAppM ``Automation.logic_equiv_trans_rule #[ops.rules, p, q, r, first, second]

private def equivSepconMono (ops : Ops) (p p' q q' hp hq : Expr) : MetaM Expr :=
  mkAppM ``Automation.logic_equiv_sepcon_mono_rule
    #[ops.rules, p, p', q, q', hp, hq]

private def equivAndpMono (ops : Ops) (p p' q q' hp hq : Expr) : MetaM Expr :=
  mkAppM ``Automation.logic_equiv_andp_mono_rule
    #[ops.rules, p, p', q, q', hp, hq]

private def equivComm (ops : Ops) (p q : Expr) : MetaM Expr :=
  mkAppM ``Automation.logic_equiv_sepcon_comm_rule #[ops.rules, p, q]

private def equivAssoc (ops : Ops) (p q r : Expr) : MetaM Expr :=
  mkAppM ``Automation.logic_equiv_sepcon_assoc_rule #[ops.rules, p, q, r]

private def equivSwap (ops : Ops) (p q r : Expr) : MetaM Expr :=
  mkAppM ``Automation.logic_equiv_sepcon_swap_rule #[ops.rules, p, q, r]

private def derivableRefl (ops : Ops) (p : Expr) : MetaM Expr :=
  mkAppM ``Automation.derivable_refl_rule #[ops.rules, p]

private def derivableTrans (ops : Ops) (p q r first second : Expr) : MetaM Expr :=
  mkAppM ``Automation.derivable_trans_rule #[ops.rules, p, q, r, first, second]

private def derivableSepconMono (ops : Ops) (p p' q q' hp hq : Expr) : MetaM Expr :=
  mkAppM ``Automation.derivable_sepcon_mono_rule
    #[ops.rules, p, p', q, q', hp, hq]

private def derivableAndpMono (ops : Ops) (p p' q q' hp hq : Expr) : MetaM Expr :=
  mkAppM ``Automation.derivable_andp_mono_rule
    #[ops.rules, p, p', q, q', hp, hq]

private structure KnownPureNormalized where
  expression : Expr
  proof : Expr
  sideGoals : List MVarId := []

private structure StoreGuardsEliminated where
  expression : Expr
  proof : Expr

private def findLocalProof? (proposition : Expr) : MetaM (Option Expr) := do
  for localDecl in ← getLCtx do
    let saved ← saveState
    if ← withTransparency .all <| isDefEq localDecl.type proposition then
      return some (mkFVar localDecl.fvarId)
    restoreState saved
  return none

private def dischargeLocalPureSideGoals (sideGoals : List MVarId) :
    MetaM (List MVarId) := do
  let mut pending := []
  for sideGoal in sideGoals do
    unless ← sideGoal.isAssigned do
      let proposition ← instantiateMVars (← sideGoal.getType)
      match ← findLocalProof? proposition with
      | some proof => sideGoal.assign proof
      | none => pending := pending.concat sideGoal
  return pending

private partial def stripKnownPureStoreGuards (ops : Ops) (expression : Expr) :
    MetaM KnownPureNormalized := do
  let expression ← instantiateMVars expression
  let expression := expression.headBeta
  if let some (left, right) ← matchBinary ops.sepcon expression then
    let leftNorm ← stripKnownPureStoreGuards ops left
    let rightNorm ← stripKnownPureStoreGuards ops right
    let normalized := mkApp2 ops.sepcon leftNorm.expression rightNorm.expression
    let proof ← derivableSepconMono ops leftNorm.expression left
      rightNorm.expression right leftNorm.proof rightNorm.proof
    return {
      expression := normalized
      proof
      sideGoals := leftNorm.sideGoals ++ rightNorm.sideGoals
    }
  let inspected ←
    match ← unfoldStoreForInspection? ops expression with
    | some unfolded => pure unfolded
    | none => pure expression
  if let some (pureAssertion, spatial) ← matchBinary ops.andp inspected then
    if let some proposition ← matchUnary ops.coqProp pureAssertion then
      let spatialNorm ← stripKnownPureStoreGuards ops spatial
      let (pureProof, pureSideGoals) ←
        if proposition.hasMVar then
          let pureGoal ← mkFreshExprSyntheticOpaqueMVar proposition
          pure (pureGoal, [pureGoal.mvarId!])
        else match ← findLocalProof? proposition with
        | some localProof => pure (localProof, [])
        | none => do
            let pureGoal ← mkFreshExprSyntheticOpaqueMVar proposition
            pure (pureGoal, [pureGoal.mvarId!])
      let proof ← mkAppM ``coq_prop_andp_right
        #[ops.rules, proposition, spatial, spatialNorm.expression,
          spatialNorm.proof, pureProof]
      return {
        expression := spatialNorm.expression
        proof
        sideGoals := spatialNorm.sideGoals ++ pureSideGoals
      }
    else
      logInfo m!"store guard was not recognized as coq_prop: {pureAssertion}"
  return { expression, proof := ← derivableRefl ops expression }

private def storeWrapperSpatial? (ops : Ops) (expression : Expr) :
    MetaM (Option Expr) := do
  let some inspected ← unfoldStoreForInspection? ops expression | return none
  let some (_, spatial) ← matchBinary ops.andp inspected | return none
  return some spatial

private def matchesAnyAtomNoCommit (_ops : Ops) (expression : Expr)
    (candidates : List Expr) : MetaM Bool := do
  if isStoreFacadeAtom expression || isCanonicalStoreWrapper expression then
    for candidate in candidates do
      unless isStoreFacadeAtom candidate || isCanonicalStoreWrapper candidate do
        continue
      match ← isDefEqStoreWrapperAtom expression candidate with
      | some true => return true
      | some false | none =>
          if ← defEqNoCommit expression candidate then
            return true
    return false
  for candidate in candidates do
    let equivalent ← defEqNoCommit expression candidate
    if equivalent then
      return true
  return false

private partial def stripUnmatchedPureStoreGuards (ops : Ops)
    (goalAtoms : List Expr) (expression : Expr) : MetaM KnownPureNormalized := do
  let expression ← instantiateMVars expression
  let expression := expression.headBeta
  if let some (left, right) ← matchBinary ops.sepcon expression then
    let leftNorm ← stripUnmatchedPureStoreGuards ops goalAtoms left
    let rightNorm ← stripUnmatchedPureStoreGuards ops goalAtoms right
    let normalized := mkApp2 ops.sepcon leftNorm.expression rightNorm.expression
    let proof ← derivableSepconMono ops leftNorm.expression left
      rightNorm.expression right leftNorm.proof rightNorm.proof
    return {
      expression := normalized
      proof
      sideGoals := leftNorm.sideGoals ++ rightNorm.sideGoals
    }
  if ← matchesAnyAtomNoCommit ops expression goalAtoms then
    return { expression, proof := ← derivableRefl ops expression }
  let inspected ←
    match ← unfoldStoreForInspection? ops expression with
    | some unfolded => pure unfolded
    | none => pure expression
  if let some (pureAssertion, spatial) ← matchBinary ops.andp inspected then
    if let some proposition ← matchUnary ops.coqProp pureAssertion then
      let spatialNorm ← stripUnmatchedPureStoreGuards ops goalAtoms spatial
      let (pureProof, pureSideGoals) ←
        if proposition.hasMVar then
          let pureGoal ← mkFreshExprSyntheticOpaqueMVar proposition
          pure (pureGoal, [pureGoal.mvarId!])
        else match ← findLocalProof? proposition with
        | some localProof => pure (localProof, [])
        | none => do
            let pureGoal ← mkFreshExprSyntheticOpaqueMVar proposition
            pure (pureGoal, [pureGoal.mvarId!])
      let proof ← mkAppM ``coq_prop_andp_right
        #[ops.rules, proposition, spatial, spatialNorm.expression,
          spatialNorm.proof, pureProof]
      return {
        expression := spatialNorm.expression
        proof
        sideGoals := spatialNorm.sideGoals ++ pureSideGoals
      }
  return { expression, proof := ← derivableRefl ops expression }

private partial def eliminateStoreGuards (ops : Ops) (expression : Expr) :
    MetaM StoreGuardsEliminated := do
  let expression ← instantiateMVars expression
  let expression := expression.headBeta
  if let some (left, right) ← matchBinary ops.sepcon expression then
    let leftNorm ← eliminateStoreGuards ops left
    let rightNorm ← eliminateStoreGuards ops right
    let normalized := mkApp2 ops.sepcon leftNorm.expression rightNorm.expression
    let proof ← derivableSepconMono ops left leftNorm.expression
      right rightNorm.expression leftNorm.proof rightNorm.proof
    return { expression := normalized, proof }
  let inspected ←
    match ← unfoldStoreForInspection? ops expression with
    | some unfolded => pure unfolded
    | none => pure expression
  if let some (pureAssertion, spatial) ← matchBinary ops.andp inspected then
    if let some proposition ← matchUnary ops.coqProp pureAssertion then
      let spatialNorm ← eliminateStoreGuards ops spatial
      let implication ← withLocalDeclD `_ proposition fun premise =>
        mkLambdaFVars #[premise] spatialNorm.proof
      let proof ← mkAppM ``coq_prop_andp_left
        #[ops.rules, proposition, spatial, spatialNorm.expression, implication]
      return { expression := spatialNorm.expression, proof }
  return { expression, proof := ← derivableRefl ops expression }

private partial def eliminateSelectedStoreGuards (ops : Ops)
    (storeAtoms : List Expr) (expression : Expr) : MetaM StoreGuardsEliminated := do
  let expression ← instantiateMVars expression
  let expression := expression.headBeta
  if let some (left, right) ← matchBinary ops.sepcon expression then
    let leftNorm ← eliminateSelectedStoreGuards ops storeAtoms left
    let rightNorm ← eliminateSelectedStoreGuards ops storeAtoms right
    let normalized := mkApp2 ops.sepcon leftNorm.expression rightNorm.expression
    let proof ← derivableSepconMono ops left leftNorm.expression
      right rightNorm.expression leftNorm.proof rightNorm.proof
    return { expression := normalized, proof }
  let inspected ←
    match ← unfoldStoreForInspection? ops expression with
    | some unfolded => pure unfolded
    | none => pure expression
  if let some (pureAssertion, spatial) ← matchBinary ops.andp inspected then
    if let some proposition ← matchUnary ops.coqProp pureAssertion then
      if ← matchesAnyAtomNoCommit ops spatial storeAtoms then
        let spatialNorm ← eliminateSelectedStoreGuards ops storeAtoms spatial
        let implication ← withLocalDeclD `_ proposition fun premise =>
          mkLambdaFVars #[premise] spatialNorm.proof
        let proof ← mkAppM ``coq_prop_andp_left
          #[ops.rules, proposition, spatial, spatialNorm.expression, implication]
        return { expression := spatialNorm.expression, proof }
  return { expression, proof := ← derivableRefl ops expression }

private def hasConflictingStoreWrappers (ops : Ops) (lemmaAtoms goalAtoms : List Expr) :
    MetaM Bool := do
  for lemmaAtom in lemmaAtoms do
    let some lemmaName := storeFacadeBaseName? lemmaAtom | continue
    let some lemmaSpatial ← storeWrapperSpatial? ops lemmaAtom | continue
    for goalAtom in goalAtoms do
      let some goalName := storeFacadeBaseName? goalAtom | continue
      if lemmaName == goalName then
        continue
      let some goalSpatial ← storeWrapperSpatial? ops goalAtom | continue
      if ← defEqNoCommit lemmaSpatial goalSpatial then
        return true
  return false

private partial def normalizeStoreGuardsForMatch (ops : Ops) (expression : Expr) :
    MetaM (Expr × Expr) := do
  let expression ← instantiateMVars expression
  let expression := expression.headBeta
  if let some unfolded ← unfoldStoreForInspection? ops expression then
    if unfolded != expression then
      let (normalized, normalizedProof) ←
        normalizeStoreGuardsForMatch ops unfolded
      let unfoldProof ← equivRefl ops expression
      return (normalized, ← equivTrans ops expression unfolded normalized
        unfoldProof normalizedProof)
  if let some (left, right) ← matchBinary ops.andp expression then
    let (newLeft, leftProof) ← normalizeStoreGuardsForMatch ops left
    let (newRight, rightProof) ← normalizeStoreGuardsForMatch ops right
    let combined := mkApp2 ops.andp newLeft newRight
    let proof ← equivAndpMono ops left newLeft right newRight leftProof rightProof
    return (combined, proof)
  if let some (left, right) ← matchBinary ops.sepcon expression then
    let (newLeft, leftProof) ← normalizeStoreGuardsForMatch ops left
    let (newRight, rightProof) ← normalizeStoreGuardsForMatch ops right
    let combined := mkApp2 ops.sepcon newLeft newRight
    let congruence ←
      equivSepconMono ops left newLeft right newRight leftProof rightProof
    if let some (pureAssertion, spatial) ← matchBinary ops.andp newLeft then
      if let some proposition ← matchUnary ops.coqProp pureAssertion then
        let lifted := mkApp2 ops.andp pureAssertion
          (mkApp2 ops.sepcon spatial newRight)
        let liftProof ← mkAppM
          ``Automation.logic_equiv_coq_prop_andp_sepcon_rule
          #[ops.rules, proposition, spatial, newRight]
        let combinedProof ← equivTrans ops expression combined lifted
          congruence liftProof
        let (normalized, normalizedProof) ←
          normalizeStoreGuardsForMatch ops lifted
        return (normalized, ← equivTrans ops expression lifted normalized
          combinedProof normalizedProof)
    if let some (pureAssertion, spatial) ← matchBinary ops.andp newRight then
      if let some proposition ← matchUnary ops.coqProp pureAssertion then
        let regrouped := mkApp2 ops.sepcon
          (mkApp2 ops.andp pureAssertion newLeft) spatial
        let lifted := mkApp2 ops.andp pureAssertion
          (mkApp2 ops.sepcon newLeft spatial)
        let movePure ← mkAppM
          ``Automation.logic_equiv_sepcon_coq_prop_andp_rule
          #[ops.rules, newLeft, proposition, spatial]
        let liftPure ← mkAppM
          ``Automation.logic_equiv_coq_prop_andp_sepcon_rule
          #[ops.rules, proposition, newLeft, spatial]
        let moved ← equivTrans ops combined regrouped lifted movePure liftPure
        let combinedProof ← equivTrans ops expression combined lifted
          congruence moved
        let (normalized, normalizedProof) ←
          normalizeStoreGuardsForMatch ops lifted
        return (normalized, ← equivTrans ops expression lifted normalized
          combinedProof normalizedProof)
    return (combined, congruence)
  return (expression, ← equivRefl ops expression)

private partial def leadingPureGuards (ops : Ops) (expression : Expr) :
    MetaM (List Expr × Expr) := do
  if let some (pureAssertion, rest) ← matchBinary ops.andp expression then
    if (← matchUnary ops.coqProp pureAssertion).isSome then
      let (guards, spatial) ← leadingPureGuards ops rest
      return (pureAssertion :: guards, spatial)
  return ([], expression)

private def wrapPureGuards (ops : Ops) (guards : List Expr) (spatial : Expr) : Expr :=
  guards.foldr (fun guard rest => mkApp2 ops.andp guard rest) spatial

private partial def liftEquivThroughPureGuards (ops : Ops) (guards : List Expr)
    (source target proof : Expr) : MetaM Expr := do
  match guards with
  | [] => return proof
  | guard :: guards =>
      let liftedTail ← liftEquivThroughPureGuards ops guards source target proof
      equivAndpMono ops guard guard (wrapPureGuards ops guards source)
        (wrapPureGuards ops guards target) (← equivRefl ops guard) liftedTail

private partial def factorPureGuardsAcrossSepcon (ops : Ops) (guards : List Expr)
    (left right : Expr) : MetaM Expr := do
  match guards with
  | [] => return (← equivRefl ops (mkApp2 ops.sepcon left right))
  | guard :: guards =>
      let tailProof ← factorPureGuardsAcrossSepcon ops guards left right
      let sourceTail := wrapPureGuards ops guards (mkApp2 ops.sepcon left right)
      let factoredTail := mkApp2 ops.sepcon (wrapPureGuards ops guards left) right
      let congruence ← equivAndpMono ops guard guard sourceTail factoredTail
        (← equivRefl ops guard) tailProof
      let some proposition ← matchUnary ops.coqProp guard
        | throwError "internal error: non-pure assertion in store guard list"
      let forward ← mkAppM
        ``Automation.logic_equiv_coq_prop_andp_sepcon_rule
        #[ops.rules, proposition, wrapPureGuards ops guards left, right]
      let backward ← equivSymm ops
        (mkApp2 ops.sepcon (mkApp2 ops.andp guard
          (wrapPureGuards ops guards left)) right)
        (mkApp2 ops.andp guard factoredTail) forward
      equivTrans ops (mkApp2 ops.andp guard sourceTail)
        (mkApp2 ops.andp guard factoredTail)
        (mkApp2 ops.sepcon (wrapPureGuards ops (guard :: guards) left) right)
        congruence backward

private partial def appendProof (ops : Ops) (left right : List Expr) : MetaM Expr := do
  match left with
  | [] => throwError "internal error: empty left sepcon list"
  | [x] => equivRefl ops (mkApp2 ops.sepcon x (foldAtoms ops right))
  | x :: rest =>
      let restExpr := foldAtoms ops rest
      let rightExpr := foldAtoms ops right
      let source := mkApp2 ops.sepcon (mkApp2 ops.sepcon x restExpr) rightExpr
      let associated := mkApp2 ops.sepcon x (mkApp2 ops.sepcon restExpr rightExpr)
      let assocForward <- equivAssoc ops x restExpr rightExpr
      let assocBackward <- equivSymm ops associated source assocForward
      let restProof <- appendProof ops rest right
      let xRefl <- equivRefl ops x
      let lifted <- equivSepconMono ops x x
        (mkApp2 ops.sepcon restExpr rightExpr) (foldAtoms ops (rest ++ right))
        xRefl restProof
      equivTrans ops source associated (foldAtoms ops (left ++ right))
        assocBackward lifted

private partial def unfoldToSepcon? (ops : Ops) (expression : Expr) :
    Nat -> MetaM (Option Expr)
  | 0 => pure none
  | fuel + 1 => do
      if (← matchBinary ops.sepcon expression).isSome then
        return some expression
      if (← matchBinary ops.exp expression).isSome ||
          (← matchBinary ops.allp expression).isSome then
        return none
      match expression.getAppFn.consumeMData with
      | .const name _ =>
          if ← Lean.isIrreducible name then
            return none
      | _ => return none
      let some unfolded ← unfoldDefinition? expression | return none
      if unfolded == expression then
        return none
      unfoldToSepcon? ops unfolded fuel

private partial def normalizeExpression (ops : Ops) (expression : Expr) : MetaM Normalized := do
  let expression ← instantiateMVars expression
  let expression := expression.headBeta
  if let some (left, right) <- matchBinary ops.sepcon expression then
    let leftNorm <- normalizeExpression ops left
    let rightNorm <- normalizeExpression ops right
    let combined := mkApp2 ops.sepcon leftNorm.expression rightNorm.expression
    let congr <- equivSepconMono ops left leftNorm.expression right rightNorm.expression
      leftNorm.proof rightNorm.proof
    let appended <- appendProof ops leftNorm.atoms rightNorm.atoms
    let atoms := leftNorm.atoms ++ rightNorm.atoms
    let proof <- equivTrans ops expression combined (foldAtoms ops atoms) congr appended
    pure { atoms, expression := foldAtoms ops atoms, proof }
  else if let some unfolded <- unfoldToSepcon? ops expression 4 then
    let normalized <- normalizeExpression ops unfolded
    let unfoldedRefl <- equivRefl ops expression
    let proof <- equivTrans ops expression unfolded normalized.expression
      unfoldedRefl normalized.proof
    pure { normalized with proof }
  else
    pure { atoms := [expression], expression, proof := <- equivRefl ops expression }

-- Coq's sep_lift_L treats named assertions as atoms and only reassociates
-- sepcon nodes already exposed in the goal.  Keep that behavior as the fast
-- path; definition unfolding belongs to the compatibility fallback below.
private partial def normalizeExposedSepcon (ops : Ops) (expression : Expr) :
    MetaM Normalized := do
  let expression <- instantiateMVars expression
  let expression := expression.headBeta
  if let some (left, right) <- matchBinary ops.sepcon expression then
    let leftNorm <- normalizeExposedSepcon ops left
    let rightNorm <- normalizeExposedSepcon ops right
    let combined := mkApp2 ops.sepcon leftNorm.expression rightNorm.expression
    let congr <- equivSepconMono ops left leftNorm.expression right rightNorm.expression
      leftNorm.proof rightNorm.proof
    let appended <- appendProof ops leftNorm.atoms rightNorm.atoms
    let atoms := leftNorm.atoms ++ rightNorm.atoms
    let proof <- equivTrans ops expression combined (foldAtoms ops atoms) congr appended
    pure { atoms, expression := foldAtoms ops atoms, proof }
  else
    pure { atoms := [expression], expression, proof := <- equivRefl ops expression }

private partial def findDefEqIndex (needle : Expr) : List Expr -> MetaM (Option Nat)
  | [] => pure none
  | head :: tail => do
      if <- defEqNoCommit needle head then
        pure (some 0)
      else
        pure ((<- findDefEqIndex needle tail).map Nat.succ)

private partial def moveFront (ops : Ops) (atoms : List Expr) (index : Nat) :
    MetaM (Expr × List Expr) := do
  match index, atoms with
  | 0, _ => pure (<- equivRefl ops (foldAtoms ops atoms), atoms)
  | next + 1, x :: tail =>
      let (tailProof, movedTail) <- moveFront ops tail next
      match movedTail with
      | [] => throwError "internal error: invalid sepcon move"
      | y :: rest =>
          let xRefl <- equivRefl ops x
          let lifted <- equivSepconMono ops x x (foldAtoms ops tail)
            (foldAtoms ops movedTail) xRefl tailProof
          let beforeSwap := mkApp2 ops.sepcon x (foldAtoms ops movedTail)
          let swapped := foldAtoms ops (y :: x :: rest)
          let swapProof <- match rest with
            | [] => equivComm ops x y
            | _ => equivSwap ops x y (foldAtoms ops rest)
          let proof <- equivTrans ops (foldAtoms ops atoms) beforeSwap swapped
            lifted swapProof
          pure (proof, y :: x :: rest)
  | _, _ => throwError "internal error: sepcon move index out of bounds"

private partial def reorderProof (ops : Ops) (current desired : List Expr) : MetaM Expr := do
  match desired with
  | [] => equivRefl ops ops.emp
  | [target] =>
      match current with
      | [source] =>
          unless <- defEqNoCommit source target do
            throwError "internal error: sepcon permutations differ"
          equivRefl ops source
      | _ => throwError "internal error: sepcon permutation length mismatch"
  | target :: desiredTail =>
      let some index <- findDefEqIndex target current
        | throwError "internal error: target assertion is absent from sepcon permutation"
      let (frontProof, moved) <- moveFront ops current index
      match moved with
      | [] => throwError "internal error: empty moved sepcon permutation"
      | front :: currentTail =>
          let tailProof <- reorderProof ops currentTail desiredTail
          let frontRefl <- equivRefl ops front
          let lifted <- equivSepconMono ops front target
            (foldAtoms ops currentTail) (foldAtoms ops desiredTail)
            frontRefl tailProof
          equivTrans ops (foldAtoms ops current) (foldAtoms ops moved)
            (foldAtoms ops desired) frontProof lifted

private def normalizedTo (ops : Ops) (source : Expr) (norm : Normalized)
    (desired : List Expr) : MetaM Expr := do
  let reordered <- reorderProof ops norm.atoms desired
  equivTrans ops source norm.expression (foldAtoms ops desired)
    norm.proof reordered

-- Move only the requested assertions to the front, in request order.  The
-- untouched suffix remains the frame, matching CommonAssertion.v's
-- sep_lift_L/prop_apply_L algorithm instead of canonicalizing the whole list.
private partial def liftPrefixProof (ops : Ops) (current requested : List Expr) :
    MetaM (Expr × List Expr) := do
  match requested with
  | [] => pure (<- equivRefl ops (foldAtoms ops current), current)
  | target :: requestedTail =>
      let some index <- findDefEqIndex target current
        | throwError "internal error: requested assertion is absent from sepcon frame"
      let (frontProof, moved) <- moveFront ops current index
      match moved with
      | [] => throwError "internal error: empty lifted sepcon frame"
      | front :: currentTail =>
          if requestedTail.isEmpty then
            pure (frontProof, moved)
          else
            if currentTail.isEmpty then
              throwError "internal error: sepcon frame is shorter than the requested prefix"
            let (tailProof, liftedTail) <-
              liftPrefixProof ops currentTail requestedTail
            let frontRefl <- equivRefl ops front
            let lifted <- equivSepconMono ops front target
              (foldAtoms ops currentTail) (foldAtoms ops liftedTail)
              frontRefl tailProof
            let destination := front :: liftedTail
            let proof <- equivTrans ops (foldAtoms ops current) (foldAtoms ops moved)
              (foldAtoms ops destination) frontProof lifted
            pure (proof, destination)

private def normalizedLiftPrefix (ops : Ops) (source : Expr) (norm : Normalized)
    (requested : List Expr) : MetaM (Expr × List Expr) := do
  let (lifted, atoms) <- liftPrefixProof ops norm.atoms requested
  let proof <- equivTrans ops source norm.expression (foldAtoms ops atoms)
    norm.proof lifted
  pure (proof, atoms)

private partial def takeDefEq (needle : Expr) : List Expr -> MetaM (Option (Expr × List Expr))
  | [] => pure none
  | head :: tail => do
      if <- defEqNoCommit needle head then
        pure (some (head, tail))
      else
        match <- takeDefEq needle tail with
        | none => pure none
        | some (found, rest) => pure (some (found, head :: rest))

private partial def pairCommon (left right : List Expr) :
    MetaM (List Expr × List Expr × List Expr × List Expr) := do
  match left with
  | [] => pure ([], [], [], right)
  | atom :: tail =>
      match <- takeDefEq atom right with
      | some (matched, rightRest) =>
          let (commonLeft, commonRight, leftRest, finalRight) <-
            pairCommon tail rightRest
          pure (atom :: commonLeft, matched :: commonRight, leftRest, finalRight)
      | none =>
          let (commonLeft, commonRight, leftRest, finalRight) <-
            pairCommon tail right
          pure (commonLeft, commonRight, atom :: leftRest, finalRight)

private partial def buildCancellation (ops : Ops) (left right : List Expr)
    (commonCount : Nat) (tag : MVarId) : MetaM (Expr × List MVarId) := do
  if commonCount = 0 then
    let source := foldAtoms ops left
    let target := foldAtoms ops right
    if <- defEqNoCommit source target then
      pure (<- derivableRefl ops source, [])
    else
      let type := mkApp2 ops.derivable source target
      let residual <- mkFreshExprSyntheticOpaqueMVar type (← tag.getTag)
      pure (residual, [residual.mvarId!])
  else
    match left, right with
    | x :: leftTail, y :: rightTail =>
        unless <- defEqNoCommit x y do
          throwError "internal error: cancellation prefixes do not match"
        match leftTail, rightTail with
        | [], [] => pure (<- derivableRefl ops x, [])
        | [], _ =>
            let (residual, goals) <- buildCancellation ops [] rightTail 0 tag
            let proof <- mkAppM ``sepcon_cancel_res_emp
              #[ops.rules, x, foldAtoms ops rightTail, residual]
            pure (proof, goals)
        | _, [] =>
            let (residual, goals) <- buildCancellation ops leftTail [] 0 tag
            let proof <- mkAppM ``sepcon_cancel_lhs_emp
              #[ops.rules, x, foldAtoms ops leftTail, residual]
            pure (proof, goals)
        | _, _ =>
            let (tailProof, goals) <-
              buildCancellation ops leftTail rightTail (commonCount - 1) tag
            let headProof <- derivableRefl ops x
            let proof <- derivableSepconMono ops x y (foldAtoms ops leftTail)
              (foldAtoms ops rightTail) headProof tailProof
            pure (proof, goals)
    | _, _ => throwError "internal error: cancellation prefix is too long"

private def runCancel (specified : Option Syntax) : TacticM Unit := withMainContext do
  let goal <- getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops <- getOps
  let some (left, right) <- matchBinary ops.derivable target
    | throwError "cancel: goal is not a separation-logic entailment"
  let left ← instantiateMVars left
  let right ← instantiateMVars right
  let leftNorm <- normalizeExpression ops left
  let rightNorm <- normalizeExpression ops right
  let (commonLeft, commonRight, leftRest, rightRest) <- match specified with
    | none => pairCommon leftNorm.atoms rightNorm.atoms
    | some assertionSyntax =>
        let assertion <- Lean.Elab.Tactic.elabTermForApply assertionSyntax
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        let assertion <- instantiateMVars assertion
        let some (leftMatch, leftRest) <- takeDefEq assertion leftNorm.atoms
          | throwError "cancel: specified assertion was not found on the left"
        let some (rightMatch, rightRest) <- takeDefEq assertion rightNorm.atoms
          | throwError "cancel: specified assertion was not found on the right"
        pure ([leftMatch], [rightMatch], leftRest, rightRest)
  if commonLeft.isEmpty then
    if specified.isNone then
      return
    else
      throwError "cancel: no common spatial assertion was found"
  let desiredLeft := commonLeft ++ leftRest
  let desiredRight := commonRight ++ rightRest
  let leftEquiv <- normalizedTo ops left leftNorm desiredLeft
  let rightEquiv <- normalizedTo ops right rightNorm desiredRight
  let (middle, residualGoals) <-
    buildCancellation ops desiredLeft desiredRight commonLeft.length goal
  let leftForward <- mkAppM ``Automation.logic_equiv_forward_rule
    #[ops.rules, left, foldAtoms ops desiredLeft, leftEquiv]
  let rightBackward <- mkAppM ``Automation.logic_equiv_backward_rule
    #[ops.rules, right, foldAtoms ops desiredRight, rightEquiv]
  let first <- derivableTrans ops left (foldAtoms ops desiredLeft)
    (foldAtoms ops desiredRight) leftForward middle
  let proof <- derivableTrans ops left (foldAtoms ops desiredRight) right
    first rightBackward
  unless <- isDefEqProofType (← inferType proof) target do
    throwError "internal error: cancellation proof does not match the goal"
  goal.assign proof
  replaceMainGoal residualGoals

def runCancelProgress : TacticM Unit := do
  let before ← getGoals
  runCancel none
  if before == (← getGoals) then
    throwError "cancel made no progress"

private partial def liftAssertionInExpression (ops : Ops) (assertion expression : Expr) :
    MetaM (Option (Expr × Expr)) := do
  if let some (left, right) <- matchBinary ops.andp expression then
    if let some (newLeft, leftProof) <- liftAssertionInExpression ops assertion left then
      let proof <- equivAndpMono ops left newLeft right right leftProof
        (← equivRefl ops right)
      return some (mkApp2 ops.andp newLeft right, proof)
    if let some (newRight, rightProof) <- liftAssertionInExpression ops assertion right then
      let proof <- equivAndpMono ops left left right newRight
        (← equivRefl ops left) rightProof
      return some (mkApp2 ops.andp left newRight, proof)
    return none
  let normalized <- normalizeExpression ops expression
  let some (matched, rest) <- takeDefEq assertion normalized.atoms | return none
  let desired := matched :: rest
  let proof <- normalizedTo ops expression normalized desired
  return some (foldAtoms ops desired, proof)

private def runSepconLift (assertionSyntax : Syntax) : TacticM Unit := withMainContext do
  let goal <- getMainGoal
  let target <- goal.getType
  let ops <- getOps
  let some (left, right) <- matchBinary ops.derivable target
    | throwError "sepcon_lift: goal is not a separation-logic entailment"
  let assertion <- Lean.Elab.Tactic.elabTermForApply assertionSyntax
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let assertion <- instantiateMVars assertion
  let leftLifted <- liftAssertionInExpression ops assertion left
  let rightLifted <- liftAssertionInExpression ops assertion right
  if leftLifted.isNone && rightLifted.isNone then
    throwError "sepcon_lift: assertion was not found in the entailment"
  let (desiredLeft, leftEquiv) <- match leftLifted with
    | some result => pure result
    | none => pure (left, <- equivRefl ops left)
  let (desiredRight, rightEquiv) <- match rightLifted with
    | some result => pure result
    | none => pure (right, <- equivRefl ops right)
  let middleType := mkApp2 ops.derivable desiredLeft desiredRight
  let middle <- mkFreshExprSyntheticOpaqueMVar middleType (← goal.getTag)
  let leftForward <- mkAppM ``Automation.logic_equiv_forward_rule
    #[ops.rules, left, desiredLeft, leftEquiv]
  let rightBackward <- mkAppM ``Automation.logic_equiv_backward_rule
    #[ops.rules, right, desiredRight, rightEquiv]
  let first <- derivableTrans ops left desiredLeft desiredRight leftForward middle
  let proof <- derivableTrans ops left desiredRight right
    first rightBackward
  unless <- isDefEqProofType (← inferType proof) target do
    throwError "internal error: sepcon_lift proof does not match the goal"
  goal.assign proof
  replaceMainGoal [middle.mvarId!]

elab "cancel" : tactic => runCancel none

elab "cancel " assertion:(colGt term) : tactic => runCancel (some assertion)

elab "sepcon_lift " assertion:(colGt term) : tactic =>
  runSepconLift assertion

inductive RewriteShape where
  | sepEmpRight
  | sepEmpLeft
  | sepconAssocLeft
  | truepAndpLeft
  | truepAndpRight
  | andpAssocLeft
  | pureAndpSepconLeft
  | pureAndpSepconRight
  | sepconPureRight
  | andpPureRight
  | sepconPureLeft
  | spatialAndpRight
  | expAndpLeft
  | expSepconLeft
  | expAndpRight
  | expSepconRight
  | orpSepconLeft
  | orpSepconRight

private def isCoqProp (ops : Ops) (expression : Expr) : MetaM Bool := do
  pure (← matchUnary ops.coqProp expression).isSome

private def matchesRewriteShapeAt (ops : Ops) (shape : RewriteShape)
    (expression : Expr) : MetaM Bool := do
  match shape with
  | .sepEmpRight =>
      let some (_, right) ← matchBinary ops.sepcon expression | pure false
      defEqLogicalConstantNoCommit right ops.emp
  | .sepEmpLeft =>
      let some (left, _) ← matchBinary ops.sepcon expression | pure false
      defEqLogicalConstantNoCommit left ops.emp
  | .sepconAssocLeft =>
      let some (left, _) ← matchBinary ops.sepcon expression | pure false
      pure (← matchBinary ops.sepcon left).isSome
  | .truepAndpLeft =>
      let some (left, _) ← matchBinary ops.andp expression | pure false
      defEqLogicalConstantNoCommit left ops.truep
  | .truepAndpRight =>
      let some (_, right) ← matchBinary ops.andp expression | pure false
      defEqLogicalConstantNoCommit right ops.truep
  | .andpAssocLeft =>
      let some (left, _) ← matchBinary ops.andp expression | pure false
      pure (← matchBinary ops.andp left).isSome
  | .pureAndpSepconLeft =>
      let some (left, _) ← matchBinary ops.sepcon expression | pure false
      let some (purePart, _) ← matchBinary ops.andp left | pure false
      isCoqProp ops purePart
  | .pureAndpSepconRight =>
      let some (_, right) ← matchBinary ops.sepcon expression | pure false
      let some (purePart, _) ← matchBinary ops.andp right | pure false
      isCoqProp ops purePart
  | .sepconPureRight =>
      let some (_, right) ← matchBinary ops.sepcon expression | pure false
      isCoqProp ops right
  | .andpPureRight =>
      let some (left, right) ← matchBinary ops.andp expression | pure false
      pure (!(← isCoqProp ops left) &&
        !(← matchBinary ops.exp left).isSome &&
        (← isCoqProp ops right))
  | .sepconPureLeft =>
      let some (left, _) ← matchBinary ops.sepcon expression | pure false
      isCoqProp ops left
  | .spatialAndpRight =>
      let some (left, right) ← matchBinary ops.andp expression | pure false
      pure ((← matchBinary ops.sepcon left).isSome &&
        !(← matchBinary ops.sepcon right).isSome)
  | .expAndpLeft =>
      let some (left, _) ← matchBinary ops.andp expression | pure false
      pure (← matchBinary ops.exp left).isSome
  | .expSepconLeft =>
      let some (left, _) ← matchBinary ops.sepcon expression | pure false
      pure (← matchBinary ops.exp left).isSome
  | .expAndpRight =>
      let some (_, right) ← matchBinary ops.andp expression | pure false
      pure (← matchBinary ops.exp right).isSome
  | .expSepconRight =>
      let some (_, right) ← matchBinary ops.sepcon expression | pure false
      pure (← matchBinary ops.exp right).isSome
  | .orpSepconLeft =>
      let some (left, _) ← matchBinary ops.sepcon expression | pure false
      pure (← matchBinary ops.orp left).isSome
  | .orpSepconRight =>
      let some (_, right) ← matchBinary ops.sepcon expression | pure false
      pure (← matchBinary ops.orp right).isSome

private partial def containsRewriteShape (ops : Ops) (shape : RewriteShape)
    (expression : Expr) : MetaM Bool := do
  if ← matchesRewriteShapeAt ops shape expression then
    return true
  if let some (left, right) ← matchBinary ops.derivable expression then
    return (← containsRewriteShape ops shape left) ||
      (← containsRewriteShape ops shape right)
  if let some (left, right) ← matchBinary ops.logicEquiv expression then
    return (← containsRewriteShape ops shape left) ||
      (← containsRewriteShape ops shape right)
  if let some (left, right) ← matchBinary ops.sepcon expression then
    return (← containsRewriteShape ops shape left) ||
      (← containsRewriteShape ops shape right)
  if let some (left, right) ← matchBinary ops.andp expression then
    return (← containsRewriteShape ops shape left) ||
      (← containsRewriteShape ops shape right)
  if let some (left, right) ← matchBinary ops.orp expression then
    return (← containsRewriteShape ops shape left) ||
      (← containsRewriteShape ops shape right)
  if let some (left, right) ← matchBinary ops.wand expression then
    return (← containsRewriteShape ops shape left) ||
      (← containsRewriteShape ops shape right)
  if let some (left, right) ← matchBinary ops.impp expression then
    return (← containsRewriteShape ops shape left) ||
      (← containsRewriteShape ops shape right)
  if let some (_, body) ← matchBinary ops.exp expression then
    return ← containsRewriteShape ops shape body
  if let some (_, body) ← matchBinary ops.allp expression then
    return ← containsRewriteShape ops shape body
  match expression.consumeMData with
  | .lam _ _ body _ => containsRewriteShape ops shape body
  | .forallE _ _ body _ => containsRewriteShape ops shape body
  | .letE _ _ value body _ =>
      return (← containsRewriteShape ops shape value) ||
        (← containsRewriteShape ops shape body)
  | _ => pure false

private partial def tryRewriteCandidates (ops : Ops)
    (candidates : List (RewriteShape × Syntax)) : TacticM Bool := do
  match candidates with
  | [] => pure false
  | (shape, tactic) :: rest =>
      let target ← (← getMainGoal).getType
      if ← containsRewriteShape ops shape target then
        let saved ← saveState
        try
          evalTactic tactic
          pure true
        catch _ =>
          restoreState saved
          tryRewriteCandidates ops rest
      else
        tryRewriteCandidates ops rest

def runRewriteSet (candidates : List (RewriteShape × Syntax)) : TacticM Unit := do
  let ops ← getOps
  let rec loop : Nat → TacticM Unit
    | 0 => throwError "assertion normalization exceeded its rewrite limit"
    | fuel + 1 => do
        if (← getGoals).isEmpty then
          return
        if ← tryRewriteCandidates ops candidates then
          loop fuel
  loop 512

private partial def takeUnifying (needle : Expr) : List Expr ->
    MetaM (Option (Expr × List Expr))
  | [] => pure none
  | head :: tail => do
      let saved ← saveState
      if ← isDefEqAtom needle head then
        pure (some (head, tail))
      else
        restoreState saved
        match ← takeUnifying needle tail with
        | none => pure none
        | some (found, rest) => pure (some (found, head :: rest))

private partial def preUnifyStoreAtoms (needles available : List Expr)
    (matchedAny : Bool := false) : MetaM Bool := do
  match needles with
  | [] => return matchedAny
  | needle :: needles =>
      match ← takeUnifying needle available with
      | some (_, rest) => preUnifyStoreAtoms needles rest true
      | none => preUnifyStoreAtoms needles available matchedAny

private partial def selectUnifyingAtoms (needles available : List Expr) :
    MetaM (Option (List Expr × List Expr)) := do
  match needles with
  | [] => pure (some ([], available))
  | needle :: tail =>
      let rec tryCandidates (seen candidates : List Expr) :
          MetaM (Option (List Expr × List Expr)) := do
        match candidates with
        | [] => pure none
        | candidate :: candidates =>
            let saved ← saveState
            if ← isDefEqAtom needle candidate then
              let remaining := seen.reverse ++ candidates
              if let some (matchedTail, rest) ←
                  selectUnifyingAtoms tail remaining then
                return some (candidate :: matchedTail, rest)
            restoreState saved
            tryCandidates (candidate :: seen) candidates
      tryCandidates [] available

private structure GuardedStoreMatch where
  preparedLeft : Expr
  preparedProof : Expr
  lemmaNorm : Normalized
  matched : List Expr
  rest : List Expr
  goalNorm : Normalized

private def prepareGuardedStoreMatch (ops : Ops) (lemmaLeft lemmaRight lemmaProof
    goalLeft : Expr) : MetaM (Option GuardedStoreMatch) := do
  let (lemmaStore, lemmaStoreProof) ← normalizeStoreGuardsForMatch ops lemmaLeft
  let (lemmaGuards, lemmaSpatial) ← leadingPureGuards ops lemmaStore
  if lemmaGuards.isEmpty then
    return none
  let (goalStore, goalStoreProof) ← normalizeStoreGuardsForMatch ops goalLeft
  let (goalGuards, goalSpatial) ← leadingPureGuards ops goalStore
  unless lemmaGuards.length == goalGuards.length do
    return none
  for (lemmaGuard, goalGuard) in lemmaGuards.zip goalGuards do
    let saved ← saveState
    let guardsMatch ← withTransparency .all <| isDefEq lemmaGuard goalGuard
    restoreState saved
    unless guardsMatch do
      return none
  let lemmaSpatialNorm ← normalizeExpression ops lemmaSpatial
  let goalSpatialNorm ← normalizeExpression ops goalSpatial
  let some (matched, rest) ←
      selectUnifyingAtoms lemmaSpatialNorm.atoms goalSpatialNorm.atoms
    | return none
  let desired := matched ++ rest
  let goalSpatialToFlat ← normalizedTo ops goalSpatial goalSpatialNorm desired
  let matchedExpr := foldAtoms ops matched
  let targetSpatial :=
    if rest.isEmpty then matchedExpr
    else mkApp2 ops.sepcon matchedExpr (foldAtoms ops rest)
  let goalSpatialToTarget ←
    if rest.isEmpty then
      pure goalSpatialToFlat
    else do
      let groupedToFlat ← appendProof ops matched rest
      let flatToGrouped ← equivSymm ops targetSpatial (foldAtoms ops desired)
        groupedToFlat
      equivTrans ops goalSpatial (foldAtoms ops desired) targetSpatial
        goalSpatialToFlat flatToGrouped
  let guardedMatched := wrapPureGuards ops goalGuards matchedExpr
  let matchingExpression := foldAtoms ops (guardedMatched :: rest)
  let guardedGoalProof ← liftEquivThroughPureGuards ops goalGuards
    goalSpatial targetSpatial goalSpatialToTarget
  let goalStoreToMatching ←
    if rest.isEmpty then
      pure guardedGoalProof
    else do
      let factored ← factorPureGuardsAcrossSepcon ops goalGuards matchedExpr
        (foldAtoms ops rest)
      equivTrans ops goalStore (wrapPureGuards ops goalGuards targetSpatial)
        matchingExpression guardedGoalProof factored
  let goalProof ← equivTrans ops goalLeft goalStore matchingExpression
    goalStoreProof goalStoreToMatching

  let guardedLemma := wrapPureGuards ops lemmaGuards lemmaSpatialNorm.expression
  let liftedLemmaProof ← liftEquivThroughPureGuards ops lemmaGuards lemmaSpatial
    lemmaSpatialNorm.expression lemmaSpatialNorm.proof
  let lemmaEquiv ← equivTrans ops lemmaLeft lemmaStore guardedLemma
    lemmaStoreProof liftedLemmaProof
  let lemmaBackward ← mkAppM ``Automation.logic_equiv_backward_rule
    #[ops.rules, lemmaLeft, guardedLemma, lemmaEquiv]
  let preparedProof ← derivableTrans ops guardedLemma lemmaLeft lemmaRight
    lemmaBackward lemmaProof
  let lemmaNorm : Normalized := {
    atoms := [guardedLemma]
    expression := guardedLemma
    proof := ← equivRefl ops guardedLemma
  }
  let goalNorm : Normalized := {
    atoms := guardedMatched :: rest
    expression := matchingExpression
    proof := goalProof
  }
  return some {
    preparedLeft := guardedLemma
    preparedProof
    lemmaNorm
    matched := [guardedMatched]
    rest
    goalNorm
  }

private partial def canonicalStoreSpatialAtoms (ops : Ops)
    (expression : Expr) : MetaM (List Expr) := do
  let expression ← instantiateMVars expression
  let expression := expression.headBeta
  if let some (left, right) ← matchBinary ops.sepcon expression then
    let leftAtoms ← canonicalStoreSpatialAtoms ops left
    let rightAtoms ← canonicalStoreSpatialAtoms ops right
    return leftAtoms ++ rightAtoms
  let some unfolded ← unfoldStoreForInspection? ops expression | return []
  let some (_, spatial) ← matchBinary ops.andp unfolded | return []
  return [spatial]

private def asForwardEntailment (ops : Ops) (proof : Expr) :
    MetaM (Expr × Expr × Expr) := do
  let proofType ← inferType proof
  if let some (left, right) ← matchBinary ops.derivable proofType then
    return (left, right, proof)
  if let some (left, right) ← matchBinary ops.logicEquiv proofType then
    let forward ← mkAppM ``Automation.logic_equiv_forward_rule
      #[ops.rules, left, right, proof]
    return (left, right, forward)
  throwError "expected an entailment or logic equivalence, got {proofType}"

private def applyOnLeft (ops : Ops) (goal : MVarId) (lemmaLeft lemmaRight
    lemmaProof goalLeft goalRight : Expr) : TacticM Unit := do
  let exposedState <- saveState
  let exposedGoalNorm <- normalizeExposedSepcon ops goalLeft
  let exposedLemmaNorm <- normalizeExposedSepcon ops lemmaLeft
  let exposedMatch <-
    selectUnifyingAtoms exposedLemmaNorm.atoms exposedGoalNorm.atoms
  let (preparedLeft, preparedProof, lemmaNorm, matched, rest, pureSideGoals,
      matchingGoalLeft, matchingGoalNorm, matchingGoalProof) ←
    match exposedMatch with
    | some (matched, rest) =>
        pure (lemmaLeft, lemmaProof, exposedLemmaNorm, matched, rest, [],
          goalLeft, exposedGoalNorm, <- derivableRefl ops goalLeft)
    | none => do
        restoreState exposedState
        let goalNorm <- normalizeExpression ops goalLeft
        let directNorm <- normalizeExpression ops lemmaLeft
        let directState <- saveState
        let directMatch <- selectUnifyingAtoms directNorm.atoms goalNorm.atoms
        match directMatch with
        | some (matched, rest) =>
            pure (lemmaLeft, lemmaProof, directNorm, matched, rest, [],
              goalLeft, goalNorm, <- derivableRefl ops goalLeft)
        | none => do
          restoreState directState
          let guardedState ← saveState
          match ← prepareGuardedStoreMatch ops lemmaLeft lemmaRight lemmaProof goalLeft with
          | some guarded =>
              pure (guarded.preparedLeft, guarded.preparedProof,
                guarded.lemmaNorm, guarded.matched, guarded.rest, [],
                goalLeft, guarded.goalNorm, ← derivableRefl ops goalLeft)
          | none => do
              restoreState guardedState
              let eliminatedGoal ← eliminateStoreGuards ops goalLeft
              let eliminatedGoalNorm ← normalizeExpression ops eliminatedGoal.expression
              let storeAtoms ← canonicalStoreSpatialAtoms ops lemmaLeft
              unless storeAtoms.isEmpty do
                let storesPresent ←
                  if storeAtoms.length > 1 then
                    let preUnifyState ← saveState
                    match ← selectUnifyingAtoms storeAtoms eliminatedGoalNorm.atoms with
                    | some _ => pure true
                    | none => restoreState preUnifyState; pure false
                  else
                    let preUnifyState ← saveState
                    let storesPresent ← preUnifyStoreAtoms storeAtoms eliminatedGoalNorm.atoms
                    restoreState preUnifyState
                    pure storesPresent
                unless storesPresent do
                  throwError "sep_apply_l_atomic: the lemma's store atoms are absent from the goal premise"
              let matchingGoal ←
                eliminateSelectedStoreGuards ops storeAtoms goalLeft
              let matchingGoalNorm ← normalizeExpression ops matchingGoal.expression
              let anchoredNorm ← normalizeExpression ops lemmaLeft
              let anchoredMatch ← selectUnifyingAtoms anchoredNorm.atoms goalNorm.atoms
              match anchoredMatch with
              | some (matched, rest) =>
                  pure (lemmaLeft, lemmaProof, anchoredNorm, matched, rest, [],
                    goalLeft, goalNorm, ← derivableRefl ops goalLeft)
              | none => do
                  let mixedState ← saveState
                  let preparedLemma ←
                    stripUnmatchedPureStoreGuards ops goalNorm.atoms directNorm.expression
                  let normalizedBackward ← mkAppM ``Automation.logic_equiv_backward_rule
                    #[ops.rules, lemmaLeft, directNorm.expression, directNorm.proof]
                  let preparedToOriginal ← derivableTrans ops preparedLemma.expression
                    directNorm.expression lemmaLeft preparedLemma.proof normalizedBackward
                  let preparedProof ← derivableTrans ops preparedLemma.expression lemmaLeft
                    lemmaRight preparedToOriginal lemmaProof
                  let lemmaNorm ← normalizeExpression ops preparedLemma.expression
                  let mixedMatch ← selectUnifyingAtoms lemmaNorm.atoms goalNorm.atoms
                  match mixedMatch with
                  | some (matched, rest) =>
                      pure (preparedLemma.expression, preparedProof, lemmaNorm,
                        matched, rest, preparedLemma.sideGoals,
                        goalLeft, goalNorm, ← derivableRefl ops goalLeft)
                  | none => do
                      restoreState mixedState
                      if ← hasConflictingStoreWrappers ops directNorm.atoms goalNorm.atoms then
                        throwError "sep_apply_l_atomic: incompatible typed store wrappers share the same spatial atom"
                      let preparedLemma ← stripKnownPureStoreGuards ops directNorm.expression
                      let normalizedBackward ← mkAppM
                        ``Automation.logic_equiv_backward_rule
                        #[ops.rules, lemmaLeft, directNorm.expression, directNorm.proof]
                      let preparedToOriginal ← derivableTrans ops preparedLemma.expression
                        directNorm.expression lemmaLeft preparedLemma.proof normalizedBackward
                      let preparedProof ← derivableTrans ops preparedLemma.expression lemmaLeft
                        lemmaRight preparedToOriginal lemmaProof
                      let lemmaNorm ← normalizeExpression ops preparedLemma.expression
                      let some (matched, rest) ←
                          selectUnifyingAtoms lemmaNorm.atoms matchingGoalNorm.atoms
                        | throwError "sep_apply_l_atomic: the lemma's left-hand side is absent from the goal premise"
                      pure (preparedLemma.expression, preparedProof, lemmaNorm,
                        matched, rest, preparedLemma.sideGoals,
                        matchingGoal.expression, matchingGoalNorm, matchingGoal.proof)
  let pureSideGoals ← dischargeLocalPureSideGoals pureSideGoals
  let desired := matched ++ rest
  let (goalEquiv, liftedAtoms) <-
    normalizedLiftPrefix ops matchingGoalLeft matchingGoalNorm matched
  unless liftedAtoms.length == desired.length do
    throwError "internal error: lifted sepcon frame has the wrong length"
  let goalForward ← mkAppM ``Automation.logic_equiv_forward_rule
    #[ops.rules, matchingGoalLeft, foldAtoms ops desired, goalEquiv]
  let preparedGoalForward ← derivableTrans ops goalLeft matchingGoalLeft
    (foldAtoms ops desired) matchingGoalProof goalForward
  let lemmaBackward ← mkAppM ``Automation.logic_equiv_backward_rule
    #[ops.rules, preparedLeft, lemmaNorm.expression, lemmaNorm.proof]
  let normalizedLemma ← derivableTrans ops lemmaNorm.expression
    preparedLeft lemmaRight lemmaBackward preparedProof
  let (newLeft, rewriteStep) ← match rest with
    | [] => pure (lemmaRight, normalizedLemma)
    | _ => do
        let restExpr := foldAtoms ops rest
        let grouped := mkApp2 ops.sepcon lemmaNorm.expression restExpr
        let appended ← appendProof ops lemmaNorm.atoms rest
        let groupedToFlat := appended
        let flatToGrouped ← equivSymm ops grouped (foldAtoms ops desired)
          groupedToFlat
        let regroup ← mkAppM ``Automation.logic_equiv_forward_rule
          #[ops.rules, foldAtoms ops desired, grouped, flatToGrouped]
        let lifted ← derivableSepconMono ops lemmaNorm.expression lemmaRight
          restExpr restExpr normalizedLemma (← derivableRefl ops restExpr)
        let next := mkApp2 ops.sepcon lemmaRight restExpr
        pure (next, ← derivableTrans ops (foldAtoms ops desired) grouped next
          regroup lifted)
  let preProof ← derivableTrans ops goalLeft (foldAtoms ops desired) newLeft
    preparedGoalForward rewriteStep
  let residualType := mkApp2 ops.derivable newLeft goalRight
  let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
  let proof ← derivableTrans ops goalLeft newLeft goalRight preProof residual
  unless ← isDefEqProofType (← inferType proof) (← goal.getType) do
    throwError "internal error: left spatial application proof does not match the goal"
  goal.assign proof
  replaceMainGoal (residual.mvarId! :: pureSideGoals)

private partial def buildRightRewrite (ops : Ops) (lemmaLeft lemmaRight
    lemmaProof expression : Expr) : MetaM (Option (Expr × Expr)) := do
  let lemmaNorm ← normalizeExpression ops lemmaRight
  let goalNorm ← normalizeExpression ops expression
  if let some (matched, rest) ←
      selectUnifyingAtoms lemmaNorm.atoms goalNorm.atoms then
    let desired := matched ++ rest
    let goalEquiv ← normalizedTo ops expression goalNorm desired
    let goalBackward ← mkAppM ``Automation.logic_equiv_backward_rule
      #[ops.rules, expression, foldAtoms ops desired, goalEquiv]
    let lemmaForward ← mkAppM ``Automation.logic_equiv_forward_rule
      #[ops.rules, lemmaRight, lemmaNorm.expression, lemmaNorm.proof]
    let normalizedLemma ← derivableTrans ops lemmaLeft lemmaRight
      lemmaNorm.expression lemmaProof lemmaForward
    let (newRight, rewriteStep) ← match rest with
      | [] => pure (lemmaLeft, normalizedLemma)
      | _ => do
          let restExpr := foldAtoms ops rest
          let next := mkApp2 ops.sepcon lemmaLeft restExpr
          let grouped := mkApp2 ops.sepcon lemmaNorm.expression restExpr
          let lifted ← derivableSepconMono ops lemmaLeft lemmaNorm.expression
            restExpr restExpr normalizedLemma (← derivableRefl ops restExpr)
          let appended ← appendProof ops lemmaNorm.atoms rest
          let appendedForward ← mkAppM ``Automation.logic_equiv_forward_rule
            #[ops.rules, grouped, foldAtoms ops desired, appended]
          pure (next, ← derivableTrans ops next grouped (foldAtoms ops desired)
            lifted appendedForward)
    let suffix ← derivableTrans ops newRight (foldAtoms ops desired) expression
      rewriteStep goalBackward
    return some (newRight, suffix)
  if let some (left, right) ← matchBinary ops.andp expression then
    let saved ← saveState
    if let some (newLeft, leftProof) ←
        buildRightRewrite ops lemmaLeft lemmaRight lemmaProof left then
      let proof ← derivableAndpMono ops newLeft left right right leftProof
        (← derivableRefl ops right)
      return some (mkApp2 ops.andp newLeft right, proof)
    restoreState saved
    if let some (newRight, rightProof) ←
        buildRightRewrite ops lemmaLeft lemmaRight lemmaProof right then
      let proof ← derivableAndpMono ops left left newRight right
        (← derivableRefl ops left) rightProof
      return some (mkApp2 ops.andp left newRight, proof)
    restoreState saved
  return none

private def applyOnRight (ops : Ops) (goal : MVarId) (lemmaLeft lemmaRight
    lemmaProof goalLeft goalRight : Expr) : TacticM Unit := do
  let some (newRight, suffix) ←
      buildRightRewrite ops lemmaLeft lemmaRight lemmaProof goalRight
    | throwError "sep_apply_r_atomic: the lemma's right-hand side is absent from the goal conclusion"
  let residualType := mkApp2 ops.derivable goalLeft newRight
  let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
  let proof ← derivableTrans ops goalLeft newRight goalRight residual suffix
  unless ← isDefEqProofType (← inferType proof) (← goal.getType) do
    throwError "internal error: right spatial application proof does not match the goal"
  goal.assign proof
  replaceMainGoal [residual.mvarId!]

private def elaborateRule (rule : Syntax) : TacticM Expr := do
  let proof ← Lean.Elab.Tactic.elabTermForApply rule
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

private partial def consumeAtomicRuleArguments (ops : Ops) (proof : Expr)
    (continuation : Expr → TacticM Unit) : TacticM Unit := do
  let proofType ← inferType proof
  match proofType.consumeMData with
  | .forallE name domain _ _ =>
      if ← isProp domain then
        let goal ← getMainGoal
        let target ← goal.getType
        let some (goalLeft, goalRight) ← matchBinary ops.derivable target
          | throwError "sep_apply: a proposition premise can only be consumed on an entailment goal"
        let pureAssertion := mkApp ops.coqProp domain
        let pureGoalType := mkApp2 ops.derivable goalLeft pureAssertion
        let pureGoal ← mkFreshExprSyntheticOpaqueMVar pureGoalType (← goal.getTag)
        withLocalDeclD name domain fun premise => do
          let innerGoal ← mkFreshExprSyntheticOpaqueMVar target (← goal.getTag)
          let body ← mkLambdaFVars #[premise] innerGoal
          let restProof ← mkAppM ``coq_prop_andp_left
            #[ops.rules, domain, goalLeft, goalRight, body]
          let combined ← mkAppM ``add_pure_split
            #[ops.rules, domain, goalLeft, goalRight, pureGoal, restProof]
          goal.assign combined
          replaceMainGoal [innerGoal.mvarId!]
          consumeAtomicRuleArguments ops (mkApp proof premise) continuation
          let remaining ← getGoals
          replaceMainGoal (pureGoal.mvarId! :: remaining)
      else
        continuation proof
  | _ => continuation proof

private partial def specializeLegacyRule (proof : Expr)
    (sideGoals : List MVarId := []) : TacticM (Expr × List MVarId) := do
  let proofType ← inferType proof
  match proofType.consumeMData with
  | .forallE _ domain _ _ =>
      if ← isProp domain then
        let premise ← mkFreshExprSyntheticOpaqueMVar domain
        specializeLegacyRule (mkApp proof premise) (premise.mvarId! :: sideGoals)
      else
        let argument ← mkFreshExprMVar domain
        specializeLegacyRule (mkApp proof argument) sideGoals
  | _ => return (proof, sideGoals)

private def consumeLegacyRuleArguments (proof : Expr)
    (continuation : Expr → TacticM Unit) : TacticM Unit := do
  let (specialized, sideGoals) ← specializeLegacyRule proof
  continuation specialized
  let remaining ← getGoals
  replaceMainGoal (remaining ++ sideGoals)

private def runSepApplyProof (ops : Ops) (ruleProof : Expr)
    (onLeft : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (goalLeft, goalRight) ← matchBinary ops.derivable target
    | throwError "sep_apply: goal is not a separation-logic entailment"
  let (lemmaLeft, lemmaRight, lemmaProof) ←
    asForwardEntailment ops ruleProof
  if onLeft then
    applyOnLeft ops goal lemmaLeft lemmaRight lemmaProof goalLeft goalRight
  else
    applyOnRight ops goal lemmaLeft lemmaRight lemmaProof goalLeft goalRight

def runSepApplyAtomic (rule : Syntax) (onLeft : Bool) : TacticM Unit := withMainContext do
  let ops ← getOps
  let ruleProof ← elaborateRule rule
  consumeAtomicRuleArguments ops ruleProof fun specialized =>
    runSepApplyProof ops specialized onLeft

def runSepApply (rule : Syntax) (onLeft : Bool) : TacticM Unit := withMainContext do
  let ops ← getOps
  let ruleProof ← elaborateRule rule
  consumeLegacyRuleArguments ruleProof fun specialized =>
    runSepApplyProof ops specialized onLeft

private structure CollapsedPure where
  proposition : Expr
  assertion : Expr
  proof : Expr

private partial def collapsePureAssertion (ops : Ops) (expression : Expr) :
    MetaM CollapsedPure := do
  if let some proposition ← matchUnary ops.coqProp expression then
    return {
      proposition
      assertion := expression
      proof := ← equivRefl ops expression
    }
  let some (left, right) ← matchBinary ops.andp expression
    | throwError "prop_apply: lemma conclusion is not a conjunction of lifted Coq propositions"
  let leftCollapsed ← collapsePureAssertion ops left
  let rightCollapsed ← collapsePureAssertion ops right
  let combined := mkApp2 ops.andp leftCollapsed.assertion rightCollapsed.assertion
  let congruence ← mkAppM ``Automation.logic_equiv_andp_mono_rule
    #[ops.rules, left, leftCollapsed.assertion, right, rightCollapsed.assertion,
      leftCollapsed.proof, rightCollapsed.proof]
  let proposition := mkApp2 (mkConst ``And) leftCollapsed.proposition
    rightCollapsed.proposition
  let assertion := mkApp ops.coqProp proposition
  let expanded ← mkAppM ``Automation.logic_equiv_coq_prop_and_rule
    #[ops.rules, leftCollapsed.proposition, rightCollapsed.proposition]
  let collapsed ← equivSymm ops assertion combined expanded
  return {
    proposition
    assertion
    proof := ← equivTrans ops expression combined assertion congruence collapsed
  }

private def runPropApplyProof (ops : Ops) (ruleProof : Expr) :
    TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (goalLeft, goalRight) ← matchBinary ops.derivable target
    | throwError "prop_apply: goal is not a separation-logic entailment"
  let (lemmaLeft, sourcePureAssertion, sourceLemmaProof) ←
    asForwardEntailment ops ruleProof
  let collapsed ← collapsePureAssertion ops sourcePureAssertion
  let collapseForward ← mkAppM ``Automation.logic_equiv_forward_rule
    #[ops.rules, sourcePureAssertion, collapsed.assertion, collapsed.proof]
  let lemmaProof ← derivableTrans ops lemmaLeft sourcePureAssertion
    collapsed.assertion sourceLemmaProof collapseForward
  let equivalence ← mkAppM ``prop_add_left
    #[ops.rules, lemmaLeft, collapsed.proposition, lemmaProof]
  let enriched := mkApp2 ops.andp collapsed.assertion lemmaLeft
  let forward ← mkAppM ``Automation.logic_equiv_forward_rule
    #[ops.rules, lemmaLeft, enriched, equivalence]
  applyOnLeft ops goal lemmaLeft enriched forward goalLeft goalRight

def runPropApply (rule : Syntax) : TacticM Unit := withMainContext do
  evalTactic (← `(tactic| pureIntros_without_rename))
  let ops ← getOps
  let ruleProof ← elaborateRule rule
  consumeLegacyRuleArguments ruleProof fun specialized =>
    runPropApplyProof ops specialized

def runPropApplyInstantiated (rule : Syntax) : TacticM Unit := withMainContext do
  evalTactic (← `(tactic| pureIntros_without_rename))
  let ops ← getOps
  let ruleProof ← elaborateRule rule
  runPropApplyProof ops ruleProof

private partial def isPureAssertion (ops : Ops) (expression : Expr) : MetaM Bool := do
  if (← matchUnary ops.coqProp expression).isSome then
    pure true
  else if let some (left, right) ← matchBinary ops.andp expression then
    pure ((← isPureAssertion ops left) && (← isPureAssertion ops right))
  else
    pure false

private partial def containsNoPureAssertion (ops : Ops) (expression : Expr) : MetaM Bool := do
  if (← matchUnary ops.coqProp expression).isSome then
    pure false
  else if let some (left, right) ← matchBinary ops.sepcon expression then
    pure ((← containsNoPureAssertion ops left) &&
      (← containsNoPureAssertion ops right))
  else if let some (left, right) ← matchBinary ops.andp expression then
    pure ((← containsNoPureAssertion ops left) &&
      (← containsNoPureAssertion ops right))
  else
    pure true

def runSplitPureSpatial : TacticM Unit := withMainContext do
  let ops ← getOps
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, right) ← matchBinary ops.derivable target
    | throwError "split_pure_spatial: goal is not a separation-logic entailment"
  let some (first, second) ← matchBinary ops.andp right
    | throwError "split_pure_spatial: RHS must be (pure && spatial) or (spatial && pure)"
  if (← isPureAssertion ops first) && (← containsNoPureAssertion ops second) then
    evalTactic (← `(tactic| apply split_pure_and_spatial_goals))
  else if (← isPureAssertion ops second) &&
      (← containsNoPureAssertion ops first) then
    evalTactic (← `(tactic| apply split_spatial_and_pure_goals))
  else
    throwError "split_pure_spatial: RHS must contain one pure and one spatial part"

def runSplitPuresStep : TacticM Unit := withMainContext do
  let ops ← getOps
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, right) ← matchBinary ops.derivable target
    | throwError "split_pures: goal is not a separation-logic entailment"
  let some (first, second) ← matchBinary ops.andp right
    | throwError "split_pures: RHS is not a conjunction"
  unless (← isPureAssertion ops first) && (← isPureAssertion ops second) do
    throwError "split_pures: RHS conjunction is not entirely pure"
  evalTactic (← `(tactic| apply _derivable1_andp_intros))

partial def leftAssociateAndpRhs : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  let some (left, right) ← matchBinary ops.derivable target | return
  let some (first, rest) ← matchBinary ops.andp right | return
  let some (second, third) ← matchBinary ops.andp rest | return
  let associated := mkApp2 ops.andp (mkApp2 ops.andp first second) third
  let residualType := mkApp2 ops.derivable left associated
  let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
  let equivalence ← mkAppM ``Automation.logic_equiv_andp_assoc_rule
    #[ops.rules, first, second, third]
  let forward ← mkAppM ``Automation.logic_equiv_forward_rule
    #[ops.rules, associated, right, equivalence]
  let proof ← derivableTrans ops left associated right residual forward
  unless ← isDefEqProofType (← inferType proof) target do
    throwError "internal error: andp reassociation proof does not match the goal"
  goal.assign proof
  replaceMainGoal [residual.mvarId!]
  leftAssociateAndpRhs

partial def rightAssociateSepconLhs : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  let some (left, right) ← matchBinary ops.derivable target | return
  let some (grouped, third) ← matchBinary ops.sepcon left | return
  let some (first, second) ← matchBinary ops.sepcon grouped | return
  let associated := mkApp2 ops.sepcon first (mkApp2 ops.sepcon second third)
  let residualType := mkApp2 ops.derivable associated right
  let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
  let equivalence ← mkAppM ``Automation.logic_equiv_sepcon_assoc_rule
    #[ops.rules, first, second, third]
  let prefixProof ← mkAppM ``Automation.logic_equiv_backward_rule
    #[ops.rules, associated, left, equivalence]
  let proof ← derivableTrans ops left associated right prefixProof residual
  unless ← isDefEqProofType (← inferType proof) target do
    throwError "internal error: sepcon reassociation proof does not match the goal"
  goal.assign proof
  replaceMainGoal [residual.mvarId!]
  rightAssociateSepconLhs

private partial def normalizeSepconAssociativity (ops : Ops)
    (expression : Expr) : MetaM (Expr × Expr) := do
  let expression ← instantiateMVars expression
  let expression := expression.headBeta
  if let some (left, right) ← matchBinary ops.sepcon expression then
    let (newLeft, leftProof) ← normalizeSepconAssociativity ops left
    let (newRight, rightProof) ← normalizeSepconAssociativity ops right
    let combined := mkApp2 ops.sepcon newLeft newRight
    let congruence ← equivSepconMono ops left newLeft right newRight
      leftProof rightProof
    let normalized ← normalizeExpression ops combined
    let proof ← equivTrans ops expression combined normalized.expression
      congruence normalized.proof
    return (normalized.expression, proof)
  if let some (left, right) ← matchBinary ops.andp expression then
    let (newLeft, leftProof) ← normalizeSepconAssociativity ops left
    let (newRight, rightProof) ← normalizeSepconAssociativity ops right
    let proof ← equivAndpMono ops left newLeft right newRight
      leftProof rightProof
    return (mkApp2 ops.andp newLeft newRight, proof)
  if let some (left, right) ← matchBinary ops.orp expression then
    let (newLeft, leftProof) ← normalizeSepconAssociativity ops left
    let (newRight, rightProof) ← normalizeSepconAssociativity ops right
    let proof ← mkAppM ``Automation.logic_equiv_orp_mono_rule
      #[ops.rules, left, newLeft, right, newRight, leftProof, rightProof]
    return (mkApp2 ops.orp newLeft newRight, proof)
  if let some (left, right) ← matchBinary ops.wand expression then
    let (newLeft, leftProof) ← normalizeSepconAssociativity ops left
    let (newRight, rightProof) ← normalizeSepconAssociativity ops right
    let proof ← mkAppM ``Automation.logic_equiv_wand_mono_rule
      #[ops.rules, left, newLeft, right, newRight, leftProof, rightProof]
    return (mkApp2 ops.wand newLeft newRight, proof)
  if let some (left, right) ← matchBinary ops.impp expression then
    let (newLeft, leftProof) ← normalizeSepconAssociativity ops left
    let (newRight, rightProof) ← normalizeSepconAssociativity ops right
    let proof ← mkAppM ``Automation.logic_equiv_impp_mono_rule
      #[ops.rules, left, newLeft, right, newRight, leftProof, rightProof]
    return (mkApp2 ops.impp newLeft newRight, proof)
  if let some (left, right) ← matchBinary ops.iffp expression then
    let (newLeft, leftProof) ← normalizeSepconAssociativity ops left
    let (newRight, rightProof) ← normalizeSepconAssociativity ops right
    let proof ← mkAppM ``Automation.logic_equiv_iffp_mono_rule
      #[ops.rules, left, newLeft, right, newRight, leftProof, rightProof]
    return (mkApp2 ops.iffp newLeft newRight, proof)
  if let some (witnessType, predicate) ← matchBinary ops.exp expression then
    return ← withLocalDecl `_x .default witnessType fun witness => do
      let (newBody, bodyProof) ←
        normalizeSepconAssociativity ops (mkApp predicate witness)
      let newPredicate ← mkLambdaFVars #[witness] newBody
      let proofFamily ← mkLambdaFVars #[witness] bodyProof
      let proof ← mkAppOptM ``Automation.logic_equiv_exp_rule
        #[some ops.rules, some witnessType, some predicate,
          some newPredicate, some proofFamily]
      return (mkApp2 ops.exp witnessType newPredicate, proof)
  if let some (witnessType, predicate) ← matchBinary ops.allp expression then
    return ← withLocalDecl `_x .default witnessType fun witness => do
      let (newBody, bodyProof) ←
        normalizeSepconAssociativity ops (mkApp predicate witness)
      let newPredicate ← mkLambdaFVars #[witness] newBody
      let proofFamily ← mkLambdaFVars #[witness] bodyProof
      let proof ← mkAppOptM ``Automation.logic_equiv_allp_rule
        #[some ops.rules, some witnessType, some predicate,
          some newPredicate, some proofFamily]
      return (mkApp2 ops.allp witnessType newPredicate, proof)
  return (expression, ← equivRefl ops expression)

def rightAssociateSepconGoal : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  if let some (left, right) ← matchBinary ops.derivable target then
    let (newLeft, leftEquiv) ← normalizeSepconAssociativity ops left
    let (newRight, rightEquiv) ← normalizeSepconAssociativity ops right
    if left == newLeft && right == newRight then
      return
    let residualType := mkApp2 ops.derivable newLeft newRight
    let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
    let leftForward ← mkAppM ``Automation.logic_equiv_forward_rule
      #[ops.rules, left, newLeft, leftEquiv]
    let rightBackward ← mkAppM ``Automation.logic_equiv_backward_rule
      #[ops.rules, right, newRight, rightEquiv]
    let firstProof ← derivableTrans ops left newLeft newRight
      leftForward residual
    let proof ← derivableTrans ops left newRight right
      firstProof rightBackward
    unless ← isDefEqProofType (← inferType proof) target do
      throwError "internal error: sepcon association proof does not match the goal"
    goal.assign proof
    replaceMainGoal [residual.mvarId!]
    return
  if let some (left, right) ← matchBinary ops.logicEquiv target then
    let (newLeft, leftEquiv) ← normalizeSepconAssociativity ops left
    let (newRight, rightEquiv) ← normalizeSepconAssociativity ops right
    if left == newLeft && right == newRight then
      return
    let residualType := mkApp2 ops.logicEquiv newLeft newRight
    let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
    let firstProof ← equivTrans ops left newLeft newRight leftEquiv residual
    let rightBackward ← equivSymm ops right newRight rightEquiv
    let proof ← equivTrans ops left newRight right firstProof rightBackward
    unless ← isDefEqProofType (← inferType proof) target do
      throwError "internal error: sepcon association proof does not match the goal"
    goal.assign proof
    replaceMainGoal [residual.mvarId!]

def splitOnePreprocessedPureGoal : TacticM Bool := withMainContext do
  leftAssociateAndpRhs
  let ops ← getOps
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, right) ← matchBinary ops.derivable target | return false
  let some (first, second) ← matchBinary ops.andp right | return false
  let firstPure ← isPureAssertion ops first
  let secondPure ← isPureAssertion ops second
  if firstPure && secondPure then
    runSplitPuresStep
    return true
  else if (firstPure && (← containsNoPureAssertion ops second)) ||
      (secondPure && (← containsNoPureAssertion ops first)) then
    runSplitPureSpatial
    return true
  else
    return false

def runDumpEmptyPreSpatial : TacticM Unit := withMainContext do
  let ops ← getOps
  let target ← (← getMainGoal).getType
  let some (left, right) ← matchBinary ops.derivable target
    | throwError "dump_pre_spatial: goal is not a separation-logic entailment"
  unless ← defEqLogicalConstantNoCommit left ops.emp do
    throwError "dump_pre_spatial: aggressive fallback requires an empty spatial premise"
  unless (← matchUnary ops.coqProp right).isSome do
    throwError "dump_pre_spatial: goal conclusion is not a lifted proposition"
  evalTactic (← `(tactic| apply dump_spatial_left))

def closeAggressiveTrivial : TacticM Unit := withMainContext do
  let ops ← getOps
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let some (left, right) ← matchBinary ops.derivable target
    | throwError "aggressive_pre_process: current goal is not an entailment"
  if ← defEqNoCommit left right then
    evalTactic (← `(tactic| exact SacContext.rules.toContext.derivable1_refl _))
    return
  unless (← matchUnary ops.coqProp right).isSome do
    throwError "aggressive_pre_process: entailment is neither reflexive nor directly pure"
  evalTactic (← `(tactic| apply dump_spatial_left; assumption))

private def dumpPureConclusion : TacticM Bool := withMainContext do
  let ops ← getOps
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let some (left, right) ← matchBinary ops.derivable target | return false
  unless (← matchUnary ops.coqProp right).isSome do
    return false
  unless ← containsNoPureAssertion ops left do
    return false
  evalTactic (← `(tactic| apply dump_spatial_left))
  return true

private def runEExistsWithWitness (witness : Expr) : TacticM Unit :=
    withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  let some (left, right) ← matchBinary ops.derivable target
    | throwError "eExists: goal is not a separation-logic entailment"
  let some (_, predicate) ← matchBinary ops.exp right
    | throwError "eExists: right-hand side is not existential"
  let body := mkApp predicate witness
  let residualType := mkApp2 ops.derivable left body
  let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
  let proof ← mkAppM ``Automation.exp_right_rule #[witness, residual]
  unless ← isDefEqProofType (← inferType proof) target do
    throwError "internal error: eExists proof does not match the goal"
  goal.assign proof
  replaceMainGoal [residual.mvarId!]

def runEExists : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  let some (_, right) ← matchBinary ops.derivable target
    | throwError "eExists: goal is not a separation-logic entailment"
  let some (witnessType, _) ← matchBinary ops.exp right
    | throwError "eExists: right-hand side is not existential"
  let witness ← mkFreshExprSyntheticOpaqueMVar witnessType (← goal.getTag)
  runEExistsWithWitness witness

private def isKnownAssertionForm (ops : Ops) (expression : Expr) : MetaM Bool := do
  if (matchBinarySyntactic ops.sepcon expression).isSome then return true
  if (matchBinarySyntactic ops.andp expression).isSome then return true
  if (matchBinarySyntactic ops.orp expression).isSome then return true
  if (matchBinarySyntactic ops.wand expression).isSome then return true
  if (matchBinarySyntactic ops.impp expression).isSome then return true
  if (matchBinarySyntactic ops.exp expression).isSome then return true
  if (matchBinarySyntactic ops.allp expression).isSome then return true
  if (matchUnarySyntactic ops.coqProp expression).isSome then return true
  if ← defEqLogicalConstantNoCommit expression ops.emp then return true
  defEqLogicalConstantNoCommit expression ops.truep

private def matchLogicalBinderAfterUserUnfold (ops : Ops) (binder : Expr) :
    Expr → Nat → MetaM (Option (Expr × Expr))
  | expression, 0 => matchBinary binder expression
  | expression, fuel + 1 => do
      if let some result ← matchBinary binder expression then
        return some result
      if ← isKnownAssertionForm ops expression then
        return none
      let some unfolded ← unfoldDefinition? expression | return none
      matchLogicalBinderAfterUserUnfold ops binder unfolded fuel

def introduceExpLeft (userName : Name) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  let some (left, right) ← matchBinary ops.derivable target | return false
  let some (witnessType, predicate) ←
      matchLogicalBinderAfterUserUnfold ops ops.exp left 32 | return false
  withLocalDecl userName .default witnessType fun witness => do
    let residualType := mkApp2 ops.derivable (mkApp predicate witness) right
    let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
    let body ← mkLambdaFVars #[witness] residual
    let proof ← mkAppM ``Automation.exp_left_rule #[body]
    unless ← isDefEq (← inferType proof) target do
      throwError "internal error: Intros proof does not match the goal"
    goal.assign proof
    replaceMainGoal [residual.mvarId!]
    return true

def introduceExpSepconLeft (userName : Name) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  let some (left, right) ← matchBinary ops.derivable target
    | return false
  let some (first, rest) ← matchBinary ops.sepcon left
    | return false
  let some (witnessType, predicate) ←
      matchLogicalBinderAfterUserUnfold ops ops.exp first 32 | return false
  withLocalDecl userName .default witnessType fun witness => do
    let bodyAssertion := mkApp2 ops.sepcon (mkApp predicate witness) rest
    let liftedPredicate ← mkLambdaFVars #[witness] bodyAssertion
    let liftedExp := mkApp2 ops.exp witnessType liftedPredicate
    let residualType := mkApp2 ops.derivable bodyAssertion right
    let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
    let residualBody ← mkLambdaFVars #[witness] residual
    let expProof ← mkAppM ``Automation.exp_left_rule #[residualBody]
    let equivalence ← mkAppM ``ex_logic_equiv_sepcon
      #[ops.rules, predicate, rest]
    let prefixProof ← mkAppM ``Automation.logic_equiv_forward_rule
      #[ops.rules, left, liftedExp, equivalence]
    let proof ← derivableTrans ops left liftedExp right prefixProof expProof
    unless ← isDefEq (← inferType proof) target do
      throwError "internal error: Intros sepcon proof does not match the goal"
    goal.assign proof
    replaceMainGoal [residual.mvarId!]
    return true

def introduceExpLeftStructural (userName : Name) : TacticM Bool := do
  rightAssociateSepconLhs
  if ← introduceExpLeft userName then
    return true
  introduceExpSepconLeft userName

def introduceAllpRight (userName : Name) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  let some (left, right) ← matchBinary ops.derivable target | return false
  let some (witnessType, predicate) ←
      matchLogicalBinderAfterUserUnfold ops ops.allp right 32 | return false
  withLocalDecl userName .default witnessType fun witness => do
    let residualType := mkApp2 ops.derivable left (mkApp predicate witness)
    let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
    let body ← mkLambdaFVars #[witness] residual
    let proof ← mkAppM ``Automation.allp_right_rule #[body]
    unless ← isDefEq (← inferType proof) target do
      throwError "internal error: Intros_r proof does not match the goal"
    goal.assign proof
    replaceMainGoal [residual.mvarId!]
    return true

def rhsStartsWithExp : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let ops ← getOps
  let some (_, right) ← matchBinary ops.derivable target | return false
  return (← matchBinary ops.exp right).isSome

def closeSyntacticReflexiveEntailment : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let ops ← getOps
  let some (left, right) ← matchBinary ops.derivable target | return false
  unless left == right do
    return false
  evalTactic (← `(tactic|
    exact SacContext.rules.toContext.derivable1_refl _))
  return true

end SpatialAutomation

syntax "set_String_name" : tactic
syntax "subst_all_strings" : tactic
syntax "poly_store_unfold" : tactic
syntax "TT_simpl" : tactic
syntax "andp_assoc_change" : tactic
syntax "sepcon_assoc_change" : tactic
syntax "coq_prop_lift" : tactic
syntax "asrt_easysimpl" : tactic
syntax "asrt_complex_simpl" : tactic
syntax "asrt_simpl_pure" : tactic
syntax "asrt_simpl" : tactic
syntax "pureIntros" : tactic
syntax "unfold_arch" : tactic
syntax "fold_arch" : tactic
syntax "solve_arch" : tactic
syntax "simpl_auto_with " "(" tacticSeq ")" : tactic
syntax "simpl_auto" : tactic
syntax "simpl_entail_with " "(" tacticSeq ")" : tactic
syntax "simpl_entail" : tactic
syntax "andp_cancel" : tactic
syntax "_andp_cancel_core" : tactic
syntax "entailer_pure" : tactic
syntax "entailer_with " "(" tacticSeq ")" : tactic
syntax "entailer!" : tactic
syntax "normalize" : tactic
syntax "Intro_any" : tactic
syntax "Intros_r_any" : tactic
syntax "eExists" : tactic
syntax "Left" : tactic
syntax "Right" : tactic
syntax "Split" : tactic
syntax "elim_emp" : tactic
syntax "wand_elim" : tactic
syntax "pre_process_pure" : tactic
syntax "LLM_pre_process_tac " "(" tacticSeq ")" : tactic
syntax "LLM_pre_process " "(" tacticSeq ")" : tactic
syntax "pre_process" : tactic
syntax "pre_process_default" : tactic
syntax "dump_pre_spatial" : tactic
syntax "split_pure_spatial" : tactic
syntax "split_pures" : tactic
syntax "split_pure_and_solve" : tactic
syntax "aggressive_pre_process" : tactic
syntax "_split_pures_step" : tactic
syntax "_dump_empty_pre_spatial" : tactic
syntax "_close_aggressive_trivial" : tactic
syntax "_cancel_progress" : tactic
syntax "_split_preprocessed_pure" : tactic
syntax "_unfold_goal_head" : tactic
syntax "_sac_normalize" : tactic
syntax "_sac_normalize_stores" : tactic
syntax "_dump_pure_right" : tactic
syntax "_int_nia_compat" : tactic
syntax "_sac_unfold_transparent" : tactic
syntax "_andp_split_right" : tactic
syntax "_andp_use_left" : tactic
syntax "_andp_use_right" : tactic
syntax "_split_prop_and" : tactic
syntax "_empty_resource_cleanup" : tactic
syntax (name := sac_empty_resource) "sac_empty_resource " ident ident num : attr

namespace SpatialAutomation

open Lean Meta Elab Tactic

inductive EmptyResourceShape where
  | emptyList
  | sameLastTwo
  | zeroLast
  deriving Inhabited, BEq, Repr

structure EmptyResourceRule where
  head : Name
  shape : EmptyResourceShape
  theoremName : Name
  explicitArity : Nat
  deriving Inhabited, BEq, Repr

private def parseEmptyResourceShape (stx : Syntax) :
    AttrM EmptyResourceShape :=
  match stx.getId with
  | `emptyList => pure .emptyList
  | `sameLastTwo => pure .sameLastTwo
  | `zeroLast => pure .zeroLast
  | _ =>
      throwErrorAt stx
        "unknown empty-resource shape; expected emptyList, sameLastTwo, or zeroLast"

private def parseEmptyResourceRuleAttr
    (theoremName : Name) (stx : Syntax) : AttrM EmptyResourceRule := do
  match stx with
  | `(attr| sac_empty_resource $head:ident $shape:ident $arity:num) => do
      let headName ← realizeGlobalConstNoOverloadWithInfo head
      let shape ← parseEmptyResourceShape shape
      let some explicitArity := arity.raw.isNatLit?
        | throwErrorAt arity "expected a natural-number arity"
      unless explicitArity > 0 do
        throwErrorAt arity "empty-resource rule arity must be positive"
      return {
        head := headName
        shape
        theoremName
        explicitArity
      }
  | _ => throwUnsupportedSyntax

initialize emptyResourceRuleAttr : ParametricAttribute EmptyResourceRule ←
  registerParametricAttribute {
    name := `sac_empty_resource
    descr :=
      "Register a theorem as a conservative empty-resource cleanup rule for entailer!."
    getParam := parseEmptyResourceRuleAttr
  }

private def registeredEmptyResourceRules (env : Environment) :
    Array EmptyResourceRule := Id.run do
  let state := emptyResourceRuleAttr.ext.toEnvExtension.getState env
  let mut result := #[]
  for importedEntries in state.importedEntries do
    for (_, rule) in importedEntries do
      result := result.push rule
  let (decls, rulesByName) := state.state
  for theoremName in decls.reverse do
    if let some rule := rulesByName.find? theoremName then
      result := result.push rule
  result

private def ofNatValue? (expr : Expr) : Option Nat :=
  if expr.getAppFn.isConstOf ``OfNat.ofNat then
    let args := expr.getAppArgs
    if args.size >= 2 then args[args.size - 2]!.rawNatLit? else none
  else
    none

private def matchesEmptyResourceShape
    (expr : Expr) (name : Name) (shape : EmptyResourceShape) : Bool :=
  if !expr.getAppFn.isConstOf name then
    false
  else
    let args := expr.getAppArgs
    if args.isEmpty then
      false
    else
      let last := args[args.size - 1]!
      match shape with
      | .emptyList => last.getAppFn.isConstOf ``List.nil
      | .sameLastTwo =>
          args.size >= 2 && args[args.size - 2]! == last
      | .zeroLast => ofNatValue? last == some 0

private def firstSome {α : Type} : List (MetaM (Option α)) -> MetaM (Option α)
  | [] => pure none
  | action :: rest => do
      match ← action with
      | some value => pure (some value)
      | none => firstSome rest

private partial def findEmptyResourceMatch?
    (target : Expr) (name : Name) (shape : EmptyResourceShape) :
    MetaM (Option Expr) := do
  let target ←
    match ← withTransparency .reducible <| unfoldDefinition? target with
    | some unfolded => pure unfolded
    | none => pure target
  if matchesEmptyResourceShape target name shape then
    pure (some target)
  else
    match target with
    | .app fn arg =>
        firstSome [findEmptyResourceMatch? fn name shape,
          findEmptyResourceMatch? arg name shape]
    | .lam _ type body _ | .forallE _ type body _ =>
        firstSome [findEmptyResourceMatch? type name shape,
          findEmptyResourceMatch? body name shape]
    | .letE _ type value body _ =>
        firstSome [findEmptyResourceMatch? type name shape,
          findEmptyResourceMatch? value name shape,
          findEmptyResourceMatch? body name shape]
    | .mdata _ body | .proj _ _ body => findEmptyResourceMatch? body name shape
    | _ => pure none

private def explicitEmptyResourceArgs (expr : Expr) (arity : Nat) :
    MetaM (Array Expr) := do
  let args := expr.getAppArgs
  if args.size < arity then
    throwError
      "empty-resource rule arity {arity} exceeds matched argument count {args.size}"
  return args.extract (args.size - arity) args.size

private def buildEmptyResourceRule
    (branch : EmptyResourceRule) (matched : Expr) : MetaM Expr := do
  if matched.hasLooseBVars then
    return ← mkConstWithFreshMVarLevels branch.theoremName
  let args ← explicitEmptyResourceArgs matched branch.explicitArity
  let theoremArgs := match branch.shape with
    | .emptyList | .sameLastTwo | .zeroLast => args.extract 0 (args.size - 1)
  mkAppM branch.theoremName theoremArgs

private def tryEmptyResourceRewrite (rule : Expr) : TacticM Bool := do
  let saved ← saveState
  try
    AUXLib.SetoidRewrite.rewriteTargetOnce rule
    return true
  catch _ =>
    restoreState saved
    return false

partial def runEmptyResourceCleanup : TacticM Unit := do
  let goals ← getGoals
  let some goal := goals.head? | return
  let target ← instantiateMVars (← goal.getType)
  let env ← getEnv
  for branch in registeredEmptyResourceRules env do
    unless env.contains branch.head && env.contains branch.theoremName do
      continue
    if let some matched ← findEmptyResourceMatch? target branch.head branch.shape then
      let rule ← buildEmptyResourceRule branch matched
      if ← tryEmptyResourceRewrite rule then
        runEmptyResourceCleanup
        return

partial def runPureSplitsToFixpoint : TacticM Unit := do
  let before ← getGoals
  let mut after : List MVarId := []
  let mut changed := false
  for goal in before do
    setGoals [goal]
    if ← splitOnePreprocessedPureGoal then
      changed := true
    let produced ← getGoals
    after := after ++ produced
  setGoals after
  if changed then
    runPureSplitsToFixpoint

def unfoldGoalHead : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some unfolded ← Lean.Meta.unfoldDefinition? target | return
  replaceMainGoal [← goal.change unfolded]

def splitSyntacticPropAnd : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  unless target.getAppFn.consumeMData.isConstOf ``And do
    throwError "goal is not a syntactically exposed conjunction"
  evalTactic (← `(tactic| apply And.intro))

private def restoreSourceBinderNamesAt (goal : MVarId) : TacticM MVarId := do
  let goalDecl ← goal.getDecl
  let mut current := goal
  let mut reserved : NameSet := {}
  for localDecl in goalDecl.lctx do
    unless localDecl.userName.hasMacroScopes do
      reserved := reserved.insert localDecl.userName
  for localDecl in goalDecl.lctx do
    let sourceName := localDecl.userName.eraseMacroScopes
    if localDecl.userName.hasMacroScopes && sourceName != Name.anonymous &&
        !reserved.contains sourceName && !localDecl.isImplementationDetail then
      current ← current.rename localDecl.fvarId sourceName
      reserved := reserved.insert sourceName
  return current

def restoreSourceBinderNames : TacticM Unit := do
  setGoals (← (← getGoals).mapM restoreSourceBinderNamesAt)

private def tryNormalizedOmega : TacticM Bool := do
  let saved ← saveState
  try
    evalTactic (← `(tactic|
      simp_all only
        [AutomationHelpers.zabs_of_nonneg,
         AutomationHelpers.zabs_of_neg,
         AutomationHelpers.self_eq_zabs_iff,
         AutomationHelpers.neg_eq_zabs_iff,
         AutomationHelpers.sub_rev_eq_zabs_sub_iff,
         SimpleC.SL.IntLib.Zabs,
         Z.abs_le_iff,
         Z.abs_lt_iff,
         Int.neg_sub,
         SimpleC.SL.IntLib.INT_MIN,
         SimpleC.SL.IntLib.INT_MAX,
         SimpleC.SL.IntLib.UINT_MAX,
         Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub] <;>
      omega))
    return true
  catch _ =>
    restoreState saved
    return false

private def intLocalFVars : MetaM (List FVarId) := do
  let mut result := []
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let saved ← saveState
      let isInt ← withTransparency .reducible <|
        isDefEq localDecl.type (mkConst ``Int)
      restoreState saved
      if isInt then
        result := localDecl.fvarId :: result
  return result.reverse

private def tryOmegaProof (type : Expr) : TacticM (Option Expr) := do
  let saved ← saveState
  let savedGoals ← getGoals
  try
    let proof ← mkFreshExprSyntheticOpaqueMVar type
    setGoals [proof.mvarId!]
    evalTactic (← `(tactic| omega))
    unless (← getGoals).isEmpty do
      throwError "omega left residual equality goals"
    let proof ← instantiateMVars proof
    setGoals savedGoals
    return some proof
  catch _ =>
    restoreState saved
    return none

private partial def findOmegaIntEquality :
    List FVarId → TacticM (Option (Expr × Expr))
  | [] => return none
  | leftId :: rest => do
      let left := mkFVar leftId
      for rightId in rest do
        let right := mkFVar rightId
        let eqType := mkApp3
          (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Int) left right
        if let some proof ← tryOmegaProof eqType then
          return some (eqType, proof)
      findOmegaIntEquality rest

private partial def substituteOmegaIntEqualities : Nat → TacticM Unit
  | 0 => pure ()
  | fuel + 1 => withMainContext do
      let goal ← getMainGoal
      let some (eqType, proof) ← findOmegaIntEquality (← intLocalFVars)
        | return
      let asserted ← goal.assert `_omega_int_eq eqType proof
      let (_, next) ← asserted.intro1P
      replaceMainGoal [next]
      evalTactic (← `(tactic| subst_vars))
      substituteOmegaIntEqualities fuel

def runIntNiaCompat : TacticM Unit := do
  if ← tryNormalizedOmega then
    return
  substituteOmegaIntEqualities 8
  unless ← tryNormalizedOmega do
    throwError "integer NIA compatibility normalization did not close the goal"

end SpatialAutomation

macro_rules
  | `(tactic| set_String_name) => `(tactic| skip)
  | `(tactic| subst_all_strings) => `(tactic| skip)
  | `(tactic| solve_arch) =>
      `(tactic| unfold_arch; first | rfl | omega | skip)
  | `(tactic| _sac_unfold_transparent) =>
      `(tactic| first | simp only [sac_unfold] | skip)
  | `(tactic| poly_store_unfold) =>
      `(tactic| first
        | simp only
          [AutomationHelpers.poly_store_unfold_int,
           AutomationHelpers.poly_store_unfold_char,
           AutomationHelpers.poly_store_unfold_int64,
           AutomationHelpers.poly_store_unfold_short,
           AutomationHelpers.poly_store_unfold_uint,
           AutomationHelpers.poly_store_unfold_uchar,
           AutomationHelpers.poly_store_unfold_uint64,
           AutomationHelpers.poly_store_unfold_int128,
           AutomationHelpers.poly_store_unfold_uint128,
           AutomationHelpers.poly_store_unfold_ushort,
           AutomationHelpers.poly_store_unfold_float,
           AutomationHelpers.poly_store_unfold_double,
           AutomationHelpers.poly_store_unfold_long_double,
           AutomationHelpers.poly_store_unfold_ptr,
           AutomationHelpers.typed_poly_store_unfold_int,
           AutomationHelpers.typed_poly_store_unfold_char,
           AutomationHelpers.typed_poly_store_unfold_int64,
           AutomationHelpers.typed_poly_store_unfold_short,
           AutomationHelpers.typed_poly_store_unfold_uint,
           AutomationHelpers.typed_poly_store_unfold_uchar,
           AutomationHelpers.typed_poly_store_unfold_uint64,
           AutomationHelpers.typed_poly_store_unfold_int128,
           AutomationHelpers.typed_poly_store_unfold_uint128,
           AutomationHelpers.typed_poly_store_unfold_ushort,
           AutomationHelpers.typed_poly_store_unfold_float,
           AutomationHelpers.typed_poly_store_unfold_double,
           AutomationHelpers.typed_poly_store_unfold_long_double,
           AutomationHelpers.typed_poly_store_unfold_ptr,
           AutomationHelpers.poly_undef_store_unfold_int,
           AutomationHelpers.poly_undef_store_unfold_char,
           AutomationHelpers.poly_undef_store_unfold_int64,
           AutomationHelpers.poly_undef_store_unfold_short,
           AutomationHelpers.poly_undef_store_unfold_uint,
           AutomationHelpers.poly_undef_store_unfold_uchar,
           AutomationHelpers.poly_undef_store_unfold_uint64,
           AutomationHelpers.poly_undef_store_unfold_int128,
           AutomationHelpers.poly_undef_store_unfold_uint128,
           AutomationHelpers.poly_undef_store_unfold_ushort,
           AutomationHelpers.poly_undef_store_unfold_float,
           AutomationHelpers.poly_undef_store_unfold_double,
           AutomationHelpers.poly_undef_store_unfold_long_double,
           AutomationHelpers.poly_undef_store_unfold_ptr,
           store_finite_float,
           store_finite_double,
           store_finite_long_double,
           store_float,
           store_double,
           store_long_double,
           SimpleC.SL.FloatLib.bits_of_float_value,
           SimpleC.SL.FloatLib.bits_of_double_value,
           SimpleC.SL.FloatLib.bits_of_long_double_value]
        | skip)
  | `(tactic| simpl_auto_with ($tac:tacticSeq)) =>
      `(tactic| solve
        | exact SacContext.rules.toContext.derivable1_refl _
        | (intros <;> assumption)
        | assumption | rfl | trivial | contradiction
        | exact AUXLib.Reflexive.refl _
        | simp_all only
        | solve_by_elim only [*]
        | (apply Or.inl; assumption)
        | (apply Or.inr; assumption)
        | (apply AutomationHelpers.upper_of_abs_le <;> assumption)
        | (apply AutomationHelpers.lower_of_abs_le <;>
            first | assumption | omega)
        | (apply AutomationHelpers.upper_of_abs_lt_abs <;>
            first | assumption | omega)
        | (apply AutomationHelpers.lower_of_abs_lt_abs <;>
            first | assumption | omega)
        | (apply AutomationHelpers.int32_upper_of_abs_lt_abs <;> assumption)
        | (apply AutomationHelpers.int32_lower_of_abs_lt_abs <;> assumption)
        | $tac)
  | `(tactic| simpl_auto) =>
      `(tactic| solve
        | exact SacContext.rules.toContext.derivable1_refl _
        | (intros <;> assumption)
        | assumption | rfl | trivial | contradiction
        | exact AUXLib.Reflexive.refl _
        | simp_all only
        | solve_by_elim only [*]
        | (apply Or.inl; assumption)
        | (apply Or.inr; assumption)
        | (apply AutomationHelpers.upper_of_abs_le <;> assumption)
        | (apply AutomationHelpers.lower_of_abs_le <;>
            first | assumption | omega)
        | (apply AutomationHelpers.upper_of_abs_lt_abs <;>
            first | assumption | omega)
        | (apply AutomationHelpers.lower_of_abs_lt_abs <;>
            first | assumption | omega)
        | (apply AutomationHelpers.int32_upper_of_abs_lt_abs <;> assumption)
        | (apply AutomationHelpers.int32_lower_of_abs_lt_abs <;> assumption)
        | omega | int auto | _int_nia_compat | nia)
  | `(tactic| simpl_entail_with ($tac:tacticSeq)) =>
      `(tactic| first
        | (_split_prop_and <;> simpl_entail_with ($tac))
        | simpl_auto_with ($tac)
        | skip)
  | `(tactic| simpl_entail) =>
      `(tactic| first | (_split_prop_and <;> simpl_entail) | simpl_auto | skip)
  | `(tactic| _andp_cancel_core) =>
      `(tactic| first
        | exact SacContext.rules.toContext.derivable1_refl _
        | (_andp_split_right <;> _andp_cancel_core)
        | exact SacContext.rules.toContext.derivable1_andp_elim1 _ _
        | exact SacContext.rules.toContext.derivable1_andp_elim2 _ _
        | (_andp_use_left; _andp_cancel_core)
        | (_andp_use_right; _andp_cancel_core)
        | (_dump_pure_right; try simpl_auto)
        | _cancel_progress
        | skip)
  | `(tactic| normalize) => `(tactic| asrt_simpl)
  | `(tactic| Intro_any) =>
      `(tactic|
        pureIntros; asrt_simpl; apply Automation.exp_left_rule; intro; pureIntros)
  | `(tactic| Intros_r_any) =>
      `(tactic| asrt_simpl; apply Automation.allp_right_rule; intro; pureIntros)
  | `(tactic| Left) =>
      `(tactic| first
        | apply Automation.orp_intros_left
        | rel_rw [← SacContext.rules.toContext.derivable1_orp_intros1])
  | `(tactic| Right) =>
      `(tactic| first
        | apply Automation.orp_intros_right
        | rel_rw [← SacContext.rules.toContext.derivable1_orp_intros2])
  | `(tactic| elim_emp) => `(tactic| asrt_complex_simpl)
  | `(tactic| pre_process_default) => `(tactic| pre_process)
  | `(tactic| dump_pre_spatial) => `(tactic| apply dump_spatial_left)
  | `(tactic| split_pure_and_solve) =>
      `(tactic| split_pures <;> try (dump_pre_spatial; simpl_auto))
  | `(tactic| LLM_pre_process ($tac:tacticSeq)) =>
      `(tactic| LLM_pre_process_tac ($tac))

private def automationStep (step : Syntax) : TacticM Unit := do
  if !(← getGoals).isEmpty then
    evalTactic step

private def tryAutomationStep (step : Syntax) : TacticM Unit := do
  if (← getGoals).isEmpty then
    return
  let saved ← saveState
  try
    evalTactic step
  catch _ =>
    restoreState saved

elab_rules : tactic
  | `(tactic| _split_prop_and) => SpatialAutomation.splitSyntacticPropAnd
  | `(tactic| unfold_arch) => do
      tryAutomationStep (← `(tactic| unfold DerivedPredSig.ptr_width_Z at *))
      tryAutomationStep (← `(tactic| unfold DerivedPredSig.ptr_size_Z at *))
      tryAutomationStep (← `(tactic| unfold DerivedPredSig.ptr_size at *))
      tryAutomationStep (← `(tactic| unfold DerivedPredSig.ptr_align at *))
      tryAutomationStep (← `(tactic| unfold DerivedPredSig.addr_max_unsigned at *))
      tryAutomationStep (← `(tactic| unfold DerivedPredSig.aligned at *))
      tryAutomationStep (← `(tactic|
        simp only [SimpleC.SL.CArch.CArchSig.ptr_width_Z,
          SimpleC.SL.CArch.CArchSig.ptr_size_Z] at *))
  | `(tactic| fold_arch) => do
      tryAutomationStep (← `(tactic| rw [AutomationHelpers.fold_aligned] at *))
      tryAutomationStep
        (← `(tactic| rw [AutomationHelpers.fold_addr_max_unsigned] at *))
      tryAutomationStep (← `(tactic| rw [AutomationHelpers.fold_ptr_align] at *))
      tryAutomationStep (← `(tactic| rw [AutomationHelpers.fold_ptr_size] at *))
      tryAutomationStep (← `(tactic| rw [AutomationHelpers.fold_ptr_size_Z] at *))
      tryAutomationStep (← `(tactic| rw [AutomationHelpers.fold_ptr_width_Z] at *))
  | `(tactic| _empty_resource_cleanup) => SpatialAutomation.runEmptyResourceCleanup
  | `(tactic| entailer_with ($tac:tacticSeq)) => do
      evalTactic (← `(tactic| set_String_name))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      tryAutomationStep (← `(tactic| _empty_resource_cleanup))
      tryAutomationStep (← `(tactic| entailer_pure))
      tryAutomationStep (← `(tactic| _empty_resource_cleanup))
      tryAutomationStep (← `(tactic| entailer_pure))
      evalTactic (← `(tactic| simpl_entail_with ($tac)))
      evalTactic (← `(tactic| subst_all_strings))
      SpatialAutomation.restoreSourceBinderNames
  | `(tactic| andp_cancel) => withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let ops ← SpatialAutomation.getOps
      match ← SpatialAutomation.matchBinary ops.derivable target with
      | none => throwError "andp_cancel: goal is not a separation-logic entailment"
      | some _ =>
          evalTactic (← `(tactic|
            asrt_simpl_pure; pureIntros; all_goals _andp_cancel_core))
  | `(tactic| Split) => do
      SpatialAutomation.runRewriteSet
        [(.orpSepconLeft, ← `(tactic| rel_rw [orp_sepcon_left_equiv])),
         (.orpSepconRight, ← `(tactic| rel_rw [orp_sepcon_right_equiv]))]
      automationStep (← `(tactic| apply Automation.orp_elim))
  | `(tactic| eExists) => do
      automationStep (← `(tactic| asrt_simpl))
      SpatialAutomation.runEExists
  | `(tactic| wand_elim) => do
      automationStep (← `(tactic| asrt_simpl))
      tryAutomationStep (← `(tactic| repeat first
        | apply Automation.apply_sepcon_adjoint_rule
        | Intros_r_any))
  | `(tactic| TT_simpl) => do
      SpatialAutomation.runRewriteSet
        [(.truepAndpLeft, ← `(tactic| rel_rw [truep_andp_left_equiv])),
         (.truepAndpRight, ← `(tactic| rel_rw [truep_andp_right_equiv]))]
  | `(tactic| andp_assoc_change) => do
      SpatialAutomation.runRewriteSet
        [(.andpAssocLeft, ← `(tactic|
          rel_rw [SacContext.rules.toContext.logic_equiv_andp_assoc]))]
  | `(tactic| sepcon_assoc_change) =>
      SpatialAutomation.rightAssociateSepconGoal
  | `(tactic| coq_prop_lift) => do
      SpatialAutomation.runRewriteSet
        [(.pureAndpSepconLeft, ← `(tactic|
          rel_rw [SacContext.rules.toContext.logic_equiv_coq_prop_andp_sepcon])),
         (.pureAndpSepconRight, ← `(tactic|
          rel_rw [SacContext.rules.toContext.logic_equiv_sepcon_coq_prop_andp])),
         (.sepconPureRight, ← `(tactic| rel_rw [sepcon_prop_equiv]))]
  | `(tactic| asrt_complex_simpl) => do
      SpatialAutomation.runRewriteSet
        [(.spatialAndpRight, ← `(tactic|
          rel_rw [SimpleC.SL.CommonAssertion.DerivedPredSig.AutomationHelpers.spatial_andp_right_equiv])),
         (.sepEmpRight, ← `(tactic| rel_rw [sepcon_emp_equiv])),
         (.sepEmpLeft, ← `(tactic| rel_rw [sepcon_emp_logic_equiv'])),
         (.truepAndpLeft, ← `(tactic| rel_rw [truep_andp_left_equiv])),
         (.truepAndpRight, ← `(tactic| rel_rw [truep_andp_right_equiv])),
         (.andpPureRight, ← `(tactic|
          rel_rw [SimpleC.SL.CommonAssertion.DerivedPredSig.AutomationHelpers.coq_prop_andp_right_equiv])),
         (.pureAndpSepconLeft, ← `(tactic|
          rel_rw [SacContext.rules.toContext.logic_equiv_coq_prop_andp_sepcon])),
         (.pureAndpSepconRight, ← `(tactic|
          rel_rw [SacContext.rules.toContext.logic_equiv_sepcon_coq_prop_andp])),
         (.sepconPureRight, ← `(tactic| rel_rw [sepcon_prop_equiv])),
         (.sepconPureLeft, ← `(tactic|
          rel_rw [SimpleC.SL.CommonAssertion.DerivedPredSig.AutomationHelpers.coq_prop_sepcon_left_equiv])),
         (.expAndpLeft, ← `(tactic| rel_rw [ex_logic_equiv_andp])),
         (.expSepconLeft, ← `(tactic| rel_rw [ex_logic_equiv_sepcon])),
         (.expAndpRight, ← `(tactic|
          rel_rw [SimpleC.SL.CommonAssertion.DerivedPredSig.AutomationHelpers.exp_andp_right_equiv])),
         (.expSepconRight, ← `(tactic|
          rel_rw [SimpleC.SL.CommonAssertion.DerivedPredSig.AutomationHelpers.exp_sepcon_right_equiv])),
         (.orpSepconLeft, ← `(tactic| rel_rw [orp_sepcon_left_equiv])),
         (.orpSepconRight, ← `(tactic| rel_rw [orp_sepcon_right_equiv]))]
  | `(tactic| asrt_easysimpl) => do
      automationStep (← `(tactic| TT_simpl))
      automationStep (← `(tactic| andp_assoc_change))
      automationStep (← `(tactic| coq_prop_lift))
  | `(tactic| asrt_simpl_pure) => do
      automationStep (← `(tactic| _sac_normalize))
  | `(tactic| asrt_simpl) => do
      tryAutomationStep (← `(tactic| _sac_unfold_transparent))
      automationStep (← `(tactic| asrt_simpl_pure))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      tryAutomationStep (← `(tactic| _sac_normalize_stores))
      automationStep (← `(tactic| asrt_simpl_pure))
      tryAutomationStep (← `(tactic| _sac_unfold_transparent))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      tryAutomationStep (← `(tactic| _sac_normalize_stores))
  | `(tactic| pureIntros_without_rename) => do
      automationStep (← `(tactic| asrt_simpl_pure))
      automationStep (← `(tactic| repeat first
        | (apply coq_prop_andp_left; intro)))
      SpatialAutomation.rightAssociateSepconLhs
  | `(tactic| pureIntros) => do
      automationStep (← `(tactic| pureIntros_without_rename))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      tryAutomationStep (← `(tactic| _sac_normalize_stores))
      automationStep (← `(tactic| pureIntros_without_rename))
  | `(tactic| entailer_pure) => do
      automationStep (← `(tactic| asrt_simpl_pure))
      evalTactic (← `(tactic| sepcon_assoc_change))
      evalTactic (← `(tactic| andp_cancel))
  | `(tactic| pre_process_pure) => do
      automationStep (← `(tactic| pureIntros))
      automationStep (← `(tactic| wand_elim))
      automationStep (← `(tactic| asrt_simpl_pure))
  | `(tactic| LLM_pre_process_tac ($tac:tacticSeq)) => do
      tryAutomationStep (← `(tactic| _unfold_goal_head))
      tryAutomationStep (← `(tactic| left))
      tryAutomationStep (← `(tactic| intros))
      SpatialAutomation.restoreSourceBinderNames
      tryAutomationStep (← `(tactic| _sac_unfold_transparent))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      automationStep (← `(tactic| pre_process_pure))
      tryAutomationStep (← `(tactic| _sac_unfold_transparent))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      discard <| SpatialAutomation.closeSyntacticReflexiveEntailment
      if (← getGoals).isEmpty then
        return
      unless ← SpatialAutomation.rhsStartsWithExp do
        tryAutomationStep (← `(tactic| solve | entailer_with ($tac)))
  | `(tactic| pre_process) => do
      tryAutomationStep (← `(tactic| _unfold_goal_head))
      tryAutomationStep (← `(tactic| left))
      tryAutomationStep (← `(tactic| intros))
      SpatialAutomation.restoreSourceBinderNames
      tryAutomationStep (← `(tactic| _sac_unfold_transparent))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      automationStep (← `(tactic| pre_process_pure))
      tryAutomationStep (← `(tactic| _sac_unfold_transparent))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      discard <| SpatialAutomation.closeSyntacticReflexiveEntailment
      if (← getGoals).isEmpty then
        return
      unless ← SpatialAutomation.rhsStartsWithExp do
        tryAutomationStep (← `(tactic| solve | entailer!))
  | `(tactic| aggressive_pre_process) => do
      tryAutomationStep (← `(tactic| right))
      tryAutomationStep (← `(tactic| intros))
      tryAutomationStep (← `(tactic| poly_store_unfold))
      automationStep (← `(tactic| pre_process_pure))
      SpatialAutomation.runPureSplitsToFixpoint
      automationStep (← `(tactic| all_goals first
        | assumption
        | _close_aggressive_trivial
        | skip))
      tryAutomationStep (← `(tactic| _dump_empty_pre_spatial))
  | `(tactic| entailer!) => do
      if (← getGoals).isEmpty then
        return
      evalTactic (← `(tactic|
        entailer_with (first | omega | int auto | _int_nia_compat | nia)))
  | `(tactic| split_pure_spatial) => do
      automationStep (← `(tactic| asrt_simpl_pure))
      SpatialAutomation.leftAssociateAndpRhs
      SpatialAutomation.runSplitPureSpatial
  | `(tactic| split_pures) => do
      automationStep (← `(tactic| asrt_simpl_pure))
      SpatialAutomation.leftAssociateAndpRhs
      evalTactic (← `(tactic| all_goals repeat _split_pures_step))
  | `(tactic| _split_pures_step) =>
      SpatialAutomation.runSplitPuresStep
  | `(tactic| _dump_empty_pre_spatial) =>
      SpatialAutomation.runDumpEmptyPreSpatial
  | `(tactic| _close_aggressive_trivial) =>
      SpatialAutomation.closeAggressiveTrivial
  | `(tactic| _dump_pure_right) => do
      let dumped ← SpatialAutomation.dumpPureConclusion
      unless dumped do
        throwError "_dump_pure_right: conclusion is not a standalone lifted proposition"
  | `(tactic| _int_nia_compat) =>
      SpatialAutomation.runIntNiaCompat
  | `(tactic| _andp_split_right) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let ops ← SpatialAutomation.getOps
      let some (_, right) ← SpatialAutomation.matchBinary ops.derivable target
        | throwError "_andp_split_right: goal is not an entailment"
      unless (← SpatialAutomation.matchBinary ops.andp right).isSome do
        throwError "_andp_split_right: conclusion is not a conjunction"
      evalTactic (← `(tactic| apply _derivable1_andp_intros))
      match ← getGoals with
      | first :: second :: rest => setGoals (second :: first :: rest)
      | _ => throwError "internal error: conjunction split did not create two goals"
  | `(tactic| _andp_use_left) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let ops ← SpatialAutomation.getOps
      let some (left, _) ← SpatialAutomation.matchBinary ops.derivable target
        | throwError "_andp_use_left: goal is not an entailment"
      unless (← SpatialAutomation.matchBinary ops.andp left).isSome do
        throwError "_andp_use_left: premise is not a conjunction"
      evalTactic (← `(tactic| apply Automation.andp_left_rule))
  | `(tactic| _andp_use_right) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let ops ← SpatialAutomation.getOps
      let some (left, _) ← SpatialAutomation.matchBinary ops.derivable target
        | throwError "_andp_use_right: goal is not an entailment"
      unless (← SpatialAutomation.matchBinary ops.andp left).isSome do
        throwError "_andp_use_right: premise is not a conjunction"
      evalTactic (← `(tactic| apply Automation.andp_right_rule))
  | `(tactic| _cancel_progress) =>
      SpatialAutomation.runCancelProgress
  | `(tactic| _split_preprocessed_pure) =>
      discard SpatialAutomation.splitOnePreprocessedPureGoal
  | `(tactic| _unfold_goal_head) =>
      SpatialAutomation.unfoldGoalHead

private def introPatternName (pattern : TSyntax `rcasesPat) : TacticM (Name × Bool) := do
  match pattern with
  | `(rcasesPat| $id:ident) => return (id.getId, false)
  | _ => return (← mkFreshUserName `_intro, true)

private def applyIntroPattern (name : Name) (pattern : TSyntax `rcasesPat) :
    TacticM Unit := do
  let id := mkIdent name
  evalTactic (← `(tactic| rcases $id:ident with $pattern:rcasesPat))

elab "Intros" patterns:(colGt rcasesPat)* : tactic => do
  if patterns.size > 20 then
    throwError "Intros: supports at most 20 arguments"
  if patterns.isEmpty then
    evalTactic (← `(tactic| pureIntros))
  unless patterns.isEmpty do
    evalTactic (← `(tactic| pureIntros))
  for pattern in patterns do
    let (name, applyPattern) ← introPatternName pattern
    unless ← SpatialAutomation.introduceExpLeftStructural name do
      evalTactic (← `(tactic| pureIntros))
      unless ← SpatialAutomation.introduceExpLeftStructural name do
        evalTactic (← `(tactic| asrt_simpl))
        unless ← SpatialAutomation.introduceExpLeftStructural name do
          throwError "Intros: no existential assertion on the left"
    if applyPattern then
      applyIntroPattern name pattern
  unless patterns.isEmpty do
    evalTactic (← `(tactic| pureIntros))

elab "Intros_r" patterns:(colGt rcasesPat)* : tactic => do
  if patterns.size > 20 then
    throwError "Intros_r: supports at most 20 arguments"
  for pattern in patterns do
    let (name, applyPattern) ← introPatternName pattern
    let mut introduced ← SpatialAutomation.introduceAllpRight name
    unless introduced do
      evalTactic (← `(tactic| asrt_simpl))
      introduced ← SpatialAutomation.introduceAllpRight name
    unless introduced do
      let id := mkIdent name
      evalTactic (← `(tactic|
        apply Automation.allp_right_rule <;>
        intro $id:ident <;>
        pureIntros))
    if applyPattern then
      applyIntroPattern name pattern
  evalTactic (← `(tactic| pureIntros))

elab "Exists" values:(colGt term:max)* : tactic => do
  if values.size > 20 then
    throwError "Exists: supports at most 20 arguments"
  if values.isEmpty then
    evalTactic (← `(tactic| asrt_simpl))
  for value in values do
    evalTactic (← `(tactic| asrt_simpl))
    evalTactic (← `(tactic|
      refine Automation.exp_right_rule (CRules := SacContext.rules) $value ?_))

elab "Exists_l" values:(colGt term:max)* : tactic => do
  if values.size > 20 then
    throwError "Exists_l: supports at most 20 arguments"
  if values.isEmpty then
    evalTactic (← `(tactic| asrt_simpl))
  for value in values do
    evalTactic (← `(tactic| asrt_simpl))
    evalTactic (← `(tactic|
      first
      | refine Automation.allp_left_rule (CRules := SacContext.rules) $value ?_
      | refine Exists.intro $value ?_))

elab "Intros_p " id:ident : tactic => do
  evalTactic (← `(tactic| asrt_simpl_pure))
  evalTactic (← `(tactic|
    refine coq_prop_andp_left SacContext.rules _ _ _ ?_))
  let goal ← getMainGoal
  let (_, nextGoal) ← goal.intro id.getId
  replaceMainGoal [nextGoal]

syntax "add_pure " term " as " ident : tactic
macro_rules
  | `(tactic| add_pure $p:term as $id:ident) =>
      `(tactic| apply add_pure_split SacContext.rules $p <;> try Intros_p $id)

elab "sep_apply_l_atomic " rule:(colGt term) : tactic =>
  SpatialAutomation.runSepApplyAtomic rule true

elab "sep_apply_r_atomic " rule:(colGt term) : tactic =>
  SpatialAutomation.runSepApplyAtomic rule false

elab "sep_apply " rule:(colGt term) : tactic =>
  SpatialAutomation.runSepApply rule true

elab "sep_apply_left " rule:(colGt term) : tactic =>
  SpatialAutomation.runSepApply rule true

elab "sep_apply_right " rule:(colGt term) : tactic =>
  SpatialAutomation.runSepApply rule false

elab "prop_apply " rule:(colGt term) : tactic =>
  SpatialAutomation.runPropApply rule

elab "prop_apply_p " rule:(colGt term) : tactic =>
  SpatialAutomation.runPropApplyInstantiated rule

namespace SpatialAutomation

open Lean Meta Elab Tactic

private partial def normalizeGoalApplyAssertion (unfoldStores : Bool)
    (ops : Ops) (expression : Expr) : MetaM (Expr × Expr) := do
  let expression := expression.headBeta
  if isLowLevelStoreAtom expression then
    return (expression, ← equivRefl ops expression)
  if unfoldStores then
    if let some unfolded ← unfoldStoreForInspection? ops expression then
      if unfolded != expression then
        let (normalized, normalizedProof) ←
          normalizeGoalApplyAssertion unfoldStores ops unfolded
        let unfoldProof ← equivRefl ops expression
        return (normalized, ← equivTrans ops expression unfolded normalized
          unfoldProof normalizedProof)
  if let some (left, right) ← matchBinary ops.andp expression then
    let (newLeft, leftProof) ← normalizeGoalApplyAssertion unfoldStores ops left
    let (newRight, rightProof) ← normalizeGoalApplyAssertion unfoldStores ops right
    let combined := mkApp2 ops.andp newLeft newRight
    let congruence ←
      equivAndpMono ops left newLeft right newRight leftProof rightProof
    if ← defEqLogicalConstantNoCommit newLeft ops.truep then
      let eliminate ← mkAppM ``truep_andp_left_equiv #[ops.rules, newRight]
      return (newRight,
        ← equivTrans ops expression combined newRight congruence eliminate)
    if ← defEqLogicalConstantNoCommit newRight ops.truep then
      let eliminate ← mkAppM ``truep_andp_right_equiv #[ops.rules, newLeft]
      return (newLeft,
        ← equivTrans ops expression combined newLeft congruence eliminate)
    if (← matchUnary ops.coqProp newRight).isSome then
      if (← matchUnary ops.coqProp newLeft).isNone then
        let swapped := mkApp2 ops.andp newRight newLeft
        let swapProof ← mkAppM ``Automation.logic_equiv_andp_comm_rule
          #[ops.rules, newLeft, newRight]
        return (swapped,
          ← equivTrans ops expression combined swapped congruence swapProof)
    if let some (witnessType, predicate) ← matchBinary ops.exp newLeft then
      return ← withLocalDecl `_x .default witnessType fun witness => do
        let body := mkApp2 ops.andp (mkApp predicate witness) newRight
        let newPredicate ← mkLambdaFVars #[witness] body
        let lifted := mkApp2 ops.exp witnessType newPredicate
        let liftProof ← mkAppM ``ex_logic_equiv_andp
          #[ops.rules, predicate, newRight]
        let combinedProof ← equivTrans ops expression combined lifted
          congruence liftProof
        let (normalized, normalizedProof) ←
          normalizeGoalApplyAssertion unfoldStores ops lifted
        return (normalized, ← equivTrans ops expression lifted normalized
          combinedProof normalizedProof)
    if let some (witnessType, predicate) ← matchBinary ops.exp newRight then
      return ← withLocalDecl `_x .default witnessType fun witness => do
        let body := mkApp2 ops.andp (mkApp predicate witness) newLeft
        let newPredicate ← mkLambdaFVars #[witness] body
        let swapped := mkApp2 ops.andp newRight newLeft
        let lifted := mkApp2 ops.exp witnessType newPredicate
        let swapProof ← mkAppM
          ``AutomationHelpers.exp_andp_right_equiv
          #[ops.rules, newLeft, predicate]
        let liftProof ← mkAppM ``ex_logic_equiv_andp
          #[ops.rules, predicate, newLeft]
        let moved ← equivTrans ops combined swapped lifted
          swapProof liftProof
        let combinedProof ← equivTrans ops expression combined lifted
          congruence moved
        let (normalized, normalizedProof) ←
          normalizeGoalApplyAssertion unfoldStores ops lifted
        return (normalized, ← equivTrans ops expression lifted normalized
          combinedProof normalizedProof)
    return (combined, congruence)
  if let some (left, right) ← matchBinary ops.sepcon expression then
    let (newLeft, leftProof) ← normalizeGoalApplyAssertion unfoldStores ops left
    let (newRight, rightProof) ← normalizeGoalApplyAssertion unfoldStores ops right
    let combined := mkApp2 ops.sepcon newLeft newRight
    let congruence ←
      equivSepconMono ops left newLeft right newRight leftProof rightProof
    if let some proposition ← matchUnary ops.coqProp newRight then
      let liftedSpatial := mkApp2 ops.sepcon newLeft ops.truep
      let lifted := mkApp2 ops.andp newRight liftedSpatial
      let liftProof ← mkAppM ``sepcon_prop_equiv
        #[ops.rules, newLeft, proposition]
      let combinedProof ← equivTrans ops expression combined lifted
        congruence liftProof
      let (normalized, normalizedProof) ←
        normalizeGoalApplyAssertion unfoldStores ops lifted
      return (normalized, ← equivTrans ops expression lifted normalized
        combinedProof normalizedProof)
    if let some proposition ← matchUnary ops.coqProp newLeft then
      let swapped := mkApp2 ops.sepcon newRight newLeft
      let liftedSpatial := mkApp2 ops.sepcon newRight ops.truep
      let lifted := mkApp2 ops.andp newLeft liftedSpatial
      let swapProof ← mkAppM ``Automation.logic_equiv_coq_prop_sepcon_rule
        #[ops.rules, proposition, newRight]
      let liftProof ← mkAppM ``sepcon_prop_equiv
        #[ops.rules, newRight, proposition]
      let swappedProof ← equivTrans ops combined swapped lifted
        swapProof liftProof
      let combinedProof ← equivTrans ops expression combined lifted
        congruence swappedProof
      let (normalized, normalizedProof) ←
        normalizeGoalApplyAssertion unfoldStores ops lifted
      return (normalized, ← equivTrans ops expression lifted normalized
        combinedProof normalizedProof)
    if let some (witnessType, predicate) ← matchBinary ops.exp newLeft then
      return ← withLocalDecl `_x .default witnessType fun witness => do
        let body := mkApp2 ops.sepcon (mkApp predicate witness) newRight
        let newPredicate ← mkLambdaFVars #[witness] body
        let lifted := mkApp2 ops.exp witnessType newPredicate
        let liftProof ← mkAppM ``ex_logic_equiv_sepcon
          #[ops.rules, predicate, newRight]
        let combinedProof ← equivTrans ops expression combined lifted
          congruence liftProof
        let (normalized, normalizedProof) ←
          normalizeGoalApplyAssertion unfoldStores ops lifted
        return (normalized, ← equivTrans ops expression lifted normalized
          combinedProof normalizedProof)
    if let some (witnessType, predicate) ← matchBinary ops.exp newRight then
      return ← withLocalDecl `_x .default witnessType fun witness => do
        let body := mkApp2 ops.sepcon (mkApp predicate witness) newLeft
        let newPredicate ← mkLambdaFVars #[witness] body
        let swapped := mkApp2 ops.sepcon newRight newLeft
        let lifted := mkApp2 ops.exp witnessType newPredicate
        let swapProof ← mkAppM
          ``AutomationHelpers.exp_sepcon_right_equiv
          #[ops.rules, newLeft, predicate]
        let liftProof ← mkAppM ``ex_logic_equiv_sepcon
          #[ops.rules, predicate, newLeft]
        let moved ← equivTrans ops combined swapped lifted
          swapProof liftProof
        let combinedProof ← equivTrans ops expression combined lifted
          congruence moved
        let (normalized, normalizedProof) ←
          normalizeGoalApplyAssertion unfoldStores ops lifted
        return (normalized, ← equivTrans ops expression lifted normalized
          combinedProof normalizedProof)
    if let some (first, second) ← matchBinary ops.orp newLeft then
      let distributed := mkApp2 ops.orp
        (mkApp2 ops.sepcon first newRight)
        (mkApp2 ops.sepcon second newRight)
      let distribute ← mkAppM ``orp_sepcon_left_equiv
        #[ops.rules, first, second, newRight]
      let combinedProof ← equivTrans ops expression combined distributed
        congruence distribute
      let (normalized, normalizedProof) ←
        normalizeGoalApplyAssertion unfoldStores ops distributed
      return (normalized, ← equivTrans ops expression distributed normalized
        combinedProof normalizedProof)
    if let some (first, second) ← matchBinary ops.orp newRight then
      let distributed := mkApp2 ops.orp
        (mkApp2 ops.sepcon newLeft first)
        (mkApp2 ops.sepcon newLeft second)
      let distribute ← mkAppM ``orp_sepcon_right_equiv
        #[ops.rules, newLeft, first, second]
      let combinedProof ← equivTrans ops expression combined distributed
        congruence distribute
      let (normalized, normalizedProof) ←
        normalizeGoalApplyAssertion unfoldStores ops distributed
      return (normalized, ← equivTrans ops expression distributed normalized
        combinedProof normalizedProof)
    if let some (pureAssertion, spatial) ← matchBinary ops.andp newLeft then
      if let some proposition ← matchUnary ops.coqProp pureAssertion then
        let liftedSpatial := mkApp2 ops.sepcon spatial newRight
        let lifted := mkApp2 ops.andp pureAssertion liftedSpatial
        let liftProof ← mkAppM
          ``Automation.logic_equiv_coq_prop_andp_sepcon_rule
          #[ops.rules, proposition, spatial, newRight]
        let combinedProof ← equivTrans ops expression combined lifted
          congruence liftProof
        let (normalized, normalizedProof) ←
          normalizeGoalApplyAssertion unfoldStores ops lifted
        return (normalized, ← equivTrans ops expression lifted normalized
          combinedProof normalizedProof)
    if let some (pureAssertion, spatial) ← matchBinary ops.andp newRight then
      if let some proposition ← matchUnary ops.coqProp pureAssertion then
        let regrouped := mkApp2 ops.sepcon
          (mkApp2 ops.andp pureAssertion newLeft) spatial
        let liftedSpatial := mkApp2 ops.sepcon newLeft spatial
        let lifted := mkApp2 ops.andp pureAssertion liftedSpatial
        let movePure ← mkAppM
          ``Automation.logic_equiv_sepcon_coq_prop_andp_rule
          #[ops.rules, newLeft, proposition, spatial]
        let liftPure ← mkAppM
          ``Automation.logic_equiv_coq_prop_andp_sepcon_rule
          #[ops.rules, proposition, newLeft, spatial]
        let moved ← equivTrans ops combined regrouped lifted movePure liftPure
        let combinedProof ← equivTrans ops expression combined lifted
          congruence moved
        let (normalized, normalizedProof) ←
          normalizeGoalApplyAssertion unfoldStores ops lifted
        return (normalized, ← equivTrans ops expression lifted normalized
          combinedProof normalizedProof)
    if ← defEqLogicalConstantNoCommit newLeft ops.emp then
      let eliminate ← mkAppM ``sepcon_emp_logic_equiv' #[ops.rules, newRight]
      return (newRight,
        ← equivTrans ops expression combined newRight congruence eliminate)
    if ← defEqLogicalConstantNoCommit newRight ops.emp then
      let eliminate ← mkAppM ``sepcon_emp_equiv #[ops.rules, newLeft]
      return (newLeft,
        ← equivTrans ops expression combined newLeft congruence eliminate)
    return (combined, congruence)
  if let some (left, right) ← matchBinary ops.orp expression then
    let (newLeft, leftProof) ← normalizeGoalApplyAssertion unfoldStores ops left
    let (newRight, rightProof) ← normalizeGoalApplyAssertion unfoldStores ops right
    let combined := mkApp2 ops.orp newLeft newRight
    let proof ← mkAppM ``Automation.logic_equiv_orp_mono_rule
      #[ops.rules, left, newLeft, right, newRight, leftProof, rightProof]
    if let some leftProp ← matchUnary ops.coqProp newLeft then
      if let some rightProp ← matchUnary ops.coqProp newRight then
        let proposition := mkApp2 (mkConst ``Or) leftProp rightProp
        let collapsed := mkApp ops.coqProp proposition
        let expanded ← mkAppM ``Automation.logic_equiv_coq_prop_or_rule
          #[ops.rules, leftProp, rightProp]
        let collapse ← equivSymm ops collapsed combined expanded
        return (collapsed, ← equivTrans ops expression combined collapsed
          proof collapse)
    return (combined, proof)
  if let some (left, right) ← matchBinary ops.wand expression then
    let (newLeft, leftProof) ← normalizeGoalApplyAssertion unfoldStores ops left
    let (newRight, rightProof) ← normalizeGoalApplyAssertion unfoldStores ops right
    let combined := mkApp2 ops.wand newLeft newRight
    let congruence ← mkAppM ``Automation.logic_equiv_wand_mono_rule
      #[ops.rules, left, newLeft, right, newRight, leftProof, rightProof]
    if (← defEqLogicalConstantNoCommit newLeft ops.emp) &&
        (← defEqLogicalConstantNoCommit newRight ops.emp) then
      let identity ← mkAppM ``elim_wand_emp_emp #[ops.rules]
      let eliminate ← equivSymm ops ops.emp combined identity
      return (ops.emp,
        ← equivTrans ops expression combined ops.emp congruence eliminate)
    return (combined, congruence)
  if let some (left, right) ← matchBinary ops.impp expression then
    let (newLeft, leftProof) ← normalizeGoalApplyAssertion unfoldStores ops left
    let (newRight, rightProof) ← normalizeGoalApplyAssertion unfoldStores ops right
    let proof ← mkAppM ``Automation.logic_equiv_impp_mono_rule
      #[ops.rules, left, newLeft, right, newRight, leftProof, rightProof]
    return (mkApp2 ops.impp newLeft newRight, proof)
  if let some (left, right) ← matchBinary ops.iffp expression then
    let (newLeft, leftProof) ← normalizeGoalApplyAssertion unfoldStores ops left
    let (newRight, rightProof) ← normalizeGoalApplyAssertion unfoldStores ops right
    let proof ← mkAppM ``Automation.logic_equiv_iffp_mono_rule
      #[ops.rules, left, newLeft, right, newRight, leftProof, rightProof]
    return (mkApp2 ops.iffp newLeft newRight, proof)
  if let some (witnessType, predicate) ← matchBinary ops.exp expression then
    return ← withLocalDecl `_x .default witnessType fun witness => do
      let (newBody, bodyProof) ←
        normalizeGoalApplyAssertion unfoldStores ops (mkApp predicate witness)
      let newPredicate ← mkLambdaFVars #[witness] newBody
      let proofFamily ← mkLambdaFVars #[witness] bodyProof
      let proof ← mkAppOptM ``Automation.logic_equiv_exp_rule
        #[some ops.rules, some witnessType, some predicate,
          some newPredicate, some proofFamily]
      return (mkApp2 ops.exp witnessType newPredicate, proof)
  if let some (witnessType, predicate) ← matchBinary ops.allp expression then
    return ← withLocalDecl `_x .default witnessType fun witness => do
      let (newBody, bodyProof) ←
        normalizeGoalApplyAssertion unfoldStores ops (mkApp predicate witness)
      let newPredicate ← mkLambdaFVars #[witness] newBody
      let proofFamily ← mkLambdaFVars #[witness] bodyProof
      let proof ← mkAppOptM ``Automation.logic_equiv_allp_rule
        #[some ops.rules, some witnessType, some predicate,
          some newPredicate, some proofFamily]
      return (mkApp2 ops.allp witnessType newPredicate, proof)
  return (expression, ← equivRefl ops expression)

private def normalizeEntailmentGoal (unfoldStores : Bool) : TacticM Unit :=
    withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ops ← getOps
  let some (left, right) ← matchBinary ops.derivable target
    | return
  let (newLeft, leftEquiv) ← normalizeGoalApplyAssertion unfoldStores ops left
  let (newRight, rightEquiv) ← normalizeGoalApplyAssertion unfoldStores ops right
  if left == newLeft && right == newRight then
    return
  let residualType := mkApp2 ops.derivable newLeft newRight
  let residual ← mkFreshExprSyntheticOpaqueMVar residualType (← goal.getTag)
  let leftForward ← mkAppM ``Automation.logic_equiv_forward_rule
    #[ops.rules, left, newLeft, leftEquiv]
  let rightBackward ← mkAppM ``Automation.logic_equiv_backward_rule
    #[ops.rules, right, newRight, rightEquiv]
  let firstProof ← derivableTrans ops left newLeft newRight leftForward residual
  let proof ← derivableTrans ops left newRight right firstProof rightBackward
  unless ← isDefEqProofType (← inferType proof) target do
    throwError "internal error: canonical entailment proof does not match the goal"
  goal.assign proof
  replaceMainGoal [residual.mvarId!]

elab_rules : tactic
  | `(tactic| _sac_normalize) => normalizeEntailmentGoal false
  | `(tactic| _sac_normalize_stores) => normalizeEntailmentGoal true

private def normalizeGoalApplyProof (ops : Ops) (proof : Expr) : MetaM Expr := do
  let rec normalizeType (proofType : Expr) : Nat → MetaM Expr
    | 0 =>
        throwError "Goal_apply: expected an entailment or logic equivalence, got {proofType}"
    | fuel + 1 => do
        let proofType ← instantiateMVars proofType
        if let some (left, right) ← matchBinary ops.derivable proofType then
          let (newLeft, leftEquiv) ← normalizeGoalApplyAssertion true ops left
          let (newRight, rightEquiv) ← normalizeGoalApplyAssertion true ops right
          let leftBackward ← mkAppM ``Automation.logic_equiv_backward_rule
            #[ops.rules, left, newLeft, leftEquiv]
          let rightForward ← mkAppM ``Automation.logic_equiv_forward_rule
            #[ops.rules, right, newRight, rightEquiv]
          let first ← derivableTrans ops newLeft left right leftBackward proof
          return ← derivableTrans ops newLeft right newRight first rightForward
        if let some (left, right) ← matchBinary ops.logicEquiv proofType then
          let (newLeft, leftEquiv) ← normalizeGoalApplyAssertion true ops left
          let (newRight, rightEquiv) ← normalizeGoalApplyAssertion true ops right
          let leftBackward ← equivSymm ops left newLeft leftEquiv
          let first ← equivTrans ops newLeft left right leftBackward proof
          return ← equivTrans ops newLeft right newRight first rightEquiv
        if let some unfolded ← unfoldDefinition? proofType then
          normalizeType unfolded fuel
        else
          throwError "Goal_apply: expected an entailment or logic equivalence, got {proofType}"
  normalizeType (← inferType proof) 32

private def closeGoalWithProof (goal : MVarId) (proof : Expr) : MetaM Bool := do
  let saved ← saveState
  try
    let remaining ← goal.apply proof
    if remaining.isEmpty then
      return true
    restoreState saved
    return false
  catch _ =>
    restoreState saved
    return false

private def finishGoalApply (proof : Expr) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  if ← closeGoalWithProof goal proof then
    replaceMainGoal []
  else
    let ops ← getOps
    let proof ← normalizeGoalApplyProof ops proof
    if ← closeGoalWithProof goal proof then
      replaceMainGoal []
      return
    runSepApplyProof ops proof true
    evalTactic (← `(tactic| all_goals entailer!))

private def tryApplyGoalRuleDirect (goal : MVarId) (proof : Expr) : TacticM Bool := do
  let saved ← saveState
  let siblingGoals := (← getGoals).tail
  try
    let remaining ← goal.apply proof
    setGoals remaining
    evalTactic (← `(tactic| all_goals try assumption; all_goals try entailer!))
    if (← getGoals).isEmpty then
      setGoals siblingGoals
      return true
    restoreState saved
    return false
  catch _ =>
    restoreState saved
    return false

private partial def exposeGoalApplyProofType (ops : Ops) (proofType : Expr) :
    Nat → MetaM Expr
  | 0 => pure proofType
  | fuel + 1 => do
      let proofType ← instantiateMVars proofType
      if (← matchBinary ops.derivable proofType).isSome ||
          (← matchBinary ops.logicEquiv proofType).isSome then
        return proofType
      if proofType.consumeMData.isForall then
        return proofType
      if let some unfolded ← unfoldDefinition? proofType then
        exposeGoalApplyProofType ops unfolded fuel
      else
        return proofType

private partial def runGoalApplyProof (proof : Expr)
    (used : List FVarId := []) : TacticM Unit := withMainContext do
  let ops ← getOps
  let proofType ← exposeGoalApplyProofType ops (← inferType proof) 32
  match proofType.consumeMData with
  | .forallE _ domain _ _ =>
      let mut candidates := []
      for localDecl in (← getLCtx) do
        unless localDecl.isImplementationDetail || used.contains localDecl.fvarId do
          candidates := localDecl :: candidates
      -- Coq's `match reverse goal` searches the oldest matching hypothesis first.
      for localDecl in candidates.reverse do
        let saved ← saveState
        try
          if ← defEqNoCommit (← instantiateMVars localDecl.type) domain then
            runGoalApplyProof (mkApp proof localDecl.toExpr)
              (localDecl.fvarId :: used)
            return
          restoreState saved
        catch _ =>
          restoreState saved
      throwError "Goal_apply: no unused local hypothesis matches parameter type{indentExpr domain}"
  | _ =>
      if ← tryApplyGoalRuleDirect (← getMainGoal) proof then
        return
      finishGoalApply proof

def runGoalApply (rule : Syntax) : TacticM Unit := withMainContext do
  let saved ← saveState
  let siblingGoals := (← getGoals).tail
  try
    let proof ← elaborateRule rule
    runGoalApplyProof proof
    unless (← getGoals) == siblingGoals do
      throwError "Goal_apply: greedy instantiation did not completely solve the goal; use explicit sep_apply/exact with manually supplied parameters"
  catch ex =>
    restoreState saved
    throw ex

def runGoalApplyFinish (rule : Syntax) : TacticM Unit := withMainContext do
  let proof ← elaborateRule rule
  finishGoalApply proof

end SpatialAutomation

syntax "Goal_apply_finish " term : tactic
syntax "Goal_apply " term : tactic

elab_rules : tactic
  | `(tactic| Goal_apply_finish $h:term) =>
      SpatialAutomation.runGoalApplyFinish h
  | `(tactic| Goal_apply $h:term) => SpatialAutomation.runGoalApply h

end SimpleC.SL.CommonAssertion.DerivedPredSig
