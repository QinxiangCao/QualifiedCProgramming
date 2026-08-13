import AUXLib.IntAuto
import AUXLib.ListLib
import SimpleC.SL.CNotation
import SimpleC.SL.IntLib
import SimpleC.SL.Mem
import SimpleC.SL.UnifyslBridge
import Unifysl.LogicGenerator.demo932.Facade
import Lean.Elab.Tactic.Omega

namespace SimpleC.SL.CommonAssertion

open AUXLib
open CompCert
open SimpleC.SL.CNotation
open Unifysl.LogicGenerator.demo932

structure BasePredSig (ctx : Facade.Context.{0, 0}) : Type where
  mstore : addr -> Int -> ctx.expr
  mstore_noninit : addr -> ctx.expr
  mstore_mstore_noninit :
    forall p value state, mstore p value state -> mstore_noninit p state
  mstore_eqm :
    forall p value value', Byte.eqm value value' ->
      ctx.derivable1 (mstore p value) (mstore p value')
  dup_mstore_noninit :
    forall x,
      ctx.derivable1
        (ctx.sepcon (mstore_noninit x) (mstore_noninit x))
        (ctx.coq_prop False)

structure SeparationLogicSig : Type 1 extends Facade.Context.{0, 0} where
  mstore : addr -> Int -> toContext.expr
  mstore_noninit : addr -> toContext.expr
  mstore_mstore_noninit :
    forall p value state, mstore p value state -> mstore_noninit p state
  mstore_eqm :
    forall p value value', Byte.eqm value value' ->
      toContext.derivable1 (mstore p value) (mstore p value')
  dup_mstore_noninit :
    forall x,
      toContext.derivable1
        (toContext.sepcon (mstore_noninit x) (mstore_noninit x))
        (toContext.coq_prop False)

-- The Coq module type adds no abstract data beyond `CRules`; all of its
-- definitions and lemmas are the canonical declarations in the namespace below.
structure DerivedPredSig (_CRules : SeparationLogicSig) : Type where

namespace SeparationLogicSig

def toBasePredSig (CRules : SeparationLogicSig) :
    BasePredSig CRules.toContext where
  mstore := CRules.mstore
  mstore_noninit := CRules.mstore_noninit
  mstore_mstore_noninit := CRules.mstore_mstore_noninit
  mstore_eqm := CRules.mstore_eqm
  dup_mstore_noninit := CRules.dup_mstore_noninit

abbrev model (CRules : SeparationLogicSig) := CRules.toContext.model
abbrev expr (CRules : SeparationLogicSig) := CRules.toContext.expr
abbrev join (CRules : SeparationLogicSig) := CRules.toContext.join
abbrev is_unit (CRules : SeparationLogicSig) := CRules.toContext.is_unit
abbrev sepcon (CRules : SeparationLogicSig) := CRules.toContext.sepcon
abbrev wand (CRules : SeparationLogicSig) := CRules.toContext.wand
abbrev orp (CRules : SeparationLogicSig) := CRules.toContext.orp
abbrev andp (CRules : SeparationLogicSig) := CRules.toContext.andp
abbrev impp (CRules : SeparationLogicSig) := CRules.toContext.impp
abbrev exp (CRules : SeparationLogicSig) := CRules.toContext.exp
abbrev allp (CRules : SeparationLogicSig) := CRules.toContext.allp
abbrev emp (CRules : SeparationLogicSig) := CRules.toContext.emp
abbrev coq_prop (CRules : SeparationLogicSig) := CRules.toContext.coq_prop
abbrev truep (CRules : SeparationLogicSig) := CRules.toContext.truep
abbrev derivable1 (CRules : SeparationLogicSig) := CRules.toContext.derivable1
abbrev logic_equiv (CRules : SeparationLogicSig) := CRules.toContext.logic_equiv

end SeparationLogicSig

def aligned_2 (x : Int) : Prop := x % 2 = 0

def aligned_4 (x : Int) : Prop := x % 4 = 0

def aligned_8 (x : Int) : Prop := x % 8 = 0

def isvalidptr_char (x : Int) : Prop :=
  x >= 0 ∧ x <= Int.max_unsigned

def isvalidptr_short (x : Int) : Prop :=
  x >= 0 ∧ x + 1 <= Int.max_unsigned ∧ aligned_2 x

def isvalidptr_int (x : Int) : Prop :=
  x >= 0 ∧ x + 3 <= Int.max_unsigned ∧ aligned_4 x

def isvalidptr_int64 (x : Int) : Prop :=
  x >= 0 ∧ x + 7 <= Int.max_unsigned ∧ aligned_4 x

def isvalidptr (x : Int) : Prop :=
  x >= 0 ∧ x + 3 <= Int.max_unsigned ∧ aligned_4 x

def merge_short (x1 x2 y : Int) : Prop :=
  y % (2 ^ 16) = x1 % (2 ^ 8) * (2 ^ 8) + x2 % (2 ^ 8)

theorem merge_short_255_255_neg_1 : merge_short 255 255 (-1) := by rfl

theorem merge_short_255_neg1_neg_1 : merge_short 255 (-1) (-1) := by rfl

def merge_int (x1 x2 x3 x4 y : Int) : Prop :=
  y % (2 ^ 32) =
    x1 % (2 ^ 8) * (2 ^ 24) +
    x2 % (2 ^ 8) * (2 ^ 16) +
    x3 % (2 ^ 8) * (2 ^ 8) +
    x4 % (2 ^ 8)

def merge_int64 (x1 x2 x3 x4 x5 x6 x7 x8 y : Int) : Prop :=
  y % (2 ^ 64) =
    x1 % (2 ^ 8) * (2 ^ 56) +
    x2 % (2 ^ 8) * (2 ^ 48) +
    x3 % (2 ^ 8) * (2 ^ 40) +
    x4 % (2 ^ 8) * (2 ^ 32) +
    x5 % (2 ^ 8) * (2 ^ 24) +
    x6 % (2 ^ 8) * (2 ^ 16) +
    x7 % (2 ^ 8) * (2 ^ 8) +
    x8 % (2 ^ 8)

theorem merge_int_equiv
    (x1 x2 x3 x4 v1 v2 v3 v4 z : Int)
    (hx1 : -128 <= x1 ∧ x1 < 128)
    (hx2 : -128 <= x2 ∧ x2 < 128)
    (hx3 : -128 <= x3 ∧ x3 < 128)
    (hx4 : -128 <= x4 ∧ x4 < 128)
    (hv1 : -128 <= v1 ∧ v1 < 128)
    (hv2 : -128 <= v2 ∧ v2 < 128)
    (hv3 : -128 <= v3 ∧ v3 < 128)
    (hv4 : -128 <= v4 ∧ v4 < 128)
    (hx : merge_int x1 x2 x3 x4 z)
    (hv : merge_int v1 v2 v3 v4 z) :
    x1 = v1 ∧ x2 = v2 ∧ x3 = v3 ∧ x4 = v4 := by
  simp [merge_int] at hx hv
  omega

theorem merge_uint_equiv
    (x1 x2 x3 x4 v1 v2 v3 v4 z : Int)
    (hx1 : 0 <= x1 ∧ x1 < 256)
    (hx2 : 0 <= x2 ∧ x2 < 256)
    (hx3 : 0 <= x3 ∧ x3 < 256)
    (hx4 : 0 <= x4 ∧ x4 < 256)
    (hv1 : 0 <= v1 ∧ v1 < 256)
    (hv2 : 0 <= v2 ∧ v2 < 256)
    (hv3 : 0 <= v3 ∧ v3 < 256)
    (hv4 : 0 <= v4 ∧ v4 < 256)
    (hx : merge_int x1 x2 x3 x4 z)
    (hv : merge_int v1 v2 v3 v4 z) :
    x1 = v1 ∧ x2 = v2 ∧ x3 = v3 ∧ x4 = v4 := by
  simp [merge_int] at hx hv
  omega

end SimpleC.SL.CommonAssertion
