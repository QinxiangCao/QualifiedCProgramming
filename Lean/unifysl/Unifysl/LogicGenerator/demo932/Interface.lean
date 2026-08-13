/- Coq inventory: unifysl-prp_qcp/LogicGenerator/demo932/Interface.v
   Active declarations migrated:
   - LanguageSig
   - DerivedNamesSig
   - PrimitiveRuleSig
   - LogicTheoremSig
   - LogicTheoremSig'

   Lean-safe surface notes:
   - Coq module types are represented by structures plus namespaced
     definitions.
   - Coq `positive` is the migrated `PTree.positive`; this file exposes a
     local alias under the demo932 namespace because `PTree` is a top-level
     namespace in the current Lean port.
   - Coq exported instance leaf names that begin with `_` are represented in
     `LogicTheoremSig'` with Lean-safe `*_inst` field names.
   - The commented IPSolver block in the Coq source is intentionally outside
     the active declaration set.
-/

import Unifysl.Lib.PTree
import Unifysl.Lib.Relation_ext
import Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage
import Unifysl.GeneralLogic.ProofTheory.BasicDeduction
import Unifysl.GeneralLogic.ProofTheory.BasicLogicEquiv
import Unifysl.MetaLogicInj.ProofTheory.ProofRules
import Unifysl.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic
import Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic
import Unifysl.MinimumLogic.ProofTheory.RewriteClass
import Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic
import Unifysl.PropositionalLogic.ProofTheory.Intuitionistic
import Unifysl.PropositionalLogic.ProofTheory.RewriteClass
import Unifysl.SeparationLogic.Model.SeparationAlgebra
import Unifysl.SeparationLogic.ProofTheory.Corable
import Unifysl.SeparationLogic.ProofTheory.Deduction
import Unifysl.SeparationLogic.ProofTheory.DerivedRules
import Unifysl.SeparationLogic.ProofTheory.IterSepcon
import Unifysl.SeparationLogic.ProofTheory.RewriteClass
import Unifysl.SeparationLogic.ProofTheory.TheoryOfCancel
import Unifysl.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms
import Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic
import Unifysl.ShallowQuantifierLogic.ModelConstrALL
import Unifysl.ShallowQuantifierLogic.ModelConstrEX

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u v

namespace Unifysl
namespace LogicGenerator
namespace demo932

open Relation_ext

abbrev positive : Type :=
  PTree.positive

structure LanguageSig : Type (u + 1) where
  model : Type u
  join : model -> model -> model -> Prop
  is_unit : model -> Prop

namespace LanguageSig

abbrev expr (Names : LanguageSig.{u}) : Type u :=
  Names.model -> Prop

end LanguageSig

structure DerivedNamesSig (Names : LanguageSig.{u}) : Type (u + 1) where

namespace DerivedNamesSig

abbrev expr {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) : Type u :=
  Names.expr

def sepcon {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Names.expr -> Names.expr :=
  fun x y m => exists m1 m2 : Names.model, Names.join m1 m2 m /\ x m1 /\ y m2

def wand {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Names.expr -> Names.expr :=
  fun x y m => forall m1 m2 : Names.model, Names.join m m1 m2 -> x m1 -> y m2

def orp {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Names.expr -> Names.expr :=
  fun x y m => x m \/ y m

def andp {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Names.expr -> Names.expr :=
  fun x y m => x m /\ y m

def impp {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Names.expr -> Names.expr :=
  fun x y m => x m -> y m

def exp {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names)
    (A : Type v) (x : A -> Names.expr) : Names.expr :=
  fun m => exists a : A, x a m

def allp {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names)
    (A : Type v) (x : A -> Names.expr) : Names.expr :=
  fun m => forall a : A, x a m

def emp {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) :
    Names.expr :=
  fun m => Names.is_unit m

def coq_prop {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names)
    (P : Prop) : Names.expr :=
  fun _ => P

def truep {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) :
    Names.expr :=
  fun _ => True

def multi_imp {Names : LanguageSig.{u}} (DerivedNames : DerivedNamesSig Names)
    (xs : List Names.expr) (y : Names.expr) : Names.expr :=
  List.foldr (fun x acc => impp DerivedNames x acc) y xs

def iter_sepcon {Names : LanguageSig.{u}} (DerivedNames : DerivedNamesSig Names)
    (xs : List Names.expr) : Names.expr :=
  List.foldl (fun acc x => sepcon DerivedNames acc x) (emp DerivedNames) xs

def iffp {Names : LanguageSig.{u}} (DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Names.expr -> Names.expr :=
  fun x y => andp DerivedNames (impp DerivedNames x y) (impp DerivedNames y x)

def derivable1 {Names : LanguageSig.{u}} (_DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Names.expr -> Prop :=
  fun x y => forall m : Names.model, x m -> y m

def provable {Names : LanguageSig.{u}} (DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Prop :=
  fun x => derivable1 DerivedNames (impp DerivedNames x x) x

def logic_equiv {Names : LanguageSig.{u}} (DerivedNames : DerivedNamesSig Names) :
    Names.expr -> Names.expr -> Prop :=
  fun x y => derivable1 DerivedNames x y /\ derivable1 DerivedNames y x

end DerivedNamesSig

structure PrimitiveRuleSig (Names : LanguageSig.{u})
    (DerivedNames : DerivedNamesSig Names) : Type (u + 1) where
  unit_join :
    forall n : Names.model, exists u : Names.model, Names.is_unit u /\ Names.join n u n
  unit_spec :
    forall n m u : Names.model, Names.is_unit u -> Names.join n u m -> n = m
  join_comm :
    forall m1 m2 m : Names.model, Names.join m1 m2 m -> Names.join m2 m1 m
  join_assoc :
    forall mx my mz mxy mxyz : Names.model,
      Names.join mx my mxy ->
      Names.join mxy mz mxyz ->
      exists myz : Names.model, Names.join my mz myz /\ Names.join mx myz mxyz

private def modelOf (Names : LanguageSig.{u}) : Model.{u} where
  model := Names.model

private def languageOf (Names : LanguageSig.{u}) : Language.{u} where
  expr := Names.expr

private def joinOf (Names : LanguageSig.{u}) : Join Names.model where
  join := Names.join

private def unitOf (Names : LanguageSig.{u}) : Unit Names.model where
  is_unit := Names.is_unit

private def sepconLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : SepconLanguage (languageOf Names) where
  sepcon := DerivedNamesSig.sepcon DerivedNames

private def wandLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : WandLanguage (languageOf Names) where
  wand := DerivedNamesSig.wand DerivedNames

private def orLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : OrLanguage (languageOf Names) where
  orp := DerivedNamesSig.orp DerivedNames

private def andLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : AndLanguage (languageOf Names) where
  andp := DerivedNamesSig.andp DerivedNames

private def minimumLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : MinimumLanguage (languageOf Names) where
  impp := DerivedNamesSig.impp DerivedNames

private def expLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) :
    ShallowExistsLanguage.{u, v} (languageOf Names) where
  exp := fun {A} x => DerivedNamesSig.exp DerivedNames A x

private def allpLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) :
    ShallowForallLanguage.{u, v} (languageOf Names) where
  allp := fun {A} x => DerivedNamesSig.allp DerivedNames A x

private def empLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : EmpLanguage (languageOf Names) where
  emp := DerivedNamesSig.emp DerivedNames

private def coqPropLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : CoqPropLanguage (languageOf Names) where
  coq_prop := DerivedNamesSig.coq_prop DerivedNames

private def trueLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : TrueLanguage (languageOf Names) where
  truep := DerivedNamesSig.truep DerivedNames

private def iterSepconLanguageOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : IterSepconLanguage (languageOf Names) where
  iter_sepcon := DerivedNamesSig.iter_sepcon DerivedNames

private def derivable1Of {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : Derivable1 (languageOf Names) where
  derivable1 := DerivedNamesSig.derivable1 DerivedNames

private def logicEquivOf {Names : LanguageSig.{u}}
    (DerivedNames : DerivedNamesSig Names) : LogicEquiv (languageOf Names) where
  logic_equiv := DerivedNamesSig.logic_equiv DerivedNames

private def separationAlgebraOf {Names : LanguageSig.{u}}
    {DerivedNames : DerivedNamesSig Names}
    (Rules : PrimitiveRuleSig Names DerivedNames) : by
      letI : Join Names.model := joinOf Names
      exact SeparationAlgebra Names.model := by
  letI : Join Names.model := joinOf Names
  exact {
    join_comm := Rules.join_comm
    join_assoc := Rules.join_assoc }

private def unitJoinRelationOf {Names : LanguageSig.{u}}
    {DerivedNames : DerivedNamesSig Names}
    (Rules : PrimitiveRuleSig Names DerivedNames) : by
      letI : Unit Names.model := unitOf Names
      letI : Join Names.model := joinOf Names
      exact UnitJoinRelation Names.model := by
  letI : Unit Names.model := unitOf Names
  letI : Join Names.model := joinOf Names
  exact {
    unit_join := Rules.unit_join
    unit_spec := Rules.unit_spec }

structure LogicTheoremSig (Names : LanguageSig.{u})
    (DerivedNames : DerivedNamesSig Names)
    (Rules : PrimitiveRuleSig Names DerivedNames) : Type (max (u + 1) (v + 1)) where
  tree_pos : Type u
  coq_prop_right :
    forall (P : Prop) (x : Names.expr),
      P -> DerivedNamesSig.derivable1 DerivedNames x (DerivedNamesSig.coq_prop DerivedNames P)
  coq_prop_left :
    forall (P : Prop) (x : Names.expr),
      (P -> DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.truep DerivedNames) x) ->
        DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) x
  iter_sepcon_d1_left1 :
    forall xs : List Names.expr,
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.iter_sepcon DerivedNames xs)
        (List.foldl (fun acc x => DerivedNamesSig.sepcon DerivedNames acc x)
          (DerivedNamesSig.emp DerivedNames) xs)
  iter_sepcon_d1_left2 :
    forall xs : List Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (List.foldl (fun acc x => DerivedNamesSig.sepcon DerivedNames acc x)
          (DerivedNamesSig.emp DerivedNames) xs)
        (DerivedNamesSig.iter_sepcon DerivedNames xs)
  shallow_exp_right :
    forall (A : Type v) (P : Names.expr) (Q : A -> Names.expr) (x : A),
      DerivedNamesSig.derivable1 DerivedNames P (Q x) ->
      DerivedNamesSig.derivable1 DerivedNames P (DerivedNamesSig.exp DerivedNames A Q)
  shallow_exp_left :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      (forall x : A, DerivedNamesSig.derivable1 DerivedNames (P x) Q) ->
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.exp DerivedNames A P) Q
  shallow_allp_right :
    forall (A : Type v) (P : Names.expr) (Q : A -> Names.expr),
      (forall x : A, DerivedNamesSig.derivable1 DerivedNames P (Q x)) ->
      DerivedNamesSig.derivable1 DerivedNames P (DerivedNamesSig.allp DerivedNames A Q)
  shallow_allp_left :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr) (x : A),
      DerivedNamesSig.derivable1 DerivedNames (P x) Q ->
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.allp DerivedNames A P) Q
  sepcon_emp_left :
    forall x : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.emp DerivedNames)) x
  sepcon_emp_right :
    forall x : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.emp DerivedNames))
  derivable1_wand_sepcon_adjoint :
    forall x y z : Names.expr,
      (DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.sepcon DerivedNames x y) z <->
        DerivedNamesSig.derivable1 DerivedNames x (DerivedNamesSig.wand DerivedNames y z))
  derivable1_sepcon_comm :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x y)
        (DerivedNamesSig.sepcon DerivedNames y x)
  derivable1_sepcon_assoc1 :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.sepcon DerivedNames y z))
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.sepcon DerivedNames x y) z)
  derivable1_sepcon_mono :
    forall x1 x2 y1 y2 : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x1 x2 ->
      DerivedNamesSig.derivable1 DerivedNames y1 y2 ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x1 y1)
        (DerivedNamesSig.sepcon DerivedNames x2 y2)
  derivable1_truep_intros :
    forall x : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x (DerivedNamesSig.truep DerivedNames)
  derivable1s_truep_intros :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x y ->
      DerivedNamesSig.derivable1 DerivedNames x z ->
      DerivedNamesSig.derivable1 DerivedNames x (DerivedNamesSig.andp DerivedNames y z)
  derivable1_andp_elim1 :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.andp DerivedNames x y) x
  derivable1_andp_elim2 :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.andp DerivedNames x y) y
  derivable1_orp_intros1 :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x (DerivedNamesSig.orp DerivedNames x y)
  derivable1_orp_intros2 :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames y (DerivedNamesSig.orp DerivedNames x y)
  derivable1_orp_elim :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x z ->
      DerivedNamesSig.derivable1 DerivedNames y z ->
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.orp DerivedNames x y) z
  derivable1s_impp_andp_adjoint :
    forall x y z : Names.expr,
      (DerivedNamesSig.derivable1 DerivedNames x (DerivedNamesSig.impp DerivedNames y z) <->
        DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.andp DerivedNames x y) z)
  derivable1_refl :
    forall x : Names.expr, DerivedNamesSig.derivable1 DerivedNames x x
  derivable1_trans :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x y ->
      DerivedNamesSig.derivable1 DerivedNames y z ->
      DerivedNamesSig.derivable1 DerivedNames x z
  expr_deep : Type
  impp_deep : expr_deep -> expr_deep -> expr_deep
  sepcon_deep : expr_deep -> expr_deep -> expr_deep
  emp_deep : expr_deep
  varp_deep : Nat -> expr_deep
  var_pos : Names.expr -> Option positive -> tree_pos
  sepcon_pos : tree_pos -> tree_pos -> tree_pos
  cancel_mark : expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos × tree_pos
  cancel_different : tree_pos -> tree_pos -> Names.expr
  cancel_same : tree_pos -> tree_pos -> Prop
  restore : tree_pos -> tree_pos -> Names.expr
  logic_equiv_sepcon_proper :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames)
      (DerivedNamesSig.sepcon DerivedNames)
  sepcon_comm_logic_equiv :
    forall x y : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x y)
        (DerivedNamesSig.sepcon DerivedNames y x)
  sepcon_assoc_logic_equiv :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.sepcon DerivedNames y z))
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.sepcon DerivedNames x y) z)
  sepcon_emp_logic_equiv :
    forall x : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.emp DerivedNames)) x
  ex_and1 :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.exp DerivedNames A P) Q)
        (DerivedNamesSig.exp DerivedNames A (fun x : A => DerivedNamesSig.andp DerivedNames (P x) Q))
  ex_and2 :
    forall (A : Type v) (P : Names.expr) (Q : A -> Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames P (DerivedNamesSig.exp DerivedNames A Q))
        (DerivedNamesSig.exp DerivedNames A (fun x : A => DerivedNamesSig.andp DerivedNames P (Q x)))
  ex_sepcon1 :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.exp DerivedNames A P) Q)
        (DerivedNamesSig.exp DerivedNames A (fun x : A => DerivedNamesSig.sepcon DerivedNames (P x) Q))
  ex_sepcon2 :
    forall (A : Type v) (P : Names.expr) (Q : A -> Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames P (DerivedNamesSig.exp DerivedNames A Q))
        (DerivedNamesSig.exp DerivedNames A (fun x : A => DerivedNamesSig.sepcon DerivedNames P (Q x)))
  iter_sepcon_flatten :
    forall xs1 xs2 xs3 : List Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.iter_sepcon DerivedNames
          (xs1 ++ (DerivedNamesSig.iter_sepcon DerivedNames xs2 :: xs3)))
        (DerivedNamesSig.iter_sepcon DerivedNames (xs1 ++ xs2 ++ xs3))
  sepcon_andp_prop1 :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q) R))
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q)
          (DerivedNamesSig.sepcon DerivedNames P R))
  sepcon_andp_prop2 :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q)
          (DerivedNamesSig.sepcon DerivedNames P R))
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q) R))
  sepcon_andp_prop3 :
    forall (P Q : Names.expr) (R : Prop),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames Q (DerivedNamesSig.coq_prop DerivedNames R)))
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames R)
          (DerivedNamesSig.sepcon DerivedNames P Q))
  sepcon_andp_prop4 :
    forall (P Q : Names.expr) (R : Prop),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames R)
          (DerivedNamesSig.sepcon DerivedNames P Q))
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames Q (DerivedNamesSig.coq_prop DerivedNames R)))
  sepcon_andp_prop5 :
    forall (P : Prop) (Q R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) R)
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.sepcon DerivedNames Q R))
  sepcon_andp_prop6 :
    forall (P : Prop) (Q R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.sepcon DerivedNames Q R))
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) R)
  sepcon_andp_prop7 :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames P (DerivedNamesSig.coq_prop DerivedNames Q)) R)
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q)
          (DerivedNamesSig.sepcon DerivedNames P R))
  sepcon_andp_prop8 :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q)
          (DerivedNamesSig.sepcon DerivedNames P R))
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames P (DerivedNamesSig.coq_prop DerivedNames Q)) R)
  iter_sepcon_andp_prop :
    forall (xs1 : List Names.expr) (P : Prop) (x2 : Names.expr) (xs3 : List Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.iter_sepcon DerivedNames
          (xs1 ++ (DerivedNamesSig.andp DerivedNames
            (DerivedNamesSig.coq_prop DerivedNames P) x2 :: xs3)))
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.iter_sepcon DerivedNames (xs1 ++ (x2 :: xs3))))
  derivable1_sepcon_iter_sepcon1 :
    forall xs ys : List Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.iter_sepcon DerivedNames xs)
          (DerivedNamesSig.iter_sepcon DerivedNames ys))
        (DerivedNamesSig.iter_sepcon DerivedNames (xs ++ ys))
  derivable1_sepcon_iter_sepcon2 :
    forall xs ys : List Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.iter_sepcon DerivedNames (xs ++ ys))
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.iter_sepcon DerivedNames xs)
          (DerivedNamesSig.iter_sepcon DerivedNames ys))
  derivable1_refl_instance :
    Reflexive (DerivedNamesSig.derivable1 DerivedNames) := by
      intro x
      exact derivable1_refl x
  derivable1_trans_instance :
    Transitive (DerivedNamesSig.derivable1 DerivedNames) := by
      intro x y z hxy hyz
      exact derivable1_trans x y z hxy hyz

namespace LogicTheoremSig

variable {Names : LanguageSig.{u}} {DerivedNames : DerivedNamesSig Names}
variable {Rules : PrimitiveRuleSig Names DerivedNames}

theorem derivable1s_coq_prop_r (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (x : Names.expr),
      P -> DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.coq_prop DerivedNames P) :=
  self.coq_prop_right

theorem derivable1s_coq_prop_l (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (x : Names.expr),
      (P -> DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.truep DerivedNames) x) ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.coq_prop DerivedNames P) x :=
  self.coq_prop_left

theorem derivable1_iter_sepcon_l (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall xs : List Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.iter_sepcon DerivedNames xs)
        (List.foldl (fun acc x => DerivedNamesSig.sepcon DerivedNames acc x)
          (DerivedNamesSig.emp DerivedNames) xs) :=
  self.iter_sepcon_d1_left1

theorem derivable1_iter_sepcon_r (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall xs : List Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (List.foldl (fun acc x => DerivedNamesSig.sepcon DerivedNames acc x)
          (DerivedNamesSig.emp DerivedNames) xs)
        (DerivedNamesSig.iter_sepcon DerivedNames xs) :=
  self.iter_sepcon_d1_left2

theorem derivable1s_exp_r (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : Names.expr) (Q : A -> Names.expr) (x : A),
      DerivedNamesSig.derivable1 DerivedNames P (Q x) ->
      DerivedNamesSig.derivable1 DerivedNames P
        (DerivedNamesSig.exp DerivedNames A Q) :=
  self.shallow_exp_right

theorem derivable1s_exp_l (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      (forall x : A, DerivedNamesSig.derivable1 DerivedNames (P x) Q) ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.exp DerivedNames A P) Q :=
  self.shallow_exp_left

theorem derivable1s_allp_r (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : Names.expr) (Q : A -> Names.expr),
      (forall x : A, DerivedNamesSig.derivable1 DerivedNames P (Q x)) ->
      DerivedNamesSig.derivable1 DerivedNames P
        (DerivedNamesSig.allp DerivedNames A Q) :=
  self.shallow_allp_right

theorem derivable1s_allp_l (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr) (x : A),
      DerivedNamesSig.derivable1 DerivedNames (P x) Q ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.allp DerivedNames A P) Q :=
  self.shallow_allp_left

theorem derivable1_sepcon_emp_l (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.emp DerivedNames)) x :=
  self.sepcon_emp_left

theorem derivable1_sepcon_emp_r (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.emp DerivedNames)) :=
  self.sepcon_emp_right

theorem derivable1s_wand_sepcon_adjoint
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      (DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x y) z <->
        DerivedNamesSig.derivable1 DerivedNames x
          (DerivedNamesSig.wand DerivedNames y z)) :=
  self.derivable1_wand_sepcon_adjoint

theorem __derivable1_provable (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x y <->
        DerivedNamesSig.provable DerivedNames
          (DerivedNamesSig.impp DerivedNames x y) := by
  intro x y
  constructor
  · intro h m _
    exact h m
  · intro h m hx
    exact h m (fun hxy => hxy) hx

theorem logic_equiv_sepcon_emp (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.emp DerivedNames)) x :=
  self.sepcon_emp_logic_equiv

theorem logic_equiv_sepcon_comm (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x y)
        (DerivedNamesSig.sepcon DerivedNames y x) :=
  self.sepcon_comm_logic_equiv

theorem logic_equiv_sepcon_assoc (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.sepcon DerivedNames y z))
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.sepcon DerivedNames x y) z) :=
  self.sepcon_assoc_logic_equiv

theorem logic_equiv_andp_comm (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.andp DerivedNames x y)
        (DerivedNamesSig.andp DerivedNames y x) := by
  intro x y
  exact ⟨fun m h => ⟨h.right, h.left⟩, fun m h => ⟨h.right, h.left⟩⟩

theorem logic_equiv_andp_assoc (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.andp DerivedNames x y) z)
        (DerivedNamesSig.andp DerivedNames x (DerivedNamesSig.andp DerivedNames y z)) := by
  intro x y z
  exact
    ⟨fun m h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩,
      fun m h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩⟩

theorem logic_equiv_andp_swap (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.andp DerivedNames x
          (DerivedNamesSig.andp DerivedNames y z))
        (DerivedNamesSig.andp DerivedNames y
          (DerivedNamesSig.andp DerivedNames x z)) := by
  intro x y z
  exact
    ⟨fun m h => ⟨h.right.left, ⟨h.left, h.right.right⟩⟩,
      fun m h => ⟨h.right.left, ⟨h.left, h.right.right⟩⟩⟩

theorem logic_equiv_coq_prop_or (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall P Q : Prop,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.coq_prop DerivedNames (P \/ Q))
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.coq_prop DerivedNames Q)) := by
  intro P Q
  exact ⟨fun _ h => h, fun _ h => h⟩

theorem logic_equiv_coq_prop_and (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall P Q : Prop,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.coq_prop DerivedNames (P /\ Q))
        (DerivedNamesSig.andp DerivedNames
          (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.coq_prop DerivedNames Q)) := by
  intro P Q
  exact ⟨fun _ h => h, fun _ h => h⟩

theorem derivables_false_coq_prop (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q : Names.expr), (P -> False) ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.coq_prop DerivedNames P) Q := by
  intro P Q hfalse
  exact self.coq_prop_left P Q (fun hP => False.elim (hfalse hP))

private theorem provable_of_forall (x : Names.expr)
    (h : forall m : Names.model, x m) :
    DerivedNamesSig.provable DerivedNames x := by
  intro m _
  exact h m

private theorem forall_of_provable (x : Names.expr)
    (h : DerivedNamesSig.provable DerivedNames x) :
    forall m : Names.model, x m := by
  intro m
  exact h m (fun hx => hx)

private theorem provable_of_derivable1
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules)
    {x y : Names.expr}
    (h : DerivedNamesSig.derivable1 DerivedNames x y) :
    DerivedNamesSig.provable DerivedNames
      (DerivedNamesSig.impp DerivedNames x y) :=
  ((__derivable1_provable self) x y).mp h

private theorem derivable1_of_provable
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules)
    {x y : Names.expr}
    (h : DerivedNamesSig.provable DerivedNames
      (DerivedNamesSig.impp DerivedNames x y)) :
    DerivedNamesSig.derivable1 DerivedNames x y :=
  ((__derivable1_provable self) x y).mpr h

theorem logic_equiv_andp_truep (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.andp DerivedNames x (DerivedNamesSig.truep DerivedNames)) x := by
  intro x
  exact ⟨fun m h => h.left, fun m hx => ⟨hx, True.intro⟩⟩

theorem logic_equiv_truep_andp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.truep DerivedNames) x) x := by
  intro x
  exact ⟨fun m h => h.right, fun m hx => ⟨True.intro, hx⟩⟩

theorem logic_equiv_orp_congr (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x1 x2 y1 y2 : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames x1 x2 ->
      DerivedNamesSig.logic_equiv DerivedNames y1 y2 ->
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.orp DerivedNames x1 y1)
        (DerivedNamesSig.orp DerivedNames x2 y2) := by
  intro x1 x2 y1 y2 hx hy
  constructor
  · intro m h
    cases h with
    | inl hx1 => exact Or.inl (hx.left m hx1)
    | inr hy1 => exact Or.inr (hy.left m hy1)
  · intro m h
    cases h with
    | inl hx2 => exact Or.inl (hx.right m hx2)
    | inr hy2 => exact Or.inr (hy.right m hy2)

theorem logic_equiv_orp_comm (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.orp DerivedNames x y)
        (DerivedNamesSig.orp DerivedNames y x) := by
  intro x y
  exact
    ⟨fun _ h => h.elim Or.inr Or.inl,
      fun _ h => h.elim Or.inr Or.inl⟩

theorem logic_equiv_orp_assoc (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.orp DerivedNames (DerivedNamesSig.orp DerivedNames x y) z)
        (DerivedNamesSig.orp DerivedNames x (DerivedNamesSig.orp DerivedNames y z)) := by
  intro x y z
  constructor
  · intro m h
    cases h with
    | inl hxy =>
        cases hxy with
        | inl hx => exact Or.inl hx
        | inr hy => exact Or.inr (Or.inl hy)
    | inr hz => exact Or.inr (Or.inr hz)
  · intro m h
    cases h with
    | inl hx => exact Or.inl (Or.inl hx)
    | inr hyz =>
        cases hyz with
        | inl hy => exact Or.inl (Or.inr hy)
        | inr hz => exact Or.inr hz

theorem logic_equiv_andp_congr (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x1 x2 y1 y2 : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames x1 x2 ->
      DerivedNamesSig.logic_equiv DerivedNames y1 y2 ->
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.andp DerivedNames x1 y1)
        (DerivedNamesSig.andp DerivedNames x2 y2) := by
  intro x1 x2 y1 y2 hx hy
  constructor
  · intro m h
    exact ⟨hx.left m h.left, hy.left m h.right⟩
  · intro m h
    exact ⟨hx.right m h.left, hy.right m h.right⟩

theorem derivable1_orp_sepcon_l (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.orp DerivedNames x y) z)
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x z)
          (DerivedNamesSig.sepcon DerivedNames y z)) := by
  intro x y z m h
  rcases h with ⟨m1, m2, hj, hxy, hz⟩
  cases hxy with
  | inl hx => exact Or.inl ⟨m1, m2, hj, hx, hz⟩
  | inr hy => exact Or.inr ⟨m1, m2, hj, hy, hz⟩

theorem derivable1_iffp_intros (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.impp DerivedNames x y)
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames y x)
          (DerivedNamesSig.iffp DerivedNames x y)) := by
  intro x y m hxy hyx
  exact ⟨hxy, hyx⟩

theorem derivable1_iffp_elim1 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.iffp DerivedNames x y)
        (DerivedNamesSig.impp DerivedNames x y) := by
  intro x y m h
  exact h.left

theorem derivable1_iffp_elim2 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.iffp DerivedNames x y)
        (DerivedNamesSig.impp DerivedNames y x) := by
  intro x y m h
  exact h.right

theorem derivable1_andp_intros (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x y ->
      DerivedNamesSig.derivable1 DerivedNames x z ->
      DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.andp DerivedNames y z) :=
  self.derivable1s_truep_intros

theorem derivable1_impp_andp_adjoint
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      (DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.impp DerivedNames y z) <->
        DerivedNamesSig.derivable1 DerivedNames
          (DerivedNamesSig.andp DerivedNames x y) z) :=
  self.derivable1s_impp_andp_adjoint

theorem derivable1s_modus_ponens (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x (DerivedNamesSig.impp DerivedNames y z) ->
      DerivedNamesSig.derivable1 DerivedNames x y ->
      DerivedNamesSig.derivable1 DerivedNames x z := by
  intro x y z hxy hy m hx
  exact hxy m hx (hy m hx)

theorem derivable1s_impp_intros (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.impp DerivedNames x y) z ->
      DerivedNamesSig.derivable1 DerivedNames x (DerivedNamesSig.impp DerivedNames y z) := by
  intro x y z h m hx hy
  exact h m (fun _ => hy)

theorem derivable1_impp_refl (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.impp DerivedNames y y) := by
  intro x y m _ hy
  exact hy

theorem derivable1_axiom1 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.impp DerivedNames y x) := by
  intro x y m hx _
  exact hx

theorem derivable1_axiom2 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.impp DerivedNames x
          (DerivedNamesSig.impp DerivedNames y z))
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x y)
          (DerivedNamesSig.impp DerivedNames x z)) := by
  intro x y z m hxy hx hx'
  exact hxy hx' (hx hx')

theorem provable_iter_sepcon_derives
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall xs : List Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.iter_sepcon DerivedNames xs)
          (List.foldl (fun acc x => DerivedNamesSig.sepcon DerivedNames acc x)
            (DerivedNamesSig.emp DerivedNames) xs)) := by
  intro xs
  exact provable_of_derivable1 self (self.iter_sepcon_d1_left1 xs)

theorem provable_derives_iter_sepcon
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall xs : List Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (List.foldl (fun acc x => DerivedNamesSig.sepcon DerivedNames acc x)
            (DerivedNamesSig.emp DerivedNames) xs)
          (DerivedNamesSig.iter_sepcon DerivedNames xs)) := by
  intro xs
  exact provable_of_derivable1 self (self.iter_sepcon_d1_left2 xs)

theorem provable_sepcon_comm_impp
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x y)
          (DerivedNamesSig.sepcon DerivedNames y x)) := by
  intro x y
  exact provable_of_derivable1 self (self.derivable1_sepcon_comm x y)

theorem provable_sepcon_assoc1
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x
            (DerivedNamesSig.sepcon DerivedNames y z))
          (DerivedNamesSig.sepcon DerivedNames
            (DerivedNamesSig.sepcon DerivedNames x y) z)) := by
  intro x y z
  exact provable_of_derivable1 self (self.derivable1_sepcon_assoc1 x y z)

theorem provable_sepcon_mono
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x1 x2 y1 y2 : Names.expr,
      DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x1 x2) ->
      DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames y1 y2) ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x1 y1)
          (DerivedNamesSig.sepcon DerivedNames x2 y2)) := by
  intro x1 x2 y1 y2 hx hy
  exact provable_of_derivable1 self
    (self.derivable1_sepcon_mono x1 x2 y1 y2
      (derivable1_of_provable self hx) (derivable1_of_provable self hy))

theorem provables_coq_prop_intros (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall P : Prop,
      P -> DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.coq_prop DerivedNames P) := by
  intro P hP
  exact provable_of_forall _ (fun _ => hP)

theorem provables_coq_prop_elim (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (x : Names.expr),
      (P -> DerivedNamesSig.provable DerivedNames x) ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.coq_prop DerivedNames P) x) := by
  intro P x h
  exact provable_of_forall _ (fun m hP => forall_of_provable x (h hP) m)

theorem provable_iffp_intros (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x y)
          (DerivedNamesSig.impp DerivedNames
            (DerivedNamesSig.impp DerivedNames y x)
            (DerivedNamesSig.iffp DerivedNames x y))) := by
  intro x y
  exact provable_of_forall _ (fun _ hxy hyx => ⟨hxy, hyx⟩)

theorem provable_iffp_elim1 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.iffp DerivedNames x y)
          (DerivedNamesSig.impp DerivedNames x y)) := by
  intro x y
  exact provable_of_forall _ (fun _ h => h.left)

theorem provable_iffp_elim2 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.iffp DerivedNames x y)
          (DerivedNamesSig.impp DerivedNames y x)) := by
  intro x y
  exact provable_of_forall _ (fun _ h => h.right)

theorem provable_orp_intros1 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames x
          (DerivedNamesSig.orp DerivedNames x y)) := by
  intro x y
  exact provable_of_forall _ (fun _ hx => Or.inl hx)

theorem provable_orp_intros2 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames y
          (DerivedNamesSig.orp DerivedNames x y)) := by
  intro x y
  exact provable_of_forall _ (fun _ hy => Or.inr hy)

theorem provable_orp_elim (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x z)
          (DerivedNamesSig.impp DerivedNames
            (DerivedNamesSig.impp DerivedNames y z)
            (DerivedNamesSig.impp DerivedNames
              (DerivedNamesSig.orp DerivedNames x y) z))) := by
  intro x y z
  exact provable_of_forall _ (fun _ hxz hyz hxy => hxy.elim hxz hyz)

theorem provable_andp_intros (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames x
          (DerivedNamesSig.impp DerivedNames y
            (DerivedNamesSig.andp DerivedNames x y))) := by
  intro x y
  exact provable_of_forall _ (fun _ hx hy => ⟨hx, hy⟩)

theorem provable_andp_elim1 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.andp DerivedNames x y) x) := by
  intro x y
  exact provable_of_forall _ (fun _ h => h.left)

theorem provable_andp_elim2 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.andp DerivedNames x y) y) := by
  intro x y
  exact provable_of_forall _ (fun _ h => h.right)

theorem provables_modus_ponens (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y) ->
      DerivedNamesSig.provable DerivedNames x ->
      DerivedNamesSig.provable DerivedNames y := by
  intro x y hxy hx
  exact provable_of_forall _ (fun m => forall_of_provable _ hxy m (forall_of_provable _ hx m))

theorem provable_axiom1 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames x
          (DerivedNamesSig.impp DerivedNames y x)) := by
  intro x y
  exact provable_of_forall _ (fun _ hx _ => hx)

theorem provable_axiom2 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x
            (DerivedNamesSig.impp DerivedNames y z))
          (DerivedNamesSig.impp DerivedNames
            (DerivedNamesSig.impp DerivedNames x y)
            (DerivedNamesSig.impp DerivedNames x z))) := by
  intro x y z
  exact provable_of_forall _ (fun _ hxy hx hx' => hxy hx' (hx hx'))

theorem provable_impp_refl (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames x x) := by
  intro x
  exact provable_of_forall _ (fun _ hx => hx)

theorem provable_impp_refl' (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      x = y ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames x y) := by
  intro x y h
  subst y
  exact provable_of_forall _ (fun _ hx => hx)

theorem provable_impp_arg_switch (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x
            (DerivedNamesSig.impp DerivedNames y z))
          (DerivedNamesSig.impp DerivedNames y
            (DerivedNamesSig.impp DerivedNames x z))) := by
  intro x y z
  exact provable_of_forall _ (fun _ hxy hy hx => hxy hx hy)

theorem provable_impp_trans (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x y)
          (DerivedNamesSig.impp DerivedNames
            (DerivedNamesSig.impp DerivedNames y z)
            (DerivedNamesSig.impp DerivedNames x z))) := by
  intro x y z
  exact provable_of_forall _ (fun _ hxy hyz hx => hyz (hxy hx))

private theorem multi_imp_weaken_point (xs : List Names.expr)
    (x y : Names.expr) (m : Names.model)
    (hxy : x m -> y m) :
    DerivedNamesSig.multi_imp DerivedNames xs x m ->
      DerivedNamesSig.multi_imp DerivedNames xs y m := by
  induction xs with
  | nil =>
      exact hxy
  | cons a xs ih =>
      intro h ha
      exact ih (h ha)

private theorem multi_imp_intro_tail_point (xs : List Names.expr)
    (y : Names.expr) (m : Names.model) :
    y m -> DerivedNamesSig.multi_imp DerivedNames xs y m := by
  induction xs with
  | nil =>
      intro hy
      exact hy
  | cons a xs ih =>
      intro hy _
      exact ih hy

private theorem multi_imp_add_head_point (xs1 xs2 : List Names.expr)
    (y : Names.expr) (m : Names.model) :
    DerivedNamesSig.multi_imp DerivedNames xs2 y m ->
      DerivedNamesSig.multi_imp DerivedNames (xs1 ++ xs2) y m := by
  induction xs1 with
  | nil =>
      intro h
      exact h
  | cons a xs ih =>
      intro h _
      exact ih h

private theorem multi_imp_add_tail_point (xs1 xs2 : List Names.expr)
    (y : Names.expr) (m : Names.model) :
    DerivedNamesSig.multi_imp DerivedNames xs1 y m ->
      DerivedNamesSig.multi_imp DerivedNames (xs1 ++ xs2) y m := by
  induction xs1 with
  | nil =>
      intro h
      exact multi_imp_intro_tail_point xs2 y m h
  | cons a xs ih =>
      intro h ha
      exact ih (h ha)

private theorem multi_imp_arg_switch1_point (xs : List Names.expr)
    (x y : Names.expr) (m : Names.model) :
    (x m -> DerivedNamesSig.multi_imp DerivedNames xs y m) ->
      DerivedNamesSig.multi_imp DerivedNames xs
        (DerivedNamesSig.impp DerivedNames x y) m := by
  induction xs with
  | nil =>
      intro h
      exact h
  | cons a xs ih =>
      intro h ha
      exact ih (fun hx => h hx ha)

private theorem multi_imp_arg_switch2_point (xs : List Names.expr)
    (x y : Names.expr) (m : Names.model) :
    DerivedNamesSig.multi_imp DerivedNames xs
      (DerivedNamesSig.impp DerivedNames x y) m ->
      x m -> DerivedNamesSig.multi_imp DerivedNames xs y m := by
  induction xs with
  | nil =>
      intro h hx
      exact h hx
  | cons a xs ih =>
      intro h hx ha
      exact ih (h ha) hx

private theorem multi_imp_shrink_point (xs : List Names.expr)
    (x y : Names.expr) (m : Names.model) :
    (x m -> DerivedNamesSig.multi_imp DerivedNames xs
      (DerivedNamesSig.impp DerivedNames x y) m) ->
      DerivedNamesSig.multi_imp DerivedNames xs
        (DerivedNamesSig.impp DerivedNames x y) m := by
  induction xs with
  | nil =>
      intro h hx
      exact h hx hx
  | cons a xs ih =>
      intro h ha
      exact ih (fun hx => h hx ha)

private theorem multi_imp_modus_ponens_point (xs : List Names.expr)
    (y z : Names.expr) (m : Names.model) :
    DerivedNamesSig.multi_imp DerivedNames xs y m ->
      DerivedNamesSig.multi_imp DerivedNames xs
        (DerivedNamesSig.impp DerivedNames y z) m ->
      DerivedNamesSig.multi_imp DerivedNames xs z m := by
  induction xs with
  | nil =>
      intro hy hyz
      exact hyz hy
  | cons a xs ih =>
      intro hy hyz ha
      exact ih (hy ha) (hyz ha)

theorem provable_multi_imp_shrink (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (xs : List Names.expr) (x y : Names.expr),
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x
            (DerivedNamesSig.multi_imp DerivedNames xs
              (DerivedNamesSig.impp DerivedNames x y)))
          (DerivedNamesSig.multi_imp DerivedNames xs
            (DerivedNamesSig.impp DerivedNames x y))) := by
  intro xs x y
  exact provable_of_forall _ (fun m h => multi_imp_shrink_point xs x y m h)

theorem provable_multi_imp_arg_switch1
    (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (xs : List Names.expr) (x y : Names.expr),
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x
            (DerivedNamesSig.multi_imp DerivedNames xs y))
          (DerivedNamesSig.multi_imp DerivedNames xs
            (DerivedNamesSig.impp DerivedNames x y))) := by
  intro xs x y
  exact provable_of_forall _ (fun m h => multi_imp_arg_switch1_point xs x y m h)

theorem provable_multi_imp_arg_switch2
    (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (xs : List Names.expr) (x y : Names.expr),
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.multi_imp DerivedNames xs
            (DerivedNamesSig.impp DerivedNames x y))
          (DerivedNamesSig.impp DerivedNames x
            (DerivedNamesSig.multi_imp DerivedNames xs y))) := by
  intro xs x y
  exact provable_of_forall _ (fun m h hx => multi_imp_arg_switch2_point xs x y m h hx)

theorem provable_add_multi_imp_left_head
    (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (xs1 xs2 : List Names.expr) (y : Names.expr),
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.multi_imp DerivedNames xs2 y)
          (DerivedNamesSig.multi_imp DerivedNames (xs1 ++ xs2) y)) := by
  intro xs1 xs2 y
  exact provable_of_forall _ (fun m h => multi_imp_add_head_point xs1 xs2 y m h)

theorem provable_add_multi_imp_left_tail
    (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (xs1 xs2 : List Names.expr) (y : Names.expr),
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.multi_imp DerivedNames xs1 y)
          (DerivedNamesSig.multi_imp DerivedNames (xs1 ++ xs2) y)) := by
  intro xs1 xs2 y
  exact provable_of_forall _ (fun m h => multi_imp_add_tail_point xs1 xs2 y m h)

theorem provable_multi_imp_modus_ponens
    (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (xs : List Names.expr) (y z : Names.expr),
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.multi_imp DerivedNames xs y)
          (DerivedNamesSig.impp DerivedNames
            (DerivedNamesSig.multi_imp DerivedNames xs
              (DerivedNamesSig.impp DerivedNames y z))
            (DerivedNamesSig.multi_imp DerivedNames xs z))) := by
  intro xs y z
  exact provable_of_forall _ (fun m hy hyz => multi_imp_modus_ponens_point xs y z m hy hyz)

theorem provable_multi_imp_weaken
    (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (xs : List Names.expr) (x y : Names.expr),
      DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y) ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.multi_imp DerivedNames xs x)
          (DerivedNamesSig.multi_imp DerivedNames xs y)) := by
  intro xs x y hxy
  exact provable_of_forall _ (fun m h =>
    multi_imp_weaken_point xs x y m (forall_of_provable _ hxy m) h)

theorem provable_impp_refl_instance
    (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Reflexive
      (fun x y : Names.expr =>
        DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) := by
  intro x
  exact provable_of_forall _ (fun _ hx => hx)

theorem provable_proper_impp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
        DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==> implRel)
      (DerivedNamesSig.provable DerivedNames) := by
  constructor
  intro x y hxy hx
  exact provable_of_forall _ (fun m => forall_of_provable _ hxy m (forall_of_provable _ hx m))

theorem provables_impp_proper_impp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (flipRel (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)))
      (DerivedNamesSig.impp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m h hx2 =>
    forall_of_provable _ hy m (h (forall_of_provable _ hx m hx2)))

theorem provable_andp_comm (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.iffp DerivedNames
          (DerivedNamesSig.andp DerivedNames x y)
          (DerivedNamesSig.andp DerivedNames y x)) := by
  intro x y
  exact provable_of_forall _ (fun _ =>
    ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩)

theorem provable_andp_assoc (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.iffp DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.andp DerivedNames x y) z)
          (DerivedNamesSig.andp DerivedNames x (DerivedNamesSig.andp DerivedNames y z))) := by
  intro x y z
  exact provable_of_forall _ (fun _ =>
    ⟨fun h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩,
      fun h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩⟩)

theorem provable_orp_comm (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.iffp DerivedNames
          (DerivedNamesSig.orp DerivedNames x y)
          (DerivedNamesSig.orp DerivedNames y x)) := by
  intro x y
  exact provable_of_forall _ (fun _ =>
    ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩)

theorem provable_orp_dup (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.iffp DerivedNames
          (DerivedNamesSig.orp DerivedNames x x) x) := by
  intro x
  exact provable_of_forall _ (fun _ =>
    ⟨fun h => h.elim id id, fun hx => Or.inl hx⟩)

theorem provable_impp_curry (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames x
            (DerivedNamesSig.impp DerivedNames y z))
          (DerivedNamesSig.impp DerivedNames
            (DerivedNamesSig.andp DerivedNames x y) z)) := by
  intro x y z
  exact provable_of_forall _ (fun _ hxy hxy' => hxy hxy'.left hxy'.right)

theorem provable_impp_uncurry (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.impp DerivedNames
            (DerivedNamesSig.andp DerivedNames x y) z)
          (DerivedNamesSig.impp DerivedNames x
            (DerivedNamesSig.impp DerivedNames y z))) := by
  intro x y z
  exact provable_of_forall _ (fun _ h hx hy => h ⟨hx, hy⟩)

theorem provables_impp_trans (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y) ->
      DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames y z) ->
      DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x z) := by
  intro x y z hxy hyz
  exact provable_of_forall _ (fun m hx => forall_of_provable _ hyz m (forall_of_provable _ hxy m hx))

theorem provables_andp_proper_impp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)))
      (DerivedNamesSig.andp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m h =>
    ⟨forall_of_provable _ hx m h.left, forall_of_provable _ hy m h.right⟩)

theorem provables_orp_proper_impp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)))
      (DerivedNamesSig.orp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m h =>
    h.elim
      (fun hx1 => Or.inl (forall_of_provable _ hx m hx1))
      (fun hy1 => Or.inr (forall_of_provable _ hy m hy1)))

theorem provable_iffp_rewrite (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    RewriteRelation
      (fun x y : Names.expr =>
        DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) := by
  constructor

theorem provable_iffp_equiv (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Equivalence
      (fun x y : Names.expr =>
        DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) := by
  constructor
  · intro x
    exact provable_of_forall _ (fun _ => ⟨id, id⟩)
  · intro x y h
    exact provable_of_forall _ (fun m =>
      let hxy := forall_of_provable _ h m
      ⟨hxy.right, hxy.left⟩)
  · intro x y z hxy hyz
    exact provable_of_forall _ (fun m =>
      let hxy' := forall_of_provable _ hxy m
      let hyz' := forall_of_provable _ hyz m
      ⟨fun hx => hyz'.left (hxy'.left hx),
        fun hz => hxy'.right (hyz'.right hz)⟩)

theorem provable_proper_iffp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
        DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==> Iff)
      (DerivedNamesSig.provable DerivedNames) := by
  constructor
  intro x y hxy
  constructor
  · intro hx
    exact provable_of_forall _ (fun m =>
      (forall_of_provable _ hxy m).left (forall_of_provable _ hx m))
  · intro hy
    exact provable_of_forall _ (fun m =>
      (forall_of_provable _ hxy m).right (forall_of_provable _ hy m))

theorem provables_impp_proper_iffp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)))
      (DerivedNamesSig.impp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m =>
    let hx' := forall_of_provable _ hx m
    let hy' := forall_of_provable _ hy m
    ⟨fun h hx2 => hy'.left (h (hx'.right hx2)),
      fun h hx1 => hy'.right (h (hx'.left hx1))⟩)

theorem provables_andp_proper_iffp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)))
      (DerivedNamesSig.andp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m =>
    let hx' := forall_of_provable _ hx m
    let hy' := forall_of_provable _ hy m
    ⟨fun h => ⟨hx'.left h.left, hy'.left h.right⟩,
      fun h => ⟨hx'.right h.left, hy'.right h.right⟩⟩)

theorem provables_orp_proper_iffp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)))
      (DerivedNamesSig.orp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m =>
    let hx' := forall_of_provable _ hx m
    let hy' := forall_of_provable _ hy m
    ⟨fun h => h.elim (fun hx1 => Or.inl (hx'.left hx1)) (fun hy1 => Or.inr (hy'.left hy1)),
      fun h => h.elim (fun hx2 => Or.inl (hx'.right hx2)) (fun hy2 => Or.inr (hy'.right hy2))⟩)

theorem provables_iffp_proper_iffp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)))
      (DerivedNamesSig.iffp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m =>
    let hx' := forall_of_provable _ hx m
    let hy' := forall_of_provable _ hy m
    ⟨fun h =>
      ⟨fun hx2 => hy'.left (h.left (hx'.right hx2)),
        fun hy2 => hx'.left (h.right (hy'.right hy2))⟩,
      fun h =>
      ⟨fun hx1 => hy'.right (h.left (hx'.left hx1)),
        fun hy1 => hx'.right (h.right (hy'.left hy1))⟩⟩)

theorem derivables_coq_prop_imply (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall P Q : Prop,
      (P -> Q) ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.coq_prop DerivedNames P)
        (DerivedNamesSig.coq_prop DerivedNames Q) := by
  intro P Q h _ hP
  exact h hP

theorem derivable1s_coq_prop_andp_l (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q R : Names.expr),
      (P -> DerivedNamesSig.derivable1 DerivedNames Q R) ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) R := by
  intro P Q R h m hpq
  exact h hpq.left m hpq.right

theorem derivable1s_coq_prop_andp_r (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames R Q ->
      P ->
      DerivedNamesSig.derivable1 DerivedNames R
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) := by
  intro P Q R h hP m hR
  exact ⟨hP, h m hR⟩

theorem logic_equiv_coq_prop_andp2 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q : Names.expr),
      P ->
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) Q := by
  intro P Q hP
  exact ⟨fun _ h => h.right, fun _ hQ => ⟨hP, hQ⟩⟩

theorem derivable1_sepcon_orp_l (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames z (DerivedNamesSig.orp DerivedNames x y))
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames z x)
          (DerivedNamesSig.sepcon DerivedNames z y)) := by
  intro x y z m h
  rcases h with ⟨m1, m2, hj, hz, hxy⟩
  cases hxy with
  | inl hx => exact Or.inl ⟨m1, m2, hj, hz, hx⟩
  | inr hy => exact Or.inr ⟨m1, m2, hj, hz, hy⟩

theorem derivable1_orp_sepcon_r (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x z)
          (DerivedNamesSig.sepcon DerivedNames y z))
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.orp DerivedNames x y) z) := by
  intro x y z m h
  cases h with
  | inl hxz =>
      rcases hxz with ⟨m1, m2, hj, hx, hz⟩
      exact ⟨m1, m2, hj, Or.inl hx, hz⟩
  | inr hyz =>
      rcases hyz with ⟨m1, m2, hj, hy, hz⟩
      exact ⟨m1, m2, hj, Or.inr hy, hz⟩

theorem derivable1_sepcon_orp_r (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames z x)
          (DerivedNamesSig.sepcon DerivedNames z y))
        (DerivedNamesSig.sepcon DerivedNames z (DerivedNamesSig.orp DerivedNames x y)) := by
  intro x y z m h
  cases h with
  | inl hzx =>
      rcases hzx with ⟨m1, m2, hj, hz, hx⟩
      exact ⟨m1, m2, hj, hz, Or.inl hx⟩
  | inr hzy =>
      rcases hzy with ⟨m1, m2, hj, hz, hy⟩
      exact ⟨m1, m2, hj, hz, Or.inr hy⟩

theorem logic_equiv_orp_sepcon (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.orp DerivedNames x y) z)
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x z)
          (DerivedNamesSig.sepcon DerivedNames y z)) := by
  intro x y z
  exact ⟨derivable1_orp_sepcon_l _self x y z, derivable1_orp_sepcon_r _self x y z⟩

theorem logic_equiv_sepcon_orp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames z (DerivedNamesSig.orp DerivedNames x y))
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames z x)
          (DerivedNamesSig.sepcon DerivedNames z y)) := by
  intro x y z
  exact ⟨derivable1_sepcon_orp_l _self x y z, derivable1_sepcon_orp_r _self x y z⟩

theorem derivable1s_andp_mono (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x1 x2 y1 y2 : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x1 x2 ->
      DerivedNamesSig.derivable1 DerivedNames y1 y2 ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames x1 y1)
        (DerivedNamesSig.andp DerivedNames x2 y2) := by
  intro x1 x2 y1 y2 hx hy m h
  exact ⟨hx m h.left, hy m h.right⟩

theorem logic_equiv_coq_prop_andp1 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Names.expr) (Q : Prop),
      DerivedNamesSig.derivable1 DerivedNames P (DerivedNamesSig.coq_prop DerivedNames Q) ->
      DerivedNamesSig.logic_equiv DerivedNames P
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q) P) := by
  intro P Q h
  exact ⟨fun m hP => ⟨h m hP, hP⟩, fun _ hP => hP.right⟩

theorem derivable1s_emp_l_unfold
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.emp DerivedNames) y ->
      DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.sepcon DerivedNames x y) := by
  intro x y hy m hx
  rcases Rules.unit_join m with ⟨u, hu, hju⟩
  exact ⟨m, u, hju, hx, hy u hu⟩

theorem derivable1s_emp_sepcon_unfold
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x z ->
      DerivedNamesSig.derivable1 DerivedNames (DerivedNamesSig.emp DerivedNames) y ->
      DerivedNamesSig.derivable1 DerivedNames x
        (DerivedNamesSig.sepcon DerivedNames z y) := by
  intro x y z hxz hy m hx
  rcases Rules.unit_join m with ⟨u, hu, hju⟩
  exact ⟨m, u, hju, hxz m hx, hy u hu⟩

theorem logic_equiv_sepcon_coq_prop_andp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q) R))
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q) P) R) := by
  intro P Q R
  constructor
  · intro m h
    rcases h with ⟨m1, m2, hj, hP, hQR⟩
    exact ⟨m1, m2, hj, ⟨hQR.left, hP⟩, hQR.right⟩
  · intro m h
    rcases h with ⟨m1, m2, hj, hQP, hR⟩
    exact ⟨m1, m2, hj, hQP.right, ⟨hQP.left, hR⟩⟩

theorem logic_equiv_coq_prop_andp_sepcon (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q R : Names.expr),
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) R)
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.sepcon DerivedNames Q R)) := by
  intro P Q R
  constructor
  · intro m h
    rcases h with ⟨m1, m2, hj, hPQ, hR⟩
    exact ⟨hPQ.left, ⟨m1, m2, hj, hPQ.right, hR⟩⟩
  · intro m h
    rcases h.right with ⟨m1, m2, hj, hQ, hR⟩
    exact ⟨m1, m2, hj, ⟨h.left, hQ⟩, hR⟩

theorem logic_equiv_coq_prop_andp_sepcon_truep
    (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Names.expr) (Q : Prop),
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames P (DerivedNamesSig.coq_prop DerivedNames Q))
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q) P)
          (DerivedNamesSig.truep DerivedNames)) := by
  intro P Q
  constructor
  · intro m h
    rcases h with ⟨m1, m2, hj, hP, hQ⟩
    exact ⟨m1, m2, hj, ⟨hQ, hP⟩, True.intro⟩
  · intro m h
    rcases h with ⟨m1, m2, hj, hQP, _⟩
    exact ⟨m1, m2, hj, hQP.right, hQP.left⟩

theorem derivable1s_ex_l_unfold (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      (exists x : A, DerivedNamesSig.derivable1 DerivedNames (P x) Q) ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.allp DerivedNames A P) Q := by
  intro A P Q h m hall
  rcases h with ⟨a, ha⟩
  exact ha m (hall a)

theorem derivable1_exp_allp_swap (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A B : Type v) (P : A -> B -> Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.exp DerivedNames A
          (fun x : A => DerivedNamesSig.allp DerivedNames B (fun y : B => P x y)))
        (DerivedNamesSig.allp DerivedNames B
          (fun y : B => DerivedNamesSig.exp DerivedNames A (fun x : A => P x y))) := by
  intro A B P m h b
  rcases h with ⟨a, ha⟩
  exact ⟨a, ha b⟩

theorem derivable1_allp_allp_swap (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A B : Type v) (P : A -> B -> Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.allp DerivedNames A
          (fun x : A => DerivedNamesSig.allp DerivedNames B (fun y : B => P x y)))
        (DerivedNamesSig.allp DerivedNames B
          (fun y : B => DerivedNamesSig.allp DerivedNames A (fun x : A => P x y))) := by
  intro A B P m h b a
  exact h a b

theorem logic_equiv_exp_andp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.exp DerivedNames A P) Q)
        (DerivedNamesSig.exp DerivedNames A
          (fun x : A => DerivedNamesSig.andp DerivedNames (P x) Q)) := by
  intro A P Q
  constructor
  · intro m h
    rcases h.left with ⟨a, ha⟩
    exact ⟨a, ha, h.right⟩
  · intro m h
    rcases h with ⟨a, ha, hQ⟩
    exact ⟨⟨a, ha⟩, hQ⟩

theorem logic_equiv_exp_sepcon (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.exp DerivedNames A P) Q)
        (DerivedNamesSig.exp DerivedNames A
          (fun x : A => DerivedNamesSig.sepcon DerivedNames (P x) Q)) := by
  intro A P Q
  constructor
  · intro m h
    rcases h with ⟨m1, m2, hj, hP, hQ⟩
    rcases hP with ⟨a, ha⟩
    exact ⟨a, m1, m2, hj, ha, hQ⟩
  · intro m h
    rcases h with ⟨a, m1, m2, hj, hP, hQ⟩
    exact ⟨m1, m2, hj, ⟨a, hP⟩, hQ⟩

theorem logic_equiv_wand (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y x' y' : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames x x' ->
      DerivedNamesSig.logic_equiv DerivedNames y y' ->
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.wand DerivedNames x y)
        (DerivedNamesSig.wand DerivedNames x' y') := by
  intro x y x' y' hx hy
  constructor
  · intro m hw m1 m2 hj hx'
    exact hy.left m2 (hw m1 m2 hj (hx.right m1 hx'))
  · intro m hw m1 m2 hj hx0
    exact hy.right m2 (hw m1 m2 hj (hx.left m1 hx0))

theorem derivable1_wand_elim1 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.wand DerivedNames x y) x) y := by
  intro x y m h
  rcases h with ⟨m1, m2, hj, hw, hx⟩
  exact hw m2 m hj hx

theorem derivable1_wand_elim2 (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.wand DerivedNames x y)) y := by
  intro x y m h
  rcases h with ⟨m1, m2, hj, hx, hw⟩
  exact hw m1 m (Rules.join_comm m1 m2 m hj) hx

theorem logic_equiv_refl (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr, DerivedNamesSig.logic_equiv DerivedNames x x := by
  intro x
  exact ⟨fun _ h => h, fun _ h => h⟩

theorem logic_equiv_symm (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames x y ->
      DerivedNamesSig.logic_equiv DerivedNames y x := by
  intro x y h
  exact ⟨h.right, h.left⟩

theorem logic_equiv_trans (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames x y ->
      DerivedNamesSig.logic_equiv DerivedNames y z ->
      DerivedNamesSig.logic_equiv DerivedNames x z := by
  intro x y z hxy hyz
  exact
    ⟨fun m hx => hyz.left m (hxy.left m hx),
      fun m hz => hxy.right m (hyz.right m hz)⟩

theorem logic_equiv_sepcon_swap
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x
          (DerivedNamesSig.sepcon DerivedNames y z))
        (DerivedNamesSig.sepcon DerivedNames y
          (DerivedNamesSig.sepcon DerivedNames x z)) := by
  intro x y z
  have h1 := self.sepcon_assoc_logic_equiv x y z
  have h2 :
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x y) z)
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.sepcon DerivedNames y x) z) :=
    self.logic_equiv_sepcon_proper.proper
      (DerivedNamesSig.sepcon DerivedNames x y)
      (DerivedNamesSig.sepcon DerivedNames y x)
      (self.sepcon_comm_logic_equiv x y)
      z z (logic_equiv_refl self z)
  have h3 :
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.sepcon DerivedNames y x) z)
        (DerivedNamesSig.sepcon DerivedNames y
          (DerivedNamesSig.sepcon DerivedNames x z)) :=
    logic_equiv_symm self
      (DerivedNamesSig.sepcon DerivedNames y (DerivedNamesSig.sepcon DerivedNames x z))
      (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.sepcon DerivedNames y x) z)
      (self.sepcon_assoc_logic_equiv y x z)
  exact logic_equiv_trans self _ _ _ h1 (logic_equiv_trans self _ _ _ h2 h3)

theorem logic_equiv_sepcon_orp_distr
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.orp DerivedNames y z))
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x y)
          (DerivedNamesSig.sepcon DerivedNames x z)) := by
  intro x y z
  exact logic_equiv_sepcon_orp self y z x

theorem logic_equiv_orp_sepcon_distr
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.orp DerivedNames x y) z)
        (DerivedNamesSig.orp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x z)
          (DerivedNamesSig.sepcon DerivedNames y z)) := by
  intro x y z
  exact logic_equiv_orp_sepcon self x y z

theorem provables_sepcon_impp_unfold
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall u x y z : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x y) z) ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames
            (DerivedNamesSig.sepcon DerivedNames u x) y)
          (DerivedNamesSig.sepcon DerivedNames u z)) := by
  intro u x y z h
  have hD := derivable1_of_provable self h
  have hAssocBack :
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.sepcon DerivedNames u x) y)
        (DerivedNamesSig.sepcon DerivedNames u
          (DerivedNamesSig.sepcon DerivedNames x y)) :=
    (self.sepcon_assoc_logic_equiv u x y).right
  have hMono :
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames u
          (DerivedNamesSig.sepcon DerivedNames x y))
        (DerivedNamesSig.sepcon DerivedNames u z) :=
    self.derivable1_sepcon_mono u u
      (DerivedNamesSig.sepcon DerivedNames x y) z
      (self.derivable1_refl u) hD
  exact provable_of_derivable1 self
    (self.derivable1_trans _ _ _ hAssocBack hMono)

theorem provables_sepcon_sepcon_unfold
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z w v : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x
            (DerivedNamesSig.sepcon DerivedNames y z))
          (DerivedNamesSig.sepcon DerivedNames w v)) ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames
            (DerivedNamesSig.sepcon DerivedNames y x) z)
          (DerivedNamesSig.sepcon DerivedNames w v)) := by
  intro x y z w v h
  have hD := derivable1_of_provable self h
  have hAssocBack :
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.sepcon DerivedNames y x) z)
        (DerivedNamesSig.sepcon DerivedNames y
          (DerivedNamesSig.sepcon DerivedNames x z)) :=
    (self.sepcon_assoc_logic_equiv y x z).right
  have hSwap :
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames y
          (DerivedNamesSig.sepcon DerivedNames x z))
        (DerivedNamesSig.sepcon DerivedNames x
          (DerivedNamesSig.sepcon DerivedNames y z)) :=
    (logic_equiv_sepcon_swap self y x z).left
  exact provable_of_derivable1 self
    (self.derivable1_trans _ _ _
      (self.derivable1_trans _ _ _ hAssocBack hSwap) hD)

theorem provables_sepcon_assoc
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x y z w : Names.expr,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames
            (DerivedNamesSig.sepcon DerivedNames y x) z) w) ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.sepcon DerivedNames x
            (DerivedNamesSig.sepcon DerivedNames y z)) w) := by
  intro x y z w h
  have hD := derivable1_of_provable self h
  have hSwap :
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x
          (DerivedNamesSig.sepcon DerivedNames y z))
        (DerivedNamesSig.sepcon DerivedNames y
          (DerivedNamesSig.sepcon DerivedNames x z)) :=
    (logic_equiv_sepcon_swap self x y z).left
  have hAssoc :
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames y
          (DerivedNamesSig.sepcon DerivedNames x z))
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.sepcon DerivedNames y x) z) :=
    (self.sepcon_assoc_logic_equiv y x z).left
  exact provable_of_derivable1 self
    (self.derivable1_trans _ _ _
      (self.derivable1_trans _ _ _ hSwap hAssoc) hD)

theorem provables_coq_prop_andp_derives
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q R : Names.expr),
      (P -> DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames Q R)) ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) R) := by
  intro P Q R h
  exact provable_of_derivable1 self (derivable1s_coq_prop_andp_l self P Q R
    (fun hP => derivable1_of_provable self (h hP)))

theorem provables_andp_coq_prop_derives
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q R : Names.expr),
      (P -> DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames Q R)) ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames
          (DerivedNamesSig.andp DerivedNames Q (DerivedNamesSig.coq_prop DerivedNames P)) R) := by
  intro P Q R h
  exact provable_of_forall _ (fun m hQP =>
    forall_of_provable _ (h hQP.right) m hQP.left)

theorem provables_impp_coq_prop (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q : Names.expr),
      P ->
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.impp DerivedNames Q (DerivedNamesSig.coq_prop DerivedNames P)) := by
  intro P Q hP
  exact provable_of_forall _ (fun _ _ => hP)

theorem provable_coq_prop_or (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall P Q : Prop,
      DerivedNamesSig.provable DerivedNames
        (DerivedNamesSig.iffp DerivedNames
          (DerivedNamesSig.coq_prop DerivedNames (P \/ Q))
          (DerivedNamesSig.orp DerivedNames
            (DerivedNamesSig.coq_prop DerivedNames P)
            (DerivedNamesSig.coq_prop DerivedNames Q))) := by
  intro P Q
  exact provable_of_forall _ (fun _ => ⟨fun h => h, fun h => h⟩)

theorem provables_sepcon_proper_impp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.impp DerivedNames x y)))
      (DerivedNamesSig.sepcon DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m h =>
    let hx' := forall_of_provable _ hx
    let hy' := forall_of_provable _ hy
    match h with
    | ⟨m1, m2, hj, hx1, hy1⟩ => ⟨m1, m2, hj, hx' m1 hx1, hy' m2 hy1⟩)

theorem provables_sepcon_proper_iffp (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      ((fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)) ==>
        (fun x y : Names.expr =>
          DerivedNamesSig.provable DerivedNames (DerivedNamesSig.iffp DerivedNames x y)))
      (DerivedNamesSig.sepcon DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact provable_of_forall _ (fun m =>
    let hx' := forall_of_provable _ hx
    let hy' := forall_of_provable _ hy
    ⟨fun h =>
      match h with
      | ⟨m1, m2, hj, hx1, hy1⟩ => ⟨m1, m2, hj, (hx' m1).left hx1, (hy' m2).left hy1⟩,
      fun h =>
      match h with
      | ⟨m1, m2, hj, hx2, hy2⟩ => ⟨m1, m2, hj, (hx' m1).right hx2, (hy' m2).right hy2⟩⟩)

theorem logic_equiv_refl_instance (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Reflexive (DerivedNamesSig.logic_equiv DerivedNames) := by
  intro x
  exact logic_equiv_refl _self x

theorem logic_equiv_symm_instance (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Symmetric (DerivedNamesSig.logic_equiv DerivedNames) := by
  intro x y h
  exact logic_equiv_symm _self x y h

theorem logic_equiv_trans_instance (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Transitive (DerivedNamesSig.logic_equiv DerivedNames) := by
  intro x y z hxy hyz
  exact logic_equiv_trans _self x y z hxy hyz

theorem provable_sepcon_emp_logic_equiv
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall x : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.emp DerivedNames)) x :=
  self.sepcon_emp_logic_equiv

theorem derivable1_exp_andp_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.exp DerivedNames A P) Q)
        (DerivedNamesSig.exp DerivedNames A
          (fun x : A => DerivedNamesSig.andp DerivedNames (P x) Q)) :=
  self.ex_and1

theorem derivable1_andp_exp_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : Names.expr) (Q : A -> Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames P (DerivedNamesSig.exp DerivedNames A Q))
        (DerivedNamesSig.exp DerivedNames A
          (fun x : A => DerivedNamesSig.andp DerivedNames P (Q x))) :=
  self.ex_and2

theorem derivable1_exp_sepcon_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : A -> Names.expr) (Q : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.exp DerivedNames A P) Q)
        (DerivedNamesSig.exp DerivedNames A
          (fun x : A => DerivedNamesSig.sepcon DerivedNames (P x) Q)) :=
  self.ex_sepcon1

theorem derivable1_sepcon_exp_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (A : Type v) (P : Names.expr) (Q : A -> Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames P (DerivedNamesSig.exp DerivedNames A Q))
        (DerivedNamesSig.exp DerivedNames A
          (fun x : A => DerivedNamesSig.sepcon DerivedNames P (Q x))) :=
  self.ex_sepcon2

theorem derivable1_iter_sepcon_flatten
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall xs1 xs2 xs3 : List Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.iter_sepcon DerivedNames
          (xs1 ++ (DerivedNamesSig.iter_sepcon DerivedNames xs2 :: xs3)))
        (DerivedNamesSig.iter_sepcon DerivedNames (xs1 ++ xs2 ++ xs3)) :=
  self.iter_sepcon_flatten

theorem derivable1_sepcon_coq_prop_andp_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q) R))
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q)
          (DerivedNamesSig.sepcon DerivedNames P R)) :=
  self.sepcon_andp_prop1

theorem derivable1_sepcon_coq_prop_andp_r
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q)
          (DerivedNamesSig.sepcon DerivedNames P R))
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q) R)) :=
  self.sepcon_andp_prop2

theorem derivable1_sepcon_andp_coq_prop_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P Q : Names.expr) (R : Prop),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames Q (DerivedNamesSig.coq_prop DerivedNames R)))
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames R)
          (DerivedNamesSig.sepcon DerivedNames P Q)) :=
  self.sepcon_andp_prop3

theorem derivable1_sepcon_andp_coq_prop_r
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P Q : Names.expr) (R : Prop),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames R)
          (DerivedNamesSig.sepcon DerivedNames P Q))
        (DerivedNamesSig.sepcon DerivedNames P
          (DerivedNamesSig.andp DerivedNames Q (DerivedNamesSig.coq_prop DerivedNames R))) :=
  self.sepcon_andp_prop4

theorem derivable1_coq_prop_andp_sepcon_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) R)
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.sepcon DerivedNames Q R)) :=
  self.sepcon_andp_prop5

theorem derivable1_coq_prop_andp_sepcon_r
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Prop) (Q R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.sepcon DerivedNames Q R))
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P) Q) R) :=
  self.sepcon_andp_prop6

theorem derivable1_andp_coq_prop_sepcon_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames P (DerivedNamesSig.coq_prop DerivedNames Q)) R)
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q)
          (DerivedNamesSig.sepcon DerivedNames P R)) :=
  self.sepcon_andp_prop7

theorem derivable1_andp_coq_prop_sepcon_r
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (P : Names.expr) (Q : Prop) (R : Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames Q)
          (DerivedNamesSig.sepcon DerivedNames P R))
        (DerivedNamesSig.sepcon DerivedNames
          (DerivedNamesSig.andp DerivedNames P (DerivedNamesSig.coq_prop DerivedNames Q)) R) :=
  self.sepcon_andp_prop8

theorem derivable1_iter_sepcon_coq_prop_andp_l
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    forall (xs1 : List Names.expr) (P : Prop) (x2 : Names.expr) (xs3 : List Names.expr),
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.iter_sepcon DerivedNames
          (xs1 ++ (DerivedNamesSig.andp DerivedNames
            (DerivedNamesSig.coq_prop DerivedNames P) x2 :: xs3)))
        (DerivedNamesSig.andp DerivedNames (DerivedNamesSig.coq_prop DerivedNames P)
          (DerivedNamesSig.iter_sepcon DerivedNames (xs1 ++ (x2 :: xs3)))) :=
  self.iter_sepcon_andp_prop

theorem derivable1_proper_derivable1
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (flipRel (DerivedNamesSig.derivable1 DerivedNames) ==>
        DerivedNamesSig.derivable1 DerivedNames ==> implRel)
      (DerivedNamesSig.derivable1 DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy hxy
  exact self.derivable1_trans x2 y1 y2
    (self.derivable1_trans x2 x1 y1 hx hxy) hy

theorem logic_equiv_proper_logic_equiv
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==> implRel)
      (DerivedNamesSig.logic_equiv DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy hxy
  exact logic_equiv_trans self x2 y1 y2
    (logic_equiv_trans self x2 x1 y1 (logic_equiv_symm self x1 x2 hx) hxy) hy

theorem logic_equiv_proper_derivable1
    (self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==> implRel)
      (DerivedNamesSig.derivable1 DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy hxy
  exact self.derivable1_trans x2 y1 y2
    (self.derivable1_trans x2 x1 y1 hx.right hxy) hy.left

theorem derivable1s_andp_proper (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.andp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy m h
  exact ⟨hx m h.left, hy m h.right⟩

theorem derivable1s_orp_proper (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.orp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy m h
  exact h.elim (fun hx1 => Or.inl (hx m hx1)) (fun hy1 => Or.inr (hy m hy1))

theorem derivable1s_sepcon_proper (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.sepcon DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy m h
  rcases h with ⟨m1, m2, hj, hx1, hy1⟩
  exact ⟨m1, m2, hj, hx m1 hx1, hy m2 hy1⟩

theorem logic_equiv_wand_proper (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames)
      (DerivedNamesSig.wand DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact logic_equiv_wand _self x1 y1 x2 y2 hx hy

theorem derivable1s_wand_proper (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (flipRel (DerivedNamesSig.derivable1 DerivedNames) ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.wand DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy m hw m1 m2 hj hx2
  exact hy m2 (hw m1 m2 hj (hx m1 hx2))

theorem logic_equiv_orp_proper (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames)
      (DerivedNamesSig.orp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact logic_equiv_orp_congr _self x1 x2 y1 y2 hx hy

theorem logic_equiv_andp_proper (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames)
      (DerivedNamesSig.andp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy
  exact logic_equiv_andp_congr _self x1 x2 y1 y2 hx hy

theorem derivable1s_impp_proper (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    Proper
      (flipRel (DerivedNamesSig.derivable1 DerivedNames) ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.impp DerivedNames) := by
  constructor
  intro x1 x2 hx y1 y2 hy m h hx2
  exact hy m (h (hx m hx2))

theorem Derivable_impp_rewrite (_self : LogicTheoremSig.{u, v} Names DerivedNames Rules) :
    RewriteRelation (DerivedNamesSig.derivable1 DerivedNames) := by
  constructor

end LogicTheoremSig

structure LogicTheoremSig' (Names : LanguageSig.{u})
    (DerivedNames : DerivedNamesSig Names)
    (Rules : PrimitiveRuleSig Names DerivedNames) :
    Type (max (u + 1) (v + 1)) extends
    LogicTheoremSig.{u, v} Names DerivedNames Rules where
  derivable1_wand_sepcon_modus_ponens1 :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames (DerivedNamesSig.wand DerivedNames x y) x) y
  derivable1_wand_sepcon_modus_ponens2 :
    forall x y : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.sepcon DerivedNames x (DerivedNamesSig.wand DerivedNames x y)) y
  derivable1_wand_mono :
    forall x1 x2 y1 y2 : Names.expr,
      DerivedNamesSig.derivable1 DerivedNames x2 x1 ->
      DerivedNamesSig.derivable1 DerivedNames y1 y2 ->
      DerivedNamesSig.derivable1 DerivedNames
        (DerivedNamesSig.wand DerivedNames x1 y1)
        (DerivedNamesSig.wand DerivedNames x2 y2)
  wand_andp_logic_equiv :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames
        (DerivedNamesSig.wand DerivedNames x (DerivedNamesSig.andp DerivedNames y z))
        (DerivedNamesSig.andp DerivedNames
          (DerivedNamesSig.wand DerivedNames x y)
          (DerivedNamesSig.wand DerivedNames x z))
  logic_equiv_refl :
    forall x : Names.expr, DerivedNamesSig.logic_equiv DerivedNames x x
  logic_equiv_symm :
    forall x y : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames x y ->
      DerivedNamesSig.logic_equiv DerivedNames y x
  logic_equiv_trans :
    forall x y z : Names.expr,
      DerivedNamesSig.logic_equiv DerivedNames x y ->
      DerivedNamesSig.logic_equiv DerivedNames y z ->
      DerivedNamesSig.logic_equiv DerivedNames x z
  logic_equiv_derivable1 :
    forall x y : Names.expr,
      (DerivedNamesSig.logic_equiv DerivedNames x y <->
        DerivedNamesSig.derivable1 DerivedNames x y /\
        DerivedNamesSig.derivable1 DerivedNames y x)
  derivable_impp_rewrite_inst :
    RewriteRelation (DerivedNamesSig.derivable1 DerivedNames)
  derivable1_refl_inst :
    Reflexive (DerivedNamesSig.derivable1 DerivedNames)
  derivable1_trans_inst :
    Transitive (DerivedNamesSig.derivable1 DerivedNames)
  logic_equiv_impp_rewrite_inst :
    RewriteRelation (DerivedNamesSig.logic_equiv DerivedNames)
  logic_equiv_refl_inst :
    Reflexive (DerivedNamesSig.logic_equiv DerivedNames)
  logic_equiv_symm_inst :
    Symmetric (DerivedNamesSig.logic_equiv DerivedNames)
  logic_equiv_trans_inst :
    Transitive (DerivedNamesSig.logic_equiv DerivedNames)
  logic_equiv_equivalence_inst :
    Equivalence (DerivedNamesSig.logic_equiv DerivedNames)
  derivable1_proper_derivable1_inst :
    Proper
      (flipRel (DerivedNamesSig.derivable1 DerivedNames) ==>
        DerivedNamesSig.derivable1 DerivedNames ==> implRel)
      (DerivedNamesSig.derivable1 DerivedNames)
  logic_equiv_proper_logic_equiv_inst :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==> implRel)
      (DerivedNamesSig.logic_equiv DerivedNames)
  logic_equiv_proper_derivable1_inst :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==> implRel)
      (DerivedNamesSig.derivable1 DerivedNames)
  andp_proper_derivable1_inst :
    Proper
      (DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.andp DerivedNames)
  andp_proper_equiv_inst :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames)
      (DerivedNamesSig.andp DerivedNames)
  orp_proper_equiv_inst :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames)
      (DerivedNamesSig.orp DerivedNames)
  orp_proper_derivable1_inst :
    Proper
      (DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.orp DerivedNames)
  logic_equiv_sepcon_proper_inst :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames)
      (DerivedNamesSig.sepcon DerivedNames)
  derivable1s_sepcon_proper_inst :
    Proper
      (DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.sepcon DerivedNames)
  logic_equiv_wand_proper_inst :
    Proper
      (DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames ==>
        DerivedNamesSig.logic_equiv DerivedNames)
      (DerivedNamesSig.wand DerivedNames)
  derivable1s_wand_proper_inst :
    Proper
      (flipRel (DerivedNamesSig.derivable1 DerivedNames) ==>
        DerivedNamesSig.derivable1 DerivedNames ==>
        DerivedNamesSig.derivable1 DerivedNames)
      (DerivedNamesSig.wand DerivedNames)

namespace LogicTheoremSig'

def default (Names : LanguageSig.{u}) (DerivedNames : DerivedNamesSig Names)
    (Rules : PrimitiveRuleSig Names DerivedNames) :
    LogicTheoremSig'.{u, v} Names DerivedNames Rules := by
  let M : Model.{u} := modelOf Names
  let L : Language.{u} := languageOf Names
  letI : Join (@Model.model M) := joinOf Names
  letI : Unit (@Model.model M) := unitOf Names
  letI : SepconLanguage L := sepconLanguageOf DerivedNames
  letI : WandLanguage L := wandLanguageOf DerivedNames
  letI : OrLanguage L := orLanguageOf DerivedNames
  letI : AndLanguage L := andLanguageOf DerivedNames
  letI : MinimumLanguage L := minimumLanguageOf DerivedNames
  letI : ShallowExistsLanguage.{u, v} L := expLanguageOf DerivedNames
  letI : ShallowForallLanguage.{u, v} L := allpLanguageOf DerivedNames
  letI : EmpLanguage L := empLanguageOf DerivedNames
  letI : CoqPropLanguage L := coqPropLanguageOf DerivedNames
  letI : TrueLanguage L := trueLanguageOf DerivedNames
  letI : IterSepconLanguage L := iterSepconLanguageOf DerivedNames
  letI GammaD1 : Derivable1 L := derivable1Of DerivedNames
  letI GammaE : LogicEquiv L := logicEquivOf DerivedNames
  letI : SeparationAlgebra (@Model.model M) := separationAlgebraOf Rules
  letI : UnitJoinRelation (@Model.model M) := unitJoinRelationOf Rules
  letI : Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.SepconDefinition_Join
      (M := M) (Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.Join2Sepcon M) :=
    Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.Join2Sepcon_Normal M
  letI : Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.WandDefinition_Join
      (M := M) (Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.Join2Wand M) :=
    Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.Join2Wand_Normal M
  letI : Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.OrpDefinition_Model
      (M := M) (Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2Orp M) :=
    Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2Orp_Normal M
  letI : Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.AndpDefinition_Model
      (M := M) (Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2Andp M) :=
    Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2Andp_Normal M
  letI : Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.ImppDefinition_Model
      (M := M) (Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.Model2Impp M) :=
    Unifysl.MinimumLogic.ShallowEmbedded.ModelLanguageMinimumLogic.Model2Impp_Normal M
  letI : Unifysl.ShallowQuantifierLogic.ModelConstrEX.ExpDefinition_Model
      (M := M) (Unifysl.ShallowQuantifierLogic.ModelConstrEX.Model2Exp.{u, v} M) :=
    Unifysl.ShallowQuantifierLogic.ModelConstrEX.Model2Exp_Normal (M := M)
  letI : Unifysl.ShallowQuantifierLogic.ModelConstrALL.AllpDefinition_Model
      (M := M) (Unifysl.ShallowQuantifierLogic.ModelConstrALL.Model2All.{u, v} M) :=
    Unifysl.ShallowQuantifierLogic.ModelConstrALL.Model2Allp_Normal (M := M)
  letI : Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.EmpDefinition_Unit
      (M := M) (Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.Unit2Emp M) :=
    Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.Unit2Emp_Normal M
  letI : Unifysl.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic.CoqPropDefinition_Model
      (M := M) (Unifysl.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic.Model2CoqProp M) :=
    Unifysl.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic.Model2CoqProp_Normal M
  letI : Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.TrueDefinition_Model
      (M := M) (Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2Truep M) :=
    Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2Truep_Normal M
  letI : Unifysl.IterSepconDefinition_left L :=
    Unifysl.FoldLeftSepcon2IterSepcon_Normal (L := L)
  letI : Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Derivable1Definition_Model
      (M := M) (Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model2Derivable1 M) :=
    Unifysl.GeneralLogic.ShallowEmbedded.ModelLanguage.Model2Derivable1_Normal M
  letI : EquivDerivable1 L GammaD1 GammaE := {
    __logic_equiv_derivable1 := by
      intro x y
      rfl }
  letI : SepconDeduction L GammaD1 :=
    Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.SeparationAlgebra2SepconDeduction M
  letI : WandDeduction L GammaD1 :=
    Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.SeparationAlgebra2WandDeduction M
  letI : ImpAndAdjointDeduction L GammaD1 :=
    Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2ImpAdjoint M
  letI : AndDeduction L GammaD1 :=
    Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2AndDeduction M
  letI : OrDeduction L GammaD1 :=
    Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2OrDeduction M
  letI : ShallowExistsDeduction L GammaD1 :=
    Unifysl.ShallowQuantifierLogic.ModelConstrEX.Model2ExpDeduction.{u, v} M
  letI : ShallowForallDeduction L GammaD1 :=
    Unifysl.ShallowQuantifierLogic.ModelConstrALL.Model2AllDeduction.{u, v} M
  letI : BasicDeduction L GammaD1 :=
    Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2BasicDeduction M
  letI : deduction_exp_and (L := L) := ExpDeduction2ExsitsAnd (L := L)
  letI : IterSepconDeduction_left L GammaD1 := IterSepconFromDefToD1_L2L (L := L)
  letI : deduction_exp_sepcon (L := L) := ExpDeduction2ExsitsSepcon (L := L)
  letI : EmpDeduction L GammaD1 :=
    Unifysl.SeparationLogic.ShallowEmbedded.ModelLanguageSeparationLogic.Model2EmpDeduction M
  letI : IterSepconFlatten (L := L) := DeductionSepconFlatten (L := L)
  letI : CoqPropDeduction L GammaD1 :=
    Unifysl.MetaLogicInj.ShallowEmbedded.ModelLanguageMetaLogic.Model2CoqPropDeduction M
  letI : TrueDeduction L GammaD1 :=
    Unifysl.PropositionalLogic.ShallowEmbedded.ModelLanguagePropositionalLogic.Model2TrueDeduction M
  letI : sepcon_andp_prop (L := L) := Derived_sepcon_andp_prop (L := L)
  letI : sepcon_andp_prop_ext (L := L) := Derived_sepcon_andp_prop_ext (L := L)
  letI : Iter_sepcon_andp_prop (L := L) := Derived_iter_sepcon_andp_prop (L := L)
  let logic_equiv_refl_local :
      forall x : @Language.expr L, logic_equiv (L := L) x x := by
    intro x
    exact ⟨derivable1_refl x, derivable1_refl x⟩
  let logic_equiv_symm_local :
      forall x y : @Language.expr L, logic_equiv (L := L) x y -> logic_equiv (L := L) y x := by
    intro x y h
    exact ⟨h.right, h.left⟩
  let logic_equiv_trans_local :
      forall x y z : @Language.expr L,
        logic_equiv (L := L) x y -> logic_equiv (L := L) y z -> logic_equiv (L := L) x z := by
    intro x y z hxy hyz
    exact
      ⟨derivable1_trans x y z hxy.left hyz.left,
        derivable1_trans z y x hyz.right hxy.right⟩
  letI : BasicLogicEquiv L GammaE := {
    logic_equiv_refl := logic_equiv_refl_local
    logic_equiv_symm := logic_equiv_symm_local
    logic_equiv_trans := logic_equiv_trans_local }
  exact {
    tree_pos := Unifysl.tree_pos L
    coq_prop_right := by
      intro P x hP
      exact CoqPropDeduction.coq_prop_right (GammaD1 := GammaD1) P x hP
    coq_prop_left := by
      intro P x h
      exact CoqPropDeduction.coq_prop_left (GammaD1 := GammaD1) P x h
    iter_sepcon_d1_left1 := by
      intro xs
      exact IterSepconDeduction_left.iter_sepcon_d1_left1 (Gamma := GammaD1) xs
    iter_sepcon_d1_left2 := by
      intro xs
      exact IterSepconDeduction_left.iter_sepcon_d1_left2 (Gamma := GammaD1) xs
    shallow_exp_right := by
      intro A P Q x h
      exact ShallowExistsDeduction.shallow_exp_right (Gamma := GammaD1) P Q x h
    shallow_exp_left := by
      intro A P Q h
      exact ShallowExistsDeduction.shallow_exp_left (Gamma := GammaD1) P Q h
    shallow_allp_right := by
      intro A P Q h
      exact ShallowForallDeduction.shallow_all_right (Gamma := GammaD1) P Q h
    shallow_allp_left := by
      intro A P Q x h
      exact ShallowForallDeduction.shallow_all_left (Gamma := GammaD1) P Q x h
    sepcon_emp_left := by
      intro x
      exact EmpDeduction.sepcon_emp_left (GammaD1 := GammaD1) x
    sepcon_emp_right := by
      intro x
      exact EmpDeduction.sepcon_emp_right (GammaD1 := GammaD1) x
    derivable1_wand_sepcon_adjoint := by
      intro x y z
      exact WandDeduction.derivable1_wand_sepcon_adjoint (GammaD1 := GammaD1) x y z
    derivable1_sepcon_comm := by
      intro x y
      exact SepconDeduction.derivable1_sepcon_comm (GammaD1 := GammaD1) x y
    derivable1_sepcon_assoc1 := by
      intro x y z
      exact SepconDeduction.derivable1_sepcon_assoc1 (GammaD1 := GammaD1) x y z
    derivable1_sepcon_mono := by
      intro x1 x2 y1 y2 hx hy
      exact SepconDeduction.derivable1_sepcon_mono (GammaD1 := GammaD1) x1 x2 y1 y2 hx hy
    derivable1_truep_intros := by
      intro x
      exact TrueDeduction.derivable1_truep_intros (GammaD1 := GammaD1) x
    derivable1s_truep_intros := by
      intro x y z hxy hxz
      exact AndDeduction.derivable1s_truep_intros (GammaD1 := GammaD1) x y z hxy hxz
    derivable1_andp_elim1 := by
      intro x y
      exact AndDeduction.derivable1_andp_elim1 (GammaD1 := GammaD1) x y
    derivable1_andp_elim2 := by
      intro x y
      exact AndDeduction.derivable1_andp_elim2 (GammaD1 := GammaD1) x y
    derivable1_orp_intros1 := by
      intro x y
      exact OrDeduction.derivable1_orp_intros1 (GammaD1 := GammaD1) x y
    derivable1_orp_intros2 := by
      intro x y
      exact OrDeduction.derivable1_orp_intros2 (GammaD1 := GammaD1) x y
    derivable1_orp_elim := by
      intro x y z hxz hyz
      exact OrDeduction.derivable1_orp_elim (GammaD1 := GammaD1) x y z hxz hyz
    derivable1s_impp_andp_adjoint := by
      intro x y z
      exact ImpAndAdjointDeduction.derivable1s_impp_andp_adjoint (GammaD1 := GammaD1) x y z
    derivable1_refl := by
      intro x
      exact derivable1_refl x
    derivable1_trans := by
      intro x y z hxy hyz
      exact derivable1_trans x y z hxy hyz
    expr_deep := Unifysl.expr_deep
    impp_deep := Unifysl.impp_deep
    sepcon_deep := Unifysl.sepcon_deep
    emp_deep := Unifysl.emp_deep
    varp_deep := Unifysl.varp_deep
    var_pos := Unifysl.var_pos
    sepcon_pos := Unifysl.sepcon_pos
    cancel_mark := Unifysl.cancel_mark
    cancel_different := Unifysl.cancel_different
    cancel_same := Unifysl.cancel_same
    restore := Unifysl.restore
    logic_equiv_sepcon_proper := Unifysl.logic_equiv_sepcon_proper (L := L)
    sepcon_comm_logic_equiv := by
      intro x y
      exact Unifysl.sepcon_comm_logic_equiv (L := L) x y
    sepcon_assoc_logic_equiv := by
      intro x y z
      exact Unifysl.sepcon_assoc_logic_equiv (L := L) x y z
    sepcon_emp_logic_equiv := by
      intro x
      exact Unifysl.sepcon_emp_logic_equiv (L := L) x
    ex_and1 := by
      intro A P Q
      exact deduction_exp_and.ex_and1 (L := L) A P Q
    ex_and2 := by
      intro A P Q
      exact deduction_exp_and.ex_and2 (L := L) A P Q
    ex_sepcon1 := by
      intro A P Q
      exact deduction_exp_sepcon.ex_sepcon1 (L := L) A P Q
    ex_sepcon2 := by
      intro A P Q
      exact deduction_exp_sepcon.ex_sepcon2 (L := L) A P Q
    iter_sepcon_flatten := by
      intro xs1 xs2 xs3
      exact IterSepconFlatten.iter_sepcon_flatten (L := L) xs1 xs2 xs3
    sepcon_andp_prop1 := by
      intro P Q R
      exact sepcon_andp_prop.sepcon_andp_prop1 (L := L) P Q R
    sepcon_andp_prop2 := by
      intro P Q R
      exact sepcon_andp_prop.sepcon_andp_prop2 (L := L) P Q R
    sepcon_andp_prop3 := by
      intro P Q R
      exact sepcon_andp_prop_ext.sepcon_andp_prop3 (L := L) P Q R
    sepcon_andp_prop4 := by
      intro P Q R
      exact sepcon_andp_prop_ext.sepcon_andp_prop4 (L := L) P Q R
    sepcon_andp_prop5 := by
      intro P Q R
      exact sepcon_andp_prop_ext.sepcon_andp_prop5 (L := L) P Q R
    sepcon_andp_prop6 := by
      intro P Q R
      exact sepcon_andp_prop_ext.sepcon_andp_prop6 (L := L) P Q R
    sepcon_andp_prop7 := by
      intro P Q R
      exact sepcon_andp_prop_ext.sepcon_andp_prop7 (L := L) P Q R
    sepcon_andp_prop8 := by
      intro P Q R
      exact sepcon_andp_prop_ext.sepcon_andp_prop8 (L := L) P Q R
    iter_sepcon_andp_prop := by
      intro xs1 P x2 xs3
      exact Iter_sepcon_andp_prop.iter_sepcon_andp_prop (L := L) xs1 P x2 xs3
    derivable1_sepcon_iter_sepcon1 := by
      intro xs ys
      exact Unifysl.derivable1_sepcon_iter_sepcon1 (L := L) xs ys
    derivable1_sepcon_iter_sepcon2 := by
      intro xs ys
      exact Unifysl.derivable1_sepcon_iter_sepcon2 (L := L) xs ys
    derivable1_wand_sepcon_modus_ponens1 := by
      intro x y
      exact Unifysl.derivable1_wand_sepcon_modus_ponens1 (L := L) x y
    derivable1_wand_sepcon_modus_ponens2 := by
      intro x y
      exact Unifysl.derivable1_wand_sepcon_modus_ponens2 (L := L) x y
    derivable1_wand_mono := by
      intro x1 x2 y1 y2 hx hy
      exact Unifysl.derivable1_wand_mono (L := L) x1 x2 y1 y2 hx hy
    wand_andp_logic_equiv := by
      intro x y z
      constructor
      · intro m h
        exact
          ⟨fun m1 m2 hj hx => (h m1 m2 hj hx).left,
            fun m1 m2 hj hx => (h m1 m2 hj hx).right⟩
      · intro m h m1 m2 hj hx
        exact ⟨h.left m1 m2 hj hx, h.right m1 m2 hj hx⟩
    logic_equiv_refl := logic_equiv_refl_local
    logic_equiv_symm := logic_equiv_symm_local
    logic_equiv_trans := logic_equiv_trans_local
    logic_equiv_derivable1 := by
      intro x y
      rfl
    derivable_impp_rewrite_inst := by
      change RewriteRelation (derivable1 (L := L))
      exact inferInstance
    derivable1_refl_inst := by
      change Reflexive (derivable1 (L := L))
      exact Unifysl.derivable1_refl_instance (L := L)
    derivable1_trans_inst := by
      change Transitive (derivable1 (L := L))
      exact Unifysl.derivable1_trans_instance (L := L)
    logic_equiv_impp_rewrite_inst := by
      change RewriteRelation (logic_equiv (L := L))
      exact inferInstance
    logic_equiv_refl_inst := by
      change Reflexive (logic_equiv (L := L))
      exact Unifysl.logic_equiv_refl_instance (L := L)
    logic_equiv_symm_inst := by
      change Symmetric (logic_equiv (L := L))
      exact Unifysl.logic_equiv_symm_instance (L := L)
    logic_equiv_trans_inst := by
      change Transitive (logic_equiv (L := L))
      exact Unifysl.logic_equiv_trans_instance (L := L)
    logic_equiv_equivalence_inst := by
      change Equivalence (logic_equiv (L := L))
      exact {
        refl := logic_equiv_refl_local
        symm := by
          intro x y h
          exact logic_equiv_symm_local x y h
        trans := by
          intro x y z hxy hyz
          exact logic_equiv_trans_local x y z hxy hyz }
    derivable1_proper_derivable1_inst := by
      change Proper (flipRel (derivable1 (L := L)) ==> derivable1 (L := L) ==> implRel)
        (derivable1 (L := L))
      exact inferInstance
    logic_equiv_proper_logic_equiv_inst := by
      change Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> implRel)
        (logic_equiv (L := L))
      exact inferInstance
    logic_equiv_proper_derivable1_inst := by
      change Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> implRel)
        (derivable1 (L := L))
      exact inferInstance
    andp_proper_derivable1_inst := by
      change Proper (derivable1 (L := L) ==> derivable1 (L := L) ==> derivable1 (L := L))
        (andp (L := L))
      exact inferInstance
    andp_proper_equiv_inst := by
      change Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
        (andp (L := L))
      constructor
      intro x1 x2 hx y1 y2 hy
      constructor
      · intro m h
        exact ⟨hx.left m h.left, hy.left m h.right⟩
      · intro m h
        exact ⟨hx.right m h.left, hy.right m h.right⟩
    orp_proper_equiv_inst := by
      change Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
        (orp (L := L))
      constructor
      intro x1 x2 hx y1 y2 hy
      constructor
      · intro m h
        cases h with
        | inl hx1 => exact Or.inl (hx.left m hx1)
        | inr hy1 => exact Or.inr (hy.left m hy1)
      · intro m h
        cases h with
        | inl hx2 => exact Or.inl (hx.right m hx2)
        | inr hy2 => exact Or.inr (hy.right m hy2)
    orp_proper_derivable1_inst := by
      change Proper (derivable1 (L := L) ==> derivable1 (L := L) ==> derivable1 (L := L))
        (orp (L := L))
      exact inferInstance
    logic_equiv_sepcon_proper_inst := by
      change Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
        (sepcon (L := L))
      exact inferInstance
    derivable1s_sepcon_proper_inst := by
      change Proper (derivable1 (L := L) ==> derivable1 (L := L) ==> derivable1 (L := L))
        (sepcon (L := L))
      exact inferInstance
    logic_equiv_wand_proper_inst := by
      change Proper (logic_equiv (L := L) ==> logic_equiv (L := L) ==> logic_equiv (L := L))
        (wand (L := L))
      exact inferInstance
    derivable1s_wand_proper_inst := by
      change Proper (flipRel (derivable1 (L := L)) ==> derivable1 (L := L) ==> derivable1 (L := L))
        (wand (L := L))
      exact inferInstance }

end LogicTheoremSig'

end demo932
end LogicGenerator
end Unifysl
