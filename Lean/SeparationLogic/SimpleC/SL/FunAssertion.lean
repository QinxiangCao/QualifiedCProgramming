import SimpleC.CoreLang.CTypes
import SimpleC.SL.Assertion
import MonadLib.MonadErr.MonadErrHoare

/-! Function specifications retain one shared function environment across
separating conjunction. HoareExpr quantifies over every disjoint frame, as in
the Rocq FunAssertion module. -/
namespace SimpleC.SL.FunAssertion

open SimpleC.Common.CTypes SimpleC.CoreLang.CTypes
open SimpleC.SL.Mem SimpleC.SL.CommonAssertion
open Unifysl.LogicGenerator.demo932 MonadLib

abbrev ParamSig := List SimpleCtype
abbrev FuncSig := ParamSig × SimpleCtype

def RetType : SimpleCtype → Type
  | .CT_basic .CT_void => Unit
  | _ => Int

def ParamTuple : ParamSig → Type
  | [] => Unit
  | [_] => Int
  | _ :: t :: ts => Int × ParamTuple (t :: ts)

abbrev FunSem (s : FuncSig) := ParamTuple s.1 → program mem (RetType s.2)
abbrev FunEnv := (s : FuncSig) → Int → Option (FunSem s)

structure state where
  st_mem : mem
  st_χ : FunEnv

abbrev model := state
abbrev expr := state → Prop
abbrev Assertion := expr

def join (left right result : state) : Prop :=
  mem_join left.st_mem right.st_mem result.st_mem ∧
    result.st_χ = left.st_χ ∧ result.st_χ = right.st_χ

def is_unit (st : state) : Prop := mem_empty st.st_mem

def Names : LanguageSig.{0} where
  model := state
  join := join
  is_unit := is_unit

def DerivedNames : DerivedNamesSig Names := {}

def PrimitiveRules : PrimitiveRuleSig Names DerivedNames where
  unit_join := by
    intro st
    exact ⟨⟨empty_mem, st.st_χ⟩, empty_mem_empty, mem_join_emp2 st.st_mem, rfl, rfl⟩
  unit_spec := by
    intro st result unit hunit hjoin
    rcases st with ⟨m, χ⟩
    rcases result with ⟨m', χ'⟩
    rcases unit with ⟨u, χu⟩
    rcases hjoin with ⟨hm, hχ, _⟩
    have hu := mem_empty_IS_empty_mem' u hunit
    subst u
    have heq := mem_join_emp_r m m' hm
    cases heq
    cases hχ
    rfl
  join_comm := by
    intro left right result h
    exact ⟨mem_join_comm h.1, h.2.2, h.2.1⟩
  join_assoc := by
    intro left middle right leftMiddle result hl hr
    obtain ⟨mr, hm, hfinal⟩ := mem_join_assoc2 hl.1 hr.1
    refine ⟨⟨mr, left.st_χ⟩, ⟨hm, ?_, ?_⟩, ⟨hfinal, ?_, ?_⟩⟩
    · exact hl.2.1.symm.trans hl.2.2
    · exact hl.2.1.symm.trans (hr.2.1.symm.trans hr.2.2)
    · exact hr.2.1.trans hl.2.1
    · exact hr.2.1.trans hl.2.1

def Context : Facade.Context.{0, 0} where
  Names := Names
  DerivedNames := DerivedNames
  Rules := PrimitiveRules

abbrev derivable1 := Context.derivable1
abbrev logic_equiv := Context.logic_equiv
abbrev sepcon := Context.sepcon
abbrev andp := Context.andp
abbrev coq_prop := Context.coq_prop
abbrev emp := Context.emp
abbrev wand := Context.wand

def mstore (p v : Int) : expr := fun st => SimpleC.SL.Assertion.mstore p v st.st_mem
def mstore_noninit (p : Int) : expr := fun st => SimpleC.SL.Assertion.mstore_noninit p st.st_mem

def SL : SeparationLogicSig where
  toContext := Context
  mstore := mstore
  mstore_noninit := mstore_noninit
  mstore_mstore_noninit := by
    intro p v st h
    exact SimpleC.SL.Assertion.mstore_mstore_noninit p v st.st_mem h
  mstore_eqm := by
    intro p v v' heq st h
    exact SimpleC.SL.Assertion.mstore_eqm p v v' heq st.st_mem h
  dup_mstore_noninit := by
    intro p st h
    rcases h with ⟨left, right, hj, hl, hr⟩
    exact SimpleC.SL.Assertion.dup_mstore_noninit p st.st_mem
      ⟨left.st_mem, right.st_mem, hj.1, hl, hr⟩

abbrev Spec (s : FuncSig) := FunSem s → Assertion

def HoareExpr_raw {R : Type} (P : Assertion) (c : program mem R)
    (Q : R → Assertion) : Assertion := fun st =>
  Hoare (fun m => P ⟨m, st.st_χ⟩) c (fun r m => Q r ⟨m, st.st_χ⟩)

def HoareExpr {R : Type} (P : Assertion) (c : program mem R)
    (Q : R → Assertion) : Assertion := fun st =>
  ∀ frame : Assertion, HoareExpr_raw (sepcon P frame) c (fun r => sepcon (Q r) frame) st

def func_ptr_spec {s : FuncSig} (f : Int) (S : Spec s) : Assertion := fun st =>
  f ≠ 0 ∧ ∃ F, st.st_χ s f = some F ∧ S F st

def HoareFun (s : FuncSig) (P : ParamTuple s.1 → Assertion)
    (Q : ParamTuple s.1 → RetType s.2 → Assertion) : Spec s := fun F st =>
  ∀ θ, HoareExpr (P θ) (F θ) (Q θ) st

def corable (P : Assertion) : Prop :=
  ∀ st1 st2 st, join st1 st2 st → (P st1 ↔ P st)

theorem func_ptr_spec_mono {s : FuncSig} (f : Int) (S1 S2 : Spec s)
    (h : ∀ F, derivable1 (S1 F) (S2 F)) :
    derivable1 (func_ptr_spec f S1) (func_ptr_spec f S2) := by
  rintro st ⟨hn, F, hf, hs⟩
  exact ⟨hn, F, hf, h F st hs⟩

theorem func_ptr_spec_nonzero {s : FuncSig} (f : Int) (S : Spec s) :
    derivable1 (func_ptr_spec f S) (coq_prop (f ≠ 0)) := by
  intro st h
  exact h.1

theorem func_ptr_spec_nonzero' {s : FuncSig} (f : Int) (S : Spec s) :
    derivable1 (func_ptr_spec f S) (andp (coq_prop (f ≠ 0)) (func_ptr_spec f S)) := by
  intro st h
  exact ⟨h.1, h⟩

theorem HoareExpr_corable {R : Type} (P : Assertion) (c : program mem R)
    (Q : R → Assertion) : corable (HoareExpr P c Q) := by
  intro st1 st2 st hj
  unfold HoareExpr HoareExpr_raw
  simp only [hj.2.1]

theorem HoareFun_corable {s : FuncSig} (P : ParamTuple s.1 → Assertion)
    (Q : ParamTuple s.1 → RetType s.2 → Assertion) (F : FunSem s) :
    corable (HoareFun s P Q F) := by
  intro st1 st2 st hj
  exact ⟨fun h θ => (HoareExpr_corable (P θ) (F θ) (Q θ) st1 st2 st hj).mp (h θ),
    fun h θ => (HoareExpr_corable (P θ) (F θ) (Q θ) st1 st2 st hj).mpr (h θ)⟩

theorem func_ptr_spec_corable {s : FuncSig} (f : Int) (S : Spec s)
    (h : ∀ F, corable (S F)) : corable (func_ptr_spec f S) := by
  intro st1 st2 st hj
  constructor
  · rintro ⟨hn, F, hf, hs⟩
    exact ⟨hn, F, by simpa only [hj.2.1] using hf, (h F st1 st2 st hj).mp hs⟩
  · rintro ⟨hn, F, hf, hs⟩
    exact ⟨hn, F, by simpa only [hj.2.1] using hf, (h F st1 st2 st hj).mpr hs⟩

def func_ptr_hoare (f : Int) (s : FuncSig) (P : ParamTuple s.1 → Assertion)
    (Q : ParamTuple s.1 → RetType s.2 → Assertion) : Assertion :=
  func_ptr_spec f (HoareFun s P Q)

theorem func_ptr_hoare_corable {s : FuncSig} (f : Int) (P : ParamTuple s.1 → Assertion)
    (Q : ParamTuple s.1 → RetType s.2 → Assertion) : corable (func_ptr_hoare f s P Q) :=
  func_ptr_spec_corable f _ (HoareFun_corable P Q)


abbrev exp (P : α → Assertion) : Assertion := fun st => ∃ a, P a st
abbrev allp (P : α → Assertion) : Assertion := fun st => ∀ a, P a st

theorem allp_corable (P : α → Assertion) (h : ∀ a, corable (P a)) :
    corable (allp P) := by
  intro l r st hj
  exact ⟨fun hp a => (h a l r st hj).mp (hp a),
    fun hp a => (h a l r st hj).mpr (hp a)⟩

theorem HoareExpr_raw_mono {R : Type} {P1 P2 : Assertion}
    {c : program mem R} {Q1 Q2 : R → Assertion}
    (hP : derivable1 P2 P1) (hQ : ∀ r, derivable1 (Q1 r) (Q2 r)) :
    derivable1 (HoareExpr_raw P1 c Q1) (HoareExpr_raw P2 c Q2) := by
  intro st h
  exact ⟨fun a m1 m2 hp hc => hQ a _ (h.1 a m1 m2 (hP _ hp) hc),
    fun m hp => h.2 m (hP _ hp)⟩

theorem HoareExpr_mono {R : Type} {P1 P2 : Assertion}
    {c : program mem R} {Q1 Q2 : R → Assertion}
    (hP : derivable1 P2 P1) (hQ : ∀ r, derivable1 (Q1 r) (Q2 r)) :
    derivable1 (HoareExpr P1 c Q1) (HoareExpr P2 c Q2) := by
  intro st h frame
  apply HoareExpr_raw_mono (P1 := sepcon P1 frame) (Q1 := fun r => sepcon (Q1 r) frame) _ _ st (h frame)
  · rintro s ⟨l, r, hj, hp, hf⟩
    exact ⟨l, r, hj, hP l hp, hf⟩
  · rintro a s ⟨l, r, hj, hq, hf⟩
    exact ⟨l, r, hj, hQ a l hq, hf⟩

theorem HoareExpr_exists {A R : Type} (P : A → Assertion)
    (c : program mem R) (Q : R → Assertion) :
    logic_equiv (HoareExpr (exp P) c Q) (allp (fun a => HoareExpr (P a) c Q)) := by
  constructor
  · intro st h x
    apply HoareExpr_mono (P1 := exp P) (Q1 := Q) _ (fun _ _ hq => hq) st h
    intro s hp
    exact ⟨x, hp⟩
  · intro st h frame
    constructor
    · rintro a m1 m2 ⟨l, r, hj, ⟨x, hp⟩, hf⟩ hc
      exact (h x frame).1 a m1 m2 ⟨l, r, hj, hp, hf⟩ hc
    · rintro m ⟨l, r, hj, ⟨x, hp⟩, hf⟩ hc
      exact (h x frame).2 m ⟨l, r, hj, hp, hf⟩ hc

theorem HoareExpr_forget_frame {A : Type} (P : Assertion)
    (c : program mem A) (Q : A → Assertion) :
    derivable1 (HoareExpr P c Q) (HoareExpr_raw P c Q) := by
  intro st h
  exact HoareExpr_raw_mono (Context.derivable1_sepcon_emp_r P)
    (fun a => Context.derivable1_sepcon_emp_l (Q a)) st (h emp)

theorem frame_rule_sound {A : Type} (c : program mem A)
    (P : Assertion) (Q : A → Assertion) (R : Assertion) :
    derivable1 (HoareExpr P c Q)
      (HoareExpr (sepcon P R) c (fun a => sepcon (Q a) R)) := by
  intro st h frame
  exact HoareExpr_raw_mono ((Context.logic_equiv_sepcon_assoc P R frame).2)
    (fun a => Context.derivable1_sepcon_assoc1 (Q a) R frame) st (h (sepcon R frame))

theorem HoareFun_exists {A : Type} {s : FuncSig}
    (P : A → ParamTuple s.1 → Assertion)
    (Q : ParamTuple s.1 → RetType s.2 → Assertion) (F : FunSem s) :
    logic_equiv (HoareFun s (fun θ => exp (fun a => P a θ)) Q F)
      (allp (fun a => HoareFun s (P a) Q F)) := by
  constructor
  · intro st h a θ
    exact (HoareExpr_exists (fun a => P a θ) (F θ) (Q θ)).1 st (h θ) a
  · intro st h θ
    exact (HoareExpr_exists (fun a => P a θ) (F θ) (Q θ)).2 st (fun a => h a θ)

def safety_mono {A : Type} (c : program mem A) : Prop :=
  ∀ m1, ¬ c.err m1 → ∀ m2, mem_incl m1 m2 → ¬ c.err m2

def frame_property {A : Type} (c : program mem A) : Prop :=
  ∀ m a m', c.nrm m a m' → ∀ m1 m2, mem_join m1 m2 m → ¬ c.err m1 →
    ∃ m1', mem_join m1' m2 m' ∧ c.nrm m1 a m1'

def frame_properties {A : Type} (c : program mem A) : Prop :=
  safety_mono c ∧ frame_property c

def funsem_frame_properties {s : FuncSig} (F : FunSem s) : Prop :=
  ∀ θ, frame_properties (F θ)

theorem HoareExpr_raw_frame_rule {A : Type} (c : program mem A)
    (P : Assertion) (Q : A → Assertion) (R : Assertion) (hlocal : frame_properties c) :
    derivable1 (HoareExpr_raw P c Q)
      (HoareExpr_raw (sepcon P R) c (fun a => sepcon (Q a) R)) := by
  rintro ⟨m, χ⟩ ⟨hnrm, herr⟩
  constructor
  · rintro a m0 m' ⟨⟨m1, χ1⟩, ⟨m2, χ2⟩, ⟨hj, hχ1, hχ2⟩, hp, hr⟩ hc
    change χ = χ1 at hχ1
    change χ = χ2 at hχ2
    subst χ1
    subst χ2
    obtain ⟨m1', hj', hc'⟩ := hlocal.2 m0 a m' hc m1 m2 hj (herr m1 hp)
    exact ⟨⟨m1', χ⟩, ⟨m2, χ⟩, ⟨hj', rfl, rfl⟩, hnrm a m1 m1' hp hc', hr⟩
  · rintro m0 ⟨⟨m1, χ1⟩, ⟨m2, χ2⟩, ⟨hj, hχ1, hχ2⟩, hp, _⟩ hc
    change χ = χ1 at hχ1
    subst χ1
    exact hlocal.1 m1 (herr m1 hp) m0 (mem_join_incl_l m1 m2 m0 hj) hc

theorem HoareExpr_of_raw {A : Type} (P : Assertion) (c : program mem A)
    (Q : A → Assertion) (hlocal : frame_properties c) :
    derivable1 (HoareExpr_raw P c Q) (HoareExpr P c Q) := by
  intro st h frame
  exact HoareExpr_raw_frame_rule c P Q frame hlocal st h

theorem HoareFun_conseq {s : FuncSig} (Pbase Pderived : ParamTuple s.1 → Assertion)
    (Qbase Qderived : ParamTuple s.1 → RetType s.2 → Assertion)
    (hp : ∀ θ, derivable1 (Pderived θ) (Pbase θ))
    (hq : ∀ θ r, derivable1 (Qbase θ r) (Qderived θ r)) (F : FunSem s) :
    derivable1 (HoareFun s Pbase Qbase F) (HoareFun s Pderived Qderived F) := by
  intro st h θ
  exact HoareExpr_mono (hp θ) (hq θ) st (h θ)

theorem HoareFun_ramification {s : FuncSig}
    (Pbase Pderived : ParamTuple s.1 → Assertion)
    (Qbase Qderived : ParamTuple s.1 → RetType s.2 → Assertion)
    (hram : ∀ θ, derivable1 (Pderived θ)
      (sepcon (Pbase θ) (allp (fun r => wand (Qbase θ r) (Qderived θ r)))))
    (F : FunSem s) :
    derivable1 (HoareFun s Pbase Qbase F) (HoareFun s Pderived Qderived F) := by
  intro st h θ
  have hpost : ∀ r, derivable1
      (sepcon (Qbase θ r) (allp (fun r' => wand (Qbase θ r') (Qderived θ r'))))
      (Qderived θ r) := by
    rintro r st ⟨l, rr, hj, hq, hw⟩
    exact hw r l st (PrimitiveRules.join_comm _ _ _ hj) hq
  exact HoareExpr_mono (hram θ) hpost st
    (frame_rule_sound (F θ) (Pbase θ) (Qbase θ) _ st (h θ))

end SimpleC.SL.FunAssertion
