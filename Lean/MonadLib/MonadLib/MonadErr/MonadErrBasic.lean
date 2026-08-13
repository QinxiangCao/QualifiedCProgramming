import MonadLib.Monad
import FP.BourbakiWitt
import FP.PartialOrder_Setoid
import AUXLib.SetoidRewrite

universe u

namespace MonadLib

open AUXLib
open FP
open scoped SetsNotation MonadNotation

namespace MonadErr

structure M (Sigma : Type u) (A : Type) : Type u where
  nrm : Sigma -> A -> Sigma -> Prop
  err : Sigma -> Prop

def ret {Sigma : Type u} {A : Type} (a : A) : M Sigma A where
  nrm s1 r s2 := r = a /\ s2 = s1
  err _ := False

def nrm_err {Sigma : Type u} {A : Type} (f : Sigma -> A -> Sigma -> Prop)
    (g : A -> Sigma -> Prop) : Sigma -> Prop :=
  fun s1 => exists a s0, f s1 a s0 /\ g a s0

def nrm_nrm {Sigma : Type u} {A B : Type} (f : Sigma -> A -> Sigma -> Prop)
    (g : A -> Sigma -> B -> Sigma -> Prop) : Sigma -> B -> Sigma -> Prop :=
  fun s1 b s2 => exists a s0, f s1 a s0 /\ g a s0 b s2

def bind {Sigma : Type u} {A B : Type} (m : M Sigma A) (f : A -> M Sigma B) : M Sigma B where
  nrm := nrm_nrm m.nrm (fun a => (f a).nrm)
  err s := m.err s \/ nrm_err m.nrm (fun a => (f a).err) s

end MonadErr

instance state_rel_monad (Sigma : Type u) : Monad (MonadErr.M Sigma) where
  bind := MonadErr.bind
  ret := MonadErr.ret

abbrev program := MonadErr.M
abbrev MONAD (A : Type) := program Unit A

abbrev step (Sigma : Type u) := Sigma -> Sigma -> Prop

def step_to_program {Sigma : Type u} (m : step Sigma) : program Sigma Unit where
  nrm s1 a s2 := a = () /\ m s1 s2
  err _ := False

instance {Sigma : Type u} : Coe (step Sigma) (program Sigma Unit) :=
  ⟨step_to_program⟩

def choice {Sigma : Type u} {A : Type} (f g : program Sigma A) : program Sigma A where
  nrm s a s' := f.nrm s a s' \/ g.nrm s a s'
  err s := f.err s \/ g.err s

def testPure {Sigma : Type u} (P : Prop) : program Sigma Unit where
  nrm s1 _ s2 := s1 = s2 /\ P
  err _ := False

def test {Sigma : Type u} (P : Sigma -> Prop) : program Sigma Unit where
  nrm s1 _ s2 := s1 = s2 /\ P s1
  err _ := False

def assert {Sigma : Type u} (P : Prop) : program Sigma Unit where
  nrm s1 _ s2 := s1 = s2 /\ P
  err _ := Not P

def assertS {Sigma : Type u} (P : Sigma -> Prop) : program Sigma Unit where
  nrm s1 _ s2 := s1 = s2 /\ P s1
  err s1 := Not (P s1)

def put {Sigma : Type u} (s : Sigma) : program Sigma Unit where
  nrm _ a s2 := a = () /\ s2 = s
  err _ := False

def any {Sigma : Type u} (A : Type) : program Sigma A where
  nrm s1 _ s2 := s1 = s2
  err _ := False

def get {Sigma : Type u} {A : Type} (P : Sigma -> A -> Prop) : program Sigma A where
  nrm s1 a s2 := P s1 a /\ s1 = s2
  err _ := False

def get' {Sigma : Type u} {A : Type} (f : Sigma -> A) : program Sigma A :=
  get fun s a => a = f s

def update {Sigma : Type u} (P : Sigma -> Sigma -> Prop) : program Sigma Unit where
  nrm s1 _ s2 := P s1 s2
  err _ := False

def update' {Sigma : Type u} (f : Sigma -> Sigma) : program Sigma Unit :=
  update fun s s' => s' = f s

def read {Sigma : Type} : program Sigma Sigma where
  nrm s1 a s2 := a = s1 /\ s1 = s2
  err _ := False

def If {Sigma : Type u} (cond : Sigma -> Prop) (c : program Sigma Unit) :
    program Sigma Unit :=
  choice (test cond ;; c) (test (fun s => Not (cond s)))

def if_else {Sigma : Type u} {A : Type} (cond : Sigma -> Prop)
    (c1 c2 : program Sigma A) : program Sigma A :=
  choice (test cond ;; c1) (test (fun s => Not (cond s)) ;; c2)

namespace MonadNotation

scoped notation "skip" => MonadErr.ret ()
scoped notation:50 "assume!! " P:50 => testPure P
scoped notation:50 "assume " P:50 => test P

end MonadNotation

namespace ProgramPO

def full {Sigma : Type u} {A : Type} : program Sigma A where
  nrm _ _ _ := True
  err _ := True

def bot {Sigma : Type u} {A : Type} : program Sigma A where
  nrm _ _ _ := False
  err _ := False

def intersect {Sigma : Type u} {A : Type} (x1 x2 : program Sigma A) : program Sigma A where
  nrm s a s' := x1.nrm s a s' /\ x2.nrm s a s'
  err s := x1.err s /\ x2.err s

def union {Sigma : Type u} {A : Type} (x1 x2 : program Sigma A) : program Sigma A where
  nrm s a s' := x1.nrm s a s' \/ x2.nrm s a s'
  err s := x1.err s \/ x2.err s

def indexed_intersect {Sigma : Type u} {A I : Type} (x : I -> program Sigma A) :
    program Sigma A where
  nrm s a s' := forall i, (x i).nrm s a s'
  err s := forall i, (x i).err s

def indexed_union {Sigma : Type u} {A I : Type} (x : I -> program Sigma A) :
    program Sigma A where
  nrm s a s' := exists i, (x i).nrm s a s'
  err s := exists i, (x i).err s

structure equiv {Sigma : Type u} {A : Type} (p1 p2 : program Sigma A) : Prop where
  nrmequiv : forall s a s', p1.nrm s a s' <-> p2.nrm s a s'
  errequiv : forall s, p1.err s <-> p2.err s

structure order {Sigma : Type u} {A : Type} (p1 p2 : program Sigma A) : Prop where
  nrmle : forall s a s', p1.nrm s a s' -> p2.nrm s a s'
  errle : forall s, p1.err s -> p2.err s

end ProgramPO

instance program_equiv {Sigma : Type u} {A : Type} : Equiv (program Sigma A) where
  equiv := ProgramPO.equiv

instance Equivalence_program {Sigma : Type u} {A : Type} :
    AUXLib.Equivalence (@FP.equiv (program Sigma A) _) where
  refl p := ⟨fun _ _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  symm _ _ h := ⟨fun _ _ _ => (h.nrmequiv _ _ _).symm,
    fun _ => (h.errequiv _).symm⟩
  trans _ _ _ h1 h2 := ⟨fun s a s' => (h1.nrmequiv s a s').trans (h2.nrmequiv s a s'),
    fun s => (h1.errequiv s).trans (h2.errequiv s)⟩

instance program_order {Sigma : Type u} {A : Type} : Order (program Sigma A) where
  order_rel := ProgramPO.order

instance Transitive_program {Sigma : Type u} {A : Type} :
    AUXLib.Transitive (@order_rel (program Sigma A) _) where
  trans _ _ _ h1 h2 := ⟨fun _ _ _ h => h2.nrmle _ _ _ (h1.nrmle _ _ _ h),
    fun _ h => h2.errle _ (h1.errle _ h)⟩

instance Reflexive_program {Sigma : Type u} {A : Type} :
    AUXLib.Reflexive (@order_rel (program Sigma A) _) where
  refl _ := ⟨fun _ _ _ h => h, fun _ h => h⟩

instance program_PO {Sigma : Type u} {A : Type} : PartialOrder_Setoid (program Sigma A) where
  PO_AntiSymmetric_Setoid := ⟨by
    intro p q hpq hqp
    exact ⟨fun s a s' => ⟨fun h => hpq.nrmle s a s' h,
        fun h => hqp.nrmle s a s' h⟩,
      fun s => ⟨fun h => hpq.errle s h, fun h => hqp.errle s h⟩⟩⟩
  PO_Reflexive_Setoid := by
    intro p q hpq
    exact ⟨fun s a s' h => (hpq.nrmequiv s a s').mp h,
      fun s h => (hpq.errequiv s).mp h⟩
  PO_Transitive := Transitive_program

instance program_equiv_Proper {Sigma : Type u} {A : Type} :
    Proper (equiv ==> equiv ==> Iff) (@equiv (program Sigma A) _) where
  proper x x' hxx y y' hyy := by
    constructor
    · intro hxy
      exact AUXLib.Equivalence.trans _ _ _
        (AUXLib.Equivalence.symm _ _ hxx)
        (AUXLib.Equivalence.trans _ _ _ hxy hyy)
    · intro hxy
      exact AUXLib.Equivalence.trans _ _ _ hxx
        (AUXLib.Equivalence.trans _ _ _ hxy
          (AUXLib.Equivalence.symm _ _ hyy))

theorem bind_equiv {Sigma : Type u} {A B : Type} (c1 c1' : program Sigma A)
    (c2 c2' : A -> program Sigma B) :
    equiv c1 c1' -> equiv c2 c2' -> equiv (MonadErr.bind c1 c2) (MonadErr.bind c1' c2') := by
  intro h1 h2
  constructor
  · intro s b s'
    constructor
    · rintro ⟨a, s0, ha, hb⟩
      exact ⟨a, s0, (h1.nrmequiv s a s0).mp ha, ((h2 a).nrmequiv s0 b s').mp hb⟩
    · rintro ⟨a, s0, ha, hb⟩
      exact ⟨a, s0, (h1.nrmequiv s a s0).mpr ha, ((h2 a).nrmequiv s0 b s').mpr hb⟩
  · intro s
    constructor
    · intro h
      rcases h with h | ⟨a, s0, ha, he⟩
      · exact Or.inl ((h1.errequiv s).mp h)
      · exact Or.inr ⟨a, s0, (h1.nrmequiv s a s0).mp ha,
          ((h2 a).errequiv s0).mp he⟩
    · intro h
      rcases h with h | ⟨a, s0, ha, he⟩
      · exact Or.inl ((h1.errequiv s).mpr h)
      · exact Or.inr ⟨a, s0, (h1.nrmequiv s a s0).mpr ha,
          ((h2 a).errequiv s0).mpr he⟩

theorem bindpat_equiv {Sigma : Type u} {A B : Type} (c1 c1' : program Sigma A)
    (c2 c2' : A -> program Sigma B) :
    equiv c1 c1' -> equiv c2 c2' ->
      equiv (MonadErr.bind c1 fun x => c2 x) (MonadErr.bind c1' fun x => c2' x) :=
  bind_equiv c1 c1' c2 c2'

theorem assume_equiv {Sigma : Type u} {A : Type} (P : Prop) (c : program Sigma A) :
    P -> equiv (testPure P ;; c) c := by
  intro hP
  constructor
  · intro s a s'
    constructor
    · rintro ⟨_, s0, ⟨rfl, _⟩, hc⟩
      exact hc
    · intro hc
      exact ⟨(), s, ⟨rfl, hP⟩, hc⟩
  · intro s
    constructor
    · rintro (h | ⟨_, s0, ⟨rfl, _⟩, hc⟩)
      · contradiction
      · exact hc
    · intro hc
      exact Or.inr ⟨(), s, ⟨rfl, hP⟩, hc⟩

theorem assert_equiv {Sigma : Type u} {A : Type} (P : Prop) (c : program Sigma A) :
    P -> equiv (assert P ;; c) c := by
  intro hP
  constructor
  · intro s a s'
    constructor
    · rintro ⟨_, s0, ⟨rfl, _⟩, hc⟩; exact hc
    · intro hc; exact ⟨(), s, ⟨rfl, hP⟩, hc⟩
  · intro s
    constructor
    · rintro (h | ⟨_, s0, ⟨rfl, _⟩, hc⟩)
      · exact False.elim (h hP)
      · exact hc
    · intro hc; exact Or.inr ⟨(), s, ⟨rfl, hP⟩, hc⟩

theorem bind_assoc {Sigma : Type u} {A B C : Type} (c0 : program Sigma A)
    (c1 : A -> program Sigma B) (c2 : B -> program Sigma C) :
    equiv (MonadErr.bind (MonadErr.bind c0 c1) c2)
      (MonadErr.bind c0 fun y => MonadErr.bind (c1 y) c2) := by
  constructor
  · intro s c s'
    constructor
    · rintro ⟨b, s1, ⟨a, s0, h0, h1⟩, h2⟩
      exact ⟨a, s0, h0, ⟨b, s1, h1, h2⟩⟩
    · rintro ⟨a, s0, h0, b, s1, h1, h2⟩
      exact ⟨b, s1, ⟨a, s0, h0, h1⟩, h2⟩
  · intro s
    constructor
    · rintro ((h | ⟨a, s0, h0, h1⟩) | ⟨b, s1, ⟨a, s0, h0, h1⟩, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, s0, h0, Or.inl h1⟩
      · exact Or.inr ⟨a, s0, h0, Or.inr ⟨b, s1, h1, h2⟩⟩
    · rintro (h | ⟨a, s0, h0, h1 | ⟨b, s1, h1, h2⟩⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨a, s0, h0, h1⟩)
      · exact Or.inr ⟨b, s1, ⟨a, s0, h0, h1⟩, h2⟩

theorem bind_choice_equiv {Sigma : Type u} {A B : Type} (c0 c1 : program Sigma A)
    (c2 : A -> program Sigma B) :
    equiv (MonadErr.bind (choice c0 c1) c2)
      (choice (MonadErr.bind c0 c2) (MonadErr.bind c1 c2)) := by
  constructor
  · intro s b s'
    constructor
    · rintro ⟨a, s0, h0 | h1, h2⟩
      · exact Or.inl ⟨a, s0, h0, h2⟩
      · exact Or.inr ⟨a, s0, h1, h2⟩
    · rintro (⟨a, s0, h0, h2⟩ | ⟨a, s0, h1, h2⟩)
      · exact ⟨a, s0, Or.inl h0, h2⟩
      · exact ⟨a, s0, Or.inr h1, h2⟩
  · intro s
    constructor <;> intro h
    · rcases h with (h0 | h1) | ⟨a, s0, h0 | h1, h2⟩
      · exact Or.inl (Or.inl h0)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl (Or.inr ⟨a, s0, h0, h2⟩)
      · exact Or.inr (Or.inr ⟨a, s0, h1, h2⟩)
    · rcases h with (h0 | ⟨a, s0, h0, h2⟩) | (h1 | ⟨a, s0, h1, h2⟩)
      · exact Or.inl (Or.inl h0)
      · exact Or.inr ⟨a, s0, Or.inl h0, h2⟩
      · exact Or.inl (Or.inr h1)
      · exact Or.inr ⟨a, s0, Or.inr h1, h2⟩

theorem choice_comm {Sigma : Type u} {A : Type} (c0 c1 : program Sigma A) :
    equiv (choice c0 c1) (choice c1 c0) := by
  exact ⟨fun _ _ _ => or_comm, fun _ => or_comm⟩

theorem choice_case_equiv {Sigma : Type u} {A : Type} (c0 c1 c2 c3 : program Sigma A) :
    equiv c0 c2 -> equiv c1 c3 -> equiv (choice c0 c1) (choice c2 c3) := by
  intro h0 h1
  exact ⟨fun s a s' => or_congr (h0.nrmequiv s a s') (h1.nrmequiv s a s'),
    fun s => or_congr (h0.errequiv s) (h1.errequiv s)⟩

theorem bind_ret_l {Sigma : Type u} {A B : Type} (a : A) (c : A -> program Sigma B) :
    equiv (MonadErr.bind (MonadErr.ret a) c) (c a) := by
  constructor
  · intro s b s'
    constructor
    · rintro ⟨_, s0, ⟨rfl, rfl⟩, h⟩; exact h
    · intro h; exact ⟨a, s, ⟨rfl, rfl⟩, h⟩
  · intro s
    constructor
    · rintro (h | ⟨_, s0, ⟨rfl, rfl⟩, h⟩)
      · contradiction
      · exact h
    · intro h; exact Or.inr ⟨a, s, ⟨rfl, rfl⟩, h⟩

theorem bind_ret_r {Sigma : Type u} {A : Type} (c : program Sigma A) :
    equiv (MonadErr.bind c MonadErr.ret) c := by
  constructor
  · intro s a s'
    constructor
    · rintro ⟨_, s0, h, rfl, rfl⟩; exact h
    · intro h; exact ⟨a, s', h, rfl, rfl⟩
  · intro s
    constructor
    · rintro (h | ⟨_, _, _, h⟩)
      · exact h
      · contradiction
    · exact Or.inl

theorem bind_ret_l' {Sigma : Type u} {A B C : Type} (f : A -> B)
    (c : A -> B -> program Sigma C) :
    equiv (fun k => MonadErr.bind (MonadErr.ret (f k)) (c k))
      (fun k => c k (f k)) := by
  intro k
  exact bind_ret_l (f k) (c k)

theorem common_step_equiv {Sigma : Type u} {A B : Type} (c0 : program Sigma A)
    (c1 c2 : A -> program Sigma B) :
    (forall a, equiv (c1 a) (c2 a)) ->
      equiv (MonadErr.bind c0 c1) (MonadErr.bind c0 c2) := by
  intro h
  exact bind_equiv c0 c0 c1 c2 (AUXLib.Equivalence.refl c0) h

theorem choice_l_equiv {Sigma : Type u} {A : Type} (c0 c1 : program Sigma A) :
    equiv c1 ProgramPO.bot -> equiv (choice c0 c1) c0 := by
  intro h
  constructor
  · intro s a s'
    constructor
    · rintro (hc | h1)
      · exact hc
      · exact False.elim ((h.nrmequiv s a s').mp h1)
    · exact Or.inl
  · intro s
    constructor
    · rintro (hc | h1)
      · exact hc
      · exact False.elim ((h.errequiv s).mp h1)
    · exact Or.inl

theorem choice_r_equiv {Sigma : Type u} {A : Type} (c0 c1 : program Sigma A) :
    equiv c0 ProgramPO.bot -> equiv (choice c0 c1) c1 := by
  intro h
  exact AUXLib.Equivalence.trans _ _ _ (choice_comm c0 c1) (choice_l_equiv c1 c0 h)

theorem choice_idem_equiv {Sigma : Type u} {A : Type} (c : program Sigma A) :
    equiv (choice c c) c :=
  ⟨fun _ _ _ => ⟨fun h => h.elim id id, Or.inl⟩,
    fun _ => ⟨fun h => h.elim id id, Or.inl⟩⟩

theorem assume_false_equiv {Sigma : Type u} {A : Type} (P : Prop) (c : program Sigma A) :
    Not P -> equiv (testPure P ;; c) ProgramPO.bot := by
  intro hP
  constructor
  · intro s a s'
    constructor
    · rintro ⟨_, _, ⟨_, hp⟩, _⟩; exact False.elim (hP hp)
    · intro h; exact False.elim (by simpa [ProgramPO.bot] using h)
  · intro s
    constructor
    · rintro (h | ⟨_, _, ⟨_, hp⟩, _⟩)
      · contradiction
      · exact False.elim (hP hp)
    · intro h; exact False.elim (by simpa [ProgramPO.bot] using h)

theorem bind_err_iff {Sigma : Type u} {A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (sigma : Sigma) :
    (MonadErr.bind c1 c2).err sigma <->
      c1.err sigma \/ exists a sigma', c1.nrm sigma a sigma' /\ (c2 a).err sigma' :=
  Iff.rfl

theorem bind_noerr_iff {Sigma : Type u} {A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (sigma : Sigma) :
    Not ((MonadErr.bind c1 c2).err sigma) <->
      Not (c1.err sigma) /\ forall a sigma', c1.nrm sigma a sigma' -> Not ((c2 a).err sigma') := by
  rw [bind_err_iff]
  constructor
  · intro h
    exact ⟨fun he => h (Or.inl he), fun a s hn he => h (Or.inr ⟨a, s, hn, he⟩)⟩
  · rintro ⟨he, hn⟩ (h | ⟨a, s, ha, herr⟩)
    · exact he h
    · exact hn a s ha herr

theorem bind_err_left {Sigma : Type u} {A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (sigma : Sigma) :
    c1.err sigma -> (MonadErr.bind c1 c2).err sigma := Or.inl

theorem bind_noerr_left {Sigma : Type u} {A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (sigma : Sigma) :
    Not ((MonadErr.bind c1 c2).err sigma) -> Not (c1.err sigma) :=
  fun h he => h (Or.inl he)

theorem bind_err_right {Sigma : Type u} {A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (sigma : Sigma) (a : A) (sigma' : Sigma) :
    c1.nrm sigma a sigma' -> (c2 a).err sigma' -> (MonadErr.bind c1 c2).err sigma :=
  fun hn he => Or.inr ⟨a, sigma', hn, he⟩

theorem bind_noerr_right {Sigma : Type u} {A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (sigma : Sigma) :
    Not ((MonadErr.bind c1 c2).err sigma) ->
      forall a sigma', c1.nrm sigma a sigma' -> Not ((c2 a).err sigma') :=
  fun h a s hn he => h (Or.inr ⟨a, s, hn, he⟩)

theorem bind_nrm_iff {Sigma : Type u} {A B : Type} (c1 : program Sigma A)
    (c2 : A -> program Sigma B) (sigma1 : Sigma) (b : B) (sigma2 : Sigma) :
    (MonadErr.bind c1 c2).nrm sigma1 b sigma2 <->
      exists a sigma', c1.nrm sigma1 a sigma' /\ (c2 a).nrm sigma' b sigma2 :=
  Iff.rfl

instance programbind_Proper {Sigma : Type u} {A B : Type} :
    Proper (equiv ==> equiv ==> equiv) (@MonadErr.bind Sigma A B) where
  proper _ _ h1 _ _ h2 := bind_equiv _ _ _ _ h1 h2

instance programbindpat_Proper {Sigma : Type u} {A B : Type} :
    Proper (equiv ==> equiv ==> equiv)
      (fun (c1 : program Sigma A) (c2 : A -> program Sigma B) =>
        MonadErr.bind c1 c2) := programbind_Proper

instance programbind_included_Proper {Sigma : Type u} {A B : Type} :
    Proper (order_rel ==> order_rel ==> order_rel) (@MonadErr.bind Sigma A B) where
  proper _ _ h1 _ _ h2 := by
    constructor
    · rintro s b s' ⟨a, s0, ha, hb⟩
      exact ⟨a, s0, h1.nrmle s a s0 ha, (h2 a).nrmle s0 b s' hb⟩
    · intro s h
      rcases h with h | ⟨a, s0, ha, he⟩
      · exact Or.inl (h1.errle s h)
      · exact Or.inr ⟨a, s0, h1.nrmle s a s0 ha, (h2 a).errle s0 he⟩

instance choice_equiv_Proper {Sigma : Type u} {A : Type} :
    Proper (equiv ==> equiv ==> equiv) (@choice Sigma A) where
  proper _ _ h1 _ _ h2 := choice_case_equiv _ _ _ _ h1 h2

def ATrue {Sigma : Type u} : Sigma -> Prop := fun _ => True

macro "err_prog_nf" : tactic =>
  `(tactic|
    first
      | apply bind_ret_l'
      | ((repeat first
          | rel_rw [bind_assoc]
          | rel_rw [bind_choice_equiv]
          | rel_rw [bind_ret_l]
          | rel_rw [bind_ret_l']
          | rel_rw [bind_ret_r]) <;>
        try exact AUXLib.Equivalence.refl _))

macro "err_prog_nf" " in " loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic|
    repeat first
      | rel_rw [bind_assoc] at $loc
      | rel_rw [bind_choice_equiv] at $loc
      | rel_rw [bind_ret_l] at $loc
      | rel_rw [bind_ret_l'] at $loc
      | rel_rw [bind_ret_r] at $loc)

end MonadLib
