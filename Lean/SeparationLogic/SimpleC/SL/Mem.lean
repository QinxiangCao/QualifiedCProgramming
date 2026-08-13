import AUXLib.Axioms
import AUXLib.Feq
import Std.Tactic
import Lean.Elab.Tactic.Omega

namespace SimpleC.SL.Mem

open AUXLib

abbrev addr : Type := Int

def addr_eqb (x y : addr) : Bool := decide (x = y)

def addr_dec (x y : addr) : Decidable (x = y) := inferInstance

def addr_eqb_eq (p1 p2 : addr) : Iff (addr_eqb p1 p2 = true) (p1 = p2) := by
  simp [addr_eqb]

def addr_eqb_neq (p1 p2 : addr) : Iff (addr_eqb p1 p2 = false) (Not (p1 = p2)) := by
  simp [addr_eqb]

def addr_eqb_refl (p : addr) : addr_eqb p p = true := by
  simp [addr_eqb]

abbrev byte : Type := Int

def byte_eqb (x y : byte) : Bool := decide (x = y)

inductive mem_var where
  | Noperm
  | Noninit
  | value (b : byte)

export mem_var (Noperm Noninit value)

def mem_var_eqb (a b : mem_var) : Bool :=
  match a, b with
  | Noperm, Noperm => true
  | Noninit, Noninit => true
  | value v1, value v2 => byte_eqb v1 v2
  | _, _ => false

abbrev mem : Type := addr -> mem_var

def empty_mem : mem := fun _ => Noperm

def single_byte_mem (p : addr) (n : byte) : mem :=
  fun p' => if addr_eqb p' p then value n else Noperm

def single_Noninit_mem (p : addr) : mem :=
  fun p' => if addr_eqb p' p then Noninit else Noperm

def mem_byte_update (m : mem) (p : addr) (n : byte) : mem :=
  fun p' => if addr_eqb p' p then value n else m p'

set_option linter.unusedVariables false in
def mem_noninit_update (m : mem) (p : addr) : mem :=
  fun p' => if addr_eqb p' p then Noninit else Noperm

def mem_remove (m : mem) (p : addr) : mem :=
  fun p' => if addr_eqb p' p then Noperm else m p'

def mem_update_list : mem -> List addr -> List (Option byte) -> mem
  | m, p :: ps, n :: ns =>
      match n with
      | some n => mem_byte_update (mem_update_list m ps ns) p n
      | none => mem_noninit_update (mem_update_list m ps ns) p
  | m, _, _ => m

def Z_seq_nat (p : Int) : Nat -> List Int
  | 0 => []
  | n + 1 => p :: Z_seq_nat (p + 1) n

def Z_seq (p n : Int) : List Int :=
  Z_seq_nat p n.toNat

def mem_update_N (m : mem) (p : addr) (v : byte) (n : Int) : mem :=
  mem_update_list m (Z_seq p n) (List.replicate n.toNat (some v))

def mem_empty (m : mem) : Prop :=
  forall p, m p = Noperm

def mem_single (m : mem) (p : addr) (n : byte) : Prop :=
  m p = value n /\ (forall p', Not (p' = p) -> m p' = Noperm)

def mem_join (m1 m2 m : mem) : Prop :=
  forall p,
    (m1 p = Noperm /\ m2 p = Noperm /\ m p = Noperm) \/
    (m1 p = Noperm /\ m2 p = Noninit /\ m p = Noninit) \/
    (m1 p = Noninit /\ m2 p = Noperm /\ m p = Noninit) \/
    (exists n, m1 p = Noperm /\ m2 p = value n /\ m p = value n) \/
    (exists n, m1 p = value n /\ m2 p = Noperm /\ m p = value n)

instance mem_join_congr :
    Proper (f_eq ==> f_eq ==> f_eq ==> Iff) mem_join where
  proper := by
    intro m1 m1' h1 m2 m2' h2 m m' h3
    have e1 : m1 = m1' := funext h1
    have e2 : m2 = m2' := funext h2
    have e3 : m = m' := funext h3
    subst e1
    subst e2
    subst e3
    rfl

def mem_incl (m1 m2 : mem) : Prop :=
  forall p, Not (m1 p = Noperm) -> m2 p = m1 p

theorem empty_mem_empty : mem_empty empty_mem := by
  intro p
  rfl

theorem mem_empty_IS_empty_mem (m : mem) (h : mem_empty m) : f_eq m empty_mem := by
  intro p
  exact h p

theorem single_mem_single (p : addr) (n : byte) : mem_single (single_byte_mem p n) p n := by
  constructor
  · simp [single_byte_mem, addr_eqb]
  · intro p' hne
    simp [single_byte_mem, addr_eqb, hne]

theorem mem_join_comm {m1 m2 m : mem} (h : mem_join m1 m2 m) : mem_join m2 m1 m := by
  intro p
  rcases h p with h | h | h | h | h
  · exact Or.inl ⟨h.2.1, h.1, h.2.2⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩))
  · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)
  · rcases h with ⟨n, h1, h2, h3⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, h2, h1, h3⟩)))
  · rcases h with ⟨n, h1, h2, h3⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h2, h1, h3⟩)))

theorem mem_join_assoc1 {m1 m2 m3 m23 m123 : mem}
    (h23 : mem_join m2 m3 m23) (h123 : mem_join m1 m23 m123) :
    exists m12, mem_join m1 m2 m12 /\ mem_join m12 m3 m123 := by
  let m12 : mem := fun p => match m1 p with | Noperm => m2 p | x => x
  refine ⟨m12, ?_, ?_⟩
  · intro p
    have hA := h23 p
    have hB := h123 p
    cases e1 : m1 p <;> cases e2 : m2 p <;> cases e3 : m3 p <;>
      cases e23 : m23 p <;> cases e123 : m123 p <;> simp_all [m12]
  · intro p
    have hA := h23 p
    have hB := h123 p
    cases e1 : m1 p <;> cases e2 : m2 p <;> cases e3 : m3 p <;>
      cases e23 : m23 p <;> cases e123 : m123 p <;> simp_all [m12]

theorem mem_join_assoc2 {m1 m2 m3 m12 m123 : mem}
    (h12 : mem_join m1 m2 m12) (h123 : mem_join m12 m3 m123) :
    exists m23, mem_join m2 m3 m23 /\ mem_join m1 m23 m123 := by
  have h := mem_join_assoc1 (mem_join_comm h12) (mem_join_comm h123)
  rcases h with ⟨m23, h3, h4⟩
  exact ⟨m23, mem_join_comm h3, mem_join_comm h4⟩

theorem mem_join_emp1 (m : mem) : mem_join empty_mem m m := by
  intro p
  cases h : m p <;> simp [empty_mem]

theorem mem_join_emp2 (m : mem) : mem_join m empty_mem m :=
  mem_join_comm (mem_join_emp1 m)

theorem mem_join_eq_inv1 (m1 m1' m2 m2' m m' : mem)
    (h2 : f_eq m2 m2') (hm : f_eq m m')
    (hj : mem_join m1 m2 m) (hj' : mem_join m1' m2' m') : f_eq m1 m1' := by
  intro p
  have h2p := h2 p
  have hmp := hm p
  have hp := hj p
  have hp' := hj' p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp' with hp' | hp' | hp' | hp' | hp' <;>
    rcases hp with ⟨a, b, c⟩ <;>
    rcases hp' with ⟨a', b', c'⟩ <;> simp_all

theorem mem_join_eq_inv2 (m1 m1' m2 m2' m m' : mem)
    (h1 : f_eq m1 m1') (hm : f_eq m m')
    (hj : mem_join m1 m2 m) (hj' : mem_join m1' m2' m') : f_eq m2 m2' := by
  exact mem_join_eq_inv1 m2 m2' m1 m1' m m' h1 hm
    (mem_join_comm hj) (mem_join_comm hj')

theorem mem_join_None1 {m1 m2 m : mem} (p : addr)
    (hj : mem_join m1 m2 m) (h : m1 p = Noperm) : m p = m2 p := by
  have hp := hj p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp with ⟨a, b, c⟩ <;> simp_all

theorem mem_join_None2 {m1 m2 m : mem} (p : addr)
    (hj : mem_join m1 m2 m) (h : m2 p = Noperm) : m p = m1 p := by
  exact mem_join_None1 p (mem_join_comm hj) h

theorem mem_join_None3 {m1 m2 m : mem} (p : addr)
    (hj : mem_join m1 m2 m) (h : m p = Noperm) :
    m1 p = Noperm /\ m2 p = Noperm := by
  have hp := hj p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp with ⟨a, b, c⟩ <;> simp_all

theorem mem_join_Some1 (m1 m2 m : mem) (p : addr)
    (hj : mem_join m1 m2 m) (h : m1 p = Noninit) :
    m2 p = Noperm /\ m p = Noninit := by
  have hp := hj p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp with ⟨a, b, c⟩ <;> simp_all

theorem mem_join_Some2 (m1 m2 m : mem) (p : addr)
    (hj : mem_join m1 m2 m) (h : m2 p = Noninit) :
    m1 p = Noperm /\ m p = Noninit := by
  exact mem_join_Some1 m2 m1 m p (mem_join_comm hj) h

theorem mem_join_Some3 (m1 m2 m : mem) (p : addr) (n : byte)
    (hj : mem_join m1 m2 m) (h : m1 p = value n) :
    m2 p = Noperm /\ m p = value n := by
  have hp := hj p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp with ⟨a, b, c⟩ <;> simp_all

theorem mem_join_Some4 (m1 m2 m : mem) (p : addr) (n : byte)
    (hj : mem_join m1 m2 m) (h : m2 p = value n) :
    m1 p = Noperm /\ m p = value n := by
  exact mem_join_Some3 m2 m1 m p n (mem_join_comm hj) h

theorem mem_join_Some6 (m1 m2 m : mem) (p : addr) (n : byte)
    (hj : mem_join m1 m2 m) (h : m p = value n) :
    (m1 p = value n /\ m2 p = Noperm) \/
      (m1 p = Noperm /\ m2 p = value n) := by
  have hp := hj p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp with ⟨a, b, c⟩ <;> simp_all

theorem mem_join_Some5 (m1 m2 m : mem) (p : addr)
    (hj : mem_join m1 m2 m) (h : m p = Noninit) :
    (m1 p = Noninit /\ m2 p = Noperm) \/
      (m1 p = Noperm /\ m2 p = Noninit) := by
  have hp := hj p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp with ⟨a, b, c⟩ <;> simp_all

private theorem mem_join_replace_left {m1 m1' m2 m m' : mem} {p : addr}
    (hj : mem_join m1 m2 m) (h2none : m2 p = Noperm)
    (hleft : forall p', Not (p' = p) -> m1 p' = m1' p')
    (hat : m' p = m1' p)
    (hout : forall p', Not (p' = p) -> m p' = m' p') :
    mem_join m1' m2 m' := by
  intro q
  by_cases hqp : q = p
  · subst q
    cases hcell : m1' p <;> simp_all
  · have hp := hj q
    have hl := hleft q hqp
    have ho := hout q hqp
    rcases hp with hp | hp | hp | hp | hp <;>
      rcases hp with ⟨a, b, c⟩ <;> simp_all

theorem mem_join_update1 (m1 m1' m2 m m' : mem) (p : addr) (n0 : byte)
    (hj : mem_join m1 m2 m) (hvalue : m1 p = value n0)
    (hleft : forall p', Not (p' = p) -> m1 p' = m1' p')
    (hat : m' p = m1' p)
    (hout : forall p', Not (p' = p) -> m p' = m' p') :
    mem_join m1' m2 m' := by
  have h2none := (mem_join_Some3 m1 m2 m p n0 hj hvalue).1
  exact mem_join_replace_left hj h2none hleft hat hout

theorem mem_join_update2 (m1 m1' m2 m m' : mem) (p : addr)
    (hj : mem_join m1 m2 m) (hnoninit : m1 p = Noninit)
    (hleft : forall p', Not (p' = p) -> m1 p' = m1' p')
    (hat : m' p = m1' p)
    (hout : forall p', Not (p' = p) -> m p' = m' p') :
    mem_join m1' m2 m' := by
  have h2none := (mem_join_Some1 m1 m2 m p hj hnoninit).1
  exact mem_join_replace_left hj h2none hleft hat hout

theorem mem_join_update_None1 (m1 m1' m2 m m' : mem) (p : addr)
    (hj : mem_join m1 m2 m) (hnone : m p = Noperm)
    (hleft : forall p', Not (p' = p) -> m1 p' = m1' p')
    (hat : m' p = m1' p)
    (hout : forall p', Not (p' = p) -> m p' = m' p') :
    mem_join m1' m2 m' := by
  have h2none := (mem_join_None3 p hj hnone).2
  exact mem_join_replace_left hj h2none hleft hat hout

theorem mem_join_update_list (m1 m1' m2 m m' : mem) (ps : List addr)
    (hj : mem_join m1 m2 m)
    (hempty : forall p, p ∈ ps -> m p = Noperm)
    (heqIn : forall p, p ∈ ps -> m1' p = m' p)
    (hleft : forall p, p ∉ ps -> m1 p = m1' p)
    (hout : forall p, p ∉ ps -> m p = m' p) :
    mem_join m1' m2 m' := by
  intro p
  by_cases hin : p ∈ ps
  · have hnone := hempty p hin
    have h2none := (mem_join_None3 p hj hnone).2
    have heq := heqIn p hin
    cases hcell : m1' p <;> simp_all
  · have hp := hj p
    have hl := hleft p hin
    have ho := hout p hin
    rcases hp with hp | hp | hp | hp | hp <;>
      rcases hp with ⟨a, b, c⟩ <;> simp_all

theorem mem_join_update_range (m1 m1' m2 m m' : mem) (p1 p2 : addr)
    (hj : mem_join m1 m2 m)
    (hempty : forall p, p >= p1 -> p < p2 -> m p = Noperm)
    (heqIn : forall p, p >= p1 -> p < p2 -> m1' p = m' p)
    (hleft : forall p, (p < p1 \/ p >= p2) -> m1 p = m1' p)
    (hout : forall p, (p < p1 \/ p >= p2) -> m p = m' p) :
    mem_join m1' m2 m' := by
  intro p
  by_cases hlo : p < p1
  · have hp := hj p
    have hl := hleft p (Or.inl hlo)
    have ho := hout p (Or.inl hlo)
    cases em' : m' p <;>
    rcases hp with hp | hp | hp | hp | hp <;>
      rcases hp with ⟨a, b, c⟩ <;> simp_all
  · by_cases hhi : p >= p2
    · have hp := hj p
      have hl := hleft p (Or.inr hhi)
      have ho := hout p (Or.inr hhi)
      cases em' : m' p <;>
      rcases hp with hp | hp | hp | hp | hp <;>
        rcases hp with ⟨a, b, c⟩ <;> simp_all
    · have hp1 : p >= p1 := Int.le_of_not_gt hlo
      have hp2 : p < p2 := Int.lt_of_not_ge hhi
      have hnone := hempty p hp1 hp2
      have h2none := (mem_join_None3 p hj hnone).2
      have heq := heqIn p hp1 hp2
      cases hcell : m1' p <;> cases em' : m' p <;> simp_all

theorem mem_join_incl_l (m1 m2 m : mem) (hj : mem_join m1 m2 m) : mem_incl m1 m := by
  intro p hnot
  have hp := hj p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp with ⟨a, b, c⟩ <;> simp_all

theorem mem_join_incl_r (m1 m2 m : mem) (hj : mem_join m1 m2 m) : mem_incl m2 m :=
  mem_join_incl_l m2 m1 m (mem_join_comm hj)

private theorem mem_update_seq_in_nat (m : mem) (p : addr) (v : byte) (n : Nat)
    (p' : addr) (hlo : p' >= p) (hhi : p' < p + (n : Int)) :
    mem_update_list m (Z_seq_nat p n) (List.replicate n (some v)) p' = value v := by
  induction n generalizing p with
  | zero =>
      have hhi' : p' < p := by simpa using hhi
      exact (Int.not_lt_of_ge hlo hhi').elim
  | succ n ih =>
      simp only [Z_seq_nat, List.replicate_succ, mem_update_list]
      unfold mem_byte_update
      by_cases heq : p' = p
      · simp [addr_eqb, heq]
      · simp [addr_eqb, heq]
        apply ih (p := p + 1)
        · apply Int.add_one_le_iff.mpr
          apply Int.lt_of_not_ge
          intro hrev
          exact heq (Int.le_antisymm hrev hlo)
        · simpa [Int.natCast_succ, Int.add_assoc, Int.add_comm, Int.add_left_comm] using hhi

private theorem mem_update_seq_notin_nat (m : mem) (p : addr) (v : byte) (n : Nat)
    (p' : addr) (hout : p' < p \/ p' >= p + (n : Int)) :
    mem_update_list m (Z_seq_nat p n) (List.replicate n (some v)) p' = m p' := by
  induction n generalizing p with
  | zero => simp [Z_seq_nat, mem_update_list]
  | succ n ih =>
      simp only [Z_seq_nat, List.replicate_succ, mem_update_list]
      unfold mem_byte_update
      by_cases heq : p' = p
      · subst p'
        rcases hout with hlt | hge
        · exact (Int.not_lt_of_ge (Int.le_refl p) hlt).elim
        · have hpos : 0 < (Nat.succ n : Int) := Int.natCast_pos.mpr (Nat.zero_lt_succ n)
          exact (Int.not_le_of_gt (Int.lt_add_of_pos_right p hpos) hge).elim
      · simp [addr_eqb, heq]
        apply ih (p := p + 1)
        rcases hout with hlt | hge
        · exact Or.inl (Int.lt_trans hlt (Int.lt_add_one_iff.mpr (Int.le_refl p)))
        · exact Or.inr (by
            simpa [Int.natCast_succ, Int.add_assoc, Int.add_comm, Int.add_left_comm] using hge)

theorem mem_update_N_in (m : mem) (p : addr) (v : byte) (n : Int) (p' : addr)
    (hlo : p' >= p) (hhi : p' < p + n) : mem_update_N m p v n p' = value v := by
  cases n with
  | ofNat n =>
      exact mem_update_seq_in_nat m p v n p' hlo hhi
  | negSucc n =>
      have hneg : p + Int.negSucc n < p := by
        simpa using Int.add_lt_add_left (Int.negSucc_lt_zero n) p
      exact (Int.not_lt_of_ge hlo (Int.lt_trans hhi hneg)).elim

theorem mem_update_N_notin (m : mem) (p : addr) (v : byte) (n : Int) (p' : addr)
    (hout : p' < p \/ p' >= p + n) : mem_update_N m p v n p' = m p' := by
  cases n with
  | ofNat n =>
      exact mem_update_seq_notin_nat m p v n p' hout
  | negSucc n =>
      simp [mem_update_N, Z_seq, Z_seq_nat, mem_update_list]

theorem single_mem_get_eq (x : addr) (v : byte) : single_byte_mem x v x = value v := by
  simp [single_byte_mem, addr_eqb]

theorem single_mem_get_neq (x : addr) (v : byte) (y : addr) (h : Not (x = y)) :
    Not (single_byte_mem x v y = value v) := by
  simp [single_byte_mem, addr_eqb, Ne.symm h]

theorem mem_join_emp : mem_join empty_mem empty_mem empty_mem :=
  mem_join_emp1 empty_mem

theorem mem_empty_IS_empty_mem' (m : mem) (h : mem_empty m) : m = empty_mem := by
  funext p
  exact h p

theorem mem_join_emp_l (m m1 : mem) (h : mem_join empty_mem m m1) : m1 = m := by
  funext p
  exact mem_join_None1 p h rfl

theorem mem_join_emp_r (m m1 : mem) (h : mem_join m empty_mem m1) : m1 = m := by
  funext p
  exact mem_join_None2 p h rfl

theorem mem_join_eq {m1 m2 m m' : mem}
    (h : mem_join m1 m2 m) (h' : mem_join m1 m2 m') : m = m' := by
  funext p
  have hp := h p
  have hp' := h' p
  rcases hp with hp | hp | hp | hp | hp <;>
    rcases hp' with hp' | hp' | hp' | hp' | hp' <;>
    rcases hp with ⟨a, b, c⟩ <;>
    rcases hp' with ⟨a', b', c'⟩ <;> simp_all

theorem mem_join_eq_l {m1 m1' m2 m : mem}
    (h : mem_join m1 m2 m) (h' : mem_join m1' m2 m) : m1 = m1' := by
  funext p
  exact mem_join_eq_inv1 m1 m1' m2 m2 m m
    ((f_eq_refl _ _).refl m2) ((f_eq_refl _ _).refl m) h h' p

theorem mem_join_eq_r {m1 m2 m2' m : mem}
    (h : mem_join m1 m2 m) (h' : mem_join m1 m2' m) : m2 = m2' := by
  exact mem_join_eq_l (mem_join_comm h) (mem_join_comm h')

theorem mem_join_Some_eq_l {m1 m2 m3 : mem} {x : addr} {v1 v2 : byte}
    (h : mem_join m1 m2 m3) (h1 : m1 x = value v1) (h3 : m3 x = value v2) : v2 = v1 := by
  have hp := mem_join_Some3 m1 m2 m3 x v1 h h1
  simp_all

theorem mem_join_Some_eq_r {m1 m2 m3 : mem} {x : addr} {v1 v2 : byte}
    (h : mem_join m1 m2 m3) (h2 : m2 x = value v1) (h3 : m3 x = value v2) : v2 = v1 := by
  exact mem_join_Some_eq_l (mem_join_comm h) h2 h3

theorem mem_join_None {m1 m2 m3 : mem} {x : addr}
    (h : mem_join m1 m2 m3) (h3 : m3 x = Noperm) :
    m1 x = Noperm /\ m2 x = Noperm :=
  mem_join_None3 x h h3

theorem mem_update_eq (m : mem) (x : addr) (v : byte) :
    mem_byte_update m x v x = value v := by
  simp [mem_byte_update, addr_eqb]

theorem mem_update_neq (m : mem) (x : addr) (v : byte) (x' : addr)
    (h : Not (x' = x)) : mem_byte_update m x v x' = m x' := by
  simp [mem_byte_update, addr_eqb, h]

theorem mem_update_single_eq (x : addr) (v v0 : byte) :
    mem_byte_update (single_byte_mem x v) x v0 = single_byte_mem x v0 := by
  funext p
  by_cases h : p = x <;> simp [mem_byte_update, single_byte_mem, addr_eqb, h]

theorem mem_update_unfold (m m' : mem) (x : addr) (v : byte)
    (hat : m' x = value v)
    (hout : forall p', Not (p' = x) -> m p' = m' p') :
    m' = mem_byte_update m x v := by
  funext p
  by_cases h : p = x
  · subst p
    simp [mem_byte_update, addr_eqb, hat]
  · simp [mem_byte_update, addr_eqb, h, (hout p h).symm]

private theorem right_noperm_of_left_owned {m1 m2 m3 : mem} {x : addr}
    (hj : mem_join m1 m2 m3) (howned : Not (m1 x = Noperm)) : m2 x = Noperm := by
  cases hcell : m1 x with
  | Noperm => exact False.elim (howned hcell)
  | Noninit => exact (mem_join_Some1 m1 m2 m3 x hj hcell).1
  | value b => exact (mem_join_Some3 m1 m2 m3 x b hj hcell).1

theorem mem_join_mem_update_l (m1 m2 m3 : mem) (x : addr) (v : byte)
    (hj : mem_join m1 m2 m3) (howned : Not (m1 x = Noperm)) :
    mem_join (mem_byte_update m1 x v) m2 (mem_byte_update m3 x v) := by
  intro p
  by_cases h : p = x
  · subst p
    have h2 := right_noperm_of_left_owned hj howned
    simp [mem_byte_update, addr_eqb, h2]
  · have hp := hj p
    simp only [mem_byte_update, addr_eqb, h]
    exact hp

theorem mem_join_mem_update_l' (m1 m2 m3 : mem) (x : addr) (v : byte)
    (hj : mem_join m1 m2 m3) (hnone : m3 x = Noperm) :
    mem_join (mem_byte_update m1 x v) m2 (mem_byte_update m3 x v) := by
  intro p
  by_cases h : p = x
  · subst p
    have h2 := (mem_join_None3 x hj hnone).2
    simp [mem_byte_update, addr_eqb, h2]
  · have hp := hj p
    simp only [mem_byte_update, addr_eqb, h]
    exact hp

theorem mem_join_single_mem_update_l (m : mem) (p : addr) (v : byte)
    (hnone : m p = Noperm) :
    mem_join m (single_byte_mem p v) (mem_byte_update m p v) := by
  intro q
  by_cases h : q = p
  · subst q
    simp [single_byte_mem, mem_byte_update, addr_eqb, hnone]
  · cases hcell : m q <;>
      simp [single_byte_mem, mem_byte_update, addr_eqb, h, hcell]

theorem mem_join_single_mem_remove_l {m : mem} {p : addr} {v : byte} {m1 : mem}
    (hj : mem_join m (single_byte_mem p v) m1) : m = mem_remove m1 p := by
  funext q
  by_cases h : q = p
  · subst q
    have hright : single_byte_mem p v p = value v := single_mem_get_eq p v
    have hleft := (mem_join_Some4 m (single_byte_mem p v) m1 p v hj hright).1
    simp [mem_remove, addr_eqb, hleft]
  · have hright : single_byte_mem p v q = Noperm := by
      simp [single_byte_mem, addr_eqb, h]
    have heq := mem_join_None2 q hj hright
    simp [mem_remove, addr_eqb, h, heq]

theorem mem_remove_eq (m : mem) (x : addr) : mem_remove m x x = Noperm := by
  simp [mem_remove, addr_eqb]

theorem mem_remove_neq (m : mem) (x x' : addr) (h : Not (x' = x)) :
    mem_remove m x x' = m x' := by
  simp [mem_remove, addr_eqb, h]

theorem mem_remove_unfold (m m' : mem) (x : addr) (hat : m' x = Noperm)
    (hout : forall p', Not (p' = x) -> m p' = m' p') :
    m' = mem_remove m x := by
  funext p
  by_cases h : p = x
  · subst p
    simp [mem_remove, addr_eqb, hat]
  · simp [mem_remove, addr_eqb, h, (hout p h).symm]

theorem mem_join_mem_remove_l (m1 m2 m3 : mem) (x : addr)
    (hj : mem_join m1 m2 m3) (howned : Not (m1 x = Noperm)) :
    mem_join (mem_remove m1 x) m2 (mem_remove m3 x) := by
  intro p
  by_cases h : p = x
  · subst p
    have h2 := right_noperm_of_left_owned hj howned
    simp [mem_remove, addr_eqb, h2]
  · have hp := hj p
    simp only [mem_remove, addr_eqb, h]
    exact hp

def disjoint (m1 m2 : mem) : Prop :=
  forall x,
    match m1 x, m2 x with
    | _, Noperm => True
    | Noperm, _ => True
    | _, _ => False

def merge (m1 m2 : mem) : mem :=
  fun a =>
    match m1 a, m2 a with
    | value b1, _ => value b1
    | Noninit, value b2 => value b2
    | Noninit, _ => Noninit
    | Noperm, _ => m2 a

def minus (m1 m2 : mem) : mem :=
  fun a =>
    match m1 a, m2 a with
    | value b1, Noperm => value b1
    | value _, _ => Noperm
    | Noninit, Noperm => Noninit
    | Noninit, _ => Noperm
    | Noperm, _ => Noperm

def sub (m1 m2 : mem) : Prop :=
  forall x, Not (m1 x = Noperm) -> m2 x = m1 x

theorem mem_get_single_mem_sub {m : mem} {x : addr} {v : byte}
    (hat : m x = value v) : sub (single_byte_mem x v) m := by
  intro q howned
  by_cases h : q = x
  · subst q
    simpa [single_byte_mem, addr_eqb] using hat
  · have hnone : single_byte_mem x v q = Noperm := by
      simp [single_byte_mem, addr_eqb, h]
    exact False.elim (howned hnone)

theorem disjoint_comm {m1 m2 : mem} (h : disjoint m1 m2) : disjoint m2 m1 := by
  intro x
  have hx := h x
  cases e1 : m1 x <;> cases e2 : m2 x <;> simp_all

theorem disjoint_merge_mem_join {m1 m2 : mem} (h : disjoint m1 m2) :
    mem_join m1 m2 (merge m1 m2) := by
  intro p
  have hp := h p
  cases e1 : m1 p <;> cases e2 : m2 p <;> simp_all [disjoint, merge]

theorem sub_minus_mem_join {m1 m2 : mem} (h : sub m1 m2) :
    mem_join m1 (minus m2 m1) m2 := by
  intro p
  have hp := h p
  cases e1 : m1 p <;> cases e2 : m2 p <;> simp_all [sub, minus]

theorem mem_join_sub_l {m1 m2 m : mem} (h : mem_join m1 m2 m) : sub m1 m :=
  mem_join_incl_l m1 m2 m h

theorem sub_merge_sub (m1 m2 m : mem) (h1 : sub m1 m) (h2 : sub m2 m) :
    sub (merge m1 m2) m := by
  intro x howned
  have hp1 := h1 x
  have hp2 := h2 x
  cases e1 : m1 x <;> cases e2 : m2 x <;> simp_all [merge]

theorem mem_join_disjoint_l_ex (m1 m2 m3 m4 m : mem)
    (hd : disjoint m1 m3) (h12 : mem_join m1 m2 m) (h34 : mem_join m3 m4 m) :
    exists m5 m6, mem_join m1 m3 m5 /\ mem_join m5 m6 m := by
  refine ⟨merge m1 m3, minus m (merge m1 m3), disjoint_merge_mem_join hd, ?_⟩
  apply sub_minus_mem_join
  apply sub_merge_sub m1 m3 m
  · exact mem_join_sub_l h12
  · exact mem_join_sub_l h34

theorem mem_join_disjoint {m1 m2 m3 : mem} (h : mem_join m1 m2 m3) : disjoint m1 m2 := by
  intro x
  have hx := h x
  cases e1 : m1 x <;> cases e2 : m2 x <;> cases e3 : m3 x <;>
    simp_all

theorem disjoint_mem_join_l {m1 m2 m3 m4 : mem}
    (hd : disjoint m1 m4) (hj : mem_join m2 m3 m4) : disjoint m1 m2 := by
  intro x
  have hdx := hd x
  have hjx := hj x
  cases e1 : m1 x <;> cases e2 : m2 x <;> cases e3 : m3 x <;> cases e4 : m4 x <;>
    simp_all [disjoint]

theorem disjoint_mem_join_r {m1 m2 m3 m4 : mem}
    (hd : disjoint m1 m4) (hj : mem_join m2 m3 m4) : disjoint m1 m3 :=
  disjoint_mem_join_l hd (mem_join_comm hj)

theorem mem_join_eqmerge {m1 m2 m3 : mem} (h : mem_join m1 m2 m3) :
    m3 = merge m1 m2 := by
  exact mem_join_eq h (disjoint_merge_mem_join (mem_join_disjoint h))

theorem mem_join_merge_assoc_l {m1 m2 m3 m4 : mem}
    (hd : disjoint m1 m2) (hj : mem_join (merge m1 m2) m3 m4) :
    mem_join m1 (merge m2 m3) m4 := by
  rcases mem_join_assoc2 (disjoint_merge_mem_join hd) hj with ⟨m23, h23, h1⟩
  have heq : m23 = merge m2 m3 := mem_join_eqmerge h23
  simpa [heq] using h1

theorem mem_join_merge_assoc_r {m1 m2 m3 m4 : mem}
    (hd : disjoint m2 m3) (hj : mem_join m1 (merge m2 m3) m4) :
    mem_join (merge m1 m2) m3 m4 := by
  rcases mem_join_assoc1 (disjoint_merge_mem_join hd) hj with ⟨m12, h12, h3⟩
  have heq : m12 = merge m1 m2 := mem_join_eqmerge h12
  simpa [heq] using h3

private theorem mem_empty_iff_eq (m : mem) : Iff (mem_empty m) (m = empty_mem) := by
  constructor
  · exact mem_empty_IS_empty_mem' m
  · intro h
    subst m
    exact empty_mem_empty

private theorem mem_join_empty_left_iff (m out : mem) :
    Iff (mem_join empty_mem m out) (out = m) := by
  constructor
  · exact mem_join_emp_l m out
  · intro h
    subst out
    exact mem_join_emp1 m

private theorem mem_join_empty_right_iff (m out : mem) :
    Iff (mem_join m empty_mem out) (out = m) := by
  constructor
  · exact mem_join_emp_r m out
  · intro h
    subst out
    exact mem_join_emp2 m

private theorem mem_join_result_empty_iff (m1 m2 : mem) :
    Iff (mem_join m1 m2 empty_mem) (m1 = empty_mem /\ m2 = empty_mem) := by
  constructor
  · intro h
    constructor
    · funext p
      exact (mem_join_None3 p h rfl).1
    · funext p
      exact (mem_join_None3 p h rfl).2
  · rintro ⟨rfl, rfl⟩
    exact mem_join_emp

syntax "addr_destruct " term:max term:max : tactic

macro_rules
  | `(tactic| addr_destruct $x:term $y:term) =>
      `(tactic| by_cases E : $x = $y)

syntax "my_destruct " term:max : tactic

namespace MemAutomation

open Lean Meta Elab Tactic

private def freshIdent (baseName : Name) : TacticM (TSyntax `ident) := do
  pure ⟨mkIdent (← mkFreshUserName baseName)⟩

partial def runMyDestruct (hypothesis : TSyntax `term) : TacticM Unit := withMainContext do
  let proof ← Lean.Elab.Tactic.elabTermForApply hypothesis
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let type ← whnf (← inferType (← instantiateMVars proof))
  if type.isAppOfArity ``Exists 2 then
    let witness ← freshIdent `witness
    let rest ← freshIdent `Hrest
    evalTactic (← `(tactic|
      rcases ($hypothesis) with ⟨$witness:ident, $rest:ident⟩ <;>
        my_destruct $rest:ident))
  else if type.isAppOfArity ``And 2 then
    let left ← freshIdent `Hleft
    let right ← freshIdent `Hright
    evalTactic (← `(tactic|
      rcases ($hypothesis) with ⟨$left:ident, $right:ident⟩ <;>
        my_destruct $left:ident <;> my_destruct $right:ident))
  else if type.isAppOfArity ``Or 2 then
    let branch ← freshIdent `Hcase
    evalTactic (← `(tactic|
      rcases ($hypothesis) with $branch:ident | $branch:ident <;>
        my_destruct $branch:ident))
  else
    evalTactic (← `(tactic| first | contradiction | skip))

end MemAutomation

elab_rules : tactic
  | `(tactic| my_destruct $h:term) =>
      MemAutomation.runMyDestruct h

syntax "solve_empmem" : tactic

namespace MemAutomation

open Lean Meta Elab Tactic

private def assertAndSubst (goal : MVarId) (sourceHyp : FVarId)
    (variableExpr : Expr) (proof : Expr) : MetaM MVarId := do
  unless variableExpr.isFVar do
    throwError "solve_empmem: expected a local variable to substitute"
  let (asserted, nextGoal) ← goal.assertHypotheses #[{
    userName := ← mkFreshUserName `Hempmem
    type := ← inferType proof
    value := proof
    binderInfo := .default
    kind := .default }]
  let nextGoal ← Meta.subst nextGoal variableExpr.fvarId!
  let nextGoal ← asserted.foldlM (fun nextGoal assertedHyp =>
    nextGoal.tryClear assertedHyp) nextGoal
  nextGoal.tryClear sourceHyp

private def substEqualitySide (goal : MVarId) (sourceHyp : FVarId)
    (left right proof : Expr) : MetaM (Option MVarId) := do
  if ← isDefEq left right then
    return some (← goal.tryClear sourceHyp)
  if left.isFVar && !(← isDefEq left right) then
    return some (← assertAndSubst goal sourceHyp left proof)
  if right.isFVar && !(← isDefEq left right) then
    return some (← assertAndSubst goal sourceHyp right proof)
  return none

private def eliminateOneEmptyHypothesis : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if type.isAppOfArity ``mem_empty 1 then
        let m := type.getAppArgs[0]!
        if m.isFVar then
          let proof ← mkAppM ``mem_empty_IS_empty_mem' #[m, localDecl.toExpr]
          replaceMainGoal [← assertAndSubst goal localDecl.fvarId m proof]
          let hypothesis := mkIdent localDecl.userName
          evalTactic (← `(tactic| try clear $hypothesis:ident))
          return true
      if type.isAppOfArity ``mem_join 3 then
        let args := type.getAppArgs
        let left := args[0]!
        let right := args[1]!
        let out := args[2]!
        if ← isDefEq right (mkConst ``empty_mem) then
          let proof ← mkAppM ``mem_join_emp_r #[left, out, localDecl.toExpr]
          if let some nextGoal ←
              substEqualitySide goal localDecl.fvarId out left proof then
            replaceMainGoal [nextGoal]
            return true
        if ← isDefEq left (mkConst ``empty_mem) then
          let proof ← mkAppM ``mem_join_emp_l #[right, out, localDecl.toExpr]
          if let some nextGoal ←
              substEqualitySide goal localDecl.fvarId out right proof then
            replaceMainGoal [nextGoal]
            return true
  return false

private def closeSourceEmptyGoal : TacticM Unit := withMainContext do
  evalTactic (← `(tactic|
    first
    | exact SimpleC.SL.Mem.mem_join_emp
    | exact SimpleC.SL.Mem.mem_join_emp2 _
    | exact SimpleC.SL.Mem.mem_join_emp1 _
    | exact SimpleC.SL.Mem.empty_mem_empty
    | skip))

partial def runSolveEmpMem : TacticM Unit := do
  if ← eliminateOneEmptyHypothesis then
    runSolveEmpMem
  else
    closeSourceEmptyGoal

end MemAutomation

elab_rules : tactic
  | `(tactic| solve_empmem) => MemAutomation.runSolveEmpMem

end SimpleC.SL.Mem
