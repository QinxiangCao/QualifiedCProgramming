import Lean.Elab.Tactic.Omega
import MaxMinLib.MaxMin

open AUXLib

namespace MaxMinLib

private theorem pred_equiv_intro {A : Type} {P Q : A -> Prop}
    (h : forall a, P a <-> Q a) : Sets.equiv P Q := by
  change forall a, P a <-> Q a
  exact h

private theorem union_mem_iff {A : Type} (P Q : A -> Prop) (a : A) :
    (Sets.union P Q) a <-> P a \/ Q a := by
  change P a \/ Q a <-> P a \/ Q a
  rfl

private theorem union_left {A : Type} {P Q : A -> Prop} {a : A}
    (h : P a) : (Sets.union P Q) a :=
  (union_mem_iff P Q a).mpr (Or.inl h)

private theorem union_right {A : Type} {P Q : A -> Prop} {a : A}
    (h : Q a) : (Sets.union P Q) a :=
  (union_mem_iff P Q a).mpr (Or.inr h)

private theorem max_n_in_range_nat (Q : Int -> Prop) :
    forall K : Nat,
      (exists n, 0 <= n /\ n <= (K : Int) /\ Q n) ->
      exists m, Q m /\ (0 <= m /\ m <= (K : Int)) /\
        (forall k, 0 <= k /\ k <= (K : Int) -> Q k -> k <= m) := by
  intro K
  induction K with
  | zero =>
      rintro ⟨n, hn0, hnK, hQn⟩
      have hn : n = 0 := by omega
      subst n
      refine ⟨0, hQn, ⟨by omega, by omega⟩, ?_⟩
      intro k hk _
      omega
  | succ K ih =>
      intro hExists
      by_cases hTop : Q ((K.succ : Nat) : Int)
      · refine ⟨(K.succ : Int), hTop, ⟨by omega, by omega⟩, ?_⟩
        intro k hk _
        omega
      · rcases hExists with ⟨n, hn0, hnK, hQn⟩
        have hnPred : n <= (K : Int) := by
          by_cases hnEq : n = (K.succ : Int)
          · subst n
            contradiction
          · omega
        rcases ih ⟨n, hn0, hnPred, hQn⟩ with ⟨m, hQm, hmRange, hmMax⟩
        refine ⟨m, hQm, ⟨hmRange.1, by omega⟩, ?_⟩
        intro k hk hQk
        have hkPred : k <= (K : Int) := by
          by_cases hkEq : k = (K.succ : Int)
          · subst k
            contradiction
          · omega
        exact hmMax k ⟨hk.1, hkPred⟩ hQk

private theorem min_n_in_range_nat (Q : Int -> Prop) :
    forall K : Nat,
      (exists n, 0 <= n /\ n <= (K : Int) /\ Q n) ->
      exists m, Q m /\ (0 <= m /\ m <= (K : Int)) /\
        (forall k, 0 <= k /\ k <= (K : Int) -> Q k -> m <= k) := by
  intro K
  induction K with
  | zero =>
      rintro ⟨n, hn0, hnK, hQn⟩
      have hn : n = 0 := by omega
      subst n
      refine ⟨0, hQn, ⟨by omega, by omega⟩, ?_⟩
      intro k hk _
      omega
  | succ K ih =>
      intro hExists
      by_cases hPrefix : exists n, 0 <= n /\ n <= (K : Int) /\ Q n
      · rcases ih hPrefix with ⟨m, hQm, hmRange, hmMin⟩
        refine ⟨m, hQm, ⟨hmRange.1, by omega⟩, ?_⟩
        intro k hk hQk
        by_cases hkPred : k <= (K : Int)
        · exact hmMin k ⟨hk.1, hkPred⟩ hQk
        · omega
      · have hQTop : Q ((K.succ : Nat) : Int) := by
          rcases hExists with ⟨n, hn0, hnK, hQn⟩
          have hnTop : n = (K.succ : Int) := by
            by_cases hnEq : n = (K.succ : Int)
            · exact hnEq
            · have hnPred : n <= (K : Int) := by omega
              exact False.elim (hPrefix ⟨n, hn0, hnPred, hQn⟩)
          subst n
          exact hQn
        refine ⟨(K.succ : Int), hQTop, ⟨by omega, by omega⟩, ?_⟩
        intro k hk hQk
        by_cases hkPred : k <= (K : Int)
        · exact False.elim (hPrefix ⟨k, hk.1, hkPred, hQk⟩)
        · omega

opaque Z_le_total (x y : Int) : AUXLib.Sumbool (x <= y) (y <= x) := by
  by_cases h : x <= y
  · exact AUXLib.Sumbool.left h
  · exact AUXLib.Sumbool.right (by omega)

theorem max_n_in_range (Q : Int -> Prop) (K : Int) :
    0 <= K ->
    (exists n, (0 <= n /\ n <= K) /\ Q n) ->
    exists m, Q m /\ (0 <= m /\ m <= K) /\
      (forall k, 0 <= k /\ k <= K -> Q k -> k <= m) := by
  intro hK hExists
  have hKcast : ((K.toNat : Nat) : Int) = K := Int.toNat_of_nonneg hK
  rcases hExists with ⟨n, ⟨hn0, hnK⟩, hQn⟩
  have hExistsNat : exists n, 0 <= n /\ n <= ((K.toNat : Nat) : Int) /\ Q n := by
    refine ⟨n, hn0, ?_, hQn⟩
    simpa [hKcast] using hnK
  rcases max_n_in_range_nat Q K.toNat hExistsNat with ⟨m, hQm, hmRange, hmMax⟩
  refine ⟨m, hQm, ⟨hmRange.1, ?_⟩, ?_⟩
  · simpa [hKcast] using hmRange.2
  · intro k hk hQk
    apply hmMax k
    · exact ⟨hk.1, by simpa [hKcast] using hk.2⟩
    · exact hQk

theorem min_n_in_range (Q : Int -> Prop) (K : Int) :
    0 <= K ->
    (exists n, (0 <= n /\ n <= K) /\ Q n) ->
    exists m, Q m /\ (0 <= m /\ m <= K) /\
      (forall k, 0 <= k /\ k <= K -> Q k -> m <= k) := by
  intro hK hExists
  have hKcast : ((K.toNat : Nat) : Int) = K := Int.toNat_of_nonneg hK
  rcases hExists with ⟨n, ⟨hn0, hnK⟩, hQn⟩
  have hExistsNat : exists n, 0 <= n /\ n <= ((K.toNat : Nat) : Int) /\ Q n := by
    refine ⟨n, hn0, ?_, hQn⟩
    simpa [hKcast] using hnK
  rcases min_n_in_range_nat Q K.toNat hExistsNat with ⟨m, hQm, hmRange, hmMin⟩
  refine ⟨m, hQm, ⟨hmRange.1, ?_⟩, ?_⟩
  · simpa [hKcast] using hmRange.2
  · intro k hk hQk
    apply hmMin k
    · exact ⟨hk.1, by simpa [hKcast] using hk.2⟩
    · exact hQk

instance Zle_TotalOrder : TotalOrder (fun x y : Int => x <= y) where
  le_refl := by intro x; omega
  le_trans := by intro x y z hxy hyz; omega
  le_antisym := by intro x y hxy hyx; omega
  le_total := Z_le_total

opaque Nat_le_total (x y : Nat) : AUXLib.Sumbool (x <= y) (y <= x) := by
  by_cases h : x <= y
  · exact AUXLib.Sumbool.left h
  · exact AUXLib.Sumbool.right (by omega)

theorem min_nonempty_exists {A : Type} (f : A -> Nat) (P : A -> Prop) :
    (exists a, P a) ->
    exists b, min_value_of_subset Nat.le P f b := by
  classical
  rintro ⟨a0, ha0⟩
  have hmain :
      forall n, forall a0, P a0 -> f a0 = n ->
        exists b, min_value_of_subset Nat.le P f b := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro a0 ha0 hfa0
        by_cases hsmall : exists a', P a' /\ f a' < f a0
        · rcases hsmall with ⟨a', ha', hlt⟩
          exact ih (f a') (by omega) a' ha' rfl
        · refine ⟨f a0, ⟨a0, ⟨?_, rfl⟩⟩⟩
          constructor
          · exact ha0
          · intro a ha
            by_cases hle : f a0 <= f a
            · exact hle
            · exact False.elim (hsmall ⟨a, ha, by omega⟩)
  exact hmain (f a0) a0 ha0 rfl

theorem min_union_iff {A : Type} (f : A -> Nat) (P Q : A -> Prop) :
    Sets.equiv
      (min_value_of_subset Nat.le (Sets.union P Q) f)
      (min_value_of_subset Nat.le
        (Sets.union (min_value_of_subset Nat.le P f)
          (min_value_of_subset Nat.le Q f)) id) := by
  apply pred_equiv_intro
  intro n
  constructor
  · intro h
    rcases h with ⟨x, ⟨⟨hxUnion, hxMin⟩, hfx⟩⟩
    subst n
    refine ⟨f x, ⟨?_, rfl⟩⟩
    constructor
    · rcases (union_mem_iff P Q x).mp hxUnion with hxP | hxQ
      · exact union_left ⟨x, ⟨⟨hxP, fun y hy => hxMin y (union_left hy)⟩, rfl⟩⟩
      · exact union_right ⟨x, ⟨⟨hxQ, fun y hy => hxMin y (union_right hy)⟩, rfl⟩⟩
    · intro y hy
      rcases (union_mem_iff (min_value_of_subset Nat.le P f)
          (min_value_of_subset Nat.le Q f) y).mp hy with hyP | hyQ
      · rcases hyP with ⟨a, ⟨⟨haP, _⟩, hfa⟩⟩
        rw [← hfa]
        exact hxMin a (union_left haP)
      · rcases hyQ with ⟨a, ⟨⟨haQ, _⟩, hfa⟩⟩
        rw [← hfa]
        exact hxMin a (union_right haQ)
  · intro h
    rcases h with ⟨value, ⟨⟨hValueUnion, hValueMin⟩, hvalue⟩⟩
    subst n
    rcases (union_mem_iff (min_value_of_subset Nat.le P f)
        (min_value_of_subset Nat.le Q f) value).mp hValueUnion with hPmin | hQmin
    · rcases hPmin with ⟨a, ⟨⟨haP, haMin⟩, hfa⟩⟩
      subst value
      refine ⟨a, ⟨⟨union_left haP, ?_⟩, rfl⟩⟩
      intro b hb
      rcases (union_mem_iff P Q b).mp hb with hbP | hbQ
      · exact haMin b hbP
      · rcases min_nonempty_exists f Q ⟨b, hbQ⟩ with ⟨qv, qmin⟩
        have hle1v : f a <= qv := hValueMin qv (union_right qmin)
        rcases qmin with ⟨q, ⟨⟨hqQ, hqMin⟩, hfq⟩⟩
        have hqv_le_b : qv <= f b := by
          rw [← hfq]
          exact hqMin b hbQ
        exact Nat.le_trans hle1v hqv_le_b
    · rcases hQmin with ⟨a, ⟨⟨haQ, haMin⟩, hfa⟩⟩
      subst value
      refine ⟨a, ⟨⟨union_right haQ, ?_⟩, rfl⟩⟩
      intro b hb
      rcases (union_mem_iff P Q b).mp hb with hbP | hbQ
      · rcases min_nonempty_exists f P ⟨b, hbP⟩ with ⟨pv, pmin⟩
        have hle1v : f a <= pv := hValueMin pv (union_left pmin)
        rcases pmin with ⟨p, ⟨⟨hpP, hpMin⟩, hfp⟩⟩
        have hpv_le_b : pv <= f b := by
          rw [← hfp]
          exact hpMin b hbP
        exact Nat.le_trans hle1v hpv_le_b
      · exact haMin b hbQ

instance NatLe_TotalOrder : TotalOrder (fun x y : Nat => x <= y) where
  le_refl := by intro x; omega
  le_trans := by intro x y z hxy hyz; omega
  le_antisym := by intro x y hxy hyx; omega
  le_total := Nat_le_total

def Nat_op_le : Option Nat -> Option Nat -> Prop :=
  fun x y =>
    match x, y with
    | some x, some y => x <= y
    | _, none => True
    | none, _ => False

def Nat_op_plus : Option Nat -> Option Nat -> Option Nat :=
  fun x y =>
    match x, y with
    | some x, some y => some (x + y)
    | none, _ => none
    | _, none => none

def Nat_op_min (x y : Option Nat) : Option Nat :=
  match x, y with
  | some x, some y => some (min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

theorem Nat_op_le_refl (x : Option Nat) : Nat_op_le x x := by
  cases x <;> simp [Nat_op_le]

theorem Nat_op_le_trans (x y z : Option Nat) :
    Nat_op_le x y -> Nat_op_le y z -> Nat_op_le x z := by
  cases x <;> cases y <;> cases z <;> simp [Nat_op_le] <;> omega

theorem Nat_op_le_antisym (x y : Option Nat) :
    Nat_op_le x y -> Nat_op_le y x -> x = y := by
  cases x <;> cases y <;> simp [Nat_op_le] <;> intro h1 h2 <;> try omega

opaque Nat_op_le_total (x y : Option Nat) :
    AUXLib.Sumbool (Nat_op_le x y) (Nat_op_le y x) := by
  cases x <;> cases y <;> simp [Nat_op_le]
  · exact AUXLib.Sumbool.left True.intro
  · exact AUXLib.Sumbool.right True.intro
  · exact AUXLib.Sumbool.left True.intro
  · apply Nat_le_total

instance Nat_op_le_TotalOrder : TotalOrder Nat_op_le where
  le_refl := Nat_op_le_refl
  le_trans := Nat_op_le_trans
  le_antisym := Nat_op_le_antisym
  le_total := Nat_op_le_total

def Z_op_le : Option Int -> Option Int -> Prop :=
  fun x y =>
    match x, y with
    | some x, some y => x <= y
    | _, none => True
    | none, _ => False

def Z_op_plus : Option Int -> Option Int -> Option Int :=
  fun x y =>
    match x, y with
    | some x, some y => some (x + y)
    | none, _ => none
    | _, none => none

def Z_op_min : Option Int -> Option Int -> Option Int :=
  fun x y =>
    match x, y with
    | some x, some y => some (min x y)
    | some x, none => some x
    | none, some y => some y
    | none, none => none

theorem Z_op_le_refl (x : Option Int) : Z_op_le x x := by
  cases x <;> simp [Z_op_le]

theorem Z_op_le_trans (x y z : Option Int) :
    Z_op_le x y -> Z_op_le y z -> Z_op_le x z := by
  cases x <;> cases y <;> cases z <;> simp [Z_op_le] <;> omega

theorem Z_op_le_antisym (x y : Option Int) :
    Z_op_le x y -> Z_op_le y x -> x = y := by
  cases x <;> cases y <;> simp [Z_op_le] <;> intro h1 h2 <;> try omega

opaque Z_op_le_total (x y : Option Int) :
    AUXLib.Sumbool (Z_op_le x y) (Z_op_le y x) := by
  cases x <;> cases y <;> simp [Z_op_le]
  · exact AUXLib.Sumbool.left True.intro
  · exact AUXLib.Sumbool.right True.intro
  · exact AUXLib.Sumbool.left True.intro
  · apply Z_le_total

instance Z_op_le_TotalOrder : TotalOrder Z_op_le where
  le_refl := Z_op_le_refl
  le_trans := Z_op_le_trans
  le_antisym := Z_op_le_antisym
  le_total := Z_op_le_total

theorem Z_op_plus_mono (x1 x2 y1 y2 : Option Int) :
    Z_op_le x1 x2 -> Z_op_le y1 y2 ->
    Z_op_le (Z_op_plus x1 y1) (Z_op_plus x2 y2) := by
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;>
    simp [Z_op_le, Z_op_plus] <;> omega

theorem Z_op_none_le_iff (x : Option Int) :
    Z_op_le none x <-> x = none := by
  cases x <;> simp [Z_op_le]

theorem Z_op_le_ge_cases (x y : Option Int) :
    Z_op_le x y \/ Z_op_le y x := by
  cases Z_op_le_total x y with
  | left h => exact Or.inl h
  | right h => exact Or.inr h

theorem Z_op_plus_O_r (x : Option Int) :
    Z_op_plus x (some 0) = x := by
  cases x <;> simp [Z_op_plus]

theorem Z_op_plus_O_l (x : Option Int) :
    Z_op_plus (some 0) x = x := by
  cases x <;> simp [Z_op_plus]

theorem Z_op_plus_none_r (x : Option Int) :
    Z_op_plus x none = none := by
  cases x <;> rfl

theorem Z_op_plus_comm (x y : Option Int) :
    Z_op_plus x y = Z_op_plus y x := by
  cases x <;> cases y <;> simp [Z_op_plus, Int.add_comm]

theorem Z_op_plus_assoc (x y z : Option Int) :
    Z_op_plus x (Z_op_plus y z) = Z_op_plus (Z_op_plus x y) z := by
  cases x <;> cases y <;> cases z <;> simp [Z_op_plus, Int.add_assoc]

theorem Z_op_min_none_r (x : Option Int) :
    Z_op_min x none = x := by
  cases x <;> rfl

theorem Z_op_min_le_l (x : Option Int) :
    Z_op_min none x = x := by
  cases x <;> rfl

theorem Z_op_le_none_r (x : Option Int) :
    Z_op_le x none := by
  cases x <;> simp [Z_op_le]

theorem Z_op_le_min_l (x y : Option Int) :
    Z_op_le x y -> Z_op_min x y = x := by
  cases x <;> cases y <;> simp [Z_op_le, Z_op_min]
  intro h
  exact Int.min_eq_left h

theorem Z_op_le_min_r (x y : Option Int) :
    Z_op_le y x -> Z_op_min x y = y := by
  cases x <;> cases y <;> simp [Z_op_le, Z_op_min]
  intro h
  exact Int.min_eq_right h

theorem Z_op_le_min_imply (x y z : Option Int) :
    Z_op_le x y -> Z_op_le x z -> Z_op_le x (Z_op_min y z) := by
  cases x <;> cases y <;> cases z <;> simp [Z_op_le, Z_op_min] <;>
    intro hxy hxz
  exact (Int.le_min).mpr ⟨hxy, hxz⟩

theorem Z_op_le_min_le_l (x y : Option Int) :
    Z_op_le (Z_op_min x y) x := by
  cases x <;> cases y <;> simp [Z_op_le, Z_op_min, Int.min_le_left]

theorem Z_op_le_min_le_r (x y : Option Int) :
    Z_op_le (Z_op_min x y) y := by
  cases x <;> cases y <;> simp [Z_op_le, Z_op_min, Int.min_le_right]

theorem Z_op_finite_min {A : Type} (f : A -> Option Int) (P : A -> Prop)
    (xs : List A) (x : A) :
    x ∈ xs -> P x -> (forall y, P y -> y ∈ xs) ->
    exists m, min_object_of_subset Z_op_le P f m := by
  classical
  revert P x
  induction xs with
  | nil =>
      intro P x hx _ _
      cases hx
  | cons a xs ih =>
      intro P x hx hp hsub
      by_cases hPa : P a
      · by_cases hTail : exists y, y ∈ xs /\ P y
        · rcases hTail with ⟨y, hyxs, hyP⟩
          let Ptail : A -> Prop := fun z => P z /\ z ∈ xs
          have hsubTail : forall z, Ptail z -> z ∈ xs := by
            intro z hz
            exact hz.2
          rcases ih Ptail y hyxs ⟨hyP, hyxs⟩ hsubTail with ⟨m, hmTail, hmMin⟩
          rcases Z_op_le_total (f a) (f m) with ham | hma
          · refine ⟨a, hPa, ?_⟩
            intro z hzP
            have hzmem := hsub z hzP
            rw [List.mem_cons] at hzmem
            rcases hzmem with hza | hzxs
            · subst z
              exact Z_op_le_refl (f a)
            · exact Z_op_le_trans (f a) (f m) (f z) ham (hmMin z ⟨hzP, hzxs⟩)
          · refine ⟨m, hmTail.1, ?_⟩
            intro z hzP
            have hzmem := hsub z hzP
            rw [List.mem_cons] at hzmem
            rcases hzmem with hza | hzxs
            · subst z
              exact hma
            · exact hmMin z ⟨hzP, hzxs⟩
        · refine ⟨a, hPa, ?_⟩
          intro z hzP
          have hzmem := hsub z hzP
          rw [List.mem_cons] at hzmem
          rcases hzmem with hza | hzxs
          · subst z
            exact Z_op_le_refl (f a)
          · exact False.elim (hTail ⟨z, hzxs, hzP⟩)
      · have hxxs : x ∈ xs := by
          have hxmem := hx
          rw [List.mem_cons] at hxmem
          rcases hxmem with hxa | hxs
          · subst x
            contradiction
          · exact hxs
        have hsub' : forall y, P y -> y ∈ xs := by
          intro y hy
          have hymem := hsub y hy
          rw [List.mem_cons] at hymem
          rcases hymem with hya | hyxs
          · subst y
            contradiction
          · exact hyxs
        exact ih P x hxxs hp hsub'

end MaxMinLib
