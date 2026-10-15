import AUXLib.MorphismsProp
import AUXLib.OrdersDecFact
import SetsClass.SetsClass

open AUXLib

namespace MaxMinLib

class TotalOrder {T : Type} (le : T -> T -> Prop) where
  le_refl : forall x, le x x
  le_trans : forall x y z, le x y -> le y z -> le x z
  le_antisym : forall x y, le x y -> le y x -> x = y
  le_total : forall x y, AUXLib.Sumbool (le x y) (le y x)

theorem le_total_cases {T : Type} (le : T -> T -> Prop) [TotalOrder le] :
    forall x y, le x y \/ le y x := by
  intro x y
  cases TotalOrder.le_total (le := le) x y with
  | left h => exact Or.inl h
  | right h => exact Or.inr h

def le_max {T : Type} (le : T -> T -> Prop) [TotalOrder le] (x y : T) : T :=
  match TotalOrder.le_total (le := le) x y with
  | AUXLib.Sumbool.left _ => y
  | AUXLib.Sumbool.right _ => x

def le_min {T : Type} (le : T -> T -> Prop) [TotalOrder le] (x y : T) : T :=
  match TotalOrder.le_total (le := le) x y with
  | AUXLib.Sumbool.left _ => x
  | AUXLib.Sumbool.right _ => y

theorem max_r {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    (x y : T) (h : le x y) : le_max le x y = y := by
  unfold le_max
  cases TotalOrder.le_total (le := le) x y with
  | left _ => rfl
  | right hyx =>
      exact TotalOrder.le_antisym (le := le) x y h hyx

theorem max_l {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    (x y : T) (h : le y x) : le_max le x y = x := by
  unfold le_max
  cases TotalOrder.le_total (le := le) x y with
  | left hxy =>
      exact (TotalOrder.le_antisym (le := le) x y hxy h).symm
  | right _ => rfl

theorem max_comm {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    (x y : T) : le_max le x y = le_max le y x := by
  cases TotalOrder.le_total (le := le) x y with
  | left hxy =>
      rw [max_r le x y hxy, max_l le y x hxy]
  | right hyx =>
      rw [max_l le x y hyx, max_r le y x hyx]

theorem max_assoc {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    (x y z : T) : le_max le x (le_max le y z) = le_max le (le_max le x y) z := by
  cases TotalOrder.le_total (le := le) y z with
  | left hyz =>
      rw [max_r le y z hyz]
      cases TotalOrder.le_total (le := le) x y with
      | left hxy =>
          have hxz : le x z := TotalOrder.le_trans (le := le) x y z hxy hyz
          rw [max_r le x z hxz, max_r le x y hxy, max_r le y z hyz]
      | right hyx =>
          rw [max_l le x y hyx]
  | right hzy =>
      rw [max_l le y z hzy]
      cases TotalOrder.le_total (le := le) x y with
      | left hxy =>
          rw [max_r le x y hxy, max_l le y z hzy]
      | right hyx =>
          have hzx : le z x := TotalOrder.le_trans (le := le) z y x hzy hyx
          rw [max_l le x y hyx, max_l le x z hzx]

theorem min_r {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    (x y : T) (h : le x y) : le_min le x y = x := by
  unfold le_min
  cases TotalOrder.le_total (le := le) x y with
  | left _ => rfl
  | right hyx =>
      exact (TotalOrder.le_antisym (le := le) x y h hyx).symm

theorem min_l {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    (x y : T) (h : le y x) : le_min le x y = y := by
  unfold le_min
  cases TotalOrder.le_total (le := le) x y with
  | left hxy =>
      exact TotalOrder.le_antisym (le := le) x y hxy h
  | right _ => rfl

private theorem pred_equiv_as_forall {A : Type} {P Q : A -> Prop}
    (h : Sets.equiv P Q) : forall a, P a <-> Q a := by
  change forall a, P a <-> Q a at h
  exact h

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

private theorem empty_false {A : Type} (a : A) :
    (Sets.empty : A -> Prop) a <-> False := by
  change False <-> False
  rfl

private theorem singleton_eq {A : Type} (a b : A) :
    Sets.singleton a b <-> a = b := by
  rfl

def max_object_of_subset {T : Type} (le : T -> T -> Prop)
    {A : Type} (X : A -> Prop) (f : A -> T) (a : A) : Prop :=
  X a /\ forall b, X b -> le (f b) (f a)

def max_value_of_subset {T : Type} (le : T -> T -> Prop)
    {A : Type} (X : A -> Prop) (f : A -> T) (n : T) : Prop :=
  exists a, max_object_of_subset le X f a /\ f a = n

def max_value_of_subset_with_default {T : Type} (le : T -> T -> Prop)
    {A : Type} (X : A -> Prop) (f : A -> T)
    (default : T) (n : T) : Prop :=
  (max_value_of_subset le X f n /\ le default n) \/
  ((forall a, X a -> le (f a) default) /\ default = n)

namespace MaxMinNotation

scoped syntax term " is-the-max-of " term " in-which " ident " satisfies " term : term
scoped syntax term " is-the-max-of " term " in-which " ident " satisfies " term
  " with-default " term : term
scoped syntax "the-max-of " term " in-which " ident " satisfies " term : term

scoped macro_rules
  | `($a:term is-the-max-of $e:term in-which $x:ident satisfies $P:term) => do
      let leId := Lean.mkIdent `le
      `(max_value_of_subset $leId (fun $x => $P) (fun $x => $e) $a)
  | `($a:term is-the-max-of $e:term in-which $x:ident satisfies $P:term
      with-default $default:term) => do
      let leId := Lean.mkIdent `le
      `(max_value_of_subset_with_default $leId (fun $x => $P) (fun $x => $e) $default $a)
  | `(the-max-of $e:term in-which $x:ident satisfies $P:term) => do
      let leId := Lean.mkIdent `le
      `(max_value_of_subset $leId (fun $x => $P) (fun $x => $e))

end MaxMinNotation

theorem max_object_sound {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (a : A) :
    max_object_of_subset le P f a ->
    forall b : A, P b -> le (f b) (f a) := by
  intro h b hb
  exact h.2 b hb

theorem max_object_legal {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (a : A) :
    max_object_of_subset le P f a -> P a := by
  intro h
  exact h.1

theorem max_default_ge_default {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n : T) (f : A -> T) (P : A -> Prop) (default : T) :
    max_value_of_subset_with_default le P f default n -> le default n := by
  intro h
  rcases h with ⟨_, hle⟩ | ⟨_, hEq⟩
  · exact hle
  · rw [← hEq]
    exact TotalOrder.le_refl (le := le) default

private theorem max_object_of_subset_congr_set {T : Type}
    (le : T -> T -> Prop) {A : Type}
    {X Y : A -> Prop} (hXY : Sets.equiv X Y) (f : A -> T) (a : A) :
    max_object_of_subset le X f a <-> max_object_of_subset le Y f a := by
  have hXY' := pred_equiv_as_forall hXY
  constructor
  · intro h
    exact ⟨(hXY' a).mp h.1, fun b hb => h.2 b ((hXY' b).mpr hb)⟩
  · intro h
    exact ⟨(hXY' a).mpr h.1, fun b hb => h.2 b ((hXY' b).mp hb)⟩

instance max_object_of_subset_congr {T : Type} (le : T -> T -> Prop)
    {A : Type} :
    Proper (Sets.equiv ==> Eq ==> Eq ==> Iff)
      (max_object_of_subset (T := T) (A := A) le) where
  proper := by
    intro X Y hXY f g hfg a b hab
    subst g
    subst b
    exact max_object_of_subset_congr_set le hXY f a

instance max_value_of_subset_congr {T : Type} (le : T -> T -> Prop)
    {A : Type} :
    Proper (Sets.equiv ==> Eq ==> Eq ==> Iff)
      (max_value_of_subset (T := T) (A := A) le) where
  proper := by
    intro X Y hXY f g hfg n m hnm
    subst g
    subst m
    constructor
    · rintro ⟨a, hobj, hEq⟩
      exact ⟨a, (max_object_of_subset_congr_set le hXY f a).mp hobj, hEq⟩
    · rintro ⟨a, hobj, hEq⟩
      exact ⟨a, (max_object_of_subset_congr_set le hXY f a).mpr hobj, hEq⟩

instance max_value_of_subset_with_default_congr {T : Type} (le : T -> T -> Prop)
    {A : Type} :
    Proper (Sets.equiv ==> Eq ==> Eq ==> Eq ==> Iff)
      (max_value_of_subset_with_default (T := T) (A := A) le) where
  proper := by
    intro X Y hXY f g hfg default default' hdef n m hnm
    subst g
    subst default'
    subst m
    have hXY' := pred_equiv_as_forall hXY
    constructor
    · intro h
      rcases h with ⟨hmax, hle⟩ | ⟨hall, hEq⟩
      · exact Or.inl ⟨((max_value_of_subset_congr le).proper X Y hXY f f rfl n n rfl).mp hmax, hle⟩
      · exact Or.inr ⟨(fun a ha => hall a ((hXY' a).mpr ha)), hEq⟩
    · intro h
      rcases h with ⟨hmax, hle⟩ | ⟨hall, hEq⟩
      · exact Or.inl ⟨((max_value_of_subset_congr le).proper X Y hXY f f rfl n n rfl).mpr hmax, hle⟩
      · exact Or.inr ⟨(fun a ha => hall a ((hXY' a).mp ha)), hEq⟩

theorem max_unique {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (n m : T) :
    max_value_of_subset le P f n ->
    max_value_of_subset le P f m ->
    n = m := by
  rintro ⟨a, ⟨⟨haP, haMax⟩, hfa⟩⟩ ⟨b, ⟨⟨hbP, hbMax⟩, hfb⟩⟩
  subst n
  subst m
  exact TotalOrder.le_antisym (le := le) (f a) (f b) (hbMax a haP) (haMax b hbP)

theorem max_default_unique {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (default n m : T) :
    max_value_of_subset_with_default le P f default n ->
    max_value_of_subset_with_default le P f default m ->
    n = m := by
  intro hn hm
  rcases hn with ⟨hnmax, hdefn⟩ | ⟨hnall, hneq⟩
  · rcases hm with ⟨hmmax, _⟩ | ⟨hmall, hmeq⟩
    · exact max_unique le f P n m hnmax hmmax
    · subst m
      rcases hnmax with ⟨a, ⟨⟨haP, _⟩, hfa⟩⟩
      subst n
      exact TotalOrder.le_antisym (le := le) (f a) default (hmall a haP) hdefn
  · rcases hm with ⟨hmmax, hdefm⟩ | ⟨_, hmeq⟩
    · subst n
      rcases hmmax with ⟨a, ⟨⟨haP, _⟩, hfa⟩⟩
      subst m
      exact (TotalOrder.le_antisym (le := le) (f a) default (hnall a haP) hdefm).symm
    · subst n
      exact hmeq

theorem max_le {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (n1 n2 : T) :
    max_value_of_subset le P1 f1 n1 ->
    max_value_of_subset le P2 f2 n2 ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f1 a1) (f2 a2)) ->
    le n1 n2 := by
  rintro ⟨a1, ⟨⟨ha1, _⟩, h1⟩⟩ ⟨a2, ⟨⟨_, ha2max⟩, h2⟩⟩ hrel
  subst n1
  subst n2
  rcases hrel a1 ha1 with ⟨a2', ha2', hle⟩
  exact TotalOrder.le_trans (le := le) (f1 a1) (f2 a2') (f2 a2) hle (ha2max a2' ha2')

theorem max_default_le {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop)
    (default n1 n2 : T) :
    max_value_of_subset_with_default le P1 f1 default n1 ->
    max_value_of_subset_with_default le P2 f2 default n2 ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f1 a1) (f2 a2)) ->
    le n1 n2 := by
  intro h1 h2 hrel
  rcases h1 with ⟨hmax1, hdef1⟩ | ⟨hall1, hEq1⟩
  · rcases h2 with ⟨hmax2, _⟩ | ⟨hall2, hEq2⟩
    · exact max_le le f1 f2 P1 P2 n1 n2 hmax1 hmax2 hrel
    · subst n2
      rcases hmax1 with ⟨a1, ⟨⟨ha1, _⟩, hfa1⟩⟩
      subst n1
      rcases hrel a1 ha1 with ⟨a2, ha2, hle⟩
      exact TotalOrder.le_trans (le := le) (f1 a1) (f2 a2) default hle (hall2 a2 ha2)
  · subst n1
    rcases h2 with ⟨_, hdef2⟩ | ⟨_, hEq2⟩
    · exact hdef2
    · subst n2
      exact TotalOrder.le_refl (le := le) default

theorem max_eq {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (n1 n2 : T) :
    max_value_of_subset le P1 f1 n1 ->
    max_value_of_subset le P2 f2 n2 ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f1 a1) (f2 a2)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f2 a2) (f1 a1)) ->
    n1 = n2 := by
  intro h1 h2 h12 h21
  exact TotalOrder.le_antisym (le := le) n1 n2
    (max_le le f1 f2 P1 P2 n1 n2 h1 h2 h12)
    (max_le le f2 f1 P2 P1 n2 n1 h2 h1 h21)

theorem max_default_eq {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (default n1 n2 : T) :
    max_value_of_subset_with_default le P1 f1 default n1 ->
    max_value_of_subset_with_default le P2 f2 default n2 ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f1 a1) (f2 a2)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f2 a2) (f1 a1)) ->
    n1 = n2 := by
  intro h1 h2 h12 h21
  exact TotalOrder.le_antisym (le := le) n1 n2
    (max_default_le le f1 f2 P1 P2 default n1 n2 h1 h2 h12)
    (max_default_le le f2 f1 P2 P1 default n2 n1 h2 h1 h21)

theorem max_eq_forward' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (n : T) :
    max_value_of_subset le P1 f1 n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f1 a1) (f2 a2)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f2 a2) (f1 a1)) ->
    max_value_of_subset le P2 f2 n := by
  rintro ⟨a, ⟨⟨ha, haMax⟩, hfa⟩⟩ h12 h21
  subst n
  rcases h12 a ha with ⟨a2, ha2, hle2⟩
  refine ⟨a2, ?_, ?_⟩
  · constructor
    · exact ha2
    · intro b hb
      rcases h21 b hb with ⟨a1, ha1, hb_le_a1⟩
      exact TotalOrder.le_trans (le := le) (f2 b) (f1 a1) (f2 a2) hb_le_a1
        (TotalOrder.le_trans (le := le) (f1 a1) (f1 a) (f2 a2) (haMax a1 ha1) hle2)
  · rcases h21 a2 ha2 with ⟨a1, ha1, ha2_le_a1⟩
    have hback : le (f2 a2) (f1 a) :=
      TotalOrder.le_trans (le := le) (f2 a2) (f1 a1) (f1 a) ha2_le_a1 (haMax a1 ha1)
    exact TotalOrder.le_antisym (le := le) (f2 a2) (f1 a) hback hle2

theorem max_eq_forward {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (n : T) :
    max_value_of_subset le P1 f1 n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f1 a1) (f2 a2)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f2 a2) (f1 a1)) ->
    max_value_of_subset le P2 f2 n :=
  max_eq_forward' le f1 f2 P1 P2 n

theorem max_default_eq_forward' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (default n : T) :
    max_value_of_subset_with_default le P1 f1 default n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f1 a1) (f2 a2)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f2 a2) (f1 a1)) ->
    max_value_of_subset_with_default le P2 f2 default n := by
  intro h h12 h21
  rcases h with ⟨hmax, hdef⟩ | ⟨hall, hEq⟩
  · exact Or.inl ⟨max_eq_forward' le f1 f2 P1 P2 n hmax h12 h21, hdef⟩
  · refine Or.inr ⟨?_, hEq⟩
    intro a2 ha2
    rcases h21 a2 ha2 with ⟨a1, ha1, hle⟩
    exact TotalOrder.le_trans (le := le) (f2 a2) (f1 a1) default hle (hall a1 ha1)

theorem max_default_eq_forward {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (default n : T) :
    max_value_of_subset_with_default le P1 f1 default n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f1 a1) (f2 a2)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f2 a2) (f1 a1)) ->
    max_value_of_subset_with_default le P2 f2 default n :=
  max_default_eq_forward' le f1 f2 P1 P2 default n

theorem max_mono_incr_bind' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (g : T -> T) (P : A -> Prop) (n : T) :
    max_value_of_subset le P f n ->
    (forall n1 n2, le n1 n2 -> le (g n1) (g n2)) ->
    max_value_of_subset le P (fun a => g (f a)) (g n) := by
  rintro ⟨a, ⟨⟨ha, haMax⟩, hfa⟩⟩ hg
  subst n
  exact ⟨a, ⟨⟨ha, fun b hb => hg (f b) (f a) (haMax b hb)⟩, rfl⟩⟩

theorem max_mono_incr_bind {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (h : T -> T) (f g : A -> T) (P : A -> Prop) (n m : T) :
    max_value_of_subset le P f n ->
    (forall a, g a = h (f a)) ->
    (forall n1 n2, le n1 n2 -> le (h n1) (h n2)) ->
    m = h n ->
    max_value_of_subset le P g m := by
  intro hmax hgdef hh hmeq
  subst m
  rcases max_mono_incr_bind' le f h P n hmax hh with ⟨a, ⟨⟨ha, haMax⟩, hha⟩⟩
  refine ⟨a, ⟨⟨ha, ?_⟩, ?_⟩⟩
  · intro b hb
    rw [hgdef b, hgdef a]
    exact haMax b hb
  · rw [hgdef a]
    exact hha

theorem max_object_union_left {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) (P Q : A -> Prop) (n : T) :
    max_object_of_subset le P f a ->
    (forall b, Q b -> le (f b) n) ->
    le n (f a) ->
    max_object_of_subset le (Sets.union P Q) f a := by
  intro hP hQ hn
  constructor
  · exact union_left hP.1
  · intro b hb
    rcases (union_mem_iff P Q b).mp hb with hbP | hbQ
    · exact hP.2 b hbP
    · exact TotalOrder.le_trans (le := le) (f b) n (f a) (hQ b hbQ) hn

theorem max_object_union1 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a b : A) (f : A -> T) (P Q : A -> Prop) :
    max_object_of_subset le P f a ->
    max_object_of_subset le Q f b ->
    le (f b) (f a) ->
    max_object_of_subset le (Sets.union P Q) f a := by
  intro hP hQ hba
  exact max_object_union_left le a f P Q (f b) hP (fun c hc => hQ.2 c hc) hba

theorem max_object_union_right {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) (P Q : A -> Prop) (n : T) :
    (forall b, P b -> le (f b) n) ->
    max_object_of_subset le Q f a ->
    le n (f a) ->
    max_object_of_subset le (Sets.union P Q) f a := by
  intro hP hQ hn
  constructor
  · exact union_right hQ.1
  · intro b hb
    rcases (union_mem_iff P Q b).mp hb with hbP | hbQ
    · exact TotalOrder.le_trans (le := le) (f b) n (f a) (hP b hbP) hn
    · exact hQ.2 b hbQ

theorem max_object_union2 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a b : A) (f : A -> T) (P Q : A -> Prop) :
    max_object_of_subset le P f a ->
    max_object_of_subset le Q f b ->
    le (f a) (f b) ->
    max_object_of_subset le (Sets.union P Q) f b := by
  intro hP hQ hab
  exact max_object_union_right le b f P Q (f a) (fun c hc => hP.2 c hc) hQ hab

theorem max_object_union {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a b : A) (f : A -> T) (P Q : A -> Prop) :
    max_object_of_subset le P f a ->
    max_object_of_subset le Q f b ->
    max_object_of_subset le (Sets.union P Q) f a \/
    max_object_of_subset le (Sets.union P Q) f b := by
  intro hP hQ
  cases TotalOrder.le_total (le := le) (f a) (f b) with
  | left hab => exact Or.inr (max_object_union2 le a b f P Q hP hQ hab)
  | right hba => exact Or.inl (max_object_union1 le a b f P Q hP hQ hba)

theorem max_union' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q : A -> Prop) :
    max_value_of_subset le P f n ->
    max_value_of_subset le Q f m ->
    max_value_of_subset le (Sets.union P Q) f (le_max le n m) := by
  rintro ⟨a, ⟨hPa, hfa⟩⟩ ⟨b, ⟨hQb, hfb⟩⟩
  subst n
  subst m
  cases TotalOrder.le_total (le := le) (f a) (f b) with
  | left hab =>
      rw [max_r le (f a) (f b) hab]
      exact ⟨b, ⟨max_object_union2 le a b f P Q hPa hQb hab, rfl⟩⟩
  | right hba =>
      rw [max_l le (f a) (f b) hba]
      exact ⟨a, ⟨max_object_union1 le a b f P Q hPa hQb hba, rfl⟩⟩

theorem max_union {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q R : A -> Prop) :
    max_value_of_subset le P f n ->
    max_value_of_subset le Q f m ->
    (forall a, P a \/ Q a <-> R a) ->
    max_value_of_subset le R f (le_max le n m) := by
  intro hP hQ hR
  apply max_eq_forward' le f f (Sets.union P Q) R (le_max le n m)
  · exact max_union' le n m f P Q hP hQ
  · intro a ha
    exact ⟨a, (hR a).mp ((union_mem_iff P Q a).mp ha), TotalOrder.le_refl (le := le) (f a)⟩
  · intro a ha
    exact ⟨a, (union_mem_iff P Q a).mpr ((hR a).mpr ha), TotalOrder.le_refl (le := le) (f a)⟩

theorem max_default_union' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q : A -> Prop) (default : T) :
    max_value_of_subset_with_default le P f default n ->
    max_value_of_subset_with_default le Q f default m ->
    max_value_of_subset_with_default le (Sets.union P Q) f default (le_max le n m) := by
  intro hP hQ
  rcases hP with ⟨hPmax, hdefn⟩ | ⟨hPall, hPEq⟩
  · rcases hQ with ⟨hQmax, hdefm⟩ | ⟨hQall, hQEq⟩
    · refine Or.inl ⟨max_union' le n m f P Q hPmax hQmax, ?_⟩
      cases TotalOrder.le_total (le := le) n m with
      | left hnm =>
          rw [max_r le n m hnm]
          exact hdefm
      | right hmn =>
          rw [max_l le n m hmn]
          exact hdefn
    · subst m
      have hmaxEq : le_max le n default = n := max_l le n default hdefn
      rw [hmaxEq]
      rcases hPmax with ⟨a, hobj, hEq⟩
      subst n
      refine Or.inl ⟨⟨a, ⟨?_, rfl⟩⟩, hdefn⟩
      exact max_object_union_left le a f P Q default hobj hQall hdefn
  · rcases hQ with ⟨hQmax, hdefm⟩ | ⟨hQall, hQEq⟩
    · subst n
      have hmaxEq : le_max le default m = m := max_r le default m hdefm
      rw [hmaxEq]
      rcases hQmax with ⟨a, hobj, hEq⟩
      subst m
      refine Or.inl ⟨⟨a, ⟨?_, rfl⟩⟩, hdefm⟩
      exact max_object_union_right le a f P Q default hPall hobj hdefm
    · subst n
      subst m
      rw [max_r le default default (TotalOrder.le_refl (le := le) default)]
      refine Or.inr ⟨?_, rfl⟩
      intro a ha
      rcases (union_mem_iff P Q a).mp ha with haP | haQ
      · exact hPall a haP
      · exact hQall a haQ

theorem max_default_union {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q R : A -> Prop) (default : T) :
    max_value_of_subset_with_default le P f default n ->
    max_value_of_subset_with_default le Q f default m ->
    (forall a, P a \/ Q a <-> R a) ->
    max_value_of_subset_with_default le R f default (le_max le n m) := by
  intro hP hQ hR
  apply max_default_eq_forward' le f f (Sets.union P Q) R default (le_max le n m)
  · exact max_default_union' le n m f P Q default hP hQ
  · intro a ha
    exact ⟨a, (hR a).mp ((union_mem_iff P Q a).mp ha), TotalOrder.le_refl (le := le) (f a)⟩
  · intro a ha
    exact ⟨a, (union_mem_iff P Q a).mpr ((hR a).mpr ha), TotalOrder.le_refl (le := le) (f a)⟩

theorem max_object_1 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) :
    max_object_of_subset le (Sets.singleton a) f a := by
  constructor
  · exact rfl
  · intro b hb
    have hab : a = b := (singleton_eq a b).mp hb
    subst b
    exact TotalOrder.le_refl (le := le) (f a)

theorem max_empty {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) :
    Sets.equiv (max_value_of_subset le (Sets.empty : A -> Prop) f)
      (Sets.empty : T -> Prop) := by
  apply pred_equiv_intro
  intro n
  constructor
  · rintro ⟨a, ⟨⟨ha, _⟩, _⟩⟩
    exact (empty_false a).mp ha
  · intro h
    exact False.elim ((empty_false n).mp h)

theorem max_1' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) :
    max_value_of_subset le (Sets.singleton a) f (f a) :=
  ⟨a, ⟨max_object_1 le a f, rfl⟩⟩

theorem max_1 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (P : A -> Prop) (f : A -> T) :
    (forall a0, P a0 <-> a = a0) ->
    max_value_of_subset le P f (f a) := by
  intro hP
  refine ⟨a, ⟨?_, rfl⟩⟩
  constructor
  · exact (hP a).mpr rfl
  · intro b hb
    have hab : a = b := (hP b).mp hb
    subst b
    exact TotalOrder.le_refl (le := le) (f a)

theorem max_singleton {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) :
    Sets.equiv (max_value_of_subset le (Sets.singleton a) f) (Sets.singleton (f a)) := by
  apply pred_equiv_intro
  intro n
  constructor
  · rintro ⟨b, ⟨⟨hb, _⟩, hfb⟩⟩
    have hab : a = b := (singleton_eq a b).mp hb
    subst b
    exact hfb
  · intro hn
    have hEq : f a = n := (singleton_eq (f a) n).mp hn
    rw [← hEq]
    exact max_1' le a f

theorem max_default_1 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) (default : T) :
    max_value_of_subset_with_default le (Sets.singleton a) f default
      (le_max le (f a) default) := by
  cases TotalOrder.le_total (le := le) (f a) default with
  | left h =>
      rw [max_r le (f a) default h]
      refine Or.inr ⟨?_, rfl⟩
      intro b hb
      have hab : a = b := (singleton_eq a b).mp hb
      subst b
      exact h
  | right h =>
      rw [max_l le (f a) default h]
      exact Or.inl ⟨max_1' le a f, h⟩

theorem max_union_1_right' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n : T) (a : A) (f : A -> T) (P : A -> Prop) :
    max_value_of_subset le P f n ->
    max_value_of_subset le (Sets.union P (Sets.singleton a)) f (le_max le n (f a)) := by
  intro h
  exact max_union' le n (f a) f P (Sets.singleton a) h (max_1' le a f)

theorem max_union_1_right {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (a : A) (f : A -> T) (P Q : A -> Prop) :
    max_value_of_subset le P f n ->
    m = f a ->
    (forall b, Q b <-> P b \/ a = b) ->
    max_value_of_subset le Q f (le_max le n (f a)) := by
  intro hmax hm hQ
  apply max_eq_forward' le f f (Sets.union P (Sets.singleton a)) Q (le_max le n (f a))
  · exact max_union_1_right' le n a f P hmax
  · intro b hb
    rcases (union_mem_iff P (Sets.singleton a) b).mp hb with hbP | hbS
    · exact ⟨b, (hQ b).mpr (Or.inl hbP), TotalOrder.le_refl (le := le) (f b)⟩
    · exact ⟨b, (hQ b).mpr (Or.inr ((singleton_eq a b).mp hbS)),
        TotalOrder.le_refl (le := le) (f b)⟩
  · intro b hb
    rcases (hQ b).mp hb with hbP | hbS
    · exact ⟨b, union_left hbP, TotalOrder.le_refl (le := le) (f b)⟩
    · exact ⟨b, union_right ((singleton_eq a b).mpr hbS),
        TotalOrder.le_refl (le := le) (f b)⟩

theorem max_default_union_1_right' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n : T) (a : A) (f : A -> T) (P : A -> Prop) (default : T) :
    max_value_of_subset_with_default le P f default n ->
    max_value_of_subset_with_default le (Sets.union P (Sets.singleton a)) f default
      (le_max le n (f a)) := by
  intro h
  have hdefn := max_default_ge_default le n f P default h
  have heq : le_max le n (f a) = le_max le n (le_max le (f a) default) := by
    cases TotalOrder.le_total (le := le) (f a) default with
    | left hfa =>
        have hfan : le (f a) n := TotalOrder.le_trans (le := le) (f a) default n hfa hdefn
        rw [max_r le (f a) default hfa, max_l le n default hdefn, max_l le n (f a) hfan]
    | right hdefa =>
        rw [max_l le (f a) default hdefa]
  rw [heq]
  exact max_default_union' le n (le_max le (f a) default) f P (Sets.singleton a) default
    h (max_default_1 le a f default)

theorem max_default_union_1_right {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (a : A) (f : A -> T) (P Q : A -> Prop) (default : T) :
    max_value_of_subset_with_default le P f default n ->
    m = f a ->
    (forall b, Q b <-> P b \/ a = b) ->
    max_value_of_subset_with_default le Q f default (le_max le n m) := by
  intro hmax hm hQ
  subst m
  apply max_default_eq_forward' le f f (Sets.union P (Sets.singleton a)) Q default (le_max le n (f a))
  · exact max_default_union_1_right' le n a f P default hmax
  · intro b hb
    rcases (union_mem_iff P (Sets.singleton a) b).mp hb with hbP | hbS
    · exact ⟨b, (hQ b).mpr (Or.inl hbP), TotalOrder.le_refl (le := le) (f b)⟩
    · exact ⟨b, (hQ b).mpr (Or.inr ((singleton_eq a b).mp hbS)),
        TotalOrder.le_refl (le := le) (f b)⟩
  · intro b hb
    rcases (hQ b).mp hb with hbP | hbS
    · exact ⟨b, union_left hbP, TotalOrder.le_refl (le := le) (f b)⟩
    · exact ⟨b, union_right ((singleton_eq a b).mpr hbS),
        TotalOrder.le_refl (le := le) (f b)⟩

theorem max_default_default_inv {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n : T) (f : A -> T) (P : A -> Prop) (default : T) :
    max_value_of_subset_with_default le P f default n ->
    Sets.equiv P (Sets.empty : A -> Prop) ->
    n = default := by
  intro h hEmpty
  have hEmpty' := pred_equiv_as_forall hEmpty
  rcases h with ⟨hmax, _⟩ | ⟨_, hEq⟩
  · rcases hmax with ⟨a, ⟨⟨ha, _⟩, _⟩⟩
    exact False.elim ((hEmpty' a).mp ha)
  · exact hEq.symm

theorem max_default_default' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (default : T) :
    Sets.equiv P (Sets.empty : A -> Prop) ->
    max_value_of_subset_with_default le P f default default := by
  intro hEmpty
  have hEmpty' := pred_equiv_as_forall hEmpty
  refine Or.inr ⟨?_, rfl⟩
  intro a ha
  exact False.elim ((hEmpty' a).mp ha)

theorem max_default_default {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (default : T) :
    (forall a, ¬ P a) ->
    max_value_of_subset_with_default le P f default default := by
  intro h
  apply max_default_default' le f P default
  apply pred_equiv_intro
  intro a
  constructor
  · intro ha
    exact False.elim (h a ha)
  · intro hf
    exact False.elim hf

def min_object_of_subset {T : Type} (le : T -> T -> Prop)
    {A : Type} (X : A -> Prop) (f : A -> T) (a : A) : Prop :=
  X a /\ forall b, X b -> le (f a) (f b)

def min_value_of_subset {T : Type} (le : T -> T -> Prop)
    {A : Type} (X : A -> Prop) (f : A -> T) (n : T) : Prop :=
  exists a, min_object_of_subset le X f a /\ f a = n

def min_value_of_subset_with_default {T : Type} (le : T -> T -> Prop)
    {A : Type} (X : A -> Prop) (f : A -> T)
    (default : T) (n : T) : Prop :=
  (min_value_of_subset le X f n /\ le n default) \/
  ((forall a, X a -> le default (f a)) /\ n = default)

namespace MaxMinNotation

scoped syntax term " is-the-min-of " term " in-which " ident " satisfies " term : term
scoped syntax term " is-the-min-of " term " in-which " ident " satisfies " term
  " with-default " term : term
scoped syntax "the-min-of " term " in-which " ident " satisfies " term : term

scoped macro_rules
  | `($a:term is-the-min-of $e:term in-which $x:ident satisfies $P:term) => do
      let leId := Lean.mkIdent `le
      `(min_value_of_subset $leId (fun $x => $P) (fun $x => $e) $a)
  | `($a:term is-the-min-of $e:term in-which $x:ident satisfies $P:term
      with-default $default:term) => do
      let leId := Lean.mkIdent `le
      `(min_value_of_subset_with_default $leId (fun $x => $P) (fun $x => $e) $default $a)
  | `(the-min-of $e:term in-which $x:ident satisfies $P:term) => do
      let leId := Lean.mkIdent `le
      `(min_value_of_subset $leId (fun $x => $P) (fun $x => $e))

end MaxMinNotation

theorem min_object_sound {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (a : A) :
    min_object_of_subset le P f a ->
    forall b : A, P b -> le (f a) (f b) := by
  intro h b hb
  exact h.2 b hb

theorem min_object_legal {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (a : A) :
    min_object_of_subset le P f a -> P a := by
  intro h
  exact h.1

theorem min_default_le_default {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n : T) (f : A -> T) (P : A -> Prop) (default : T) :
    min_value_of_subset_with_default le P f default n -> le n default := by
  intro h
  rcases h with ⟨_, hle⟩ | ⟨_, hEq⟩
  · exact hle
  · rw [hEq]
    exact TotalOrder.le_refl (le := le) default

private theorem min_object_of_subset_congr_set {T : Type}
    (le : T -> T -> Prop) {A : Type}
    {X Y : A -> Prop} (hXY : Sets.equiv X Y) (f : A -> T) (a : A) :
    min_object_of_subset le X f a <-> min_object_of_subset le Y f a := by
  have hXY' := pred_equiv_as_forall hXY
  constructor
  · intro h
    exact ⟨(hXY' a).mp h.1, fun b hb => h.2 b ((hXY' b).mpr hb)⟩
  · intro h
    exact ⟨(hXY' a).mpr h.1, fun b hb => h.2 b ((hXY' b).mp hb)⟩

instance min_object_of_subset_congr {T : Type} (le : T -> T -> Prop)
    {A : Type} :
    Proper (Sets.equiv ==> Eq ==> Eq ==> Iff)
      (min_object_of_subset (T := T) (A := A) le) where
  proper := by
    intro X Y hXY f g hfg a b hab
    subst g
    subst b
    exact min_object_of_subset_congr_set le hXY f a

instance min_value_of_subset_congr {T : Type} (le : T -> T -> Prop)
    {A : Type} :
    Proper (Sets.equiv ==> Eq ==> Eq ==> Iff)
      (min_value_of_subset (T := T) (A := A) le) where
  proper := by
    intro X Y hXY f g hfg n m hnm
    subst g
    subst m
    constructor
    · rintro ⟨a, hobj, hEq⟩
      exact ⟨a, (min_object_of_subset_congr_set le hXY f a).mp hobj, hEq⟩
    · rintro ⟨a, hobj, hEq⟩
      exact ⟨a, (min_object_of_subset_congr_set le hXY f a).mpr hobj, hEq⟩

instance min_value_of_subset_with_default_congr {T : Type} (le : T -> T -> Prop)
    {A : Type} :
    Proper (Sets.equiv ==> Eq ==> Eq ==> Eq ==> Iff)
      (min_value_of_subset_with_default (T := T) (A := A) le) where
  proper := by
    intro X Y hXY f g hfg default default' hdef n m hnm
    subst g
    subst default'
    subst m
    have hXY' := pred_equiv_as_forall hXY
    constructor
    · intro h
      rcases h with ⟨hmin, hle⟩ | ⟨hall, hEq⟩
      · exact Or.inl ⟨((min_value_of_subset_congr le).proper X Y hXY f f rfl n n rfl).mp hmin, hle⟩
      · exact Or.inr ⟨(fun a ha => hall a ((hXY' a).mpr ha)), hEq⟩
    · intro h
      rcases h with ⟨hmin, hle⟩ | ⟨hall, hEq⟩
      · exact Or.inl ⟨((min_value_of_subset_congr le).proper X Y hXY f f rfl n n rfl).mpr hmin, hle⟩
      · exact Or.inr ⟨(fun a ha => hall a ((hXY' a).mp ha)), hEq⟩

theorem min_unique {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (n m : T) :
    min_value_of_subset le P f n ->
    min_value_of_subset le P f m ->
    n = m := by
  rintro ⟨a, ⟨⟨haP, haMin⟩, hfa⟩⟩ ⟨b, ⟨⟨hbP, hbMin⟩, hfb⟩⟩
  subst n
  subst m
  exact TotalOrder.le_antisym (le := le) (f a) (f b) (haMin b hbP) (hbMin a haP)

theorem min_default_unique {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (default n m : T) :
    min_value_of_subset_with_default le P f default n ->
    min_value_of_subset_with_default le P f default m ->
    n = m := by
  intro hn hm
  rcases hn with ⟨hnmin, hnle⟩ | ⟨hnall, hneq⟩
  · rcases hm with ⟨hmmin, _⟩ | ⟨hmall, hmeq⟩
    · exact min_unique le f P n m hnmin hmmin
    · subst m
      rcases hnmin with ⟨a, ⟨⟨haP, _⟩, hfa⟩⟩
      subst n
      exact TotalOrder.le_antisym (le := le) (f a) default hnle (hmall a haP)
  · rcases hm with ⟨hmmin, hmle⟩ | ⟨_, hmeq⟩
    · subst n
      rcases hmmin with ⟨a, ⟨⟨haP, _⟩, hfa⟩⟩
      subst m
      exact (TotalOrder.le_antisym (le := le) (f a) default hmle (hnall a haP)).symm
    · subst n
      exact hmeq.symm

theorem min_le {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (n1 n2 : T) :
    min_value_of_subset le P1 f1 n1 ->
    min_value_of_subset le P2 f2 n2 ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f2 a2) (f1 a1)) ->
    le n2 n1 := by
  rintro ⟨a1, ⟨⟨ha1, _⟩, h1⟩⟩ ⟨a2, ⟨⟨_, ha2min⟩, h2⟩⟩ hrel
  subst n1
  subst n2
  rcases hrel a1 ha1 with ⟨a2', ha2', hle⟩
  exact TotalOrder.le_trans (le := le) (f2 a2) (f2 a2') (f1 a1) (ha2min a2' ha2') hle

theorem min_default_le {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop)
    (default n1 n2 : T) :
    min_value_of_subset_with_default le P1 f1 default n1 ->
    min_value_of_subset_with_default le P2 f2 default n2 ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f2 a2) (f1 a1)) ->
    le n2 n1 := by
  intro h1 h2 hrel
  rcases h1 with ⟨hmin1, hn1def⟩ | ⟨hall1, hEq1⟩
  · rcases h2 with ⟨hmin2, _⟩ | ⟨hall2, hEq2⟩
    · exact min_le le f1 f2 P1 P2 n1 n2 hmin1 hmin2 hrel
    · subst n2
      rcases hmin1 with ⟨a1, ⟨⟨ha1, _⟩, hfa1⟩⟩
      subst n1
      rcases hrel a1 ha1 with ⟨a2, ha2, hle⟩
      exact TotalOrder.le_trans (le := le) default (f2 a2) (f1 a1) (hall2 a2 ha2) hle
  · subst n1
    rcases h2 with ⟨_, hn2def⟩ | ⟨_, hEq2⟩
    · exact hn2def
    · subst n2
      exact TotalOrder.le_refl (le := le) default

theorem min_eq {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (n1 n2 : T) :
    min_value_of_subset le P1 f1 n1 ->
    min_value_of_subset le P2 f2 n2 ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f2 a2) (f1 a1)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f1 a1) (f2 a2)) ->
    n1 = n2 := by
  intro h1 h2 h12 h21
  exact TotalOrder.le_antisym (le := le) n1 n2
    (min_le le f2 f1 P2 P1 n2 n1 h2 h1 h21)
    (min_le le f1 f2 P1 P2 n1 n2 h1 h2 h12)

theorem min_default_eq {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (default n1 n2 : T) :
    min_value_of_subset_with_default le P1 f1 default n1 ->
    min_value_of_subset_with_default le P2 f2 default n2 ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f2 a2) (f1 a1)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f1 a1) (f2 a2)) ->
    n1 = n2 := by
  intro h1 h2 h12 h21
  exact TotalOrder.le_antisym (le := le) n1 n2
    (min_default_le le f2 f1 P2 P1 default n2 n1 h2 h1 h21)
    (min_default_le le f1 f2 P1 P2 default n1 n2 h1 h2 h12)

theorem min_eq_forward' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (n : T) :
    min_value_of_subset le P1 f1 n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f2 a2) (f1 a1)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f1 a1) (f2 a2)) ->
    min_value_of_subset le P2 f2 n := by
  rintro ⟨a, ⟨⟨ha, haMin⟩, hfa⟩⟩ h12 h21
  subst n
  rcases h12 a ha with ⟨a2, ha2, ha2_le_a⟩
  refine ⟨a2, ?_, ?_⟩
  · constructor
    · exact ha2
    · intro b hb
      rcases h21 b hb with ⟨a1, ha1, ha1_le_b⟩
      exact TotalOrder.le_trans (le := le) (f2 a2) (f1 a) (f2 b) ha2_le_a
        (TotalOrder.le_trans (le := le) (f1 a) (f1 a1) (f2 b) (haMin a1 ha1) ha1_le_b)
  · rcases h21 a2 ha2 with ⟨a1, ha1, ha1_le_a2⟩
    exact TotalOrder.le_antisym (le := le) (f2 a2) (f1 a) ha2_le_a
      (TotalOrder.le_trans (le := le) (f1 a) (f1 a1) (f2 a2) (haMin a1 ha1) ha1_le_a2)

theorem min_eq_forward {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (n : T) :
    min_value_of_subset le P1 f1 n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f2 a2) (f1 a1)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f1 a1) (f2 a2)) ->
    min_value_of_subset le P2 f2 n :=
  min_eq_forward' le f1 f2 P1 P2 n

theorem min_default_eq_forward' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (default n : T) :
    min_value_of_subset_with_default le P1 f1 default n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f2 a2) (f1 a1)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f1 a1) (f2 a2)) ->
    min_value_of_subset_with_default le P2 f2 default n := by
  intro h h12 h21
  rcases h with ⟨hmin, hnle⟩ | ⟨hall, hEq⟩
  · exact Or.inl ⟨min_eq_forward' le f1 f2 P1 P2 n hmin h12 h21, hnle⟩
  · refine Or.inr ⟨?_, hEq⟩
    intro a2 ha2
    rcases h21 a2 ha2 with ⟨a1, ha1, hle⟩
    exact TotalOrder.le_trans (le := le) default (f1 a1) (f2 a2) (hall a1 ha1) hle

theorem min_default_eq_forward {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f1 f2 : A -> T) (P1 P2 : A -> Prop) (default n : T) :
    min_value_of_subset_with_default le P1 f1 default n ->
    (forall a1, P1 a1 -> exists a2, P2 a2 /\ le (f2 a2) (f1 a1)) ->
    (forall a2, P2 a2 -> exists a1, P1 a1 /\ le (f1 a1) (f2 a2)) ->
    min_value_of_subset_with_default le P2 f2 default n :=
  min_default_eq_forward' le f1 f2 P1 P2 default n

theorem min_mono_incr_bind' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (g : T -> T) (P : A -> Prop) (n : T) :
    min_value_of_subset le P f n ->
    (forall n1 n2, le n1 n2 -> le (g n1) (g n2)) ->
    min_value_of_subset le P (fun a => g (f a)) (g n) := by
  rintro ⟨a, ⟨⟨ha, haMin⟩, hfa⟩⟩ hg
  subst n
  exact ⟨a, ⟨⟨ha, fun b hb => hg (f a) (f b) (haMin b hb)⟩, rfl⟩⟩

theorem min_mono_incr_bind {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (h : T -> T) (f g : A -> T) (P : A -> Prop) (n m : T) :
    min_value_of_subset le P f n ->
    (forall a, g a = h (f a)) ->
    (forall n1 n2, le n1 n2 -> le (h n1) (h n2)) ->
    m = h n ->
    min_value_of_subset le P g m := by
  intro hmin hgdef hh hmeq
  subst m
  rcases min_mono_incr_bind' le f h P n hmin hh with ⟨a, ⟨⟨ha, haMin⟩, hha⟩⟩
  refine ⟨a, ⟨⟨ha, ?_⟩, ?_⟩⟩
  · intro b hb
    rw [hgdef b, hgdef a]
    exact haMin b hb
  · rw [hgdef a]
    exact hha

theorem min_object_union_left {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) (P Q : A -> Prop) (n : T) :
    min_object_of_subset le P f a ->
    (forall b, Q b -> le n (f b)) ->
    le (f a) n ->
    min_object_of_subset le (Sets.union P Q) f a := by
  intro hP hQ hn
  constructor
  · exact union_left hP.1
  · intro b hb
    rcases (union_mem_iff P Q b).mp hb with hbP | hbQ
    · exact hP.2 b hbP
    · exact TotalOrder.le_trans (le := le) (f a) n (f b) hn (hQ b hbQ)

theorem min_object_union1 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a b : A) (f : A -> T) (P Q : A -> Prop) :
    min_object_of_subset le P f a ->
    min_object_of_subset le Q f b ->
    le (f a) (f b) ->
    min_object_of_subset le (Sets.union P Q) f a := by
  intro hP hQ hab
  exact min_object_union_left le a f P Q (f b) hP (fun c hc => hQ.2 c hc) hab

theorem min_object_union_right {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) (P Q : A -> Prop) (n : T) :
    (forall b, P b -> le n (f b)) ->
    min_object_of_subset le Q f a ->
    le (f a) n ->
    min_object_of_subset le (Sets.union P Q) f a := by
  intro hP hQ hn
  constructor
  · exact union_right hQ.1
  · intro b hb
    rcases (union_mem_iff P Q b).mp hb with hbP | hbQ
    · exact TotalOrder.le_trans (le := le) (f a) n (f b) hn (hP b hbP)
    · exact hQ.2 b hbQ

theorem min_object_union2 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a b : A) (f : A -> T) (P Q : A -> Prop) :
    min_object_of_subset le P f a ->
    min_object_of_subset le Q f b ->
    le (f b) (f a) ->
    min_object_of_subset le (Sets.union P Q) f b := by
  intro hP hQ hba
  exact min_object_union_right le b f P Q (f a) (fun c hc => hP.2 c hc) hQ hba

theorem min_object_union {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a b : A) (f : A -> T) (P Q : A -> Prop) :
    min_object_of_subset le P f a ->
    min_object_of_subset le Q f b ->
    min_object_of_subset le (Sets.union P Q) f a \/
    min_object_of_subset le (Sets.union P Q) f b := by
  intro hP hQ
  cases le_total_cases le (f a) (f b) with
  | inl hab => exact Or.inl (min_object_union1 le a b f P Q hP hQ hab)
  | inr hba => exact Or.inr (min_object_union2 le a b f P Q hP hQ hba)

theorem min_union' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q : A -> Prop) :
    min_value_of_subset le P f n ->
    min_value_of_subset le Q f m ->
    min_value_of_subset le (Sets.union P Q) f (le_min le n m) := by
  rintro ⟨a, ⟨hPa, hfa⟩⟩ ⟨b, ⟨hQb, hfb⟩⟩
  subst n
  subst m
  cases TotalOrder.le_total (le := le) (f a) (f b) with
  | left hab =>
      rw [min_r le (f a) (f b) hab]
      exact ⟨a, ⟨min_object_union1 le a b f P Q hPa hQb hab, rfl⟩⟩
  | right hba =>
      rw [min_l le (f a) (f b) hba]
      exact ⟨b, ⟨min_object_union2 le a b f P Q hPa hQb hba, rfl⟩⟩

theorem min_union {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q R : A -> Prop) :
    min_value_of_subset le P f n ->
    min_value_of_subset le Q f m ->
    (forall a, P a \/ Q a <-> R a) ->
    min_value_of_subset le R f (le_min le n m) := by
  intro hP hQ hR
  apply min_eq_forward' le f f (Sets.union P Q) R (le_min le n m)
  · exact min_union' le n m f P Q hP hQ
  · intro a ha
    exact ⟨a, (hR a).mp ((union_mem_iff P Q a).mp ha), TotalOrder.le_refl (le := le) (f a)⟩
  · intro a ha
    exact ⟨a, (union_mem_iff P Q a).mpr ((hR a).mpr ha), TotalOrder.le_refl (le := le) (f a)⟩

theorem min_default_union' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q : A -> Prop) (default : T) :
    min_value_of_subset_with_default le P f default n ->
    min_value_of_subset_with_default le Q f default m ->
    min_value_of_subset_with_default le (Sets.union P Q) f default (le_min le n m) := by
  intro hP hQ
  rcases hP with ⟨hPmin, hnledef⟩ | ⟨hPall, hPEq⟩
  · rcases hQ with ⟨hQmin, hmledef⟩ | ⟨hQall, hQEq⟩
    · refine Or.inl ⟨min_union' le n m f P Q hPmin hQmin, ?_⟩
      cases TotalOrder.le_total (le := le) n m with
      | left hnm =>
          rw [min_r le n m hnm]
          exact hnledef
      | right hmn =>
          rw [min_l le n m hmn]
          exact hmledef
    · subst m
      have hminEq : le_min le n default = n := min_r le n default hnledef
      rw [hminEq]
      rcases hPmin with ⟨a, hobj, hEq⟩
      subst n
      refine Or.inl ⟨⟨a, ⟨?_, rfl⟩⟩, hnledef⟩
      exact min_object_union_left le a f P Q default hobj hQall hnledef
  · rcases hQ with ⟨hQmin, hmledef⟩ | ⟨hQall, hQEq⟩
    · subst n
      have hminEq : le_min le default m = m := min_l le default m hmledef
      rw [hminEq]
      rcases hQmin with ⟨a, hobj, hEq⟩
      subst m
      refine Or.inl ⟨⟨a, ⟨?_, rfl⟩⟩, hmledef⟩
      exact min_object_union_right le a f P Q default hPall hobj hmledef
    · subst n
      subst m
      rw [min_r le default default (TotalOrder.le_refl (le := le) default)]
      refine Or.inr ⟨?_, rfl⟩
      intro a ha
      rcases (union_mem_iff P Q a).mp ha with haP | haQ
      · exact hPall a haP
      · exact hQall a haQ

theorem min_default_union {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q R : A -> Prop) (default : T) :
    min_value_of_subset_with_default le P f default n ->
    min_value_of_subset_with_default le Q f default m ->
    (forall a, P a \/ Q a <-> R a) ->
    min_value_of_subset_with_default le R f default (le_min le n m) := by
  intro hP hQ hR
  apply min_default_eq_forward' le f f (Sets.union P Q) R default (le_min le n m)
  · exact min_default_union' le n m f P Q default hP hQ
  · intro a ha
    exact ⟨a, (hR a).mp ((union_mem_iff P Q a).mp ha), TotalOrder.le_refl (le := le) (f a)⟩
  · intro a ha
    exact ⟨a, (union_mem_iff P Q a).mpr ((hR a).mpr ha), TotalOrder.le_refl (le := le) (f a)⟩

theorem min_object_1 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) :
    min_object_of_subset le (Sets.singleton a) f a := by
  constructor
  · exact rfl
  · intro b hb
    have hab : a = b := (singleton_eq a b).mp hb
    subst b
    exact TotalOrder.le_refl (le := le) (f a)

theorem min_empty {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) :
    Sets.equiv (min_value_of_subset le (Sets.empty : A -> Prop) f)
      (Sets.empty : T -> Prop) := by
  apply pred_equiv_intro
  intro n
  constructor
  · rintro ⟨a, ⟨⟨ha, _⟩, _⟩⟩
    exact (empty_false a).mp ha
  · intro h
    exact False.elim ((empty_false n).mp h)

theorem min_1' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) :
    min_value_of_subset le (Sets.singleton a) f (f a) :=
  ⟨a, ⟨min_object_1 le a f, rfl⟩⟩

theorem min_1 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (P : A -> Prop) (f : A -> T) :
    (forall a0, P a0 <-> a = a0) ->
    min_value_of_subset le P f (f a) := by
  intro hP
  refine ⟨a, ⟨?_, rfl⟩⟩
  constructor
  · exact (hP a).mpr rfl
  · intro b hb
    have hab : a = b := (hP b).mp hb
    subst b
    exact TotalOrder.le_refl (le := le) (f a)

theorem min_singleton {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) :
    Sets.equiv (min_value_of_subset le (Sets.singleton a) f) (Sets.singleton (f a)) := by
  apply pred_equiv_intro
  intro n
  constructor
  · rintro ⟨b, ⟨⟨hb, _⟩, hfb⟩⟩
    have hab : a = b := (singleton_eq a b).mp hb
    subst b
    exact hfb
  · intro hn
    have hEq : f a = n := (singleton_eq (f a) n).mp hn
    rw [← hEq]
    exact min_1' le a f

theorem min_default_1 {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (a : A) (f : A -> T) (default : T) :
    min_value_of_subset_with_default le (Sets.singleton a) f default
      (le_min le (f a) default) := by
  cases TotalOrder.le_total (le := le) (f a) default with
  | left h =>
      rw [min_r le (f a) default h]
      exact Or.inl ⟨min_1' le a f, h⟩
  | right h =>
      rw [min_l le (f a) default h]
      refine Or.inr ⟨?_, rfl⟩
      intro b hb
      have hab : a = b := (singleton_eq a b).mp hb
      subst b
      exact h

theorem min_union_1_right' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n : T) (a : A) (f : A -> T) (P : A -> Prop) :
    min_value_of_subset le P f n ->
    min_value_of_subset le (Sets.union P (Sets.singleton a)) f (le_min le n (f a)) := by
  intro h
  exact min_union' le n (f a) f P (Sets.singleton a) h (min_1' le a f)

theorem min_union_1_right {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (a : A) (f : A -> T) (P Q : A -> Prop) :
    min_value_of_subset le P f n ->
    m = f a ->
    (forall b, Q b <-> P b \/ a = b) ->
    min_value_of_subset le Q f (le_min le n (f a)) := by
  intro hmin hm hQ
  apply min_eq_forward' le f f (Sets.union P (Sets.singleton a)) Q (le_min le n (f a))
  · exact min_union_1_right' le n a f P hmin
  · intro b hb
    rcases (union_mem_iff P (Sets.singleton a) b).mp hb with hbP | hbS
    · exact ⟨b, (hQ b).mpr (Or.inl hbP), TotalOrder.le_refl (le := le) (f b)⟩
    · exact ⟨b, (hQ b).mpr (Or.inr ((singleton_eq a b).mp hbS)),
        TotalOrder.le_refl (le := le) (f b)⟩
  · intro b hb
    rcases (hQ b).mp hb with hbP | hbS
    · exact ⟨b, union_left hbP, TotalOrder.le_refl (le := le) (f b)⟩
    · exact ⟨b, union_right ((singleton_eq a b).mpr hbS),
        TotalOrder.le_refl (le := le) (f b)⟩

theorem min_default_union_1_right' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n : T) (a : A) (f : A -> T) (P : A -> Prop) (default : T) :
    min_value_of_subset_with_default le P f default n ->
    min_value_of_subset_with_default le (Sets.union P (Sets.singleton a)) f default
      (le_min le n (f a)) := by
  intro h
  have hnledef := min_default_le_default le n f P default h
  have heq : le_min le n (f a) = le_min le n (le_min le (f a) default) := by
    cases TotalOrder.le_total (le := le) (f a) default with
    | left hfdef =>
        rw [min_r le (f a) default hfdef]
    | right hdefa =>
        have hnfa : le n (f a) := TotalOrder.le_trans (le := le) n default (f a) hnledef hdefa
        rw [min_l le (f a) default hdefa, min_r le n default hnledef, min_r le n (f a) hnfa]
  rw [heq]
  exact min_default_union' le n (le_min le (f a) default) f P (Sets.singleton a) default
    h (min_default_1 le a f default)

theorem min_default_union_1_right {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (a : A) (f : A -> T) (P Q : A -> Prop) (default : T) :
    min_value_of_subset_with_default le P f default n ->
    m = f a ->
    (forall b, Q b <-> P b \/ a = b) ->
    min_value_of_subset_with_default le Q f default (le_min le n m) := by
  intro hmin hm hQ
  subst m
  apply min_default_eq_forward' le f f (Sets.union P (Sets.singleton a)) Q default (le_min le n (f a))
  · exact min_default_union_1_right' le n a f P default hmin
  · intro b hb
    rcases (union_mem_iff P (Sets.singleton a) b).mp hb with hbP | hbS
    · exact ⟨b, (hQ b).mpr (Or.inl hbP), TotalOrder.le_refl (le := le) (f b)⟩
    · exact ⟨b, (hQ b).mpr (Or.inr ((singleton_eq a b).mp hbS)),
        TotalOrder.le_refl (le := le) (f b)⟩
  · intro b hb
    rcases (hQ b).mp hb with hbP | hbS
    · exact ⟨b, union_left hbP, TotalOrder.le_refl (le := le) (f b)⟩
    · exact ⟨b, union_right ((singleton_eq a b).mpr hbS),
        TotalOrder.le_refl (le := le) (f b)⟩

theorem min_default_default_inv {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n : T) (f : A -> T) (P : A -> Prop) (default : T) :
    min_value_of_subset_with_default le P f default n ->
    Sets.equiv P (Sets.empty : A -> Prop) ->
    n = default := by
  intro h hEmpty
  have hEmpty' := pred_equiv_as_forall hEmpty
  rcases h with ⟨hmin, _⟩ | ⟨_, hEq⟩
  · rcases hmin with ⟨a, ⟨⟨ha, _⟩, _⟩⟩
    exact False.elim ((hEmpty' a).mp ha)
  · exact hEq

theorem min_default_default' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (default : T) :
    Sets.equiv P (Sets.empty : A -> Prop) ->
    min_value_of_subset_with_default le P f default default := by
  intro hEmpty
  have hEmpty' := pred_equiv_as_forall hEmpty
  refine Or.inr ⟨?_, rfl⟩
  intro a ha
  exact False.elim ((hEmpty' a).mp ha)

theorem min_default_default {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (P : A -> Prop) (default : T) :
    (forall a, ¬ P a) ->
    min_value_of_subset_with_default le P f default default := by
  intro h
  apply min_default_default' le f P default
  apply pred_equiv_intro
  intro a
  constructor
  · intro ha
    exact False.elim (h a ha)
  · intro hf
    exact False.elim hf

theorem max_mono_decr_bind' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (g : T -> T) (P : A -> Prop) (n : T) :
    max_value_of_subset le P f n ->
    (forall n1 n2, le n1 n2 -> le (g n2) (g n1)) ->
    min_value_of_subset le P (fun a => g (f a)) (g n) := by
  rintro ⟨a, ⟨⟨ha, haMax⟩, hfa⟩⟩ hg
  subst n
  exact ⟨a, ⟨⟨ha, fun b hb => hg (f b) (f a) (haMax b hb)⟩, rfl⟩⟩

theorem max_mono_decr_bind {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (h : T -> T) (f g : A -> T) (P : A -> Prop) (n m : T) :
    max_value_of_subset le P f n ->
    (forall a, g a = h (f a)) ->
    (forall n1 n2, le n1 n2 -> le (h n2) (h n1)) ->
    m = h n ->
    min_value_of_subset le P g m := by
  intro hmax hgdef hh hmeq
  subst m
  rcases max_mono_decr_bind' le f h P n hmax hh with ⟨a, ⟨⟨ha, haMin⟩, hha⟩⟩
  refine ⟨a, ⟨⟨ha, ?_⟩, ?_⟩⟩
  · intro b hb
    rw [hgdef b, hgdef a]
    exact haMin b hb
  · rw [hgdef a]
    exact hha

theorem min_mono_decr_bind' {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (f : A -> T) (g : T -> T) (P : A -> Prop) (n : T) :
    min_value_of_subset le P f n ->
    (forall n1 n2, le n1 n2 -> le (g n2) (g n1)) ->
    max_value_of_subset le P (fun a => g (f a)) (g n) := by
  rintro ⟨a, ⟨⟨ha, haMin⟩, hfa⟩⟩ hg
  subst n
  exact ⟨a, ⟨⟨ha, fun b hb => hg (f a) (f b) (haMin b hb)⟩, rfl⟩⟩

theorem min_mono_decr_bind {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (h : T -> T) (f g : A -> T) (P : A -> Prop) (n m : T) :
    min_value_of_subset le P f n ->
    (forall a, g a = h (f a)) ->
    (forall n1 n2, le n1 n2 -> le (h n2) (h n1)) ->
    m = h n ->
    max_value_of_subset le P g m := by
  intro hmin hgdef hh hmeq
  subst m
  rcases min_mono_decr_bind' le f h P n hmin hh with ⟨a, ⟨⟨ha, haMax⟩, hha⟩⟩
  refine ⟨a, ⟨⟨ha, ?_⟩, ?_⟩⟩
  · intro b hb
    rw [hgdef b, hgdef a]
    exact haMax b hb
  · rw [hgdef a]
    exact hha

theorem min_exists_union_l {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q : A -> Prop) :
    (exists a, P a /\ f a = n) ->
    min_value_of_subset le (Sets.union P Q) f m ->
    le m n := by
  rintro ⟨a, haP, hfa⟩ ⟨b, ⟨⟨_, hbMin⟩, hfb⟩⟩
  subst n
  subst m
  exact hbMin a (union_left haP)

theorem min_exists_union_r {T : Type} (le : T -> T -> Prop) [TotalOrder le]
    {A : Type} (n m : T) (f : A -> T) (P Q : A -> Prop) :
    (exists a, Q a /\ f a = n) ->
    min_value_of_subset le (Sets.union P Q) f m ->
    le m n := by
  rintro ⟨a, haQ, hfa⟩ ⟨b, ⟨⟨_, hbMin⟩, hfb⟩⟩
  subst n
  subst m
  exact hbMin a (union_right haQ)

end MaxMinLib
