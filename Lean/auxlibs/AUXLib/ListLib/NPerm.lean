import AUXLib.ListLib.Base

namespace AUXLib

universe u v

def remove_eqdec {A : Type u} [EqDec A] (x : A) : List A -> List A
  | [] => []
  | y :: ys => if x = y then remove_eqdec x ys else y :: remove_eqdec x ys

def inb {A : Type u} [EqDec A] (x : A) : List A -> Bool
  | [] => false
  | y :: ys => equiv_decb x y || inb x ys

theorem inb_true_iff {A : Type u} [EqDec A] (x : A) (l : List A) :
    inb x l = true <-> In x l := by
  induction l with
  | nil => simp [inb]
  | cons y ys ih =>
      by_cases hxy : x = y
      · subst y
        simp [inb, equiv_decb]
      · simp [inb, equiv_decb, hxy, ih]

theorem inb_false_iff {A : Type u} [EqDec A] (x : A) (l : List A) :
    inb x l = false <-> Not (In x l) := by
  constructor
  · intro hf hin
    have ht := (inb_true_iff x l).2 hin
    simp [hf] at ht
  · intro hn
    cases hb : inb x l with
    | false => rfl
    | true => exact False.elim (hn ((inb_true_iff x l).1 hb))

def In_dec {A : Type u} [EqDec A] (x : A) (l : List A) : Decidable (In x l) :=
  inferInstance

def incl_dec {A : Type u} [EqDec A] : (l1 l2 : List A) -> Decidable (incl l1 l2)
  | [], _ => isTrue (by intro x hx; simp at hx)
  | x :: xs, l2 =>
      match In_dec x l2, incl_dec xs l2 with
      | isTrue hx, isTrue hxs =>
          isTrue (by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact hx
            · exact hxs y hy)
      | isFalse hx, _ =>
          isFalse (by
            intro h
            exact hx (h x (by simp)))
      | _, isFalse hxs =>
          isFalse (by
            intro h
            apply hxs
            intro y hy
            exact h y (by simp [hy]))

def NoDup_dec {A : Type u} [EqDec A] (l : List A) : Decidable (NoDup l) :=
  inferInstance

theorem Forall2_split_app1 (A : Type u) (B : Type v)
    (P : A -> B -> Prop) (xs1 xs2 : List A) (ys : List B)
    (h : Forall2 P (xs1 ++ xs2) ys) :
    exists ys1 ys2, ys = ys1 ++ ys2 ∧ Forall2 P xs1 ys1 ∧ Forall2 P xs2 ys2 := by
  induction xs1 generalizing ys with
  | nil => exact ⟨[], ys, by simp, .nil, h⟩
  | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
          cases h with
          | cons hp ht =>
              rcases ih ys ht with ⟨ys1, ys2, rfl, h1, h2⟩
              exact ⟨y :: ys1, ys2, by simp, .cons hp h1, h2⟩

theorem Forall2_split_app2 (A : Type u) (B : Type v)
    (P : A -> B -> Prop) (xs : List A) (ys1 ys2 : List B)
    (h : Forall2 P xs (ys1 ++ ys2)) :
    exists xs1 xs2, xs = xs1 ++ xs2 ∧ Forall2 P xs1 ys1 ∧ Forall2 P xs2 ys2 := by
  induction ys1 generalizing xs with
  | nil => exact ⟨[], xs, by simp, .nil, h⟩
  | cons y ys ih =>
      cases xs with
      | nil => cases h
      | cons x xs =>
          cases h with
          | cons hp ht =>
              rcases ih xs ht with ⟨xs1, xs2, rfl, h1, h2⟩
              exact ⟨x :: xs1, xs2, by simp, .cons hp h1, h2⟩

theorem Forall2_merge (A : Type u) (B : Type v) (P : A -> B -> Prop)
    (xs1 : List A) (ys1 : List B) (xs2 : List A) (ys2 : List B)
    (h1 : Forall2 P xs1 ys1) (h2 : Forall2 P xs2 ys2) :
    Forall2 P (xs1 ++ xs2) (ys1 ++ ys2) :=
  h1.append h2

theorem list_split_nth (A : Type u) (n : Nat) (l : List A) (d : A)
    (h : n < l.length) :
    l = firstn n l ++ nth n l d :: skipn (n + 1) l := by
  induction n generalizing l with
  | zero =>
      cases l with
      | nil => simp at h
      | cons x xs => simp [firstn, skipn, nth]
  | succ n ih =>
      cases l with
      | nil => simp at h
      | cons x xs =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          change x :: xs = x :: (firstn n xs ++ nth n xs d :: skipn (n + 1) xs)
          exact congrArg (fun ys => x :: ys) (ih xs h)

theorem firstn_skipSn {A : Type u} (d : A) (n : Nat) (l : List A)
    (h : n < l.length) :
    l = firstn n l ++ nth n l d :: skipn (Nat.succ n) l := by
  simpa only [Nat.succ_eq_add_one] using list_split_nth A n l d h

theorem cons_length (A : Type u) (x : A) (l : List A) :
    (x :: l).length = l.length + 1 := by simp

theorem combine_app {A : Type u} {B : Type v}
    (l1 l2 : List A) (l1' l2' : List B) (h : l1.length = l1'.length) :
    combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2' := by
  induction l1 generalizing l1' with
  | nil =>
      cases l1' with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases l1' with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp [combine, ih ys h]

theorem forall_in_cons {A : Type u} (a : A) (l : List A) (P : A -> Prop) :
    (forall a0, In a0 (a :: l) -> P a0) <->
      P a ∧ (forall a0, In a0 l -> P a0) := by
  constructor
  · intro h
    exact ⟨h a (by simp), by intro x hx; exact h x (by simp [hx])⟩
  · rintro ⟨ha, hl⟩ x hx
    rcases (List.mem_cons.mp hx) with rfl | hx
    · exact ha
    · exact hl x hx

theorem forall_in_app {A : Type u} (l1 l2 : List A) (P : A -> Prop) :
    (forall a, In a (l1 ++ l2) -> P a) <->
      (forall a, In a l1 -> P a) ∧ (forall a, In a l2 -> P a) := by
  constructor
  · intro h
    exact ⟨by intro x hx; exact h x (List.mem_append_left _ hx),
      by intro x hx; exact h x (List.mem_append_right _ hx)⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h1 x hx
    · exact h2 x hx

def prod_eq_dec {A : Type u} {B : Type v}
    (eq_dec1 : EqDec A) (eq_dec2 : EqDec B) : EqDec (A × B) := by
  intro p1 p2
  cases p1 with
  | mk a1 b1 =>
      cases p2 with
      | mk a2 b2 =>
          match eq_dec1 a1 a2, eq_dec2 b1 b2 with
          | isTrue ha, isTrue hb => exact isTrue (by simp [ha, hb])
          | isFalse ha, _ => exact isFalse (by intro h; exact ha (Prod.mk.inj h).1)
          | _, isFalse hb => exact isFalse (by intro h; exact hb (Prod.mk.inj h).2)

def list_eq_dec {A : Type u} (eq_dec : EqDec A) : EqDec (List A) := by
  letI : DecidableEq A := eq_dec
  infer_instance

def list_eqb {A : Type u} {B : Type v} (eqb : A -> B -> Bool) :
    List A -> List B -> Bool
  | [], [] => true
  | a :: as, b :: bs => eqb a b && list_eqb eqb as bs
  | _, _ => false

theorem list_eqb_eq_nil {A : Type u} {B : Type v} (eqb : A -> B -> Bool)
    (l2 : List B) : list_eqb eqb [] l2 = true <-> ([] : List B) = l2 := by
  cases l2 <;> simp [list_eqb]

theorem list_eqb_eq_cons {A : Type u} (eqb : A -> A -> Bool)
    (a1 : A) (l1 : List A)
    (ha : forall a2, eqb a1 a2 = true <-> a1 = a2)
    (hl : forall l2, list_eqb eqb l1 l2 = true <-> l1 = l2)
    (l2 : List A) :
    list_eqb eqb (a1 :: l1) l2 = true <-> a1 :: l1 = l2 := by
  cases l2 with
  | nil => simp [list_eqb]
  | cons a2 l2 => simp [list_eqb, ha, hl]

theorem list_eqb_eq {A : Type u} (eqb : A -> A -> Bool)
    (heq : forall a1 a2, eqb a1 a2 = true <-> a1 = a2)
    (l1 l2 : List A) : list_eqb eqb l1 l2 = true <-> l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => exact list_eqb_eq_nil eqb l2
  | cons a1 l1 ih => exact list_eqb_eq_cons eqb a1 l1 (heq a1) ih l2

theorem list_eqb_refl {A : Type u} (eqb : A -> A -> Bool)
    (hrefl : forall a, eqb a a = true) (l : List A) :
    list_eqb eqb l l = true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [list_eqb, hrefl, ih]

theorem list_eqb_true {A : Type u} (eqb : A -> A -> Bool)
    (htrue : forall a1 a2, eqb a1 a2 = true -> a1 = a2)
    (l1 l2 : List A) (h : list_eqb eqb l1 l2 = true) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [list_eqb] at h ⊢
  | cons a1 l1 ih =>
      cases l2 with
      | nil => simp [list_eqb] at h
      | cons a2 l2 =>
          simp only [list_eqb, Bool.and_eq_true] at h
          have ha : a1 = a2 := htrue a1 a2 h.1
          have hl : l1 = l2 := ih l2 h.2
          subst a2
          subst l2
          rfl

def option_eqb {A : Type u} (eqb : A -> A -> Bool) : Option A -> Option A -> Bool
  | some a1, some a2 => eqb a1 a2
  | none, none => true
  | _, _ => false

theorem option_eqb_eq (A : Type u) (eqb : A -> A -> Bool)
    (heq : forall a1 a2, eqb a1 a2 = true <-> a1 = a2)
    (o1 o2 : Option A) : option_eqb eqb o1 o2 = true <-> o1 = o2 := by
  cases o1 <;> cases o2 <;> simp [option_eqb, heq]

def lift_option {A : Type u} : List (Option A) -> Option (List A)
  | [] => some []
  | some x :: xs => (lift_option xs).map (x :: .)
  | none :: _ => none

theorem lift_option_map_some {A : Type u} (l : List A) :
    lift_option (l.map some) = some l := by
  induction l <;> simp_all [lift_option]

theorem lift_option_cons {A : Type u} (x : Option A) (l : List (Option A)) :
    lift_option (x :: l) = x.bind (fun y => (lift_option l).map (y :: .)) := by
  cases x <;> rfl

theorem lift_option_app {A : Type u} (l1 l2 : List (Option A)) :
    lift_option (l1 ++ l2) =
      (lift_option l1).bind (fun l1' => (lift_option l2).map (l1' ++ .)) := by
  induction l1 with
  | nil => simp [lift_option]
  | cons x xs ih =>
      cases x with
      | none => rfl
      | some x =>
          simp only [List.cons_append, lift_option, ih]
          cases lift_option xs <;> cases lift_option l2 <;> rfl

def list_prod_split {A : Type u} {B : Type v} (l : List (A × B)) : List A × List B :=
  (l.map Prod.fst, l.map Prod.snd)

def list_prod_merge {A : Type u} {B : Type v} :
    List A -> List B -> Option (List (A × B))
  | [], [] => some []
  | a :: as, b :: bs => (list_prod_merge as bs).map ((a, b) :: .)
  | _, _ => none

theorem incl_cons_iff {A : Type u} (a : A) (l m : List A) :
    incl (a :: l) m <-> In a m ∧ incl l m := by
  constructor
  · intro h
    exact ⟨h a (by simp), by intro x hx; exact h x (by simp [hx])⟩
  · rintro ⟨ha, hl⟩ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hl x hx

def nperm (s : List Nat) : Prop :=
  Permutation (seq 0 s.length) s

def do_nperm {A : Type u} (s : List Nat) (l : List A) (d : A) : List A :=
  s.map (fun n => nth n l d)

def trivial_nperm (n : Nat) : List Nat := seq 0 n

theorem trivial_nperm_nperm (n : Nat) : nperm (trivial_nperm n) := by
  unfold nperm trivial_nperm
  simp

private theorem getD_eq_getElem_of_lt {A : Type u} (l : List A) (d : A)
    (n : Nat) (h : n < l.length) : l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem map_range_getD {A : Type u} (l : List A) (d : A) :
    (List.range l.length).map (fun n => l.getD n d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range]
    exact getD_eq_getElem_of_lt l d i h2

theorem trivial_nperm_refl (A : Type u) (n : Nat) (l : List A) (d : A)
    (h : l.length = n) : do_nperm (trivial_nperm n) l d = l := by
  subst n
  simpa [do_nperm, trivial_nperm, seq, List.range_eq_range'] using map_range_getD l d

def find_index : List Nat -> Nat -> Nat
  | [], _ => 0
  | n' :: l, n => if n' == n then 0 else find_index l n + 1

private theorem getD_mem {A : Type u} (l : List A) (d : A) (n : Nat)
    (h : n < l.length) : l.getD n d ∈ l := by
  rw [getD_eq_getElem_of_lt l d n h]
  exact List.getElem_mem h

theorem find_index_nth (l : List Nat) (n d : Nat) (hnd : NoDup l)
    (hn : n < l.length) : find_index l (nth n l d) = n := by
  induction n generalizing l with
  | zero =>
      cases l with
      | nil => simp at hn
      | cons x xs => simp [find_index, nth]
  | succ n ih =>
      cases l with
      | nil => simp at hn
      | cons x xs =>
          have hparts : x ∉ xs ∧ xs.Nodup := by simpa [NoDup] using hnd
          have hnd' : NoDup xs := hparts.2
          have hnot : x ∉ xs := hparts.1
          have hn' : n < xs.length := by simpa using hn
          have hneq : x ≠ nth n xs d := by
            intro heq
            apply hnot
            rw [heq]
            exact getD_mem xs d n hn'
          change x ≠ xs.getD n d at hneq
          have hbeq : (x == xs.getD n d) = false := by simpa using hneq
          change (if (x == xs.getD n d) = true then 0
            else find_index xs (xs.getD n d) + 1) = n + 1
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
          exact congrArg (fun k => k + 1) (ih xs hnd' hn')

theorem nth_find_index (l : List Nat) (n d : Nat) (h : In n l) :
    nth (find_index l n) l d = n := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : x = n
      · subst n
        simp [find_index, nth]
      · have hxs : n ∈ xs := by
          rcases List.mem_cons.mp h with hnx | hxs
          · exact False.elim (hx hnx.symm)
          · exact hxs
        simp only [find_index]
        simp [hx]
        change xs.getD (find_index xs n) d = n
        exact ih hxs

theorem map_nth_len (A : Type u) (B : Type v) (f : A -> B)
    (l : List A) (n : Nat) (dx : B) (dy : A) (h : n < l.length) :
    nth n (l.map f) dx = f (nth n l dy) := by
  change (l.map f).getD n dx = f (l.getD n dy)
  rw [getD_eq_getElem_of_lt (l.map f) dx n (by simpa using h)]
  rw [List.getElem_map]
  rw [getD_eq_getElem_of_lt l dy n h]

theorem map_find_index_same (l : List Nat) (hnd : NoDup l) :
    l.map (find_index l) = seq 0 l.length := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map] at h1
    rw [List.getElem_map]
    change find_index l (l[i]) = (seq 0 l.length)[i]
    have hnth : nth i l 0 = l[i] := getD_eq_getElem_of_lt l 0 i h1
    rw [← hnth, find_index_nth l i 0 hnd h1]
    rw [List.getElem_range']
    omega

theorem do_nperm_length (A : Type u) (s : List Nat) (l : List A) (d : A) :
    (do_nperm s l d).length = s.length := by simp [do_nperm]

theorem nperm_range (s : List Nat) (n0 d : Nat) (hp : nperm s)
    (hn : n0 < s.length) : nth n0 s d < s.length := by
  have hmem : nth n0 s d ∈ s := getD_mem s d n0 hn
  have hseq : nth n0 s d ∈ seq 0 s.length := hp.mem_iff.mpr hmem
  rcases List.mem_range'.mp hseq with ⟨i, hi, heq⟩
  omega

theorem nperm_NoDup (s : List Nat) (hp : nperm s) : NoDup s := by
  exact hp.nodup_iff.mp (by
    simpa [seq, List.range'_eq_map_range] using List.nodup_range)

theorem nperm_map (A : Type u) (B : Type v) (s : List Nat)
    (f : A -> B) (l : List A) (dx : A) :
    do_nperm s (l.map f) (f dx) = (do_nperm s l dx).map f := by
  unfold do_nperm
  simp only [List.map_map]
  apply List.map_congr_left
  intro n hn
  by_cases hlt : n < l.length
  · exact map_nth_len A B f l n (f dx) dx hlt
  · have hmap : Not (n < (l.map f).length) := by simpa using hlt
    simp [nth, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (Nat.le_of_not_gt hlt),
      List.getElem?_eq_none (Nat.le_of_not_gt hmap)]

theorem find_index_range (l : List Nat) (n : Nat) (h : In n l) :
    find_index l n < l.length := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : x = n
      · subst n
        simp [find_index]
      · have hxs : n ∈ xs := by
          rcases List.mem_cons.mp h with hnx | hxs
          · exact False.elim (hx hnx.symm)
          · exact hxs
        simp [find_index, hx, ih hxs]

def inverse_nperm (s : List Nat) : List Nat :=
  (seq 0 s.length).map (find_index s)

private theorem nth_seq (start len n d : Nat) (h : n < len) :
    nth n (seq start len) d = start + n := by
  change (seq start len).getD n d = start + n
  rw [getD_eq_getElem_of_lt (seq start len) d n (by simpa [seq] using h)]
  simpa only [Nat.one_mul] using
    (List.getElem_range' (n := start) (m := len) (step := 1) (i := n)
      (by simpa [seq] using h))

private theorem nth_do_nperm {A : Type u} (s : List Nat) (l : List A)
    (d : A) (n : Nat) (h : n < s.length) :
    nth n (do_nperm s l d) d = nth (nth n s 0) l d := by
  unfold do_nperm
  exact map_nth_len Nat A (fun k => nth k l d) s n d 0 h

private theorem nth_inverse_nperm (s : List Nat) (n : Nat) (h : n < s.length) :
    nth n (inverse_nperm s) 0 = find_index s n := by
  unfold inverse_nperm
  rw [map_nth_len Nat Nat (find_index s) (seq 0 s.length) n 0 0]
  · rw [nth_seq 0 s.length n 0 h]
    simp
  · simpa [seq] using h

theorem inverse_nperm_nperm (s : List Nat) (hp : nperm s) :
    nperm (inverse_nperm s) := by
  unfold nperm inverse_nperm
  simp only [List.length_map, List.length_range']
  have hm := hp.map (find_index s)
  have hsame := map_find_index_same s (nperm_NoDup s hp)
  rw [hsame] at hm
  exact hm.symm

theorem inverse_nperm_compose_refl1 (A : Type u) (s : List Nat)
    (l : List A) (d : A) (hp : nperm s) (hlen : l.length = s.length) :
    do_nperm s (do_nperm (inverse_nperm s) l d) d = l := by
  apply List.ext_getElem
  · rw [do_nperm_length]
    exact hlen.symm
  · intro k hkout hkl
    have hks : k < s.length := by simpa [do_nperm] using hkout
    rw [← getD_eq_getElem_of_lt _ d k hkout]
    change nth k (do_nperm s (do_nperm (inverse_nperm s) l d) d) d = l[k]
    rw [nth_do_nperm s _ d k hks]
    let j := nth k s 0
    have hj : j < s.length := nperm_range s k 0 hp hks
    have hjinv : j < (inverse_nperm s).length := by
      simpa [inverse_nperm] using hj
    rw [nth_do_nperm (inverse_nperm s) l d j hjinv]
    rw [nth_inverse_nperm s j hj]
    rw [find_index_nth s k 0 (nperm_NoDup s hp) hks]
    exact getD_eq_getElem_of_lt l d k hkl

theorem inverse_nperm_compose_refl2 (A : Type u) (s : List Nat)
    (l : List A) (d : A) (hp : nperm s) (hlen : l.length = s.length) :
    do_nperm (inverse_nperm s) (do_nperm s l d) d = l := by
  apply List.ext_getElem
  · rw [do_nperm_length]
    simp [inverse_nperm, hlen]
  · intro k hkout hkl
    have hks : k < s.length := by
      simpa [do_nperm, inverse_nperm] using hkout
    have hkinv : k < (inverse_nperm s).length := by
      simpa [inverse_nperm] using hks
    have hkseq : k ∈ seq 0 s.length := by
      exact (List.mem_range'.mpr ⟨k, hks, by omega⟩)
    have hkmem : k ∈ s := hp.mem_iff.mp hkseq
    let j := find_index s k
    have hj : j < s.length := find_index_range s k hkmem
    rw [← getD_eq_getElem_of_lt _ d k hkout]
    change nth k (do_nperm (inverse_nperm s) (do_nperm s l d) d) d = l[k]
    rw [nth_do_nperm (inverse_nperm s) _ d k hkinv]
    rw [nth_inverse_nperm s k hks]
    rw [nth_do_nperm s l d j hj]
    rw [nth_find_index s k 0 hkmem]
    exact getD_eq_getElem_of_lt l d k hkl

theorem do_nperm_permutation (A : Type u) (s : List Nat) (l : List A) (d : A)
    (hp : nperm s) (hlen : l.length = s.length) :
    Permutation l (do_nperm s l d) := by
  have htriv := trivial_nperm_refl A s.length l d hlen
  have hm := hp.map (fun n => nth n l d)
  change Permutation (do_nperm (trivial_nperm s.length) l d) (do_nperm s l d) at hm
  rw [htriv] at hm
  exact hm

theorem Forall2_nth_iff (A : Type u) (B : Type v) (P : A -> B -> Prop)
    (xs : List A) (ys : List B) (dx : A) (dy : B) :
    Forall2 P xs ys <->
      xs.length = ys.length ∧
        forall n, n < xs.length -> P (nth n xs dx) (nth n ys dy) := by
  constructor
  · intro h
    constructor
    · exact h.length_eq
    · intro n hn
      induction h generalizing n with
      | nil => simp at hn
      | cons hp ht ih =>
          cases n with
          | zero => exact hp
          | succ n =>
              apply ih
              simpa using hn
  · rintro ⟨hlen, hget⟩
    induction xs generalizing ys with
    | nil =>
        cases ys with
        | nil => exact .nil
        | cons y ys => simp at hlen
    | cons x xs ih =>
        cases ys with
        | nil => simp at hlen
        | cons y ys =>
            apply Forall2.cons
            · exact hget 0 (by simp)
            · apply ih
              · simpa using hlen
              · intro n hn
                exact hget (n + 1) (by simpa using hn)

theorem Forall2_nperm_congr0 (A : Type u) (B : Type v)
    (P : A -> B -> Prop) (xs : List A) (ys : List B)
    (s : List Nat) (dx : A) (dy : B) (hp : nperm s)
    (hxlen : xs.length = s.length) (hxy : Forall2 P xs ys) :
    Forall2 P (do_nperm s xs dx) (do_nperm s ys dy) := by
  apply (Forall2_nth_iff A B P _ _ dx dy).2
  constructor
  · simp [do_nperm]
  · intro n hn
    have hns : n < s.length := by simpa [do_nperm] using hn
    rw [nth_do_nperm s xs dx n hns, nth_do_nperm s ys dy n hns]
    have hidx : nth n s 0 < s.length := nperm_range s n 0 hp hns
    exact ((Forall2_nth_iff A B P xs ys dx dy).1 hxy).2 _ (by omega)

theorem Forall2_nperm_congr (A : Type u) (B : Type v)
    (P : A -> B -> Prop) (xs : List A) (ys : List B)
    (s : List Nat) (dx : A) (dy : B) (hp : nperm s)
    (hxlen : xs.length = s.length) (hylen : ys.length = s.length) :
    Forall2 P xs ys <->
      Forall2 P (do_nperm s xs dx) (do_nperm s ys dy) := by
  constructor
  · exact Forall2_nperm_congr0 A B P xs ys s dx dy hp hxlen
  · intro h
    rw [← inverse_nperm_compose_refl2 A s xs dx hp hxlen]
    rw [← inverse_nperm_compose_refl2 B s ys dy hp hylen]
    apply Forall2_nperm_congr0 A B P
    · exact inverse_nperm_nperm s hp
    · simp [do_nperm, inverse_nperm]
    · exact h
