import AUXLib.Axioms
import AUXLib.Feq
import AUXLib.Idents
import AUXLib.Morphisms
import Std.Tactic

namespace AUXLib

universe u

variable {A : Type u}

def vmap_update (f : var -> A) (x : var) (v : A) : var -> A :=
  fun y => if var_eqb y x then v else f y

def vmap_update_list (f : var -> A) : List var -> List A -> var -> A
  | x :: xs, v :: vs => vmap_update (vmap_update_list f xs vs) x v
  | _, _ => f

syntax "inv " ident : tactic

macro_rules
  | `(tactic| inv $h:ident) => `(tactic| cases ($h) <;> subst_vars)

instance vmap_update_congr0 :
    Proper (f_eq ==> Eq ==> Eq ==> f_eq) (@vmap_update A) where
  proper f g hfg x x' hxx v v' hvv z := by
    subst x'
    subst v'
    by_cases h : z = x
    · subst z
      simp [vmap_update, var_eqb]
    · simp [vmap_update, var_eqb, h]
      exact hfg z

instance vmap_update_list_congr0 :
    Proper (f_eq ==> Eq ==> Eq ==> f_eq) (@vmap_update_list A) where
  proper f g hfg xs xs' hxs vs vs' hvs := by
    subst xs'
    subst vs'
    induction xs generalizing vs with
    | nil =>
        cases vs <;> simpa [vmap_update_list] using hfg
    | cons x xs ih =>
        cases vs with
        | nil => simpa [vmap_update_list] using hfg
        | cons v vs =>
            apply vmap_update_congr0.proper
            · exact ih vs
            · rfl
            · rfl

theorem vmap_update_eq (J : var -> A) (x : var) (n : A) :
    vmap_update J x n x = n := by
  simp [vmap_update, var_eqb]

theorem vmap_update_neq (J : var -> A) (x y : var) (n : A) (hxy : x ≠ y) :
    vmap_update J x n y = J y := by
  simp [vmap_update, var_eqb, Ne.symm hxy]

theorem vmap_update_same (J : var -> A) (x : var) (n1 n2 : A) :
    f_eq (vmap_update (vmap_update J x n1) x n2) (vmap_update J x n2) := by
  intro y
  by_cases h : y = x <;> simp [vmap_update, var_eqb, h]

theorem vmap_update_perm (J : var -> A) (x y : var) (n1 n2 : A)
    (hxy : x ≠ y) :
    f_eq (vmap_update (vmap_update J x n1) y n2)
      (vmap_update (vmap_update J y n2) x n1) := by
  intro z
  by_cases hzy : z = y
  · subst z
    simp [vmap_update, var_eqb, Ne.symm hxy]
  · by_cases hzx : z = x
    · subst z
      simp [vmap_update, var_eqb, hxy]
    · simp [vmap_update, var_eqb, hzy, hzx]

theorem vmap_update_perm_list (J : var -> A) (x : var) (ys : List var)
    (n : A) (ns : List A) (hx : x ∉ ys) :
    f_eq (vmap_update_list (vmap_update J x n) ys ns)
      (vmap_update (vmap_update_list J ys ns) x n) := by
  induction ys generalizing ns with
  | nil =>
      intro z
      rfl
  | cons y ys ih =>
      cases ns with
      | nil =>
          intro z
          rfl
      | cons v vs =>
          have hxy : x ≠ y := by
            intro h
            apply hx
            simp [h]
          have hxys : x ∉ ys := by
            intro h
            exact hx (List.mem_cons_of_mem y h)
          have hcongr :
              f_eq
                (vmap_update
                  (vmap_update_list (vmap_update J x n) ys vs) y v)
                (vmap_update
                  (vmap_update (vmap_update_list J ys vs) x n) y v) := by
            apply vmap_update_congr0.proper
            · exact ih vs hxys
            · rfl
            · rfl
          intro z
          exact
            (hcongr z).trans
              (vmap_update_perm (vmap_update_list J ys vs) x y n v hxy z)

theorem vmap_update_congr (P : var -> Prop) (J J' : var -> A) (x : var) (n : A)
    (hJJ : forall y, P y -> J y = J' y) (y : var) (hy : P y) :
    vmap_update J x n y = vmap_update J' x n y := by
  by_cases h : y = x
  · subst y
    simp [vmap_update, var_eqb]
  · simp [vmap_update, var_eqb, h, hJJ y hy]

theorem vmap_update_list_congr (P : var -> Prop) (J J' : var -> A)
    (xs : List var) (ns : List A) (hJJ : forall y, P y -> J y = J' y)
    (y : var) (hy : P y) :
    vmap_update_list J xs ns y = vmap_update_list J' xs ns y := by
  induction xs generalizing ns y with
  | nil => cases ns <;> simpa [vmap_update_list] using hJJ y hy
  | cons x xs ih =>
      cases ns with
      | nil => simpa [vmap_update_list] using hJJ y hy
      | cons n ns =>
          apply vmap_update_congr P
          · intro z hz
            exact ih ns z hz
          · exact hy

theorem vmap_update_list_notin (J : var -> A) (xs : List var) (ns : List A)
    (x : var) (hx : x ∉ xs) :
    vmap_update_list J xs ns x = J x := by
  induction xs generalizing ns with
  | nil => cases ns <;> rfl
  | cons y ys ih =>
      cases ns with
      | nil => rfl
      | cons n ns =>
          have hxy : x ≠ y := by
            intro h
            apply hx
            simp [h]
          change vmap_update (vmap_update_list J ys ns) y n x = J x
          rw [vmap_update_neq]
          · exact ih ns (fun h => hx (List.mem_cons_of_mem y h))
          · exact Ne.symm hxy

theorem vmap_update_list_same (J : var -> A) (xs : List var) (x : var) :
    vmap_update_list J xs (xs.map J) x = J x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : x = y
      · subst x
        simp [vmap_update_list, vmap_update, var_eqb]
      · simp [vmap_update_list, vmap_update, var_eqb, h, ih]

theorem vmap_update_list_app (J : var -> A) (xs ys : List var)
    (ns1 ns2 : List A) (x : var) (hlen : xs.length = ns1.length) :
    vmap_update_list J (xs ++ ys) (ns1 ++ ns2) x =
      vmap_update_list (vmap_update_list J ys ns2) xs ns1 x := by
  induction xs generalizing ns1 with
  | nil =>
      cases ns1 with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons y ys' ih =>
      cases ns1 with
      | nil => simp at hlen
      | cons n ns1 =>
          simp only [List.cons_append, vmap_update_list]
          exact congrArg (fun value => if var_eqb x y then n else value)
            (ih ns1 (Nat.succ.inj hlen))

theorem vmap_update_list_app_skip1 (J : var -> A) (xs ys : List var)
    (ns1 ns2 : List A) (x : var) (hlen : xs.length = ns1.length)
    (hx : x ∉ xs) :
    vmap_update_list J (xs ++ ys) (ns1 ++ ns2) x =
      vmap_update_list J ys ns2 x := by
  rw [vmap_update_list_app J xs ys ns1 ns2 x hlen]
  exact vmap_update_list_notin _ _ _ _ hx

theorem vmap_update_list_in (J1 J2 : var -> A) (xs : List var) (ns : List A)
    (x : var) (hx : x ∈ xs) (hlen : xs.length = ns.length) :
    vmap_update_list J1 xs ns x = vmap_update_list J2 xs ns x := by
  induction xs generalizing ns with
  | nil => simp at hx
  | cons y ys ih =>
      cases ns with
      | nil => simp at hlen
      | cons n ns =>
          simp only [vmap_update_list]
          rcases List.mem_cons.mp hx with hxy | hxys
          · subst y
            simp [vmap_update, var_eqb]
          · have hlen' : ys.length = ns.length := Nat.succ.inj hlen
            by_cases h : x = y
            · subst x
              simp [vmap_update, var_eqb]
            · simp [vmap_update, var_eqb, h]
              exact ih ns hxys hlen'

theorem vmap_update_list_app_skip2 (J : var -> A) (xs ys : List var)
    (ns1 ns2 : List A) (x : var) (hlen : xs.length = ns1.length)
    (hx : x ∉ ys) :
    vmap_update_list J (xs ++ ys) (ns1 ++ ns2) x =
      vmap_update_list J xs ns1 x := by
  calc
    vmap_update_list J (xs ++ ys) (ns1 ++ ns2) x =
        vmap_update_list (vmap_update_list J ys ns2) xs ns1 x :=
      vmap_update_list_app J xs ys ns1 ns2 x hlen
    _ = vmap_update_list J xs ns1 x := by
      by_cases hmem : x ∈ xs
      · exact vmap_update_list_in _ _ xs ns1 x hmem hlen
      · rw [vmap_update_list_notin _ xs ns1 x hmem,
            vmap_update_list_notin J xs ns1 x hmem]
        exact vmap_update_list_notin J ys ns2 x hx

theorem vmap_update_update_list_in (J : var -> A) (xs : List var) (ns : List A)
    (x : var) (n : A) (hx : x ∈ xs) (hlen : xs.length = ns.length) :
    f_eq (vmap_update_list (vmap_update J x n) xs ns)
      (vmap_update_list J xs ns) := by
  intro y
  by_cases hy : y ∈ xs
  · exact vmap_update_list_in _ _ xs ns y hy hlen
  · rw [vmap_update_list_notin, vmap_update_list_notin]
    · exact vmap_update_neq J x y n (by
        intro hxy
        subst y
        exact hy hx)
    · exact hy
    · exact hy

theorem vmap_repair_eq (l1 l2 : var -> A) (x : var)
    (h : forall y, y ≠ x -> l1 y = l2 y) :
    f_eq l1 (vmap_update l2 x (l1 x)) := by
  intro y
  by_cases hy : y = x
  · subst y
    simp [vmap_update, var_eqb]
  · simp [vmap_update, var_eqb, hy, h y hy]

theorem vmap_repair_eq' (l1 l2 : var -> A) (x : var)
    (h : forall y, y ≠ x -> l1 y = l2 y) :
    vmap_update l2 x (l1 x) = l1 := by
  funext y
  exact (vmap_repair_eq l1 l2 x h y).symm

end AUXLib
