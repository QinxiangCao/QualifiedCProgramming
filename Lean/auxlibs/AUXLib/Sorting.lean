import AUXLib.ListLib

-- Recursive interfaces of Rocq/auxlibs/ListLib.v, shared by the benchmark ports.
namespace AUXLib.Sorting
open AUXLib

def increasing_aux : List Int → Int → Prop
  | [], _ => True
  | y :: l, x => x ≤ y ∧ increasing_aux l y

def increasing : List Int → Prop
  | [] => True
  | x :: l => increasing_aux l x

def lowerbound (x : Int) : List Int → Prop
  | [] => True
  | y :: l => x ≤ y ∧ lowerbound x l

def strict_lowerbound (x : Int) : List Int → Prop
  | [] => True
  | y :: l => x < y ∧ strict_lowerbound x l

def insert (x : Int) : List Int → List Int
  | [] => [x]
  | y :: l => if x > y then y :: insert x l else x :: y :: l

def last_val_local (default : Int) : List Int → Int
  | [] => default
  | y :: l => last_val_local y l

theorem lowerbound_iff (x : Int) (l : List Int) :
    lowerbound x l ↔ ∀ y ∈ l, x ≤ y := by
  induction l with
  | nil => simp [lowerbound]
  | cons y l ih => simp [lowerbound, ih]

theorem upperbound_insert_nil (x : Int) (l : List Int) (h : strict_lowerbound x l) :
    insert x l = x :: l := by
  cases l with
  | nil => rfl
  | cons y l => have := h.1; simp [insert, show ¬x > y by omega]

theorem upperbound_insert_cons (x y : Int) (l : List Int) (hy : y ≤ x)
    (h : strict_lowerbound x l) : insert x (y :: l) = y :: x :: l := by
  by_cases hx : x > y
  · simp [insert, hx, upperbound_insert_nil x l h]
  · have : x = y := by omega
    subst x
    simp [insert]

theorem increasing_aux_insert (x : Int) (l : List Int) (start : Int)
    (hi : increasing_aux l start) (hx : start ≤ x) : increasing_aux (insert x l) start := by
  induction l generalizing start with
  | nil => exact ⟨hx, trivial⟩
  | cons y l ih =>
    by_cases hxy : x > y
    · simp only [insert, if_pos hxy, increasing_aux]
      exact ⟨hi.1, ih y hi.2 (by omega)⟩
    · exact (by simpa [insert, hxy, increasing_aux] using And.intro hx (And.intro (show x ≤ y by omega) hi.2))

theorem increasing_insert (x : Int) (l : List Int) (hi : increasing l) :
    increasing (insert x l) := by
  cases l with
  | nil => trivial
  | cons y l =>
    by_cases hxy : x > y
    · simpa [insert, hxy, increasing] using increasing_aux_insert x l y hi (by omega)
    · simpa [insert, hxy, increasing, increasing_aux] using And.intro (show x ≤ y by omega) hi

theorem increasing_aux_middle (l : List Int) (y x : Int) (l2 : List Int) (start : Int)
    (hi : increasing_aux (l ++ y :: l2) start) (hyx : y ≤ x)
    (hx : strict_lowerbound x l2) : increasing_aux (l ++ y :: x :: l2) start := by
  induction l generalizing start with
  | nil =>
    refine ⟨hi.1, hyx, ?_⟩
    cases l2 with
    | nil => trivial
    | cons z l2 => exact ⟨by have := hx.1; omega, hi.2.2⟩
  | cons z l ih => exact ⟨hi.1, ih z hi.2⟩

theorem increasing_middle (l1 : List Int) (y x : Int) (l2 : List Int)
    (hi : increasing (l1 ++ y :: l2)) (hyx : y ≤ x)
    (hx : strict_lowerbound x l2) : increasing (l1 ++ y :: x :: l2) := by
  cases l1 with
  | nil =>
    refine ⟨hyx, ?_⟩
    cases l2 with
    | nil => trivial
    | cons z l2 => exact ⟨by have := hx.1; omega, hi.2⟩
  | cons z l1 => exact increasing_aux_middle l1 y x l2 z hi hyx hx

theorem last_val_local_in (x : Int) (l : List Int) : last_val_local x l ∈ x :: l := by
  induction l generalizing x with
  | nil => simp [last_val_local]
  | cons y l ih => exact List.mem_cons_of_mem x (ih y)

theorem increasing_aux_snoc_local (l : List Int) (start x : Int)
    (hi : increasing_aux l start) (hx : last_val_local start l ≤ x) :
    increasing_aux (l ++ [x]) start := by
  induction l generalizing start with
  | nil => exact ⟨hx, trivial⟩
  | cons y l ih => exact ⟨hi.1, ih y hi.2 hx⟩

theorem increasing_snoc_local (l : List Int) (x : Int) (hi : increasing l)
    (hx : match l with | [] => True | y :: l' => last_val_local y l' ≤ x) :
    increasing (l ++ [x]) := by
  cases l with
  | nil => trivial
  | cons y l => exact increasing_aux_snoc_local l y x hi hx

theorem increasing_cons_local (x : Int) (l : List Int) (hb : lowerbound x l)
    (hi : increasing l) : increasing (x :: l) := by
  cases l with
  | nil => trivial
  | cons y l => exact ⟨hb.1, hi⟩

theorem replace_Znth_length_local {A : Type} (l : List A) (n : Int) (a : A) :
    Zlength (replace_Znth n a l) = Zlength l := Zlength_replace_Znth l n a

theorem replace_Znth_boundary_local {A : Type} (pfx tail : List A) (x y : A) :
    replace_Znth (Zlength pfx) x (pfx ++ y :: tail) = pfx ++ x :: tail := by
  simp only [replace_Znth, Zlength, Int.toNat_natCast]
  induction pfx with
  | nil => rfl
  | cons a pfx ih => simpa [replace_nth] using congrArg (List.cons a) ih

theorem replace_Znth_boundary_app_local {A : Type} (pfx middle tail : List A) (x y : A) :
    replace_Znth (Zlength pfx) x ((pfx ++ y :: middle) ++ tail) =
      (pfx ++ x :: middle) ++ tail := by
  simpa only [List.append_assoc, List.cons_append] using
    replace_Znth_boundary_local pfx (middle ++ tail) x y

theorem perm_insert (x : Int) (l : List Int) : Permutation (l ++ [x]) (insert x l) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
    by_cases hx : x > a
    · simpa only [List.cons_append, insert, if_pos hx] using ih.cons a
    · simpa only [List.cons_append, insert, if_neg hx] using
        (List.perm_append_comm (l₁ := a :: l) (l₂ := [x]))

theorem perm_swap_with_prefix (l1 l2 l3 : List Int) (x y : Int) :
    Permutation (l1 ++ (x :: (l2 ++ y :: l3))) (l1 ++ (y :: (l2 ++ x :: l3))) := by
  apply List.Perm.append_left l1
  exact (List.perm_append_comm_assoc [x] l2 (y :: l3)).trans
    ((List.Perm.swap y x l3).append_left l2 |>.trans List.perm_middle)


-- Explicit list boundaries used by the array VC proofs.
theorem Znth_boundary (pfx tail : List Int) (x : Int) :
    Znth (Zlength pfx) (pfx ++ x :: tail) 0 = x := by
  rw [app_Znth2 0 pfx (x::tail) (Zlength pfx) (Int.le_refl _)]
  simp

theorem Znth_boundary_next (pfx tail : List Int) (x y : Int) :
    Znth (Zlength pfx + 1) (pfx ++ x :: y :: tail) 0 = y := by
  rw [app_Znth2 0 pfx (x::y::tail) (Zlength pfx+1) (by omega)]
  simp [Znth]

theorem swap_boundary (pfx tail : List Int) (x y : Int) :
    replace_Znth (Zlength pfx + 1) x
      (replace_Znth (Zlength pfx) y (pfx ++ x :: y :: tail)) =
      pfx ++ y :: x :: tail := by
  rw [replace_Znth_boundary_local]
  have hlen : Zlength (pfx ++ [y]) = Zlength pfx + 1 := by simp [Zlength]
  have heq : pfx ++ y :: y :: tail = (pfx ++ [y]) ++ y :: tail := by simp
  rw [heq, ← hlen, replace_Znth_boundary_local]
  simp


theorem exists_snoc_of_pos (l : List Int) (h : 0 < Zlength l) :
    ∃ pfx x, l = pfx ++ [x] := by
  induction l with
  | nil => simp [Zlength] at h
  | cons x tail ih =>
    cases tail with
    | nil => exact ⟨[], x, rfl⟩
    | cons y rest =>
      obtain ⟨pfx, z, hz⟩ := ih (by simp [Zlength])
      exact ⟨x::pfx, z, by simp [hz]⟩

theorem Znth_end (l : List Int) (d : Int) : Znth (Zlength l) l d = d := by
  simp [Znth, Zlength, List.getD_eq_getElem?_getD]

theorem Znth_boundary_d (pfx tail : List Int) (x d : Int) :
    Znth (Zlength pfx) (pfx ++ x :: tail) d = x := by
  rw [app_Znth2 d pfx (x::tail) (Zlength pfx) (Int.le_refl _)]
  simp

end AUXLib.Sorting
