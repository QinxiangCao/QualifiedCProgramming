import AUXLib.ListLib.Arithmetic
import AUXLib.ListLib.LengthCompat
import Std.Tactic
import Lean.Elab.Tactic.Omega

namespace AUXLib

universe u v

inductive interval_list (pace lo hi : Int) : List Int -> Prop where
  | interval_list_nil : interval_list pace lo hi []
  | interval_list_cons (l : List Int) (x : Int) :
      interval_list pace lo hi l ->
      lo <= x ->
      x + pace <= hi ->
      Forall (fun x' => x + pace < x' ∨ x' + pace < x) l ->
      interval_list pace lo hi (x :: l)

export interval_list (interval_list_nil interval_list_cons)

theorem interval_list_valid1 (l : List Int) (pace lo hi : Int)
    (h : interval_list pace lo hi l) (hpace : pace > 0) :
    Forall (fun x => lo <= x ∧ x < hi) l := by
  induction h with
  | interval_list_nil => exact .nil
  | interval_list_cons l x hl hlo hhi hsep ih =>
      exact .cons ⟨hlo, by omega⟩ ih

theorem interval_list_valid2 (l : List Int) (pace lo hi : Int)
    (h : interval_list pace lo hi l) (hpace : pace > 0) : NoDup l := by
  induction h with
  | interval_list_nil => exact List.nodup_nil
  | interval_list_cons l x hl hlo hhi hsep ih =>
      apply List.nodup_cons.mpr
      constructor
      · intro hx
        have hdisj := hsep.mem hx
        omega
      · exact ih

theorem interval_list_valid3 (l : List Int) (pace lo hi : Int)
    (h : interval_list pace lo hi l) :
    Forall (fun x => lo <= x ∧ x + pace <= hi) l := by
  induction h with
  | interval_list_nil => exact .nil
  | interval_list_cons l x hl hlo hhi hsep ih => exact .cons ⟨hlo, hhi⟩ ih

def Zlist_max (l : List Int) (lo : Int) : Int :=
  l.foldr max lo

theorem interval_perm_keep (l l1 : List Int) (pace lo hi : Int)
    (hinterval : interval_list pace lo hi l)
    (hperm : Permutation l l1) : interval_list pace lo hi l1 := by
  induction hperm with
  | nil => exact hinterval
  | cons x hp ih =>
      cases hinterval with
      | interval_list_cons l x hl hlo hhi hsep =>
          exact .interval_list_cons _ _ (ih hl) hlo hhi (hsep.perm hp)
  | swap x y l =>
      cases hinterval with
      | interval_list_cons _ _ hyl hylo hyhi hysep =>
          cases hyl with
          | interval_list_cons _ _ hl hxlo hxhi hxsep =>
              cases hysep with
              | cons hyx hylsep =>
                  have hyl' : interval_list pace lo hi (y :: l) :=
                    .interval_list_cons l y hl hylo hyhi hylsep
                  have hxall : Forall
                      (fun z => x + pace < z ∨ z + pace < x) (y :: l) :=
                    .cons (by rcases hyx with h | h <;> omega) hxsep
                  exact .interval_list_cons (y :: l) x hyl' hxlo hxhi hxall
  | trans hp1 hp2 ih1 ih2 => exact ih2 (ih1 hinterval)

def increasing_aux : List Int -> Int -> Prop
  | [], _ => True
  | y :: l, x => x <= y /\ increasing_aux l y

def increasing : List Int -> Prop
  | [] => True
  | x :: l => increasing_aux l x

theorem increasing_aux_tail_increasing (l : List Int) (x : Int)
    (hinc : increasing_aux l x) : increasing l := by
  cases l with
  | nil => trivial
  | cons _ _ => exact hinc.2

theorem increasing_aux_head_le_all_In (l : List Int) (x y : Int)
    (hinc : increasing_aux l x) (hin : In y l) : x <= y := by
  induction l generalizing x y with
  | nil => simp at hin
  | cons a l ih =>
      simp only [List.mem_cons] at hin
      rcases hin with hya | hin
      · simpa [hya] using hinc.1
      · exact Int.le_trans hinc.1 (ih (x := a) (y := y) hinc.2 hin)

def decreasing_aux : List Int -> Int -> Prop
  | [], _ => True
  | y :: l, x => y <= x /\ decreasing_aux l y

def decreasing : List Int -> Prop
  | [] => True
  | x :: l => decreasing_aux l x

theorem decreasing_aux_tail_decreasing (l : List Int) (x : Int)
    (hdec : decreasing_aux l x) : decreasing l := by
  cases l with
  | nil => trivial
  | cons _ _ => exact hdec.2

theorem decreasing_aux_head_ge_all_In (l : List Int) (x y : Int)
    (hdec : decreasing_aux l x) (hin : In y l) : y <= x := by
  induction l generalizing x y with
  | nil => simp at hin
  | cons a l ih =>
      simp only [List.mem_cons] at hin
      rcases hin with hya | hin
      · simpa [hya] using hdec.1
      · exact Int.le_trans (ih (x := a) (y := y) hdec.2 hin) hdec.1

def strict_decreasing_aux : List Int -> Int -> Prop
  | [], _ => True
  | y :: l, x => y < x /\ strict_decreasing_aux l y

def strict_decreasing : List Int -> Prop
  | [] => True
  | x :: l => strict_decreasing_aux l x

theorem strict_decreasing_aux_tail_strict_decreasing (l : List Int) (x : Int)
    (hdec : strict_decreasing_aux l x) : strict_decreasing l := by
  cases l with
  | nil => trivial
  | cons _ _ => exact hdec.2

theorem strict_decreasing_aux_head_gt_all_In (l : List Int) (x y : Int)
    (hdec : strict_decreasing_aux l x) (hin : In y l) : y < x := by
  induction l generalizing x y with
  | nil => simp at hin
  | cons a l ih =>
      simp only [List.mem_cons] at hin
      rcases hin with hya | hin
      · simpa [hya] using hdec.1
      · exact Int.lt_trans (ih (x := a) (y := y) hdec.2 hin) hdec.1

def upperbound (x : Int) : List Int -> Prop
  | [] => True
  | y :: l => y <= x /\ upperbound x l

def upper_bound := upperbound

def strict_upperbound (x : Int) : List Int -> Prop
  | [] => True
  | y :: l => y < x /\ strict_upperbound x l

def lowerbound (x : Int) : List Int -> Prop
  | [] => True
  | y :: l => x <= y /\ lowerbound x l

def lower_bound := lowerbound

def strict_lowerbound (x : Int) : List Int -> Prop
  | [] => True
  | y :: l => x < y /\ strict_lowerbound x l

def prefix_suffix_sorted (pre suffix : List Int) : Prop :=
  forall x, In x pre -> lowerbound x suffix

theorem upperbound_Znth (x : Int) (l : List Int) (i : Int)
    (hbound : upperbound x l) (hi : 0 <= i /\ i < Zlength l) :
    Znth i l 0 <= x := by
  induction l generalizing i with
  | nil => simp [Zlength] at hi; omega
  | cons a l ih =>
      by_cases hi0 : i = 0
      · subst i
        exact hbound.1
      · rw [Znth_cons (d := 0) (n := i) (a := a) (l := l) (by omega)]
        apply ih (i - 1) hbound.2
        rw [Zlength_cons] at hi
        omega

theorem lowerbound_Znth (x : Int) (l : List Int) (i : Int)
    (hbound : lowerbound x l) (hi : 0 <= i /\ i < Zlength l) :
    x <= Znth i l 0 := by
  induction l generalizing i with
  | nil => simp [Zlength] at hi; omega
  | cons a l ih =>
      by_cases hi0 : i = 0
      · subst i
        exact hbound.1
      · rw [Znth_cons (d := 0) (n := i) (a := a) (l := l) (by omega)]
        apply ih (i - 1) hbound.2
        rw [Zlength_cons] at hi
        omega

theorem upperbound_intro_Znth (x : Int) (l : List Int)
    (hpoint : forall i, 0 <= i /\ i < Zlength l -> Znth i l 0 <= x) :
    upperbound x l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
      constructor
      · simpa using hpoint 0 (by simp [Zlength])
      · apply ih
        intro i hi
        have h := hpoint (i + 1) (by
          rw [Zlength_cons]
          omega)
        rw [Znth_cons (d := 0) (n := i + 1) (a := a) (l := l) (by omega)] at h
        simpa using h

theorem lowerbound_intro_Znth (x : Int) (l : List Int)
    (hpoint : forall i, 0 <= i /\ i < Zlength l -> x <= Znth i l 0) :
    lowerbound x l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
      constructor
      · simpa using hpoint 0 (by simp [Zlength])
      · apply ih
        intro i hi
        have h := hpoint (i + 1) (by
          rw [Zlength_cons]
          omega)
        rw [Znth_cons (d := 0) (n := i + 1) (a := a) (l := l) (by omega)] at h
        simpa using h

theorem strict_upperbound_app (x : Int) (l : List Int) (v : Int)
    (hbound : strict_upperbound x l) (hv : v < x) :
    strict_upperbound x (l ++ [v]) := by
  induction l with
  | nil => exact ⟨hv, trivial⟩
  | cons _ l ih => exact ⟨hbound.1, ih hbound.2⟩

theorem upperbound_app (x : Int) (l : List Int) (v : Int)
    (hbound : strict_upperbound x l) (hv : v < x) :
    strict_upperbound x (l ++ [v]) :=
  strict_upperbound_app x l v hbound hv

theorem strict_lowerbound_cons (x : Int) (l : List Int) (v : Int)
    (hbound : strict_lowerbound x l) (hv : x < v) :
    strict_lowerbound x (v :: l) :=
  ⟨hv, hbound⟩

theorem lowerbound_app_cons (x : Int) (l : List Int) (y : Int)
    (hbound : lowerbound x l) (hy : x <= y) :
    lowerbound x (l ++ [y]) := by
  induction l with
  | nil => exact ⟨hy, trivial⟩
  | cons _ l ih => exact ⟨hbound.1, ih hbound.2⟩

theorem lowerbound_trans (x y : Int) (l : List Int) (hxy : x <= y)
    (hbound : lowerbound y l) : lowerbound x l := by
  induction l with
  | nil => trivial
  | cons _ l ih => exact ⟨Int.le_trans hxy hbound.1, ih hbound.2⟩

theorem lowerbound_perm (x : Int) (l1 l2 : List Int)
    (hperm : Permutation l1 l2) (hbound : lowerbound x l1) :
    lowerbound x l2 := by
  induction hperm with
  | nil => exact hbound
  | cons _ _ ih => exact ⟨hbound.1, ih hbound.2⟩
  | swap _ _ _ => exact ⟨hbound.2.1, hbound.1, hbound.2.2⟩
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hbound)

theorem upperbound_sublist_elim (x : Int) (l : List Int) (lo hi i : Int)
    (hlohi : 0 <= lo /\ lo <= hi) (hhi : hi <= Zlength l)
    (hbound : upperbound x (sublist lo hi l)) (hirange : lo <= i /\ i < hi) :
    Znth i l 0 <= x := by
  have hlenNat := sublist_length lo hi l hlohi hhi
  have hlen : Zlength (sublist lo hi l) = hi - lo := by
    unfold Zlength
    rw [hlenNat]
    exact Int.toNat_of_nonneg (by omega)
  have hlocal := upperbound_Znth x (sublist lo hi l) (i - lo) hbound (by
    rw [hlen]
    omega)
  rw [Znth_sublist (d := 0) (lo := lo) (i := i - lo) (hi := hi)
    (l := l) hlohi.1 (by omega)] at hlocal
  simpa only [Int.sub_add_cancel] using hlocal

theorem upperbound_sublist_intro (x : Int) (l : List Int) (lo hi : Int)
    (hlohi : 0 <= lo /\ lo <= hi) (hhi : hi <= Zlength l)
    (hrange : forall i, lo <= i /\ i < hi -> Znth i l 0 <= x) :
    upperbound x (sublist lo hi l) := by
  apply upperbound_intro_Znth
  intro i hirange
  have hlenNat := sublist_length lo hi l hlohi hhi
  have hlen : Zlength (sublist lo hi l) = hi - lo := by
    unfold Zlength
    rw [hlenNat]
    exact Int.toNat_of_nonneg (by omega)
  rw [Znth_sublist (d := 0) (lo := lo) (i := i) (hi := hi)
    (l := l) hlohi.1 (by rw [hlen] at hirange; omega)]
  apply hrange
  omega

theorem lowerbound_sublist_elim (x : Int) (l : List Int) (lo hi i : Int)
    (hlohi : 0 <= lo /\ lo <= hi) (hhi : hi <= Zlength l)
    (hbound : lowerbound x (sublist lo hi l)) (hirange : lo <= i /\ i < hi) :
    x <= Znth i l 0 := by
  have hlenNat := sublist_length lo hi l hlohi hhi
  have hlen : Zlength (sublist lo hi l) = hi - lo := by
    unfold Zlength
    rw [hlenNat]
    exact Int.toNat_of_nonneg (by omega)
  have hlocal := lowerbound_Znth x (sublist lo hi l) (i - lo) hbound (by
    rw [hlen]
    omega)
  rw [Znth_sublist (d := 0) (lo := lo) (i := i - lo) (hi := hi)
    (l := l) hlohi.1 (by omega)] at hlocal
  simpa only [Int.sub_add_cancel] using hlocal

theorem lowerbound_sublist_intro (x : Int) (l : List Int) (lo hi : Int)
    (hlohi : 0 <= lo /\ lo <= hi) (hhi : hi <= Zlength l)
    (hrange : forall i, lo <= i /\ i < hi -> x <= Znth i l 0) :
    lowerbound x (sublist lo hi l) := by
  apply lowerbound_intro_Znth
  intro i hirange
  have hlenNat := sublist_length lo hi l hlohi hhi
  have hlen : Zlength (sublist lo hi l) = hi - lo := by
    unfold Zlength
    rw [hlenNat]
    exact Int.toNat_of_nonneg (by omega)
  rw [Znth_sublist (d := 0) (lo := lo) (i := i) (hi := hi)
    (l := l) hlohi.1 (by rw [hlen] at hirange; omega)]
  apply hrange
  omega

def list_insert (i : Int) : List Int -> List Int
  | [] => [i]
  | h :: t => if i <= h then i :: h :: t else h :: list_insert i t

def sort : List Int -> List Int
  | [] => []
  | h :: t => list_insert h (sort t)

theorem list_insert_In (x a : Int) (l : List Int) :
    In x (list_insert a l) <-> In x l ∨ x = a := by
  induction l with
  | nil => simp [list_insert]
  | cons h t ih =>
      simp only [list_insert]
      split
      · simp only [List.mem_cons]
        constructor
        · intro hx
          rcases hx with hxa | hxh | hxt
          · exact Or.inr hxa
          · exact Or.inl (Or.inl hxh)
          · exact Or.inl (Or.inr hxt)
        · intro hx
          rcases hx with (hxh | hxt) | hxa
          · exact Or.inr (Or.inl hxh)
          · exact Or.inr (Or.inr hxt)
          · exact Or.inl hxa
      · simp only [List.mem_cons, ih]
        constructor
        · intro hx
          rcases hx with hxh | hxt | hxa
          · exact Or.inl (Or.inl hxh)
          · exact Or.inl (Or.inr hxt)
          · exact Or.inr hxa
        · intro hx
          rcases hx with (hxh | hxt) | hxa
          · exact Or.inl hxh
          · exact Or.inr (Or.inl hxt)
          · exact Or.inr (Or.inr hxa)

theorem increasing_aux_list_insert (a : Int) (l : List Int) (x : Int)
    (hinc : increasing_aux l x) (hxa : x <= a) :
    increasing_aux (list_insert a l) x := by
  induction l generalizing x with
  | nil => exact ⟨hxa, trivial⟩
  | cons y l ih =>
      by_cases hay : a <= y
      · rw [list_insert, if_pos hay]
        change x <= a /\ a <= y /\ increasing_aux l y
        exact ⟨hxa, hay, hinc.2⟩
      · rw [list_insert, if_neg hay]
        change x <= y /\ increasing_aux (list_insert a l) y
        exact ⟨hinc.1, ih y hinc.2 (by omega)⟩

theorem increasing_list_insert (a : Int) (l : List Int)
    (hinc : increasing l) : increasing (list_insert a l) := by
  cases l with
  | nil => trivial
  | cons y l =>
      by_cases hay : a <= y
      · rw [list_insert, if_pos hay]
        change a <= y /\ increasing_aux l y
        exact ⟨hay, hinc⟩
      · rw [list_insert, if_neg hay]
        change increasing_aux (list_insert a l) y
        exact increasing_aux_list_insert a l y hinc (by omega)

theorem sort_list_increasing (l : List Int) : increasing (sort l) := by
  induction l with
  | nil => trivial
  | cons a l ih => exact increasing_list_insert a (sort l) ih

theorem list_insert_perm (x : Int) (l : List Int) :
    Permutation (x :: l) (list_insert x l) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
      simp only [list_insert]
      by_cases hxa : x <= a
      · simp only [hxa, if_pos]
        exact .refl _
      · simp only [hxa]
        exact (List.Perm.swap a x l).trans (ih.cons a)

theorem sort_list_perm (l : List Int) : Permutation l (sort l) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih => exact (ih.cons a).trans (list_insert_perm a (sort l))

theorem interval_list_compress (l : List Int) (pace lo1 hi1 lo2 hi2 : Int)
    (hinterval : interval_list pace lo1 hi1 l)
    (_hlo : lo1 <= lo2) (_hhi : hi2 <= hi1)
    (hvalid : Forall (fun x => lo2 <= x ∧ x + pace <= hi2) l) :
    interval_list pace lo2 hi2 l := by
  induction hinterval with
  | interval_list_nil => exact .interval_list_nil
  | interval_list_cons l x hl _hxlo _hxhi hsep ih =>
      cases hvalid with
      | cons hx htail =>
          exact .interval_list_cons l x (ih htail) hx.1 hx.2 hsep

theorem increasing_interval_list_range (l : List Int) (pace lo hi : Int)
    (hpace : pace >= 0) (hlohi : lo <= hi)
    (hinterval : interval_list pace lo hi l) (hinc : increasing l) :
    lo + Zlength l * (pace + 1) <= hi + pace + 1 := by
  induction l generalizing lo with
  | nil =>
      simp [Zlength]
      omega
  | cons a l ih =>
      cases hinterval with
      | interval_list_cons _ _ htail halo hahi hsep =>
          have htailInterval : interval_list pace (a + pace + 1) hi l := by
            apply interval_list_compress l pace lo hi (a + pace + 1) hi htail
            · omega
            · exact Int.le_refl hi
            · have hvalid := interval_list_valid3 l pace lo hi htail
              rw [Forall.iff_forall_mem] at hvalid ⊢
              intro x hx
              have hxbound := hvalid x hx
              have hxsep := hsep.mem hx
              have hax := increasing_aux_head_le_all_In l a x hinc hx
              constructor
              · rcases hxsep with h | h <;> omega
              · exact hxbound.2
          have htailInc : increasing l :=
            increasing_aux_tail_increasing l a hinc
          cases l with
          | nil =>
              simp [Zlength]
              omega
          | cons b bs =>
              have htailValid :=
                interval_list_valid3 (b :: bs) pace lo hi htail
              have hb := htailValid.mem (by simp : b ∈ b :: bs)
              have hbsep := hsep.mem (by simp : b ∈ b :: bs)
              have hab :=
                increasing_aux_head_le_all_In (b :: bs) a b hinc (by simp)
              have htailLoHi : a + pace + 1 <= hi := by omega
              have hrec := ih (lo := a + pace + 1) htailLoHi htailInterval htailInc
              rw [Zlength_cons]
              calc
                lo + (Zlength (b :: bs) + 1) * (pace + 1) =
                    lo + Zlength (b :: bs) * (pace + 1) + (pace + 1) := by
                  rw [Int.add_mul]
                  ac_rfl
                _ <= a + Zlength (b :: bs) * (pace + 1) + (pace + 1) := by
                  omega
                _ = (a + pace + 1) + Zlength (b :: bs) * (pace + 1) := by
                  ac_rfl
                _ <= hi + pace + 1 := hrec

theorem interval_list_range (l : List Int) (pace lo hi : Int)
    (hpace : pace >= 0) (hlohi : lo <= hi)
    (hinterval : interval_list pace lo hi l) :
    lo + Zlength l * (pace + 1) <= hi + pace + 1 := by
  have hp : Permutation l (sort l) := sort_list_perm l
  have hlen : Zlength l = Zlength (sort l) := by
    unfold Zlength
    rw [hp.length_eq]
  rw [hlen]
  exact increasing_interval_list_range (sort l) pace lo hi hpace hlohi
    (interval_perm_keep l (sort l) pace lo hi hinterval hp)
    (sort_list_increasing l)

private theorem length_replace_nth {A : Type u} (l : List A) (n : Nat) (v : A) :
    (replace_nth n l v).length = l.length := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [replace_nth, List.length_cons]
          rw [ih]

theorem Zlength_replace_Znth {A : Type u} (l : List A) (n : Int) (v : A) :
    Zlength (replace_Znth n v l) = Zlength l := by
  unfold Zlength replace_Znth
  rw [length_replace_nth]
