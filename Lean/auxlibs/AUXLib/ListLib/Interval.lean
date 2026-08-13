import AUXLib.ListLib.Arithmetic
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

inductive increasing : List Int -> Prop where
  | increasing_nil : increasing []
  | increasing_cons (x : Int) (l' : List Int) :
      increasing l' ->
      Forall (fun x' => x <= x') l' ->
      increasing (x :: l')

export increasing (increasing_nil increasing_cons)

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

private theorem increasing_list_insert (a : Int) (l : List Int)
    (hinc : increasing l) : increasing (list_insert a l) := by
  induction hinc with
  | increasing_nil => exact .increasing_cons a [] .increasing_nil .nil
  | increasing_cons x l hinc hforall ih =>
      simp only [list_insert]
      by_cases hax : a <= x
      · simp only [hax, if_pos]
        apply increasing.increasing_cons a (x :: l)
        · exact .increasing_cons x l hinc hforall
        · apply Forall.cons hax
          rw [Forall.iff_forall_mem] at hforall ⊢
          intro y hy
          exact Int.le_trans hax (hforall y hy)
      · simp only [hax]
        apply increasing.increasing_cons x (list_insert a l) ih
        rw [Forall.iff_forall_mem] at hforall ⊢
        intro y hy
        rcases (list_insert_In y a l).1 hy with hy | rfl
        · exact hforall y hy
        · omega

theorem sort_list_increasing (l : List Int) : increasing (sort l) := by
  induction l with
  | nil => exact .increasing_nil
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
          cases hinc with
          | increasing_cons _ _ hinct hforall =>
              cases l with
              | nil =>
                  simp [Zlength]
                  omega
              | cons b bs =>
                  have hab_inc : a <= b := hforall.mem (by simp)
                  have hab_sep : a + pace < b ∨ b + pace < a :=
                    hsep.mem (by simp)
                  have hab : a + pace + 1 <= b := by
                    rcases hab_sep with h | h <;> omega
                  have htail_valid :=
                    interval_list_valid3 (b :: bs) pace lo hi htail
                  have hnew_valid : Forall
                      (fun x => a + pace + 1 <= x ∧ x + pace <= hi) (b :: bs) := by
                    rw [Forall.iff_forall_mem]
                    intro x hx
                    have hax := hforall.mem hx
                    have hdisj := hsep.mem hx
                    have hxbound := htail_valid.mem hx
                    constructor
                    · rcases hdisj with h | h <;> omega
                    · exact hxbound.2
                  have hnew_lo : lo <= a + pace + 1 := by omega
                  have hnew_lo_hi : a + pace + 1 <= hi := by
                    have hb := htail_valid.mem (by simp : b ∈ b :: bs)
                    omega
                  have hcompressed :
                      interval_list pace (a + pace + 1) hi (b :: bs) :=
                    interval_list_compress (b :: bs) pace lo hi
                      (a + pace + 1) hi htail hnew_lo (Int.le_refl hi) hnew_valid
                  have hrec := ih (lo := a + pace + 1) hnew_lo_hi hcompressed hinct
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
