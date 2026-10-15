import ListLib.General.Forall
import ListLib.General.Length
import Std.Tactic

namespace ListLib

universe u v

def is_indexed_elements {A : Type u}
    (l : List A) (il : List Int) (l0 : List A) : Prop :=
  Forall2 (fun i a => Znth_error l i = some a) il l0

theorem is_indexed_elements_nil {A : Type u} (l : List A) :
    is_indexed_elements l [] [] := by
  exact AUXLib.Forall2.nil

theorem is_indexed_elements_cons {A : Type u}
    (l : List A) (i : Int) (a : A) (il : List Int) (l0 : List A) :
    Znth_error l i = some a ->
    is_indexed_elements l il l0 ->
    is_indexed_elements l (i :: il) (a :: l0) := by
  intro h1 h2
  exact AUXLib.Forall2.cons h1 h2

theorem is_indexed_elements_cons_iff {A : Type u}
    (l : List A) (i : Int) (a : A) (il : List Int) (l0 : List A) :
    is_indexed_elements l (i :: il) (a :: l0) <->
      Znth_error l i = some a /\ is_indexed_elements l il l0 := by
  constructor
  · intro h
    cases h with
    | cons h1 h2 => exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact AUXLib.Forall2.cons h1 h2

theorem is_indexed_elements_app {A : Type u}
    (l : List A) (il1 il2 : List Int) (l1 l2 : List A) :
    is_indexed_elements l il1 l1 ->
    is_indexed_elements l il2 l2 ->
    is_indexed_elements l (il1 ++ il2) (l1 ++ l2) := by
  intro h1 h2
  exact AUXLib.Forall2.append h1 h2

theorem is_indexed_elements_app_inv_r {A : Type u}
    (l : List A) (il' : List Int) (l1' l2' : List A) :
    is_indexed_elements l il' (l1' ++ l2') ->
    exists il1 il2 : List Int,
      is_indexed_elements l il1 l1' /\
      is_indexed_elements l il2 l2' /\
      il' = il1 ++ il2 := by
  intro h
  rcases AUXLib.Forall2_split_app2 Int A
      (fun i a => Znth_error l i = some a) il' l1' l2' h with
    ⟨il1, il2, hsplit, h1, h2⟩
  exact ⟨il1, il2, h1, h2, hsplit⟩

theorem is_indexed_elements_app_inv_l {A : Type u}
    (l : List A) (il1 il2 : List Int) (l' : List A) :
    is_indexed_elements l (il1 ++ il2) l' ->
    exists l1' l2' : List A,
      is_indexed_elements l il1 l1' /\
      is_indexed_elements l il2 l2' /\
      l' = l1' ++ l2' := by
  intro h
  rcases AUXLib.Forall2_split_app1 Int A
      (fun i a => Znth_error l i = some a) il1 il2 l' h with
    ⟨l1', l2', hsplit, h1, h2⟩
  exact ⟨l1', l2', h1, h2, hsplit⟩

theorem is_indexed_elements_nil_inv_l {A : Type u}
    (l : List A) (l0 : List A) :
    is_indexed_elements l [] l0 -> l0 = [] := by
  intro h
  exact Forall2_cons_nil_l l0 h

theorem is_indexed_elements_nil_inv_r {A : Type u}
    (l : List A) (il : List Int) :
    is_indexed_elements l il [] -> il = [] := by
  intro h
  exact Forall2_cons_nil_r il h

theorem is_indexed_elements_cons_inv_r {A : Type u}
    (l : List A) (il : List Int) (a : A) (l' : List A) :
    is_indexed_elements l il (a :: l') ->
    exists i il',
      il = i :: il' /\
      Znth_error l i = some a /\
      is_indexed_elements l il' l' := by
  intro h
  rcases Forall2_cons_inv_r il a l' h with ⟨i, il', hil, hia, hrest⟩
  exact ⟨i, il', hil, hia, hrest⟩

theorem is_indexed_elements_cons_inv_l {A : Type u}
    (l : List A) (i : Int) (il : List Int) (l' : List A) :
    is_indexed_elements l (i :: il) l' ->
    exists a l0',
      Znth_error l i = some a /\
      is_indexed_elements l il l0' /\
      l' = a :: l0' := by
  intro h
  rcases Forall2_cons_inv_l i il l' h with ⟨a, l0', hl', hia, hrest⟩
  exact ⟨a, l0', hia, hrest, hl'⟩

def sincr_aux : List Int -> Int -> Prop
  | [], _ => True
  | y :: l0, x => x < y /\ sincr_aux l0 y

def sincr (l : List Int) : Prop :=
  match l with
  | [] => True
  | x :: l0 => sincr_aux l0 x

theorem sincr_app_cons (l1 : List Int) (x : Int) (l2 : List Int) :
    sincr (l1 ++ [x]) ->
    sincr (x :: l2) ->
    sincr (l1 ++ x :: l2) := by
  intro h1 h2
  induction l1 with
  | nil =>
      simpa [sincr] using h2
  | cons a l1 ih =>
      cases l1 with
      | nil =>
          simp [sincr, sincr_aux] at h1 h2 ⊢
          exact ⟨h1, h2⟩
      | cons b bs =>
          simp [sincr, sincr_aux] at h1 ⊢
          exact ⟨h1.1, ih h1.2⟩

theorem sincr_app_cons_inv1 (l1 : List Int) (x : Int) (l2 : List Int) :
    sincr (l1 ++ x :: l2) ->
    sincr (l1 ++ [x]) := by
  intro h
  induction l1 with
  | nil =>
      trivial
  | cons a l1 ih =>
      cases l1 with
      | nil =>
          simp [sincr, sincr_aux] at h ⊢
          exact h.1
      | cons b bs =>
          simp [sincr, sincr_aux] at h ⊢
          exact ⟨h.1, ih h.2⟩

theorem sincr_app_cons_inv2 (l1 : List Int) (x : Int) (l2 : List Int) :
    sincr (l1 ++ x :: l2) ->
    sincr (x :: l2) := by
  intro h
  induction l1 with
  | nil =>
      simpa [sincr] using h
  | cons a l1 ih =>
      cases l1 with
      | nil =>
          simp [sincr, sincr_aux] at h ⊢
          exact h.2
      | cons b bs =>
          simp [sincr, sincr_aux] at h
          exact ih h.2

def is_subsequence {A : Type u} : List A -> List A -> Prop
  | [], [] => True
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a1 :: l1', a2 :: l2' =>
      is_subsequence (a1 :: l1') l2' \/
      a1 = a2 /\ is_subsequence l1' l2'

theorem sincr_add_1 (l : List Int) :
    sincr l ->
    sincr (l.map (fun z => z + 1)) := by
  intro h
  cases l with
  | nil => trivial
  | cons z zs =>
      revert z
      induction zs with
      | nil =>
          intro z h
          trivial
      | cons y ys ih =>
          intro z h
          simp [sincr, sincr_aux] at h ⊢
          exact ⟨by omega, ih y h.2⟩

theorem sincr_sub_1 (l : List Int) :
    sincr l ->
    sincr (l.map (fun z => z - 1)) := by
  intro h
  cases l with
  | nil => trivial
  | cons z zs =>
      revert z
      induction zs with
      | nil =>
          intro z h
          trivial
      | cons y ys ih =>
          intro z h
          simp [sincr, sincr_aux] at h ⊢
          exact ⟨by omega, ih y h.2⟩

theorem sincr_cons (a : Int) (l : List Int) :
    Forall (fun z => a < z) l ->
    sincr l ->
    sincr (a :: l) := by
  intro hall hs
  cases l with
  | nil => trivial
  | cons z zs =>
      cases hall with
      | cons hz _ =>
          exact ⟨hz, hs⟩

private theorem Forall_impl {A : Type u} {P Q : A -> Prop}
    {l : List A} :
    (forall x, P x -> Q x) -> Forall P l -> Forall Q l := by
  intro himpl h
  induction h with
  | nil => exact AUXLib.Forall.nil
  | cons hp _ ih => exact AUXLib.Forall.cons (himpl _ hp) ih

private theorem Forall2_impl {A : Type u} {B : Type v}
    {P Q : A -> B -> Prop} {xs : List A} {ys : List B} :
    (forall x y, P x y -> Q x y) -> Forall2 P xs ys -> Forall2 Q xs ys := by
  intro himpl h
  induction h with
  | nil => exact AUXLib.Forall2.nil
  | cons hp _ ih => exact AUXLib.Forall2.cons (himpl _ _ hp) ih

private theorem Forall_map {A : Type u} {B : Type v}
    (P : B -> Prop) (f : A -> B) (l : List A) :
    Forall (fun x => P (f x)) l -> Forall P (l.map f) := by
  intro h
  induction h with
  | nil => exact AUXLib.Forall.nil
  | cons hp _ ih => exact AUXLib.Forall.cons hp ih

private theorem Znth_error_cons_tail {A : Type u}
    (n : Int) (x : A) (l : List A) (a : A) :
    0 < n ->
    Znth_error (x :: l) n = some a ->
    Znth_error l (n - 1) = some a := by
  intro hnpos h
  have hn0 : n ≠ 0 := by omega
  have hn : n = n - 1 + 1 := by omega
  exact (Znth_error_cons (n - 1) n x l hn0 hn).symm.trans h

theorem sincr_cons_tail_Forall_lt (a : Int) (l : List Int) :
    sincr (a :: l) ->
    Forall (fun b => a < b) l := by
  intro h
  induction l generalizing a with
  | nil => exact AUXLib.Forall.nil
  | cons b bs ih =>
      simp [sincr, sincr_aux] at h
      exact AUXLib.Forall.cons h.1
        (Forall_impl (fun c hc => by omega) (ih b h.2))

theorem sincr_cons_Forall_lt (a0 a : Int) (l : List Int) :
    a0 < a ->
    sincr (a :: l) ->
    Forall (fun b => a0 < b) (a :: l) := by
  intro ha hs
  exact AUXLib.Forall.cons ha
    (Forall_impl (fun b hb => by omega)
      (sincr_cons_tail_Forall_lt a l hs))

theorem is_indexed_elements_range {A : Type u}
    (l : List A) (il : List Int) (l0 : List A) :
    is_indexed_elements l il l0 ->
    Forall (fun i => 0 <= i /\ i < Zlength l) il := by
  intro h
  induction h with
  | nil => exact AUXLib.Forall.nil
  | cons hia _ ih =>
      exact AUXLib.Forall.cons (Znth_error_range l _ _ hia) ih

theorem is_subsequence_inv {A : Type u} (l1 l2 : List A) :
    is_subsequence l1 l2 ->
    exists il, sincr il /\ is_indexed_elements l2 il l1 := by
  intro h
  revert l1
  induction l2 with
  | nil =>
      intro l1 h
      cases l1 with
      | nil =>
          exact ⟨[], trivial, is_indexed_elements_nil []⟩
      | cons a l1 =>
          contradiction
  | cons a l2 ih =>
      intro l1 h
      cases l1 with
      | nil =>
          exact ⟨[], trivial, is_indexed_elements_nil (a :: l2)⟩
      | cons a1 l1' =>
          rcases h with hskip | ⟨ha, htake⟩
          · rcases ih (a1 :: l1') hskip with ⟨il, hsincr, hidx⟩
            refine ⟨il.map (fun z => z + 1), sincr_add_1 il hsincr, ?_⟩
            change Forall2 (fun i b => Znth_error (a :: l2) i = some b)
              (il.map (fun z => z + 1)) (a1 :: l1')
            have hmap := Forall2_impl
              (fun n b hn =>
                Znth_error_Some_cons n (n + 1) a l2 b rfl hn)
              hidx
            exact (Forall2_map1
              (fun i b => Znth_error (a :: l2) i = some b)
              il (a1 :: l1') (fun z => z + 1)).mp hmap
          · subst a1
            rcases ih l1' htake with ⟨il, hsincr, hidx⟩
            refine ⟨0 :: il.map (fun z => z + 1), ?_, ?_⟩
            · apply sincr_cons
              · have hrange := is_indexed_elements_range l2 il l1' hidx
                exact Forall_map (fun z => 0 < z) (fun z => z + 1) il
                  (Forall_impl (fun z hz => by
                    change 0 < z + 1
                    have hz0 : 0 <= z := hz.1
                    omega) hrange)
              · exact sincr_add_1 il hsincr
            · apply is_indexed_elements_cons
              · exact Znth_error_cons_0 a l2
              · change Forall2 (fun i b => Znth_error (a :: l2) i = some b)
                  (il.map (fun z => z + 1)) l1'
                have hmap := Forall2_impl
                  (fun n b hn =>
                    Znth_error_Some_cons n (n + 1) a l2 b rfl hn)
                  hidx
                exact (Forall2_map1
                  (fun i b => Znth_error (a :: l2) i = some b)
                  il l1' (fun z => z + 1)).mp hmap

theorem is_subsequence_spec {A : Type u}
    (l1 l2 : List A) (il : List Int) :
    sincr il ->
    is_indexed_elements l2 il l1 ->
    is_subsequence l1 l2 := by
  intro hsincr hidx
  revert l1 il
  induction l2 with
  | nil =>
      intro l1 il hsincr hidx
      cases l1 with
      | nil => trivial
      | cons a l1 =>
          rcases is_indexed_elements_cons_inv_r [] il a l1 hidx with
            ⟨i, il', hil, hia, _⟩
          have hrange := Znth_error_range ([] : List A) i a hia
          change 0 <= i /\ i < (0 : Int) at hrange
          omega
  | cons a l2 ih =>
      intro l1 il hsincr hidx
      cases l1 with
      | nil => trivial
      | cons b l1' =>
          rcases is_indexed_elements_cons_inv_r (a :: l2) il b l1' hidx with
            ⟨i, il', hil, hia, hrest⟩
          subst il
          by_cases hi0 : i <= 0
          · have hizero : i = 0 := by
              have hrange := Znth_error_range (a :: l2) i b hia
              omega
            subst i
            have hb : b = a := by
              symm
              simpa using hia
            subst b
            right
            constructor
            · rfl
            · apply ih l1' (il'.map (fun z => z - 1))
              · apply sincr_sub_1
                cases il' with
                | nil => trivial
                | cons j js =>
                    simp [sincr, sincr_aux] at hsincr ⊢
                    exact hsincr.2
              · have htailForall := sincr_cons_tail_Forall_lt 0 il' hsincr
                change Forall2 (fun n c => Znth_error l2 n = some c)
                  (il'.map (fun z => z - 1)) l1'
                have hmap := Forall2_impl
                  (fun n c hn => Znth_error_cons_tail n a l2 c hn.1 hn.2)
                  (Forall2_and_Forall_l
                    (fun n => 0 < n)
                    (fun n c => Znth_error (a :: l2) n = some c)
                    il' l1' htailForall hrest)
                exact (Forall2_map1
                  (fun n c => Znth_error l2 n = some c)
                  il' l1' (fun z => z - 1)).mp hmap
          · left
            apply ih (b :: l1') ((i :: il').map (fun z => z - 1))
            · apply sincr_sub_1
              exact hsincr
            · have hforall := sincr_cons_Forall_lt 0 i il' (by omega) hsincr
              change Forall2 (fun n c => Znth_error l2 n = some c)
                ((i :: il').map (fun z => z - 1)) (b :: l1')
              have hmap := Forall2_impl
                (fun n c hn => Znth_error_cons_tail n a l2 c hn.1 hn.2)
                (Forall2_and_Forall_l
                  (fun n => 0 < n)
                  (fun n c => Znth_error (a :: l2) n = some c)
                  (i :: il') (b :: l1') hforall hidx)
              exact (Forall2_map1
                (fun n c => Znth_error l2 n = some c)
                (i :: il') (b :: l1') (fun z => z - 1)).mp hmap

end ListLib
