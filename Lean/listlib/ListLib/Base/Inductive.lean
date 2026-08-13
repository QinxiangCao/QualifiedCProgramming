import ListLib.Base.Positional

namespace ListLib

theorem list_snoc_destruct {A : Type} (l : List A) :
    l = [] \/ exists a l', l = l' ++ [a] := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a l ih =>
      cases ih with
      | inl h =>
          subst l
          exact Or.inr ⟨a, [], rfl⟩
      | inr h =>
          rcases h with ⟨b, l', rfl⟩
          exact Or.inr ⟨b, a :: l', by simp⟩

theorem app_eq_app {A : Type} (l1 l2 l3 l4 : List A) :
    l1 ++ l2 = l3 ++ l4 ->
      (exists m, l1 = l3 ++ m /\ l4 = m ++ l2) \/
      (exists m, l3 = l1 ++ m /\ l2 = m ++ l4) := by
  induction l1 generalizing l3 with
  | nil =>
      intro h
      exact Or.inr ⟨l3, rfl, by simpa using h⟩
  | cons a l1 ih =>
      intro h
      cases l3 with
      | nil => exact Or.inl ⟨a :: l1, rfl, by simpa using h.symm⟩
      | cons b l3 =>
          simp only [List.cons_append, List.cons.injEq] at h
          rcases h with ⟨rfl, h⟩
          cases ih l3 h with
          | inl hm =>
              rcases hm with ⟨m, hm1, hm2⟩
              exact Or.inl ⟨m, by simp [hm1], hm2⟩
          | inr hm =>
              rcases hm with ⟨m, hm1, hm2⟩
              exact Or.inr ⟨m, by simp [hm1], hm2⟩

end ListLib
