import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_prefixes

set_option linter.unusedVariables false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

theorem StructuralLexLe_refl (values : List Int) : StructuralLexLe values values := by
  induction values with
  | nil => exact SLL_nil _
  | cons x values ih => exact SLL_eq _ _ _ ih

theorem StructuralLexLe_app (pref left right : List Int) (hl : StructuralLexLe left right) :
    StructuralLexLe (pref ++ left) (pref ++ right) := by
  induction pref with
  | nil => exact hl
  | cons x pref ih => exact SLL_eq _ _ _ ih

theorem StructuralLexLe_trans (left middle : List Int) (hf : StructuralLexLe left middle) :
    ∀ right, StructuralLexLe middle right → StructuralLexLe left right := by
  induction hf with
  | SLL_nil middle => intro right hs; exact SLL_nil _
  | SLL_lt x y left middle hxy =>
    intro right hs
    cases hs with
    | SLL_lt y z middle right hyz => exact SLL_lt _ _ _ _ (by omega)
    | SLL_eq y middle right ht => exact SLL_lt _ _ _ _ hxy
  | SLL_eq x left middle hf ih =>
    intro right hs
    cases hs with
    | SLL_lt x y middle right hxy => exact SLL_lt _ _ _ _ hxy
    | SLL_eq x middle right ht => exact SLL_eq _ _ _ (ih _ ht)

theorem StructuralLexLe_to_LexLe (left right : List Int) (hl : StructuralLexLe left right) :
    LexLe left right := by
  induction hl with
  | SLL_nil right =>
    cases right with
    | nil => exact Or.inl rfl
    | cons y right =>
      exact Or.inr (Or.inr ⟨by simp only [Zlength_nil, Zlength_cons]; have := Zlength_nonneg right; omega,
        ⟨y :: right, rfl⟩⟩)
  | SLL_lt x y left right hxy =>
    refine Or.inr (Or.inl ⟨0, ⟨by omega, ?_⟩, ?_, hxy⟩)
    · simp only [Zlength_cons]; have := Zlength_nonneg left; have := Zlength_nonneg right; omega
    · intro j hj; omega
  | SLL_eq x left right ht ih =>
    rcases ih with he | ⟨i, hi, he, hlt⟩ | ⟨hlen, suffix, hs⟩
    · exact Or.inl (congrArg (List.cons x) he)
    · refine Or.inr (Or.inl ⟨i + 1, ⟨by omega, by simp only [Zlength_cons]; omega⟩, ?_, ?_⟩)
      · intro j hj
        by_cases hz : j = 0
        · subst j; rfl
        · rw [Znth_cons 0 j x left (by omega), Znth_cons 0 j x right (by omega)]
          exact he (j - 1) ⟨by omega, by omega⟩
      · rw [Znth_cons 0 (i + 1) x left (by omega), Znth_cons 0 (i + 1) x right (by omega),
          show i + 1 - 1 = i by omega]
        exact hlt
    · exact Or.inr (Or.inr ⟨by simp only [Zlength_cons]; omega, ⟨suffix, by simp [hs]⟩⟩)

theorem LexLe_to_StructuralLexLe (left right : List Int) (hl : LexLe left right) :
    StructuralLexLe left right := by
  induction left generalizing right with
  | nil => exact SLL_nil _
  | cons x left ih =>
    cases right with
    | nil =>
      rcases hl with he | ⟨i, hi, he, hlt⟩ | ⟨hlen, hp⟩
      · contradiction
      · simp only [Zlength_nil] at hi; omega
      · simp only [Zlength_nil, Zlength_cons] at hlen; have := Zlength_nonneg left; omega
    | cons y right =>
      rcases hl with he | ⟨i, hi, he, hlt⟩ | ⟨hlen, suffix, hs⟩
      · cases he
        exact StructuralLexLe_refl _
      · by_cases hz : i = 0
        · subst i
          exact SLL_lt _ _ _ _ hlt
        · have hxy : x = y := he 0 ⟨by omega, by omega⟩
          subst y
          apply SLL_eq
          apply ih
          refine Or.inr (Or.inl ⟨i - 1, ⟨by omega, by simp only [Zlength_cons] at hi; omega⟩, ?_, ?_⟩)
          · intro j hj
            have hh := he (j + 1) ⟨by omega, by omega⟩
            rw [Znth_cons 0 (j + 1) x left (by omega), Znth_cons 0 (j + 1) x right (by omega),
              show j + 1 - 1 = j by omega] at hh
            exact hh
          · rw [Znth_cons 0 i x left (by omega), Znth_cons 0 i x right (by omega)] at hlt
            exact hlt
      · have he := List.cons.inj hs
        obtain ⟨rfl, hr⟩ := he
        apply SLL_eq
        apply ih
        exact Or.inr (Or.inr ⟨by simp only [Zlength_cons] at hlen; omega, ⟨suffix, hr⟩⟩)

theorem LexLe_trans (left middle right : List Int) (hf : LexLe left middle) (hs : LexLe middle right) :
    LexLe left right := StructuralLexLe_to_LexLe _ _
      (StructuralLexLe_trans _ _ (LexLe_to_StructuralLexLe _ _ hf) _ (LexLe_to_StructuralLexLe _ _ hs))

theorem LexLe_common_prefix_lt (pref : List Int) (x : Int) (left : List Int) (y : Int)
    (right : List Int) (hxy : x < y) : LexLe (pref ++ x :: left) (pref ++ y :: right) :=
  StructuralLexLe_to_LexLe _ _ (StructuralLexLe_app _ _ _ (SLL_lt _ _ _ _ hxy))

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
