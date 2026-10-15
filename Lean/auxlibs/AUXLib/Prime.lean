import AUXLib.RelPrime

namespace AUXLib.Prime
export AUXLib.RelPrime (Zis_gcd Zis_gcd_intro rel_prime Zgcd_1_rel_prime)

-- Coq 8.20.1 theories/ZArith/Znumtheory.v:571.
inductive prime (p : Int) : Prop where
  | prime_intro : 1<p → (∀ n : Int, 1≤n ∧ n<p → rel_prime n p) → prime p

@[match_pattern] abbrev prime_intro (p : Int) (hp : 1<p)
    (hrel : ∀ n : Int, 1≤n ∧ n<p → rel_prime n p) : prime p :=
  prime.prime_intro hp hrel

-- Coq 8.20.1 theories/ZArith/Znumtheory.v:720,725,733.
theorem prime_ge_2 (p : Int) (hp : prime p) : 2≤p := by
  cases hp with
  | prime_intro h _ => omega

def prime' (p : Int) : Prop := 1<p ∧ ∀ n : Int, 1<n ∧ n<p → ¬Z.divide n p

theorem prime_alt (p : Int) : prime' p ↔ prime p := by
  constructor
  · rintro ⟨hp,hdiv⟩
    refine .prime_intro hp ?_
    intro n hn
    apply (Zgcd_1_rel_prime n p).1
    have hgpos := Int.gcd_pos_of_ne_zero_left p (by omega : n≠0)
    have hgle := Int.gcd_le_left p (by omega : 0<n)
    have hgd := Int.gcd_dvd_right n p
    have hg1 : Int.gcd n p=1 := by
      apply Classical.byContradiction
      intro hne
      exact hdiv (Int.gcd n p) (by omega) ((Z.divide_iff_dvd _ _).2 hgd)
    simp only [Z.gcd,hg1]
    rfl
  · intro hprime
    cases hprime with
    | prime_intro hp hrel =>
      refine ⟨hp,?_⟩
      intro n hn hdiv
      have hr := hrel n ⟨by omega,hn.2⟩
      cases hr with
      | Zis_gcd_intro _ _ hmin =>
        have hd := hmin n ⟨1,by simp⟩ hdiv
        have := Int.le_of_dvd (by omega : (0:Int)<1) ((Z.divide_iff_dvd _ _).1 hd)
        omega

-- Coq 8.20.1 theories/ZArith/Znumtheory.v:577.
theorem prime_divisors (p : Int) (hp : prime p) (a : Int) (ha : Z.divide a p) :
    a = -1 ∨ a = 1 ∨ a = p ∨ a = -p := by
  have hpOld := (prime_alt p).2 hp
  have hpgt := hpOld.1
  have hpos : ∀ d : Int, 0 < d → Z.divide d p → d = 1 ∨ d = p := by
    intro d hd hdiv
    have hle := Int.le_of_dvd (by omega : 0 < p) ((Z.divide_iff_dvd _ _).1 hdiv)
    by_cases hd1 : d = 1
    · exact .inl hd1
    by_cases hdp : d = p
    · exact .inr hdp
    exact False.elim (hpOld.2 d (by omega) hdiv)
  by_cases ha0 : 0 < a
  · rcases hpos a ha0 ha with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · have han : a ≠ 0 := by rintro rfl; rcases ha with ⟨q, hq⟩; simp at hq; have := hp.1; omega
    have hdiv : Z.divide (-a) p := by
      rcases ha with ⟨q,hq⟩
      exact ⟨-q, by grind⟩
    rcases hpos (-a) (by omega) hdiv with h | h
    · exact .inl (by omega)
    · exact .inr (.inr (.inr (by omega)))

-- Coq 8.20.1 theories/ZArith/Znumtheory.v:675.
theorem prime_mult (p : Int) (hp : prime p) (a b : Int) (hd : Z.divide p (a*b)) :
    Z.divide p a ∨ Z.divide p b := by
  simp only [Z.divide_iff_dvd] at hd ⊢
  by_cases hpa : p ∣ a
  · exact .inl hpa
  · right
    have hpOld := (prime_alt p).2 hp
    have hp2 := prime_ge_2 p hp
    have hgpos := Int.gcd_pos_of_ne_zero_left a (show p ≠ 0 by omega)
    have hgle := Int.gcd_le_left a (show 0 < p by omega)
    have hgd := Int.gcd_dvd_left p a
    have hgda := Int.gcd_dvd_right p a
    have hgne : (Int.gcd p a : Int) ≠ p := by
      intro heq
      exact hpa (heq ▸ hgda)
    have hg1 : Int.gcd p a = 1 := by
      apply Classical.byContradiction
      intro hn
      exact hpOld.2 (Int.gcd p a) (by omega) ((Z.divide_iff_dvd _ _).2 hgd)
    have hm := (Int.dvd_gcd_mul_iff_dvd_mul (k := p) (n := a) (m := b)).2 hd
    simpa [hg1] using hm

-- Coq 8.20.1 theories/ZArith/Znumtheory.v:936.
theorem not_prime_divide (p : Int) (hp : 1 < p) (hn : ¬prime p) :
    ∃ n : Int, (1 < n ∧ n < p) ∧ Z.divide n p := by
  classical
  apply Classical.byContradiction
  intro h
  apply hn
  apply (prime_alt p).1
  refine ⟨hp, ?_⟩
  intro n hr hd
  exact h ⟨n, hr, hd⟩
end AUXLib.Prime
