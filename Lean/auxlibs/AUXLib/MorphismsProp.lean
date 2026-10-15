import AUXLib.Morphisms

namespace AUXLib

namespace Morphisms_Prop

theorem and_iff_morphism {P P' Q Q' : Prop}
    (hP : P ↔ P') (hQ : Q ↔ Q') : (P ∧ Q) ↔ (P' ∧ Q') :=
  and_congr hP hQ

theorem or_iff_morphism {P P' Q Q' : Prop}
    (hP : P ↔ P') (hQ : Q ↔ Q') : (P ∨ Q) ↔ (P' ∨ Q') :=
  or_congr hP hQ

theorem ex_iff_morphism {A : Sort u} {P Q : A -> Prop}
    (h : forall x, P x ↔ Q x) : (Exists P) ↔ Exists Q := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (h x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (h x).mpr hx⟩

theorem all_iff_morphism {A : Sort u} {P Q : A -> Prop}
    (h : forall x, P x ↔ Q x) : (forall x, P x) ↔ forall x, Q x := by
  constructor
  · intro hall x
    exact (h x).mp (hall x)
  · intro hall x
    exact (h x).mpr (hall x)

end Morphisms_Prop

end AUXLib
