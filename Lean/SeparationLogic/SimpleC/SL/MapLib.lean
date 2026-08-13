import SimpleC.SL.StoreAux

namespace SimpleC.SL.MapLib

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

structure MapLibSig
    (_CRules : SeparationLogicSig)
    (_DePredSig : DerivedPredSig _CRules)
    (_SLibSig : StoreLibSig _CRules _DePredSig) : Type where

namespace MapLibSig

def canonical (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    MapLibSig CRules DePredSig SLibSig := {}

def store_map (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (m : A -> Option B) : CRules.expr :=
  CRules.exp (List A) fun l =>
    CRules.andp
      (CRules.coq_prop (forall a, a ∈ l <-> exists b, m a = some b))
      (CRules.andp (CRules.coq_prop (NoDup l))
        (CRules.toContext.iter_sepcon
          (l.map fun a => match m a with
            | some b => P a b
            | none => CRules.emp)))

def store_map_missing_i (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (m : A -> Option B) (i : A) : CRules.expr :=
  CRules.exp (List A) fun l =>
    CRules.andp
      (CRules.coq_prop
        (forall a, a ∈ l <-> (exists b, m a = some b) ∧ a ≠ i))
      (CRules.andp (CRules.coq_prop (NoDup l))
        (CRules.toContext.iter_sepcon
          (l.map fun a => match m a with
            | some b => P a b
            | none => CRules.emp)))

private theorem iter_sepcon_single_equiv (CRules : SeparationLogicSig)
    (P : CRules.expr) :
    CRules.logic_equiv (CRules.toContext.iter_sepcon [P]) P := by
  constructor
  · exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_comm CRules.emp P)
      (CRules.toContext.derivable1_sepcon_emp_l P)
  · exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_emp_r P)
      (CRules.toContext.derivable1_sepcon_comm P CRules.emp)

private theorem logic_equiv_sepcon_swap_middle (CRules : SeparationLogicSig)
    (P Q R : CRules.expr) :
    CRules.logic_equiv
      (CRules.sepcon P (CRules.sepcon Q R))
      (CRules.sepcon (CRules.sepcon P R) Q) := by
  constructor
  · exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.logic_equiv_sepcon_assoc P Q R).left <|
      CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.derivable1_sepcon_comm (CRules.sepcon P Q) R) <|
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.logic_equiv_sepcon_assoc R P Q).left <|
          CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_sepcon_comm R P)
            (CRules.toContext.derivable1_refl Q)
  · exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_sepcon_comm P R)
        (CRules.toContext.derivable1_refl Q)) <|
      CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.logic_equiv_sepcon_assoc R P Q).right <|
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_comm R (CRules.sepcon P Q)) <|
          (CRules.toContext.logic_equiv_sepcon_assoc P Q R).right

private theorem iter_sepcon_extract_middle (CRules : SeparationLogicSig)
    (xs zs : List CRules.expr) (P : CRules.expr) :
    CRules.derivable1
      (CRules.toContext.iter_sepcon (xs ++ P :: zs))
      (CRules.sepcon (CRules.toContext.iter_sepcon (xs ++ zs)) P) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_iter_sepcon2 xs (P :: zs)) <|
    CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_refl _)
        (CRules.toContext.derivable1_sepcon_iter_sepcon2 [P] zs)) <|
      CRules.toContext.derivable1_trans _ _ _
        (logic_equiv_sepcon_swap_middle CRules _ _ _).left <|
        CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_sepcon_iter_sepcon1 xs zs)
          (iter_sepcon_single_equiv CRules P).left

private theorem iter_sepcon_insert_middle (CRules : SeparationLogicSig)
    (xs zs : List CRules.expr) (P : CRules.expr) :
    CRules.derivable1
      (CRules.sepcon (CRules.toContext.iter_sepcon (xs ++ zs)) P)
      (CRules.toContext.iter_sepcon (xs ++ P :: zs)) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_mono _ _ _ _
      (CRules.toContext.derivable1_sepcon_iter_sepcon2 xs zs)
      (iter_sepcon_single_equiv CRules P).right) <|
    CRules.toContext.derivable1_trans _ _ _
      (logic_equiv_sepcon_swap_middle CRules _ _ _).right <|
      CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _)
          (CRules.toContext.derivable1_sepcon_iter_sepcon1 [P] zs)) <|
        CRules.toContext.derivable1_sepcon_iter_sepcon1 xs (P :: zs)

private theorem iter_sepcon_all_emp (CRules : SeparationLogicSig)
    (xs : List CRules.expr)
    (h : forall Q, Q ∈ xs -> CRules.logic_equiv Q CRules.emp) :
    CRules.logic_equiv (CRules.toContext.iter_sepcon xs) CRules.emp := by
  induction xs with
  | nil =>
      exact ⟨CRules.toContext.derivable1_refl _,
        CRules.toContext.derivable1_refl _⟩
  | cons x xs ih =>
      have hx : CRules.logic_equiv x CRules.emp := h x (by simp)
      have htail : forall Q, Q ∈ xs -> CRules.logic_equiv Q CRules.emp := by
        intro Q hQ
        exact h Q (by simp [hQ])
      have hxs := ih htail
      constructor
      · exact CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_iter_sepcon2 [x] xs) <|
          CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (CRules.toContext.derivable1_trans _ _ _
                (iter_sepcon_single_equiv CRules x).left hx.left)
              hxs.left)
            (CRules.toContext.derivable1_sepcon_emp_l CRules.emp)
      · exact CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_emp_r CRules.emp) <|
          CRules.toContext.derivable1_trans _ _ _
            (CRules.toContext.derivable1_sepcon_mono _ _ _ _
              (CRules.toContext.derivable1_trans _ _ _
                hx.right (iter_sepcon_single_equiv CRules x).right)
              hxs.right)
            (CRules.toContext.derivable1_sepcon_iter_sepcon1 [x] xs)

theorem store_map_split (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (a : A) (b : B) (m : A -> Option B)
    (hma : m a = some b) :
    CRules.derivable1 (store_map CRules P m)
      (CRules.sepcon (store_map_missing_i CRules P m a) (P a b)) := by
  intro state hstore
  rcases hstore with ⟨l, hsupp, hnodup, hiter⟩
  have ha : a ∈ l := (hsupp a).2 ⟨b, hma⟩
  rcases List.mem_iff_append.mp ha with ⟨l1, l2, rfl⟩
  have hparts := List.nodup_append.mp hnodup
  have htail := List.nodup_cons.mp hparts.2.1
  have ha_not_l1 : a ∉ l1 := by
    intro ha1
    exact hparts.2.2 a ha1 a (by simp) rfl
  have ha_not_l2 : a ∉ l2 := htail.1
  have hsupport : forall x,
      x ∈ l1 ++ l2 <-> (exists y, m x = some y) ∧ x ≠ a := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ l1 ++ a :: l2 := by
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        exact hx.elim Or.inl (fun h => Or.inr (Or.inr h))
      refine ⟨(hsupp x).1 hx', ?_⟩
      intro hxa
      subst x
      simp only [List.mem_append] at hx
      exact hx.elim ha_not_l1 ha_not_l2
    · rintro ⟨hex, hne⟩
      have hx := (hsupp x).2 hex
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hx | hxa | hx
      · exact Or.inl hx
      · exact False.elim (hne hxa)
      · exact Or.inr hx
  have hnd : NoDup (l1 ++ l2) := by
    apply List.Nodup.sublist
      (List.Sublist.append (.refl l1) (List.Sublist.cons a (.refl l2)))
    exact hnodup
  have hspatial := iter_sepcon_extract_middle CRules
    (l1.map fun x => match m x with
      | some y => P x y
      | none => CRules.emp)
    (l2.map fun x => match m x with
      | some y => P x y
      | none => CRules.emp)
    (P a b)
  simp only [List.map_append, List.map_cons, hma] at hiter
  rcases hspatial state hiter with ⟨s1, s2, hjoin, hleft, hright⟩
  exact ⟨s1, s2, hjoin, ⟨l1 ++ l2, hsupport, hnd, by
    simpa only [List.map_append] using hleft⟩, hright⟩

theorem store_map_merge (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (a : A) (b : B) (m : A -> Option B)
    (hma : m a = some b) :
    CRules.derivable1
      (CRules.sepcon (store_map_missing_i CRules P m a) (P a b))
      (store_map CRules P m) := by
  intro state hstore
  rcases hstore with ⟨s1, s2, hjoin, hmissing, hpa⟩
  rcases hmissing with ⟨l, hsupp, hnodup, hiter⟩
  have ha_not_l : a ∉ l := by
    intro ha
    exact (hsupp a).1 ha |>.2 rfl
  have hsupport : forall x,
      x ∈ a :: l <-> exists y, m x = some y := by
    intro x
    constructor
    · intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, hma⟩
      · exact (hsupp x).1 hx |>.1
    · intro hex
      by_cases hxa : x = a
      · exact List.mem_cons.mpr (Or.inl hxa)
      · exact List.mem_cons.mpr (Or.inr ((hsupp x).2 ⟨hex, hxa⟩))
  have hnd : NoDup (a :: l) := List.nodup_cons.mpr ⟨ha_not_l, hnodup⟩
  have hspatial := iter_sepcon_insert_middle CRules []
    (l.map fun x => match m x with
      | some y => P x y
      | none => CRules.emp)
    (P a b)
  have hsource : CRules.sepcon
      (CRules.toContext.iter_sepcon
        (l.map fun x => match m x with
          | some y => P x y
          | none => CRules.emp))
      (P a b) state := ⟨s1, s2, hjoin, hiter, hpa⟩
  refine ⟨a :: l, hsupport, hnd, ?_⟩
  simpa only [List.map_cons, hma] using hspatial state hsource

theorem store_map_missing_equiv_store_map
    (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (m : A -> Option B) (a : A)
    (hma : m a = none) :
    CRules.derivable1 (store_map_missing_i CRules P m a)
      (store_map CRules P m) := by
  intro state
  rintro ⟨l, hsupp, hnodup, hiter⟩
  refine ⟨l, ?_, hnodup, hiter⟩
  intro x
  constructor
  · intro hx
    exact (hsupp x).1 hx |>.1
  · intro hex
    apply (hsupp x).2
    refine ⟨hex, ?_⟩
    intro hxa
    subst x
    rcases hex with ⟨b, hb⟩
    rw [hma] at hb
    cases hb

theorem store_map_equiv_store_map_missing
    (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (m : A -> Option B) (a : A)
    (hma : m a = none) :
    CRules.derivable1 (store_map CRules P m)
      (store_map_missing_i CRules P m a) := by
  intro state
  rintro ⟨l, hsupp, hnodup, hiter⟩
  refine ⟨l, ?_, hnodup, hiter⟩
  intro x
  constructor
  · intro hx
    have hex := (hsupp x).1 hx
    refine ⟨hex, ?_⟩
    intro hxa
    subst x
    rcases hex with ⟨b, hb⟩
    rw [hma] at hb
    cases hb
  · intro hx
    exact (hsupp x).2 hx.1

theorem store_map_equiv (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (m m1 : A -> Option B)
    (hmm : forall a, m a = m1 a) :
    CRules.logic_equiv (store_map CRules P m) (store_map CRules P m1) := by
  have hmap : forall l : List A,
      l.map (fun a => match m a with
        | some b => P a b
        | none => CRules.emp) =
      l.map (fun a => match m1 a with
        | some b => P a b
        | none => CRules.emp) := by
    intro l
    apply List.map_congr_left
    intro a _
    rw [hmm a]
  constructor <;> intro state
  · rintro ⟨l, hsupp, hnodup, hiter⟩
    refine ⟨l, ?_, hnodup, ?_⟩
    · intro a
      rw [← hmm a]
      exact hsupp a
    · rw [← hmap l]
      exact hiter
  · rintro ⟨l, hsupp, hnodup, hiter⟩
    refine ⟨l, ?_, hnodup, ?_⟩
    · intro a
      rw [hmm a]
      exact hsupp a
    · rw [hmap l]
      exact hiter

theorem store_map_missing_i_equiv
    (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (m m1 : A -> Option B) (i : A)
    (hmm : forall a, a ≠ i -> m a = m1 a) :
    CRules.logic_equiv (store_map_missing_i CRules P m i)
      (store_map_missing_i CRules P m1 i) := by
  constructor <;> intro state
  · rintro ⟨l, hsupp, hnodup, hiter⟩
    have hpoint : forall a, a ∈ l -> m a = m1 a := by
      intro a ha
      exact hmm a ((hsupp a).1 ha).2
    have hmap : l.map (fun a => match m a with
          | some b => P a b
          | none => CRules.emp) =
        l.map (fun a => match m1 a with
          | some b => P a b
          | none => CRules.emp) := by
      apply List.map_congr_left
      intro a ha
      rw [hpoint a ha]
    refine ⟨l, ?_, hnodup, ?_⟩
    · intro a
      constructor
      · intro ha
        have hs := (hsupp a).1 ha
        rw [← hmm a hs.2]
        exact hs
      · intro hs
        apply (hsupp a).2
        rw [hmm a hs.2]
        exact hs
    · rw [← hmap]
      exact hiter
  · rintro ⟨l, hsupp, hnodup, hiter⟩
    have hpoint : forall a, a ∈ l -> m a = m1 a := by
      intro a ha
      exact hmm a ((hsupp a).1 ha).2
    have hmap : l.map (fun a => match m a with
          | some b => P a b
          | none => CRules.emp) =
        l.map (fun a => match m1 a with
          | some b => P a b
          | none => CRules.emp) := by
      apply List.map_congr_left
      intro a ha
      rw [hpoint a ha]
    refine ⟨l, ?_, hnodup, ?_⟩
    · intro a
      constructor
      · intro ha
        have hs := (hsupp a).1 ha
        rw [hmm a hs.2]
        exact hs
      · intro hs
        apply (hsupp a).2
        rw [← hmm a hs.2]
        exact hs
    · rw [hmap]
      exact hiter

theorem store_map_empty (CRules : SeparationLogicSig) {A B : Type}
    (P : A -> B -> CRules.expr) (m : A -> Option B)
    (hfinite : exists l,
      (forall a, a ∈ l <-> exists b, m a = some b) ∧ NoDup l)
    (hempty : forall a,
      m a = none ∨ (forall b, m a = some b -> CRules.logic_equiv (P a b) CRules.emp)) :
    CRules.logic_equiv (store_map CRules P m) CRules.emp := by
  constructor
  · intro state
    rintro ⟨l, hsupp, _hnodup, hiter⟩
    apply (iter_sepcon_all_emp CRules _ ?_).left state hiter
    intro Q hQ
    rcases List.mem_map.mp hQ with ⟨a, ha, rfl⟩
    have hex := (hsupp a).1 ha
    rcases hex with ⟨b, hb⟩
    rw [hb]
    rcases hempty a with hnone | hsome
    · rw [hnone] at hb
      cases hb
    · exact hsome b hb
  · rcases hfinite with ⟨l, hsupp, hnodup⟩
    intro state hemp
    refine ⟨l, hsupp, hnodup, ?_⟩
    apply (iter_sepcon_all_emp CRules _ ?_).right state hemp
    intro Q hQ
    rcases List.mem_map.mp hQ with ⟨a, ha, rfl⟩
    rcases hempty a with hnone | hsome
    · rw [hnone]
      exact ⟨CRules.toContext.derivable1_refl _,
        CRules.toContext.derivable1_refl _⟩
    · cases hma : m a with
      | none =>
          exact ⟨CRules.toContext.derivable1_refl _,
            CRules.toContext.derivable1_refl _⟩
      | some b => exact hsome b hma

end MapLibSig

end SimpleC.SL.MapLib
