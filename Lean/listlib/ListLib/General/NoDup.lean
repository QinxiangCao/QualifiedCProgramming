import ListLib.Base.Positional

namespace ListLib

universe u

private theorem exists_append_cons_of_mem {A : Type u} {x : A} :
    forall l : List A, x ∈ l -> exists l1 l2, l = l1 ++ x :: l2
  | [], h => by cases h
  | y :: ys, h => by
      simp only [List.mem_cons] at h
      rcases h with hxy | hxys
      · cases hxy
        exact ⟨[], ys, rfl⟩
      · rcases exists_append_cons_of_mem ys hxys with ⟨l1, l2, hys⟩
        exact ⟨y :: l1, l2, by simp [hys]⟩

theorem Nodup_exists_repetition {A : Type u} (l : List A) :
    Not (NoDup l) ->
      exists x l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3 := by
  classical
  induction l with
  | nil =>
      intro h
      exfalso
      exact h (by simp [NoDup, AUXLib.NoDup])
  | cons a l ih =>
      intro h
      by_cases ha : a ∈ l
      · rcases exists_append_cons_of_mem l ha with ⟨l1, l2, hl⟩
        exact ⟨a, [], l1, l2, by simp [hl]⟩
      · have htail : Not (NoDup l) := by
          intro hnd
          apply h
          change (a :: l).Nodup
          exact List.nodup_cons.mpr ⟨ha, by simpa [NoDup, AUXLib.NoDup] using hnd⟩
        rcases ih htail with ⟨x, l1, l2, l3, hl⟩
        exact ⟨x, a :: l1, l2, l3, by simp [hl]⟩

theorem Nodup_split_constructors {A : Type u} (p1 p2 : List A) (e : A) :
    NoDup (p1 ++ e :: p2) ->
      Not (In e p1) /\ Not (In e p2) := by
  intro h
  change (p1 ++ e :: p2).Nodup at h
  have hsplit := List.nodup_append.mp h
  constructor
  · intro he
    exact hsplit.2.2 e he e (by simp) rfl
  · exact (List.nodup_cons.mp hsplit.2.1).1

theorem Nodup_app_comm {A : Type u} (l1 l2 : List A) :
    NoDup (l1 ++ l2) -> NoDup (l2 ++ l1) := by
  intro h
  change (l2 ++ l1).Nodup
  exact List.Perm.nodup List.perm_append_comm
    (by simpa [NoDup, AUXLib.NoDup] using h)

private def all_sublists {A : Type u} : List A -> List (List A)
  | [] => [[]]
  | a :: l =>
      let ll := all_sublists l
      ll ++ ll.map (fun x => a :: x)

private theorem all_sublists_spec {A : Type u} :
    forall l : List A,
      NoDup l ->
        (forall x, In x (all_sublists l) -> NoDup x /\ incl x l) /\
        (forall y, NoDup y -> incl y l ->
          exists x, In x (all_sublists l) /\ Permutation x y)
  | [], _ => by
      constructor
      · intro x hx
        change x ∈ ([[]] : List (List A)) at hx
        simp only [List.mem_singleton] at hx
        subst x
        exact ⟨by simp [NoDup, AUXLib.NoDup], by intro z hz; cases hz⟩
      · intro y hnodup hincl
        cases y with
        | nil =>
            exact ⟨[], by
              change [] ∈ ([[]] : List (List A))
              simp,
              by simp [Permutation, AUXLib.Permutation]⟩
        | cons b ys =>
            exfalso
            exact (by
              simpa [In, AUXLib.In] using hincl b (by simp))
  | a :: l, hnd => by
      change (a :: l).Nodup at hnd
      have hndParts := List.nodup_cons.mp hnd
      have hnotin : a ∉ l := hndParts.1
      have hndTail : NoDup l := by
        simpa [NoDup, AUXLib.NoDup] using hndParts.2
      rcases all_sublists_spec l hndTail with ⟨hsound, hcomplete⟩
      constructor
      · intro x hx
        change x ∈ all_sublists l ++ (all_sublists l).map (fun x => a :: x) at hx
        simp only [List.mem_append, List.mem_map] at hx
        rcases hx with hx | ⟨y, hy, hxy⟩
        · rcases hsound x hx with ⟨hxnd, hxincl⟩
          constructor
          · exact hxnd
          · intro z hz
            show z ∈ a :: l
            exact List.Mem.tail _ (hxincl z hz)
        · subst x
          rcases hsound y hy with ⟨hynd, hyincl⟩
          constructor
          · change (a :: y).Nodup
            apply List.nodup_cons.mpr
            constructor
            · intro hay
              exact hnotin (hyincl a hay)
            · simpa [NoDup, AUXLib.NoDup] using hynd
          · intro z hz
            change z ∈ a :: y at hz
            simp only [List.mem_cons] at hz
            rcases hz with hza | hzy
            · cases hza
              show a ∈ a :: l
              exact List.Mem.head _
            · show z ∈ a :: l
              exact List.Mem.tail _ (hyincl z hzy)
      · intro y hynodup hyincl
        classical
        by_cases hay : In a y
        · rcases exists_append_cons_of_mem y hay with ⟨y1, y2, hy⟩
          subst y
          have hndY : NoDup (y1 ++ a :: y2) := hynodup
          have hsplit := Nodup_split_constructors y1 y2 a hndY
          have hnotTail : a ∉ y1 ++ y2 := by
            intro haTail
            rcases List.mem_append.mp haTail with hy1 | hy2
            · exact hsplit.1 hy1
            · exact hsplit.2 hy2
          have hsub : List.Sublist (y1 ++ y2) (y1 ++ (a :: y2)) :=
            List.Sublist.append (List.Sublist.refl y1)
              (List.sublist_cons_self a y2)
          have hndTailY : NoDup (y1 ++ y2) := by
            change (y1 ++ y2).Nodup
            exact List.Sublist.nodup hsub hndY
          have hinclTail : incl (y1 ++ y2) l := by
            intro z hz
            have hzOrig : In z (y1 ++ a :: y2) := by
              have hzmem : z ∈ y1 ++ y2 := by
                simpa [In, AUXLib.In] using hz
              change z ∈ y1 ++ a :: y2
              simp only [List.mem_append, List.mem_cons] at hzmem ⊢
              rcases hzmem with hz1 | hz2
              · exact Or.inl hz1
              · exact Or.inr (Or.inr hz2)
            have hzAll := hyincl z hzOrig
            have hzAll' : z = a \/ z ∈ l := by
              simpa [In, AUXLib.In] using hzAll
            rcases hzAll' with hza | hzl
            · cases hza
              exact False.elim (hnotTail hz)
            · exact hzl
          rcases hcomplete (y1 ++ y2) hndTailY hinclTail with
            ⟨x, hxmem, hxperm⟩
          refine ⟨a :: x, ?_, ?_⟩
          · change a :: x ∈
              all_sublists l ++ (all_sublists l).map (fun x => a :: x)
            simp only [List.mem_append, List.mem_map]
            exact Or.inr ⟨x, hxmem, rfl⟩
          · change (a :: x).Perm (y1 ++ a :: y2)
            have hpermTail : x.Perm (y1 ++ y2) := by
              change x.Perm (y1 ++ y2) at hxperm
              exact hxperm
            exact (hpermTail.cons a).trans List.perm_middle.symm
        · have hinclTail : incl y l := by
            intro z hz
            have hzAll := hyincl z hz
            have hzAll' : z = a \/ z ∈ l := by
              simpa [In, AUXLib.In] using hzAll
            rcases hzAll' with hza | hzl
            · cases hza
              exact False.elim (hay hz)
            · exact hzl
          rcases hcomplete y hynodup hinclTail with ⟨x, hxmem, hxperm⟩
          refine ⟨x, ?_, hxperm⟩
          change x ∈ all_sublists l ++ (all_sublists l).map (fun x => a :: x)
          exact List.mem_append_left _ hxmem

theorem Nodup_all_sublists {A : Type u} (l : List A) :
    NoDup l ->
      exists ll : List (List A),
        (forall x, In x ll -> NoDup x /\ incl x l) /\
        (forall y, NoDup y -> incl y l ->
          exists x, In x ll /\ Permutation x y) := by
  intro h
  exact ⟨all_sublists l, all_sublists_spec l h⟩

end ListLib
