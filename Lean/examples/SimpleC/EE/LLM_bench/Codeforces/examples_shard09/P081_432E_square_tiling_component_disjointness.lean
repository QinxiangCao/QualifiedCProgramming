import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_exchange_fallback
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem Znth_rev_inrange__solver_final {A : Type} (l : List A) (d : A) (k : Int) :
    (0≤k ∧ k<Zlength l) → Znth k l.reverse d=Znth (Zlength l-1-k) l d := by
  intro hk
  have hk' : k.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hk; omega
  simp only [Znth,List.getD,List.getElem?_reverse hk']
  congr 2
  simp only [Zlength,Int.ofNat_eq_coe] at hk ⊢
  omega

theorem same_color_path_sym__solver_final (grid : List (List Int)) (p q : Cell) :
    SameColorPath grid p q → SameColorPath grid q p := by
  intro hpath
  have hc := same_color_path_endpoint_color__solver_final grid p q hpath
  obtain ⟨path,hne,hfirst,hlast,hall,hsteps⟩ := hpath
  have hl : 0<Zlength path := by
    cases path with
    | nil => contradiction
    | cons a l => have h:=Zlength_nonneg l; rw [Zlength_cons]; omega
  have hlrev : Zlength path.reverse=Zlength path := by simp [Zlength]
  refine ⟨path.reverse,by simpa using hne,?_,?_,?_,?_⟩
  · rw [Znth_rev_inrange__solver_final path (0,0) 0 (by omega),sub_zero]
    exact hlast
  · rw [hlrev,Znth_rev_inrange__solver_final path (0,0) (Zlength path-1) (by omega),sub_self]
    exact hfirst
  · rw [Forall.iff_forall_mem] at hall ⊢
    intro x hx
    obtain ⟨hr,hcol,hc'⟩ := hall x (List.mem_reverse.mp hx)
    exact ⟨hr,hcol,hc'.trans hc.symm⟩
  · intro k hk
    rw [hlrev] at hk
    rw [Znth_rev_inrange__solver_final path (0,0) k (by omega),Znth_rev_inrange__solver_final path (0,0) (k+1) (by omega)]
    apply adjcell_sym__solver_final
    have h := hsteps (Zlength path-2-k) (by omega)
    convert h using 1 <;> congr 1 <;> omega

theorem same_color_path_trans__solver_final (grid : List (List Int)) (p x q : Cell) :
    SameColorPath grid p x → SameColorPath grid x q → SameColorPath grid p q := by
  intro hpx hxq
  have hcolor := same_color_path_endpoint_color__solver_final grid p x hpx
  refine same_color_path_closed__solver_final grid (Znth x.2 (Znth x.1 grid []) 0)
    (fun y => SameColorPath grid p y) x q hxq hpx ?_ rfl
  intro a b hpa hbr hbc hcol hadj
  exact same_color_path_append__solver_final grid p a b hpa hbr hbc (hcol.trans hcolor) hadj

theorem exact_components_rectangles_disjoint__solver_final (grid : List (List Int)) (n m ai aj aside bi bj bside : Int) :
    (0≤ai ∧ ai<n) → (0≤aj ∧ aj<m) → (0≤bi ∧ bi<n) → (0≤bj ∧ bj<m) →
    1≤aside → ai+aside≤n → aj+aside≤m → 1≤bside → bi+bside≤n → bj+bside≤m →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath grid (ai,aj) x ↔ (ai≤x.1 ∧ x.1<ai+aside) ∧ (aj≤x.2 ∧ x.2<aj+aside))) →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath grid (bi,bj) x ↔ (bi≤x.1 ∧ x.1<bi+bside) ∧ (bj≤x.2 ∧ x.2<bj+bside))) → ai*m+aj≠bi*m+bj →
    ∀ x : Cell, (ai≤x.1 ∧ x.1<ai+aside) → (aj≤x.2 ∧ x.2<aj+aside) → ¬((bi≤x.1 ∧ x.1<bi+bside) ∧ (bj≤x.2 ∧ x.2<bj+bside)) := by
  intro hai haj hbi hbj has hain hajm hbs hbin hbjm hac hbc hne x hxr hxc hbrect
  have hr : 0≤x.1 ∧ x.1<n := by omega
  have hc : 0≤x.2 ∧ x.2<m := by omega
  have hax := (hac x hr hc).mpr ⟨hxr,hxc⟩
  have hbx := (hbc x hr hc).mpr hbrect
  have hab := same_color_path_trans__solver_final grid (ai,aj) x (bi,bj) hax (same_color_path_sym__solver_final grid (bi,bj) x hbx)
  have hba := same_color_path_sym__solver_final grid (ai,aj) (bi,bj) hab
  have ha := (hac (bi,bj) hbi hbj).mp hab
  have hb := (hbc (ai,aj) hai haj).mp hba
  have hr : ai=bi := by dsimp at ha hb; omega
  have hc : aj=bj := by dsimp at ha hb; omega
  exact hne (by rw [hr,hc])

theorem disjoint_rectangles_separate__solver_final (ar ac aside br bc bside : Int) :
    1≤aside → 1≤bside →
    (∀ x : Cell, (ar≤x.1 ∧ x.1<ar+aside) → (ac≤x.2 ∧ x.2<ac+aside) → ¬((br≤x.1 ∧ x.1<br+bside) ∧ (bc≤x.2 ∧ x.2<bc+bside))) →
    ar+aside≤br ∨ br+bside≤ar ∨ ac+aside≤bc ∨ bc+bside≤ac := by
  intro has hbs hd
  by_contra hn
  have hr1 : ar≤max ar br ∧ max ar br<ar+aside := by omega
  have hr2 : br≤max ar br ∧ max ar br<br+bside := by omega
  have hc1 : ac≤max ac bc ∧ max ac bc<ac+aside := by omega
  have hc2 : bc≤max ac bc ∧ max ac bc<bc+bside := by omega
  exact hd (max ar br,max ac bc) hr1 hc1 ⟨hr2,hc2⟩

theorem earlier_component_excluded_from_candidate_square__solver_final (n m : Int) (output : List Int) (output_grid candidate : List (List Int))
    (first current_i current_j current_side candidate_side : Int) (q : Cell) (oi oj oside : Int) (x : Cell) :
    1≤n → 1≤m → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤current_i ∧ current_i<n) → (0≤current_j ∧ current_j<m) → 1≤current_side → current_i+current_side≤n → current_j+current_side≤m →
    1≤candidate_side → current_i+candidate_side≤n → current_j+candidate_side≤m → current_side<candidate_side →
    first=current_i*m+(current_j+current_side) → (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ z : Cell, (0≤z.1 ∧ z.1<n) → (0≤z.2 ∧ z.2<m) →
      (SameColorPath candidate (current_i,current_j) z ↔ (current_i≤z.1 ∧ z.1<current_i+candidate_side) ∧ (current_j≤z.2 ∧ z.2<current_j+candidate_side))) →
    (0≤oi ∧ oi<n) → (0≤oj ∧ oj<m) → 1≤oside → oi+oside≤n → oj+oside≤m →
    (oi≤q.1 ∧ q.1<oi+oside) → (oj≤q.2 ∧ q.2<oj+oside) → oi*m+oj<current_i*m+current_j →
    (∀ z : Cell, (0≤z.1 ∧ z.1<n) → (0≤z.2 ∧ z.2<m) →
      (SameColorPath output_grid q z ↔ (oi≤z.1 ∧ z.1<oi+oside) ∧ (oj≤z.2 ∧ z.2<oj+oside))) →
    (oi≤x.1 ∧ x.1<oi+oside) → (oj≤x.2 ∧ x.2<oj+oside) →
    (current_i≤x.1 ∧ x.1<current_i+candidate_side) → (current_j≤x.2 ∧ x.2<current_j+candidate_side) → False := by
  intro hn hm hrows ht hci hcj hcs hcin hcjm hcan hcanin hcanjm hcross hf hp hcc hoi hoj hos hoin hojm hqoi hqoj ha hoc hxoi hxoj hxci hxcj
  have hqr : 0≤q.1 ∧ q.1<n := by omega
  have hqc : 0≤q.2 ∧ q.2<m := by omega
  obtain ⟨other,ho,hon,hom,hocand⟩ := candidate_component_at_output_member__solver_final n m output candidate output_grid q oi oj oside first
    hn hm hrows ht hqr hqc hoi hoj hos hoin hojm hqoi hqoj (by omega) hp hoc
  have hd := exact_components_rectangles_disjoint__solver_final candidate n m oi oj other current_i current_j candidate_side
    hoi hoj hci hcj ho hon hom hcan hcanin hcanjm hocand hcc (by omega)
  have hnotshort (hb : oi*m+(oj+other)<first) : oside≤other :=
    candidate_component_not_short_before_member__solver_final n m output candidate output_grid q oi oj oside other first
      hn hm hrows ht hqr hqc hoi hoj hos hoin hojm hqoi hqoj ho hon hom hb hp hoc hocand
  rcases disjoint_rectangles_separate__solver_final oi oj other current_i current_j candidate_side ho hcan hd with habove | hbelow | hleft | hright
  · have hlong := hnotshort (by nlinarith [hcj.1])
    exact hd x (by omega) (by omega) ⟨hxci,hxcj⟩
  · omega
  · have hile : oi≤current_i := by
      by_contra hgt
      have : current_i<oi := by omega
      nlinarith [hoj.1,hcj.2]
    have hlong := hnotshort (by nlinarith)
    exact hd x (by omega) (by omega) ⟨hxci,hxcj⟩
  · omega
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
