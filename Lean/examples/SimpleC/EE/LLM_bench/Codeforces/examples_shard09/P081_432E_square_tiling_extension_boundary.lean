import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_extension_empty
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

theorem candidate_boundary_cell_cannot_match__solver_final (n m anchor next : Int) (before output : List Int) (output_grid candidate : List (List Int))
    (first current_i current_j color current_side candidate_side : Int) (x y : Cell) :
    1≤n → 1≤m → anchor=current_i*m+current_j → (anchor<first ∧ first<next) → GreedyPlacementTrace n m anchor before →
    GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤current_i ∧ current_i<n) → (0≤current_j ∧ current_j<m) → 1≤current_side → current_i+current_side≤n → current_j+current_side≤m →
    1≤candidate_side → current_i+candidate_side≤n → current_j+candidate_side≤m → current_side<candidate_side →
    first=current_i*m+(current_j+current_side) → (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ z : Cell, (0≤z.1 ∧ z.1<n) → (0≤z.2 ∧ z.2<m) →
      (SameColorPath candidate (current_i,current_j) z ↔ (current_i≤z.1 ∧ z.1<current_i+candidate_side) ∧ (current_j≤z.2 ∧ z.2<current_j+candidate_side))) →
    65≤color → Znth (current_i*m+current_j) output 0=color → Znth (x.1*m+x.2) before 0=color →
    (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) → (0≤y.1 ∧ y.1<n) → (0≤y.2 ∧ y.2<m) →
    (current_i≤y.1 ∧ y.1<current_i+candidate_side) → (current_j≤y.2 ∧ y.2<current_j+candidate_side) → AdjCell y x → False := by
  intro hn hm ha hfr hbefore hout hrows ht hci hcj hcs hcin hcjm hcan hcanin hcanjm hcross hf hp hcc hcolor hoa hbx hxr hxc hyr hyc hyri hyci hadj
  have hnz : Znth (x.1*m+x.2) before 0≠0 := by omega
  obtain ⟨earlier,origin,painted,oi,oj,found,oside,he,hlt,htr,hos,hop,hoi,hoj,hxoi,hxoj,hfound,hcomp⟩ :=
    trace_existing_component_origin_before__solver_final n m anchor before next output output_grid x hn hm hbefore hout (by omega) hrows hxr hxc hnz
  have hplace := hos.1.2.1
  have hfc : found=color := by
    rw [← hfound,rows_of_flat_Znth__solver_final n m output output_grid x.1 x.2 hrows hxr hxc,
      greedy_trace_prefix_persistence__solver_final n m anchor next before output hn hm (by omega) hbefore hout (x.1*m+x.2)
        (p081_cell_index_bounds n m x (by omega) hxr hxc) hnz]
    exact hbx
  obtain ⟨other,ho,hon,hom,hlong,hoc⟩ := earlier_candidate_component_not_short__solver_final n m output output_grid candidate first current_i current_j current_side candidate_side x oi oj oside
    hn hm hrows ht hci hcj hcs hcin hcjm hcan hcanin hcanjm hcross hf hp hcc hoi hoj hplace.1 hplace.2.1 hplace.2.2.1 hxoi hxoj (by omega) hcomp
  have hcx := (hoc x hxr hxc).mpr (by omega)
  have hcrows := square_tiling_rows__solver_final n m candidate ht
  have hcl := hcrows.1
  have hcw := p081_rows_first_length n m (Flatten candidate) candidate (by omega) hcrows
  have hca : Znth oj (Znth oi candidate []) 0=found := by
    rw [rows_of_flat_Znth__solver_final n m (Flatten candidate) candidate oi oj hcrows hoi hoj,
      ← hp (oi*m+oj) ⟨(p081_cell_index_bounds n m (oi,oj) (by omega) hoi hoj).1,by omega⟩,
      ← rows_of_flat_Znth__solver_final n m output output_grid oi oj hrows hoi hoj]
    exact (same_color_path_endpoint_color__solver_final output_grid x (oi,oj) ((hcomp (oi,oj) hoi hoj).mpr (by dsimp; omega))).trans hfound
  have hcurrent : Znth current_j (Znth current_i candidate []) 0=color := by
    rw [rows_of_flat_Znth__solver_final n m (Flatten candidate) candidate current_i current_j hcrows hci hcj,
      ← hp (current_i*m+current_j) ⟨(p081_cell_index_bounds n m (current_i,current_j) (by omega) hci hcj).1,by omega⟩]
    exact hoa
  have hxcolor : Znth x.2 (Znth x.1 candidate []) 0=Znth current_j (Znth current_i candidate []) 0 :=
    (same_color_path_endpoint_color__solver_final candidate (oi,oj) x hcx).trans (hca.trans (hfc.trans hcurrent.symm))
  have hcy := (hcc y hyr hyc).mpr ⟨hyri,hyci⟩
  have hcurrentx := same_color_path_append__solver_final candidate (current_i,current_j) y x hcy (by omega) (by omega) hxcolor hadj
  have hxcurrent := (hcc x hxr hxc).mp hcurrentx
  exact exact_components_rectangles_disjoint__solver_final candidate n m oi oj other current_i current_j candidate_side
    hoi hoj hci hcj ho hon hom hcan hcanin hcanjm hoc hcc (by omega) x (by omega) (by omega) hxcurrent

theorem extension_candidate_can_place__solver_final (n m anchor next : Int) (before output : List Int) (output_grid candidate : List (List Int))
    (first i j color side candidate_side : Int) :
    1≤n → 1≤m → anchor=i*m+j → (anchor<first ∧ first<next) → GreedyPlacementTrace n m anchor before →
    GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤i ∧ i<n) → (0≤j ∧ j<m) → 65≤color → CanPlace before n m i j side color →
    1≤candidate_side → i+candidate_side≤n → j+candidate_side≤m → side<candidate_side → first=i*m+(j+side) →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    (∀ z : Cell, (0≤z.1 ∧ z.1<n) → (0≤z.2 ∧ z.2<m) →
      (SameColorPath candidate (i,j) z ↔ (i≤z.1 ∧ z.1<i+candidate_side) ∧ (j≤z.2 ∧ z.2<j+candidate_side))) →
    Znth (i*m+j) output 0=color → CanPlace before n m i j (side+1) color := by
  intro hn hm ha hfr hbefore hout hrows ht hi hj hcolor hplace hcs hcin hcjm hcross hf hp hcc hoa
  have hside := hplace.1
  have hin := hplace.2.1
  have hjm := hplace.2.2.1
  have hboundary := candidate_boundary_cell_cannot_match__solver_final n m anchor next before output output_grid candidate first i j color side candidate_side
  refine ⟨by omega,by omega,by omega,?_,?_,?_⟩
  · intro r c hr hc
    exact extension_candidate_square_empty__solver_final n m anchor next before output output_grid candidate first i j color side candidate_side
      hn hm ha hfr hbefore hout hrows ht hi hj hplace hcs hcin hcjm hcross hf hp hcc r c (by omega) (by omega)
  · intro c hc
    constructor
    · intro hit hmatch
      exact hboundary (i-1,c) (i,c) hn hm ha hfr hbefore hout hrows ht hi hj hside hin hjm hcs hcin hcjm hcross hf hp hcc hcolor hoa hmatch
        (by dsimp; omega) (by dsimp; omega) hi (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
        (by simp [AdjCell,Z.abs,show i-(i-1)=(1 : Int) by omega])
    · intro hib hmatch
      exact hboundary (i+(side+1),c) (i+side,c) hn hm ha hfr hbefore hout hrows ht hi hj hside hin hjm hcs hcin hcjm hcross hf hp hcc hcolor hoa hmatch
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
        (by simp [AdjCell,Z.abs,show i+side-(i+(side+1))=(-1 : Int) by omega])
  · intro r hr
    constructor
    · intro hjl hmatch
      have hmat : Znth (r*m+(j-1)) before 0=color := by simpa only [add_sub_assoc] using hmatch
      exact hboundary (r,j-1) (r,j) hn hm ha hfr hbefore hout hrows ht hi hj hside hin hjm hcs hcin hcjm hcross hf hp hcc hcolor hoa hmat
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) hj (by dsimp; omega) (by dsimp; omega)
        (by simp [AdjCell,Z.abs,show j-(j-1)=(1 : Int) by omega])
    · intro hjr hmatch
      have hmat : Znth (r*m+(j+(side+1))) before 0=color := by simpa only [add_assoc] using hmatch
      exact hboundary (r,j+(side+1)) (r,j+side) hn hm ha hfr hbefore hout hrows ht hi hj hside hin hjm hcs hcin hcjm hcross hf hp hcc hcolor hoa hmat
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
        (by simp [AdjCell,Z.abs,show j+side-(j+(side+1))=(-1 : Int) by omega])
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
