import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_extension_boundary
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

theorem extend_exchange_from_ih__solver_final (n m next : Int) (output : List Int) (output_grid candidate : List (List Int))
    (first lower : Int) (target q : Cell) (anchor : Int) (before painted : List Int) (i j side candidate_side : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) → first<next →
    65≤lower → Znth first (Flatten candidate) 0=lower → first=target.1*m+target.2 → anchor=i*m+j → anchor<first →
    GreedyPlacementTrace n m anchor before → SettledSquareState before n m i j lower side →
    PaintRectanglePrefix before painted m i j side lower (side*side) → (0≤i ∧ i<n) → (0≤j ∧ j<m) →
    (i≤q.1 ∧ q.1<i+side) → (j≤q.2 ∧ q.2<j+side) → Znth q.2 (Znth q.1 output_grid []) 0=lower →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath output_grid q x ↔ (i≤x.1 ∧ x.1<i+side) ∧ (j≤x.2 ∧ x.2<j+side))) →
    1≤candidate_side → i+candidate_side≤n → j+candidate_side≤m → side<candidate_side →
    (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
      (SameColorPath candidate (i,j) x ↔ (i≤x.1 ∧ x.1<i+candidate_side) ∧ (j≤x.2 ∧ x.2<j+candidate_side))) →
    (i≤target.1 ∧ target.1<i+candidate_side) → (j≤target.2 ∧ target.2<j+candidate_side) →
    P081ExchangeContinuation n m output output_grid candidate first anchor → Znth first output 0≤lower := by
  intro hn hm hout hrows ht hp hfn hl hcf hf ha hal hbefore hs hpaint hi hj hqi hqj hqcolor hcomp hcs hcin hcjm hcross hcc htri htci hext
  by_cases hle : Znth first output 0≤lower
  · exact hle
  · have hof : Znth first output 0≠lower := by omega
    have hplace := hs.1.2.1
    have hside := hplace.1
    have hin := hplace.2.1
    have hjm := hplace.2.2.1
    have htr : 0≤target.1 ∧ target.1<n := by omega
    have htc : 0≤target.2 ∧ target.2<m := by omega
    have hoc := exact_component_reanchor__solver_final output_grid n m q (i,j) i j side hrows.1
      (p081_rows_first_length n m output output_grid (by omega) hrows) hside hi.1 hj.1 hin hjm (by omega) (by omega) hqi hqj hi hj (by dsimp; omega) (by dsimp; omega) hcomp
    have hoa : Znth (i*m+j) output 0=lower := by
      rw [← rows_of_flat_Znth__solver_final n m output output_grid i j hrows hi hj]
      exact (same_color_path_endpoint_color__solver_final output_grid q (i,j) ((hcomp (i,j) hi hj).mpr (by dsimp; omega))).trans hqcolor
    have hfe := extend_first_is_frontier__solver_final n m output output_grid candidate first target i j lower side candidate_side
      hn hm hrows ht hi hj hside hin hjm hcross hcin hcjm htr htc hf htri htci (by omega) hp hoa hcf hof hoc hcc
    have hz : Znth anchor before 0=0 := by
      rw [ha]
      exact hplace.2.2.2.1 i j (by omega) (by omega)
    rcases hs.2 with hboundary | hcannot | ⟨fallback,hfallback,hfallle⟩
    · omega
    · exact False.elim (hcannot (extension_candidate_can_place__solver_final n m anchor next before output output_grid candidate first i j lower side candidate_side
        hn hm ha ⟨hal,hfn⟩ hbefore hout hrows ht hi hj hl hplace hcs hcin hcjm hcross hfe hp hcc hoa))
    · exact extend_fallback_from_ih__solver_final n m anchor next before painted output output_grid candidate first target q i j lower side candidate_side fallback
        hn hm ha ⟨hal,hfn⟩ hbefore hout hrows ht hf htr htc hi hj hs hz hpaint hqi hqj hqcolor hcomp hcs hcin hcjm hcross hcc htri htci hp hcf hof hfallback hfallle hext

theorem extend_exchange__solver_final (n m next : Int) (output : List Int) (output_grid candidate : List (List Int)) (first : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) → first<next →
    ∀ anchor, 0≤anchor → ∀ (lower : Int) (target q : Cell) (before painted : List Int) (i j side candidate_side : Int),
      65≤lower → Znth first (Flatten candidate) 0=lower → first=target.1*m+target.2 → anchor=i*m+j → anchor<first →
      GreedyPlacementTrace n m anchor before → SettledSquareState before n m i j lower side →
      PaintRectanglePrefix before painted m i j side lower (side*side) → (0≤i ∧ i<n) → (0≤j ∧ j<m) →
      (i≤q.1 ∧ q.1<i+side) → (j≤q.2 ∧ q.2<j+side) → Znth q.2 (Znth q.1 output_grid []) 0=lower →
      (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
        (SameColorPath output_grid q x ↔ (i≤x.1 ∧ x.1<i+side) ∧ (j≤x.2 ∧ x.2<j+side))) →
      1≤candidate_side → i+candidate_side≤n → j+candidate_side≤m → side<candidate_side →
      (∀ x : Cell, (0≤x.1 ∧ x.1<n) → (0≤x.2 ∧ x.2<m) →
        (SameColorPath candidate (i,j) x ↔ (i≤x.1 ∧ x.1<i+candidate_side) ∧ (j≤x.2 ∧ x.2<j+candidate_side))) →
      (i≤target.1 ∧ target.1<i+candidate_side) → (j≤target.2 ∧ target.2<j+candidate_side) → Znth first output 0≤lower := by
  intro hn hm hout hrows ht hp hfn
  apply nonnegative_anchor_strong_induction__solver_final
  intro anchor hanc ih lower target q before painted i j side cs hl hcf hf ha hal hbefore hs hpaint hi hj hqi hqj hqcolor hcomp hcs hcin hcjm hcross hcc htri htci
  apply extend_exchange_from_ih__solver_final n m next output output_grid candidate first lower target q anchor before painted i j side cs
    hn hm hout hrows ht hp hfn hl hcf hf ha hal hbefore hs hpaint hi hj hqi hqj hqcolor hcomp hcs hcin hcjm hcross hcc htri htci
  intro lower' target' q' earlier origin painted' oi oj oside other hl' hcf' hf' he' hlt' htr' hs' hp' hi' hj' hqr' hqc' hcolor' hcomp' hcs' hcin' hcjm' hcross' hcc' htri' htci'
  have hb := (trace_bounds_and_canonical__solver_final n m earlier origin hn hm htr').1
  exact ih earlier ⟨hb.1,hlt'⟩ lower' target' q' origin painted' oi oj oside other hl' hcf' hf' he' (by omega) htr' hs' hp' hi' hj' hqr' hqc' hcolor' hcomp' hcs' hcin' hcjm' hcross' hcc' htri' htci'

theorem first_difference_bound__solver_final (n m next : Int) (output : List Int) (output_grid candidate : List (List Int)) (first : Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next output → RowsOfFlat n m output output_grid → SquareTiling n m candidate →
    (0≤first ∧ first<next) → (∀ k, (0≤k ∧ k<first) → Znth k output 0=Znth k (Flatten candidate) 0) →
    Znth first output 0≤Znth first (Flatten candidate) 0 := by
  intro hn hm htrace hrows ht hfr hp
  by_cases heq : Znth first output 0=Znth first (Flatten candidate) 0
  · omega
  · have hb := trace_bounds_and_canonical__solver_final n m next output hn hm htrace
    let p : Cell := (first /ᶻ m,first mod m)
    have hmod : 0≤first mod m ∧ first mod m<m := ⟨Int.fmod_nonneg hfr.1 (by omega),Int.fmod_lt_of_pos first (by omega)⟩
    have hdiv : 0≤first /ᶻ m := Int.fdiv_nonneg hfr.1 (by omega)
    have hdecomp : first mod m+m*(first /ᶻ m)=first := Int.fmod_add_mul_fdiv first m
    have hpr : 0≤p.1 ∧ p.1<n := by
      change 0≤first /ᶻ m ∧ first /ᶻ m<n
      constructor
      · exact hdiv
      · have hnm := hb.1.2
        nlinarith [hmod.1]
    have hpc : 0≤p.2 ∧ p.2<m := hmod
    have hf : first=p.1*m+p.2 := by change first=(first /ᶻ m)*m+first mod m; nlinarith
    have hgnz : Znth p.2 (Znth p.1 output_grid []) 0≠0 := by
      rw [rows_of_flat_Znth__solver_final n m output output_grid p.1 p.2 hrows hpr hpc,← hf]
      have h := hb.2.2.2 first hfr
      omega
    obtain ⟨anchor,before,painted,i,j,color,side,ha,han,hbefore,hs,hpaint,hi,hj,hpri,hpci,hcolor,hcomp,hpersist⟩ :=
      trace_colored_component_origin__solver_final n m next output output_grid p hn hm htrace hrows hpr hpc hgnz
    have hplace := hs.1.2.1
    have houtfirst : Znth first output 0=color := by
      rw [hf,← rows_of_flat_Znth__solver_final n m output output_grid p.1 p.2 hrows hpr hpc]
      exact hcolor
    have hale : anchor≤first := by
      rw [ha,hf]
      exact square_anchor_le_member__solver_final m i j side p.1 p.2 hm hj.1 hpc.2 hpri hpci
    have hcontinuation : P081ExchangeContinuation n m output output_grid candidate first first := by
      intro lower target q earlier origin painted' oi oj oside other hl hcf hf' he hlt htr hset hp' hoi hoj hqr hqc hqcolor hoc hcs hcin hcjm hcross hcc htri htci
      have hb' := (trace_bounds_and_canonical__solver_final n m earlier origin hn hm htr).1
      exact extend_exchange__solver_final n m next output output_grid candidate first hn hm htrace hrows ht hp hfr.2 earlier hb'.1
        lower target q origin painted' oi oj oside other hl hcf hf' he hlt htr hset hp' hoi hoj hqr hqc hqcolor hoc hcs hcin hcjm hcross hcc htri htci
    rcases first_cell_component_dichotomy__solver_final n m output candidate output_grid first p anchor i j color side hn hm hrows ht hpr hpc hf ha hi hj
      hplace.1 hplace.2.1 hplace.2.2.1 hpri hpci houtfirst hcomp hale hp heq with horigin | ⟨cs,hcs,hcin,hcjm,hshort,hpi,hpj,hcc⟩
    · exact base_exchange_from_extend_ih__solver_final n m next output output_grid candidate first before i j color side hn hm htrace hrows ht hfr
        (by rw [← horigin]; exact ha) hi hj (by rw [← horigin]; exact hbefore) hs houtfirst hp hcontinuation
    · have hab := (trace_bounds_and_canonical__solver_final n m anchor before hn hm hbefore).1
      exact shrink_exchange_from_extend_ih__solver_final n m anchor next output output_grid candidate first before i j color side cs hn hm htrace hrows ht ha
        ⟨hab.1,han⟩ hi hj hbefore hs ⟨hcs,hshort⟩ (by rw [hf,hpi,hpj]) houtfirst hp
        (p081_continuation_mono n m output output_grid candidate first anchor first hale hcontinuation)

theorem greedy_trace_lex__solver_final (n m next : Int) (output : List Int) (candidate : List (List Int)) :
    1≤n → 1≤m → GreedyPlacementTrace n m next output → SquareTiling n m candidate → LexPrefixLe next output (Flatten candidate) := by
  intro hn hm ht hc
  have hb := trace_bounds_and_canonical__solver_final n m next output hn hm ht
  obtain ⟨grid,hrows⟩ := rows_of_flat_from_length__solver_final n m output hn hm hb.2.1
  apply local_first_difference_implies_lex__solver_final next output (Flatten candidate) hb.1.1
  intro first hf hp
  exact first_difference_bound__solver_final n m next output grid candidate first hn hm ht hrows hc hf hp

theorem greedy_trace_implies_partial_tiling__solver_final (n m next : Int) (flat : List Int) :
    1≤n → 1≤m → GreedyPlacementTrace n m next flat → PartialTilingState n m next flat := by
  intro hn hm ht
  exact greedy_trace_partial_from_lex__solver_final n m next flat hn hm ht (fun candidate hc => greedy_trace_lex__solver_final n m next flat candidate hn hm ht hc)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
