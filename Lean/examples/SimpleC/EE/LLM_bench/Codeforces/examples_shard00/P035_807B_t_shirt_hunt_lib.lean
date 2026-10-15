import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib
open AUXLib


open MaxMinLib

def ShirtSelection (score place : Int) : Prop :=
  ∃ values, Zlength values = 26 ∧ Znth 0 values 0 = Z.modulo (Z.div score 50) 475 ∧
    (∀ i, (0 ≤ i ∧ i < 25) → Znth (i + 1) values 0 = Z.modulo (Znth i values 0 * 96 + 42) 475) ∧
    ∃ i, (1 ≤ i ∧ i ≤ 25) ∧ place = 26 + Znth i values 0

def GoalWithHacks (p x y successful : Int) : Prop :=
  ∃ unsuccessful, 0 ≤ unsuccessful ∧ y ≤ x + 100 * successful - 50 * unsuccessful ∧
    ShirtSelection (x + 100 * successful - 50 * unsuccessful) p

def Pre (p x y : Int) : Prop :=
  (26 ≤ p ∧ p ≤ 500) ∧ (1 ≤ y ∧ y ≤ x) ∧ x ≤ 20000 ∧ ∃ successful, 0 ≤ successful ∧ GoalWithHacks p x y successful

def Spec (p x y out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun successful : Int => 0 ≤ successful ∧ GoalWithHacks p x y successful) (fun successful => successful) out

def ShirtTrace (score : Int) (values : List Int) : Prop :=
  Zlength values = 26 ∧ Znth 0 values 0 = Z.modulo (Z.div score 50) 475 ∧
    ∀ i, (0 ≤ i ∧ i < 25) → Znth (i + 1) values 0 = Z.modulo (Znth i values 0 * 96 + 42) 475

def NoShirtSelection (score place : Int) : Prop := ¬ ShirtSelection score place

def ShirtScanState (score place scanned current : Int) : Prop :=
  ∃ values, ShirtTrace score values ∧ (0 ≤ scanned ∧ scanned ≤ 25) ∧ current = Znth scanned values 0 ∧
    (∀ i, (1 ≤ i ∧ i ≤ scanned) → place ≠ 26 + Znth i values 0)

def AlignmentSearch (x y score : Int) : Prop :=
  y ≤ score ∧ ∀ candidate, (y ≤ candidate ∧ candidate < score) → Z.modulo (candidate - x) 50 ≠ 0

def CandidateSearch (place x y score : Int) : Prop :=
  y ≤ score ∧ Z.modulo (score - x) 50 = 0 ∧ ∀ candidate,
    (y ≤ candidate ∧ candidate < score) → Z.modulo (candidate - x) 50 = 0 → NoShirtSelection candidate place

def FirstWinningCandidate (place x y score : Int) : Prop := CandidateSearch place x y score ∧ ShirtSelection score place

private theorem app_left (a b : List Int) (i : Int) (h : 0≤i ∧ i<Zlength a) :
    Znth i (a++b) 0=Znth i a 0 := ListLib.app_Znth1 0 a b i h
private theorem app_right (a b : List Int) (i : Int) (h : Zlength a≤i) :
    Znth i (a++b) 0=Znth (i-Zlength a) b 0 := ListLib.app_Znth2 0 a b i h
private theorem modulo (a b : Int) (hb : 0≤b) : Z.modulo a b=a%b := Int.fmod_eq_emod_of_nonneg a hb
private theorem division (a b : Int) (hb : 0≤b) : Z.div a b=a/b := Int.fdiv_eq_ediv_of_nonneg a hb
private theorem rem_zero (a b : Int) (hb : 0<b) : Z.rem a b=0 ↔ Z.modulo a b=0 := by
  rw [modulo a b (by omega)]
  exact Int.dvd_iff_tmod_eq_zero.symm.trans Int.dvd_iff_emod_eq_zero
private theorem mod_bounds (a b : Int) (hb : 0<b) : 0≤Z.modulo a b ∧ Z.modulo a b<b := by
  rw [modulo a b (by omega)]
  exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hb⟩
private theorem div_mod (a b : Int) (hb : 0<b) : a=b*Z.div a b+Z.modulo a b := by
  rw [modulo a b (by omega),division a b (by omega)]
  exact (Int.mul_ediv_add_emod a b).symm

theorem shirt_trace_prefix_exists__wins_scan (score : Int) (n : Nat) :
    ∃ values,Zlength values=(n:Int)+1 ∧ Znth 0 values 0=Z.modulo (Z.div score 50) 475 ∧
      ∀ i,(0≤i ∧ i<(n:Int)) → Znth (i+1) values 0=Z.modulo (Znth i values 0*96+42) 475 := by
  induction n with
  | zero =>
    refine ⟨[Z.modulo (Z.div score 50) 475],rfl,rfl,?_⟩
    intro i hi; omega
  | succ n ih =>
    rcases ih with ⟨v,hl,hseed,hstep⟩
    let z := Z.modulo (Znth (n:Int) v 0*96+42) 475
    have hl' : Zlength (v++[z])=(n:Int)+2 := by rw [Zlength_app,Zlength_cons,Zlength_nil,hl]; omega
    refine ⟨v++[z],by simpa only [Nat.cast_add,Nat.cast_one] using hl',?_,?_⟩
    · rw [app_left v [z] 0 ⟨by omega,by omega⟩]; exact hseed
    · intro i hi
      by_cases he:i<(n:Int)
      · rw [app_left v [z] (i+1) ⟨by omega,by omega⟩,app_left v [z] i ⟨by omega,by omega⟩]
        exact hstep i ⟨hi.1,he⟩
      · have hh : i=(n:Int) := by omega
        subst i
        rw [app_right v [z] ((n:Int)+1) (by omega),hl,Int.sub_self,app_left v [z] (n:Int) ⟨by omega,by omega⟩]
        rfl

theorem shirt_trace_exists__wins_scan (score : Int) : ∃ values,ShirtTrace score values := by
  exact shirt_trace_prefix_exists__wins_scan score 25

theorem shirt_trace_unique_prefix__wins_scan (score : Int) (v₁ v₂ : List Int)
    (h₁ : ShirtTrace score v₁) (h₂ : ShirtTrace score v₂) (i : Int) (hi : 0≤i ∧ i≤25) :
    Znth i v₁ 0=Znth i v₂ 0 := by
  have hn : ∀n:Nat,(n:Int)≤25 → Znth (n:Int) v₁ 0=Znth (n:Int) v₂ 0 := by
    intro n
    induction n with
    | zero => intro _; exact h₁.2.1.trans h₂.2.1.symm
    | succ n ih =>
      intro hn
      have hb : 0≤(n:Int) ∧ (n:Int)<25 := by omega
      rw [Nat.cast_add,Nat.cast_one,h₁.2.2 (n:Int) hb,h₂.2.2 (n:Int) hb,ih (by omega)]
  have hh := hn i.toNat (by omega)
  simpa only [Int.toNat_of_nonneg hi.1] using hh

theorem shirt_scan_state_step__wins_scan (score place i z : Int) (hi : i<25)
    (hs : ShirtScanState score place i z) (hn : place≠26+Z.modulo (z*96+42) 475) :
    ShirtScanState score place (i+1) (Z.modulo (z*96+42) 475) := by
  rcases hs with ⟨v,ht,hb,hz,hm⟩
  refine ⟨v,ht,⟨by omega,by omega⟩,?_,?_⟩
  · rw [ht.2.2 i ⟨hb.1,hi⟩,hz]
  · intro j hj
    by_cases he:j=i+1
    · rw [he,ht.2.2 i ⟨hb.1,hi⟩,← hz]; exact hn
    · exact hm j ⟨hj.1,by omega⟩

theorem alignment_search_extend__alignment_search (x y score : Int) (hs : AlignmentSearch x y score)
    (hr : Z.rem (score-x) 50≠0) : AlignmentSearch x y (score+1) := by
  refine ⟨by have h:=hs.1; omega,?_⟩
  intro c hc
  by_cases he:c<score
  · exact hs.2 c ⟨hc.1,he⟩
  · have hh : c=score := by omega
    rw [hh]
    exact fun h => hr ((rem_zero _ _ (by omega)).mpr h)

theorem alignment_search_full_window__alignment_search (x y score : Int) (hy : y≤x)
    (hw : 0≤score-y ∧ score-y≤49) (hs : AlignmentSearch x y score) (hr : Z.rem (score-x) 50≠0) : score-y<49 := by
  by_contra hn
  have he : score-y=49 := by omega
  let c := y+Z.modulo (x-y) 50
  have hm := mod_bounds (x-y) 50 (by omega)
  have hcm : Z.modulo (c-x) 50=0 := by
    dsimp only [c]
    rw [modulo _ _ (by omega),modulo _ _ (by omega)]
    rw [show y+(x-y)%50-x=(x-y)%50-(x-y) by ring,Int.sub_emod]
    simp
  have hc : c≤score := by dsimp only [c]; omega
  have hne : c≠score := by intro h; rw [h] at hcm; exact hr ((rem_zero _ _ (by omega)).mpr hcm)
  exact hs.2 c ⟨by dsimp only [c]; omega,by omega⟩ hcm

theorem alignment_to_candidate_search__alignment_search (place x y score : Int)
    (hr : Z.rem (score-x) 50=0) (hs : AlignmentSearch x y score) : CandidateSearch place x y score := by
  refine ⟨hs.1,(rem_zero _ _ (by omega)).mp hr,?_⟩
  intro c hc halign
  exact False.elim (hs.2 c hc halign)

theorem shirt_selection_period__candidate_capacity (score place k : Int) (hs : ShirtSelection score place) :
    ShirtSelection (score+50*475*k) place := by
  rcases hs with ⟨v,hl,hseed,hstep,j,hj,hp⟩
  refine ⟨v,hl,?_,hstep,j,hj,hp⟩
  rw [hseed,division score 50 (by omega),division _ 50 (by omega),modulo _ 475 (by omega),modulo _ 475 (by omega)]
  rw [show score+50*475*k=score+(475*k)*50 by ring,Int.add_mul_ediv_right _ _ (by omega)]
  rw [show score/50+475*k=score/50+k*475 by ring,Int.add_mul_emod_self_right]

theorem candidate_search_room__candidate_capacity (place x y score : Int) (hp : Pre place x y)
    (hn : NoShirtSelection score place) (hs : CandidateSearch place x y score) (hb : score≤x+50*475) : score<x+50*475 := by
  by_contra hnot
  have he : score=x+50*475 := by omega
  rcases hp with ⟨_,hy,_,s,hsnon,u,hunon,hwin,hselect⟩
  let t := 2*s-u
  have hturn : x+100*s-50*u=x+50*t := by dsimp only [t]; ring
  rw [hturn] at hselect
  have hnorm := shirt_selection_period__candidate_capacity (x+50*t) place (-Z.div t 475) hselect
  have hdm := div_mod t 475 (by omega)
  have hm := mod_bounds t 475 (by omega)
  have hnume : x+50*t+50*475*(-Z.div t 475)=x+50*Z.modulo t 475 := by omega
  rw [hnume] at hnorm
  have halign : Z.modulo (x+50*Z.modulo t 475-x) 50=0 := by
    rw [modulo _ 50 (by omega)]
    rw [show x+50*Z.modulo t 475-x=Z.modulo t 475*50 by ring,Int.mul_emod_left]
  exact hs.2.2 _ ⟨by omega,by omega⟩ halign hnorm

private theorem aligned_difference (x lower upper : Int) (hl : Z.modulo (lower-x) 50=0)
    (hu : Z.modulo (upper-x) 50=0) : Z.modulo (upper-lower) 50=0 := by
  rw [modulo _ 50 (by omega)] at hl hu ⊢
  rw [show upper-lower=(upper-x)-(lower-x) by ring,Int.sub_emod,hl,hu]
  decide

theorem candidate_search_step__candidate_transitions (place x y score : Int) (hs : CandidateSearch place x y score)
    (hn : NoShirtSelection score place) : CandidateSearch place x y (score+50) := by
  refine ⟨by have h:=hs.1; omega,?_,?_⟩
  · have hm := hs.2.1
    rw [modulo _ 50 (by omega)] at hm ⊢
    rw [show score+50-x=(score-x)+50 by ring,Int.add_emod,hm]
    decide
  · intro c hc halign
    by_cases hlt:c<score
    · exact hs.2.2 c ⟨hc.1,hlt⟩ halign
    · have hh := aligned_difference x score c hs.2.1 halign
      rw [modulo _ 50 (by omega),Int.emod_eq_of_lt (by omega) (by omega)] at hh
      have he : c=score := by omega
      rw [he]; exact hn

theorem aligned_gap_at_least_fifty__candidate_transitions (x lower upper : Int)
    (hl : Z.modulo (lower-x) 50=0) (hu : Z.modulo (upper-x) 50=0) (hlt : lower<upper) : lower+50≤upper := by
  have hh := aligned_difference x lower upper hl hu
  by_contra hn
  rw [modulo _ 50 (by omega),Int.emod_eq_of_lt (by omega) (by omega)] at hh
  omega

theorem aligned_ceiling_decomposition__final_result (d : Int) (hd : 0<d) (hm : Z.modulo d 50=0) :
    ∃ unsuccessful,0≤unsuccessful ∧ d=100*Z.div (d+99) 100-50*unsuccessful ∧
      ∀ successful,d≤100*successful → Z.div (d+99) 100≤successful := by
  have hdm := div_mod d 50 (by omega)
  have hceil := div_mod (d+99) 100 (by omega)
  have hmod := mod_bounds (d+99) 100 (by omega)
  refine ⟨2*Z.div (d+99) 100-Z.div d 50,by omega,by omega,?_⟩
  intro s hs
  omega

theorem first_winning_goal_lower_bound__final_result (place x y score successful : Int) (hpos : x<score)
    (hf : FirstWinningCandidate place x y score) (hs : 0≤successful) (hg : GoalWithHacks place x y successful) :
    Z.div (score-x+99) 100≤successful := by
  rcases hg with ⟨u,hu,hy,hselection⟩
  have halign : Z.modulo (x+100*successful-50*u-x) 50=0 := by
    rw [modulo _ 50 (by omega),show x+100*successful-50*u-x=(2*successful-u)*50 by ring,Int.mul_emod_left]
  have hscore : score≤x+100*successful-50*u := by
    by_contra hn
    exact hf.1.2.2 _ ⟨hy,by omega⟩ halign hselection
  rcases aligned_ceiling_decomposition__final_result (score-x) (by omega) hf.1.2.1 with ⟨_,_,_,hceil⟩
  exact hceil successful (by omega)

theorem zero_success_is_spec__final_result (place x y score : Int) (hscore : score≤x) (hy : y≤score)
    (hf : FirstWinningCandidate place x y score) : Spec place x y 0 := by
  have hm := hf.1.2.1
  have hd := div_mod (score-x) 50 (by omega)
  have he : x+100*0-50*(-Z.div (score-x) 50)=score := by omega
  refine ⟨0,⟨⟨by omega,-Z.div (score-x) 50,by omega,?_,?_⟩,?_⟩,rfl⟩
  · rw [he]; exact hy
  · rw [he]; exact hf.2
  · intro s hs; exact hs.1

theorem first_winning_is_spec__final_result (place x y score : Int) (hpos : x<score)
    (hf : FirstWinningCandidate place x y score) : Spec place x y (Z.div (score-x+99) 100) := by
  rcases aligned_ceiling_decomposition__final_result (score-x) (by omega) hf.1.2.1 with ⟨u,hu,he,hmin⟩
  have he' : x+100*Z.div (score-x+99) 100-50*u=score := by omega
  refine ⟨Z.div (score-x+99) 100,⟨⟨(show 0≤Z.div (score-x+99) 100 from Int.fdiv_nonneg (by omega) (by omega)),u,hu,?_,?_⟩,?_⟩,rfl⟩
  · rw [he']; exact hf.1.1
  · rw [he']; exact hf.2
  · intro s hs
    exact first_winning_goal_lower_bound__final_result place x y score s hpos hf hs.1 hs.2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib
