import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib
open AUXLib


open MaxMinLib

def SegmentMex (a : List Int) (l r w : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun candidate : Int => 0 ≤ candidate ∧
    ∀ i, (l ≤ i ∧ i ≤ r) → Znth i a 0 ≠ candidate) (fun candidate => candidate) w

def OneSnap (before after : List Int) : Prop :=
  ∃ l r w, (0 ≤ l ∧ l ≤ r) ∧ r < Zlength before ∧ SegmentMex before l r w ∧
    Zlength after = Zlength before ∧ ∀ i, (0 ≤ i ∧ i < Zlength before) →
      Znth i after 0 = if l ≤ i ∧ i ≤ r then w else Znth i before 0

def SnapTrace (initial : List Int) (states : List (List Int)) : Prop :=
  0 < Zlength states ∧ Znth 0 states [] = initial ∧
  (∀ k, (0 ≤ k ∧ k < Zlength states - 1) → OneSnap (Znth k states []) (Znth (k + 1) states [])) ∧
  Forall (fun x => x = 0) (Znth (Zlength states - 1) states [])

def Pre (a : List Int) : Prop :=
  (1 ≤ Zlength a ∧ Zlength a ≤ 100000) ∧ Forall (fun x => 0 ≤ x ∧ x ≤ 1000000000) a

def Spec (a : List Int) (out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (SnapTrace a) (fun states => Zlength states - 1) out

def NonzeroStartAt (a : List Int) (i : Int) : Prop :=
  (0 ≤ i ∧ i < Zlength a) ∧ Znth i a 0 ≠ 0 ∧ (i = 0 ∨ Znth (i - 1) a 0 = 0)

def PrefixRunCount (a : List Int) (upto runs : Int) : Prop :=
  ∃ starts : List Int, Zlength starts = runs ∧ starts.Nodup ∧
    ∀ i, i ∈ starts ↔ (0 ≤ i ∧ i < upto) ∧ NonzeroStartAt a i

def PrefixTailState (a : List Int) (upto inside : Int) : Prop :=
  (upto = 0 ∧ inside = 0) ∨ ((0 < upto ∧ upto ≤ Zlength a) ∧
    ((inside = 0 ∧ Znth (upto - 1) a 0 = 0) ∨ (inside = 1 ∧ Znth (upto - 1) a 0 ≠ 0)))

def ScanState (a : List Int) (upto runs inside : Int) : Prop :=
  PrefixRunCount a upto runs ∧ PrefixTailState a upto inside



set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem scan_state_step_zero__scan_state_transitions (a : List Int) (i runs inside : Int)
    (hi : 0 ≤ i ∧ i < Zlength a) (hz : Znth i a 0 = 0) (hs : ScanState a i runs inside) :
    ScanState a (i+1) runs 0 := by
  obtain ⟨⟨starts,hlen,hnd,hm⟩,ht⟩ := hs
  refine ⟨⟨starts,hlen,hnd,?_⟩,Or.inr ⟨by omega,Or.inl ⟨rfl,?_⟩⟩⟩
  · intro j
    rw [hm]
    constructor
    · rintro ⟨hj,hjstart⟩;exact ⟨by omega,hjstart⟩
    · rintro ⟨hj,hjstart⟩
      have hn : j≠i := by intro he;rw [he] at hjstart;exact hjstart.2.1 hz
      exact ⟨by omega,hjstart⟩
  · simpa using hz

theorem scan_state_step_new_run__scan_state_transitions (a : List Int) (i runs : Int)
    (hi : 0 ≤ i ∧ i < Zlength a) (hnz : Znth i a 0 ≠ 0) (hs : ScanState a i runs 0) :
    ScanState a (i+1) (runs+1) 1 := by
  obtain ⟨⟨starts,hlen,hnd,hm⟩,ht⟩ := hs
  have hf : NonzeroStartAt a i := by
    refine ⟨hi,hnz,?_⟩
    obtain ⟨he,_⟩ | ⟨_,⟨_,hz⟩ | ⟨hfalse,_⟩⟩ := ht
    · exact Or.inl he
    · exact Or.inr hz
    · omega
  have hnot : i∉starts := by intro hh;have := (hm i).mp hh;omega
  refine ⟨⟨starts++[i],?_,?_,?_⟩,Or.inr ⟨by omega,Or.inr ⟨rfl,?_⟩⟩⟩
  · simp only [Zlength_app,Zlength_cons,Zlength_nil];omega
  · exact List.nodup_append.mpr ⟨hnd,by simp,by
      intro j hj k hk he
      have hk : k=i := by simpa using hk
      rw [he,hk] at hj
      exact hnot hj⟩
  · intro j
    simp only [List.mem_append,List.mem_singleton,hm]
    constructor
    · rintro (⟨hj,hjs⟩ | he)
      · exact ⟨by omega,hjs⟩
      · rw [he];exact ⟨by omega,hf⟩
    · rintro ⟨hj,hjs⟩
      by_cases he : j=i
      · exact Or.inr he
      · exact Or.inl ⟨by omega,hjs⟩
  · simpa using hnz

theorem scan_state_step_inside_run__scan_state_transitions (a : List Int) (i runs inside : Int)
    (hi : 0≤i ∧ i<Zlength a) (hin : 0≤inside ∧ inside≤1) (hine : inside≠0)
    (hnz : Znth i a 0≠0) (hs : ScanState a i runs inside) : ScanState a (i+1) runs inside := by
  obtain ⟨⟨starts,hlen,hnd,hm⟩,ht⟩ := hs
  have he : inside=1 := by omega
  have hp : 0<i ∧ Znth (i-1) a 0≠0 := by
    obtain ⟨_,hz⟩ | ⟨hb,⟨hz,_⟩ | ⟨_,hn⟩⟩ := ht
    · exact False.elim (hine hz)
    · exact False.elim (hine hz)
    · exact ⟨hb.1,hn⟩
  refine ⟨⟨starts,hlen,hnd,?_⟩,Or.inr ⟨by omega,Or.inr ⟨he,?_⟩⟩⟩
  · intro j
    rw [hm]
    constructor
    · rintro ⟨hj,hjs⟩;exact ⟨by omega,hjs⟩
    · rintro ⟨hj,hjs⟩
      have hne : j≠i := by
        intro hh;rw [hh] at hjs
        obtain hz | hz := hjs.2.2
        · omega
        · exact hp.2 hz
      exact ⟨by omega,hjs⟩
  · simpa using hnz

theorem Znth_repeat_exact__final_spec (a d : Int) (n : Nat) (i : Int)
    (hi : 0≤i ∧ i<(n:Int)) : Znth i (List.replicate n a) d=a :=
  Znth_repeat_lt d n i a hi

private theorem znth_mem (a : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength a) : Znth i a 0∈a := by
  have hk : i.toNat<a.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi;omega
  simpa only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] using List.getElem_mem hk

theorem Forall_zero_Znth__final_spec (a : List Int) (i : Int) (ha : Forall (fun x=>x=0) a)
    (hi : 0≤i ∧ i<Zlength a) : Znth i a 0=0 := ha.mem (znth_mem a i hi)

theorem pointwise_zero_eq_repeat__final_spec (a : List Int)
    (hz : ∀ i, (0≤i ∧ i<Zlength a) → Znth i a 0=0) : a=List.replicate a.length 0 := by
  apply List.eq_replicate_length.mpr
  intro x hx
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hx
  have hh := hz k ⟨by omega,Int.ofNat_lt.mpr hk⟩
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some,he] using hh

theorem Forall_zero_repeat__final_spec (n : Nat) : Forall (fun x : Int=>x=0) (List.replicate n 0) := by
  induction n with
  | zero => exact Forall.nil
  | succ n ih => exact Forall.cons rfl ih

theorem nonzero_has_start__final_spec (a : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength a)
    (hnz : Znth i a 0≠0) : ∃ s, (0≤s ∧ s≤i) ∧ NonzeroStartAt a s := by
  obtain ⟨s,hsnz,hs,hmin⟩ := min_n_in_range (fun j=>Znth j a 0≠0) i hi.1 ⟨i,by omega,hnz⟩
  refine ⟨s,hs,⟨by omega,hsnz,?_⟩⟩
  by_cases he : s=0
  · exact Or.inl he
  · right
    by_contra hh
    have := hmin (s-1) (by omega) hh
    omega

theorem zero_then_nonzero_has_later_start__final_spec (a : List Int) (z j : Int)
    (hb : 0≤z ∧ z<j ∧ j<Zlength a) (hz : Znth z a 0=0) (hjnz : Znth j a 0≠0) :
    ∃ s, (z<s ∧ s≤j) ∧ NonzeroStartAt a s := by
  have hex : ∃ off, (0≤off ∧ off≤j-z-1) ∧ Znth (z+1+off) a 0≠0 := by
    refine ⟨j-z-1,by omega,?_⟩
    simpa only [show z+1+(j-z-1)=j by omega] using hjnz
  obtain ⟨off,hnz,ho,hmin⟩ := min_n_in_range (fun off=>Znth (z+1+off) a 0≠0) (j-z-1) (by omega) hex
  refine ⟨z+1+off,by omega,⟨by omega,hnz,Or.inr ?_⟩⟩
  by_cases he : off=0
  · simpa only [he,Int.add_zero,show z+1-1=z by omega] using hz
  · by_contra hh
    have hn : Znth (z+1+(off-1)) a 0≠0 := by simpa only [show z+1+(off-1)=z+1+off-1 by omega] using hh
    have := hmin (off-1) (by omega) hn
    omega

theorem segment_mex_zero__final_spec (a : List Int) (l r : Int) (hlr : 0≤l ∧ l≤r)
    (hnz : ∀ i, (l≤i ∧ i≤r) → Znth i a 0≠0) : SegmentMex a l r 0 :=
  ⟨0,⟨⟨by omega,hnz⟩,fun _ hb=>hb.1⟩,rfl⟩

theorem segment_mex_exists__final_spec (a : List Int) (l r : Int) (hlr : 0≤l ∧ l≤r)
    (hr : r<Zlength a) (hu : ∀ i, (0≤i ∧ i<Zlength a) → Znth i a 0≤1000000000) :
    ∃ w, SegmentMex a l r w := by
  let Q := fun w : Int => ∀ i, (l≤i ∧ i≤r) → Znth i a 0≠w
  have hex : ∃ w, (0≤w ∧ w≤1000000001) ∧ Q w := by
    refine ⟨1000000001,by omega,?_⟩
    intro i hi he
    have := hu i (by omega)
    omega
  obtain ⟨w,hw,hb,hmin⟩ := min_n_in_range Q 1000000001 (by omega) hex
  refine ⟨w,w,⟨⟨hb.1,hw⟩,?_⟩,rfl⟩
  intro b hbb
  change w≤b
  by_cases he : b≤1000000001
  · exact hmin b ⟨hbb.1,he⟩ hbb.2
  · omega

theorem prefix_zero_all__final_spec (a : List Int) (n : Int) (hc : PrefixRunCount a n 0)
    (he : n=Zlength a) (i : Int) (hi : 0≤i ∧ i<Zlength a) : Znth i a 0=0 := by
  obtain ⟨starts,hlen,hnd,hm⟩ := hc
  have hs : starts=[] := by apply List.length_eq_zero_iff.mp;simp only [Zlength,Int.ofNat_eq_coe] at hlen;omega
  rw [hs] at hm
  by_contra hnz
  obtain ⟨t,_,ht⟩ := nonzero_has_start__final_spec a i hi hnz
  have hh := (hm t).mpr ⟨by rw [he];exact ht.1,ht⟩
  exact List.not_mem_nil hh

theorem prefix_one_run_shape__final_spec (a : List Int) (n : Int) (hn : 0<n)
    (hna : n=Zlength a) (hc : PrefixRunCount a n 1) :
    ∃ s r, (0≤s ∧ s≤r) ∧ r<Zlength a ∧
      (∀ i, (s≤i ∧ i≤r) → Znth i a 0≠0) ∧
      (∀ i, (0≤i ∧ i<Zlength a) → i<s ∨ r<i → Znth i a 0=0) := by
  obtain ⟨starts,hlen,hnd,hm⟩ := hc
  cases starts with
  | nil => simp [Zlength] at hlen
  | cons s tail =>
    have ht : tail=[] := by
      apply List.length_eq_zero_iff.mp
      simp only [Zlength,List.length_cons,Int.ofNat_eq_coe] at hlen
      omega
    rw [ht] at hm
    have hs := ((hm s).mp (by simp)).2
    have huniq : ∀ x, NonzeroStartAt a x → x=s := by
      intro x hx
      have hh := (hm x).mpr ⟨by rw [hna];exact hx.1,hx⟩
      simpa only [List.mem_singleton] using hh
    obtain ⟨r,hrnz,hr,hmax⟩ := max_n_in_range (fun x=>Znth x a 0≠0) (n-1) (by omega)
      ⟨s,by have := hs.1;omega,hs.2.1⟩
    have hsr : s≤r := hmax s (by have := hs.1;omega) hs.2.1
    refine ⟨s,r,⟨hs.1.1,hsr⟩,by omega,?_,?_⟩
    · intro i hi hz
      have hne : i≠r := by intro he;rw [he] at hz;exact hrnz hz
      obtain ⟨x,hx,hxs⟩ := zero_then_nonzero_has_later_start__final_spec a i r (by have := hs.1;omega) hz hrnz
      have := huniq x hxs
      omega
    · intro i hi hout
      by_contra hnz
      obtain hleft | hright := hout
      · obtain ⟨x,hx,hxs⟩ := nonzero_has_start__final_spec a i hi hnz
        have := huniq x hxs
        omega
      · have := hmax i (by omega) hnz
        omega

theorem prefix_two_starts__final_spec (a : List Int) (n runs : Int) (hr : 2≤runs)
    (hna : n=Zlength a) (hc : PrefixRunCount a n runs) :
    ∃ p q, p<q ∧ NonzeroStartAt a p ∧ NonzeroStartAt a q := by
  obtain ⟨starts,hlen,hnd,hm⟩ := hc
  cases starts with
  | nil => simp only [Zlength_nil] at hlen;omega
  | cons x tail =>
    cases tail with
    | nil => simp only [Zlength_cons,Zlength_nil] at hlen;omega
    | cons y tail =>
      have hx := ((hm x).mp (by simp)).2
      have hy := ((hm y).mp (by simp)).2
      have hxy : x≠y := by intro he;exact (List.nodup_cons.mp hnd).1 (by simp [he])
      by_cases hlt : x<y
      · exact ⟨x,y,hlt,hx,hy⟩
      · exact ⟨y,x,by omega,hy,hx⟩


private theorem replicate_length (a : List Int) (x : Int) : Zlength (List.replicate a.length x)=Zlength a := by simp only [Zlength,List.length_replicate]

private theorem trace_pair (a b : List Int) (hs : OneSnap a b) (hf : Forall (fun x=>x=0) b) : SnapTrace a [a,b] := by
  refine ⟨by simp [Zlength],rfl,?_,?_⟩
  · intro k hk
    have he : k=0 := by simp only [Zlength_cons,Zlength_nil] at hk;omega
    subst k
    exact hs
  · exact hf

private theorem trace_triple (a b c : List Int) (hs : OneSnap a b) (ht : OneSnap b c)
    (hf : Forall (fun x=>x=0) c) : SnapTrace a [a,b,c] := by
  refine ⟨by simp [Zlength],rfl,?_,?_⟩
  · intro k hk
    have hb : k=0 ∨ k=1 := by simp only [Zlength_cons,Zlength_nil] at hk;omega
    obtain he | he := hb
    · subst k;exact hs
    · subst k;exact ht
  · exact hf

theorem zero_trace__final_spec (a : List Int)
    (hz : ∀ i, (0≤i ∧ i<Zlength a) → Znth i a 0=0) : SnapTrace a [a] := by
  refine ⟨by simp [Zlength],rfl,?_,?_⟩
  · intro k hk;simp only [Zlength_cons,Zlength_nil] at hk;omega
  · change Forall (fun x=>x=0) a
    rw [pointwise_zero_eq_repeat__final_spec a hz]
    exact Forall_zero_repeat__final_spec _

theorem one_trace__final_spec (a : List Int) (s r : Int) (hsr : 0≤s ∧ s≤r)
    (hr : r<Zlength a) (hin : ∀ i, (s≤i ∧ i≤r) → Znth i a 0≠0)
    (hout : ∀ i, (0≤i ∧ i<Zlength a) → i<s ∨ r<i → Znth i a 0=0) :
    SnapTrace a [a,List.replicate a.length 0] := by
  apply trace_pair _ _ _ (Forall_zero_repeat__final_spec _)
  refine ⟨s,r,0,hsr,hr,segment_mex_zero__final_spec a s r hsr hin,replicate_length a 0,?_⟩
  intro i hi
  rw [Znth_repeat_exact__final_spec 0 0 a.length i hi]
  split_ifs with h
  · rfl
  · exact (hout i hi (by omega)).symm

theorem two_trace__final_spec (a : List Int) (p q : Int) (hl : 0<Zlength a)
    (hpq : p<q) (hp : NonzeroStartAt a p) (hq : NonzeroStartAt a q)
    (hu : ∀ i, (0≤i ∧ i<Zlength a) → Znth i a 0≤1000000000) :
    ∃ mid, SnapTrace a [a,mid,List.replicate a.length 0] := by
  obtain ⟨w,hm⟩ := segment_mex_exists__final_spec a 0 (Zlength a-1) (by omega) (by omega) hu
  have hsep : Znth (q-1) a 0=0 := by
    obtain hh | hh := hq.2.2
    · have := hp.1;omega
    · exact hh
  have hw : w≠0 := by
    obtain ⟨x,⟨⟨hx,hmiss⟩,_⟩,he⟩ := hm
    change x=w at he
    rw [he] at hmiss
    have hh := hmiss (q-1) (by have := hp.1;have := hq.1;omega)
    intro hz;rw [hz] at hh;exact hh hsep
  let mid := List.replicate a.length w
  have hml : Zlength mid=Zlength a := replicate_length a w
  have hs1 : OneSnap a mid := by
    refine ⟨0,Zlength a-1,w,by omega,by omega,hm,hml,?_⟩
    intro i hi
    change Znth i (List.replicate a.length w) 0= _
    rw [Znth_repeat_exact__final_spec w 0 a.length i hi,if_pos (by omega)]
  have hs2 : OneSnap mid (List.replicate a.length 0) := by
    refine ⟨0,Zlength a-1,0,by omega,by omega,?_,by rw [hml,replicate_length],?_⟩
    · apply segment_mex_zero__final_spec _ _ _ (by omega)
      intro i hi
      change Znth i (List.replicate a.length w) 0≠0
      rw [Znth_repeat_exact__final_spec w 0 a.length i (by change 0≤i ∧ i<Zlength a;omega)]
      exact hw
    · intro i hi
      rw [hml] at hi
      rw [Znth_repeat_exact__final_spec 0 0 a.length i hi,if_pos (by omega)]
  exact ⟨mid,trace_triple _ _ _ hs1 hs2 (Forall_zero_repeat__final_spec _)⟩

theorem trace_cost_ge_one__final_spec (a : List Int) (s : Int) (states : List (List Int))
    (hs : NonzeroStartAt a s) (ht : SnapTrace a states) : 1≤Zlength states-1 := by
  obtain ⟨hpos,hinit,hsteps,hfinal⟩ := ht
  cases states with
  | nil => simp only [Zlength_nil] at hpos;omega
  | cons x tail =>
    cases tail with
    | nil =>
      change x=a at hinit
      change Forall (fun x=>x=0) x at hfinal
      rw [hinit] at hfinal
      exact False.elim (hs.2.1 (Forall_zero_Znth__final_spec a s hfinal hs.1))
    | cons y tail =>
      simp only [Zlength_cons]
      have := Zlength_nonneg tail
      omega

theorem onesnap_two_starts_impossible__final_spec (a after : List Int) (p q : Int)
    (hpq : p<q) (hp : NonzeroStartAt a p) (hq : NonzeroStartAt a q)
    (hs : OneSnap a after) (hz : Forall (fun x=>x=0) after) : False := by
  obtain ⟨l,r,w,hlr,hr,hm,hlen,heq⟩ := hs
  have hpa := Forall_zero_Znth__final_spec after p hz (by rw [hlen];exact hp.1)
  have hqa := Forall_zero_Znth__final_spec after q hz (by rw [hlen];exact hq.1)
  have hep := heq p hp.1
  have heq' := heq q hq.1
  have hpb : l≤p ∧ p≤r := by
    by_contra h
    rw [if_neg h,hpa] at hep
    exact hp.2.1 hep.symm
  have hqb : l≤q ∧ q≤r := by
    by_contra h
    rw [if_neg h,hqa] at heq'
    exact hq.2.1 heq'.symm
  have hw : w=0 := by rw [if_pos hpb,hpa] at hep;exact hep.symm
  obtain ⟨x,⟨⟨hx,hmiss⟩,_⟩,he⟩ := hm
  change x=w at he
  rw [he,hw] at hmiss
  have hprev : Znth (q-1) a 0=0 := by
    obtain hh | hh := hq.2.2
    · have := hp.1;omega
    · exact hh
  exact hmiss (q-1) (by omega) hprev

theorem trace_cost_ge_two__final_spec (a : List Int) (p q : Int) (states : List (List Int))
    (hpq : p<q) (hp : NonzeroStartAt a p) (hq : NonzeroStartAt a q)
    (ht : SnapTrace a states) : 2≤Zlength states-1 := by
  have hone := trace_cost_ge_one__final_spec a p states hp ht
  obtain ⟨hpos,hinit,hsteps,hfinal⟩ := ht
  cases states with
  | nil => simp only [Zlength_nil] at hpos;omega
  | cons x tail =>
    cases tail with
    | nil => simp only [Zlength_cons,Zlength_nil] at hone;omega
    | cons y tail =>
      cases tail with
      | nil =>
        change x=a at hinit
        have hstep := hsteps 0 (by simp [Zlength])
        change OneSnap x y at hstep
        change Forall (fun x=>x=0) y at hfinal
        rw [hinit] at hstep
        exact False.elim (onesnap_two_starts_impossible__final_spec a y p q hpq hp hq hstep hfinal)
      | cons z tail =>
        simp only [Zlength_cons]
        have := Zlength_nonneg tail
        omega

theorem scan_state_complete_spec__final_spec (a : List Int) (runs inside : Int)
    (hl : 0<Zlength a) (hu : ∀ i, (0≤i ∧ i<Zlength a) → Znth i a 0≤1000000000)
    (hs : ScanState a (Zlength a) runs inside) : Spec a (min runs 2) := by
  obtain ⟨hc,ht⟩ := hs
  have hr : 0≤runs := by
    obtain ⟨starts,he,_⟩ := hc
    rw [←he]
    exact Zlength_nonneg starts
  by_cases he0 : runs=0
  · rw [he0] at hc ⊢
    rw [min_eq_left (by omega : (0:Int)≤2)]
    have hz := prefix_zero_all__final_spec a (Zlength a) hc rfl
    refine ⟨[a],⟨zero_trace__final_spec a hz,?_⟩,by rfl⟩
    intro states htrace
    change 1-1≤Zlength states-1
    have := htrace.1
    omega
  · by_cases he1 : runs=1
    · rw [he1] at hc ⊢
      rw [min_eq_left (by omega : (1:Int)≤2)]
      obtain ⟨s,r,hsr,hrr,hin,hout⟩ := prefix_one_run_shape__final_spec a (Zlength a) hl rfl hc
      obtain ⟨t,_,hts⟩ := nonzero_has_start__final_spec a s (by omega) (hin s (by omega))
      refine ⟨[a,List.replicate a.length 0],⟨one_trace__final_spec a s r hsr hrr hin hout,?_⟩,by rfl⟩
      intro states htrace
      exact trace_cost_ge_one__final_spec a t states hts htrace
    · have hr2 : 2≤runs := by omega
      rw [min_eq_right hr2]
      obtain ⟨p,q,hpq,hp,hq⟩ := prefix_two_starts__final_spec a (Zlength a) runs hr2 rfl hc
      obtain ⟨mid,htrace⟩ := two_trace__final_spec a p q hl hpq hp hq hu
      refine ⟨[a,mid,List.replicate a.length 0],⟨htrace,?_⟩,by rfl⟩
      intro states hh
      exact trace_cost_ge_two__final_spec a p q states hpq hp hq hh
end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib
