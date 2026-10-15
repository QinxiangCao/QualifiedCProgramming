import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib
open AUXLib


def GoodAdjacentSums (b : List Int) : Prop :=
  ∃ k, ∀ i, (0 ≤ i ∧ i < Zlength b - 1) → Znth i b 0 + Znth (i + 1) b 0 = k

def Pre (a : List Int) : Prop :=
  (2 ≤ Zlength a ∧ Zlength a ≤ 100) ∧ Forall (fun x => 1 ≤ x ∧ x ≤ 100000) a

def Spec (a : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ ∃ b, List.Perm a b ∧ GoodAdjacentSums b)

def Occurrences (v : Int) (l : List Int) : Int := (l.count v : Int)

def PaintScanState (a : List Int) (i x y cx cy : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength a) ∧ x = Znth 0 a 0 ∧
  (0 ≤ cx ∧ cx ≤ i) ∧ (0 ≤ cy ∧ cy ≤ i) ∧ cx + cy = i ∧
  (y = -1 ↔ cy = 0) ∧ (y ≠ -1 → y ≠ x) ∧ cx = Occurrences x (sublist 0 i a) ∧
  (y ≠ -1 → cy = Occurrences y (sublist 0 i a)) ∧
  (∀ j, (0 ≤ j ∧ j < i) → Znth j a 0 = x ∨ (y ≠ -1 ∧ Znth j a 0 = y))


set_option maxHeartbeats 2000000

theorem sublist_snoc_at_index__scan_transitions (a : List Int) (i : Int)
    (hi : 0≤i ∧ i<Zlength a) : sublist 0 (i+1) a=sublist 0 i a++[Znth i a 0] := by
  rw [sublist_split 0 (i+1) i a (by omega) (by omega),sublist_single 0 i a hi]

theorem occurrences_sublist_snoc_eq__scan_transitions (a : List Int) (i v : Int)
    (hi : 0≤i ∧ i<Zlength a) (hv : Znth i a 0=v) :
    Occurrences v (sublist 0 (i+1) a)=Occurrences v (sublist 0 i a)+1 := by
  rw [sublist_snoc_at_index__scan_transitions a i hi]
  simp [Occurrences,List.count_append,hv]

theorem occurrences_sublist_snoc_neq__scan_transitions (a : List Int) (i v : Int)
    (hi : 0≤i ∧ i<Zlength a) (hv : Znth i a 0≠v) :
    Occurrences v (sublist 0 (i+1) a)=Occurrences v (sublist 0 i a) := by
  rw [sublist_snoc_at_index__scan_transitions a i hi]
  simp [Occurrences,List.count_append,hv,Ne.symm hv]

private theorem in_index (l : List Int) (v : Int) (hv : v∈l) :
    ∃ k, (0≤k ∧ k<Zlength l) ∧ Znth k l 0=v := by
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hv
  refine ⟨k,by simp only [Zlength,Int.ofNat_eq_coe];omega,?_⟩
  simp only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some]

theorem sublist0_In_Znth_exists__scan_transitions (a : List Int) (n v : Int)
    (hn : 0≤n ∧ n≤Zlength a) (hv : v∈sublist 0 n a) :
    ∃ j, (0≤j ∧ j<n) ∧ Znth j a 0=v := by
  obtain ⟨j,hj,hjv⟩ := in_index (sublist 0 n a) v hv
  have hl : Zlength (sublist 0 n a)=n := by
    have hl : n.toNat≤a.length := by simp only [Zlength,Int.ofNat_eq_coe] at hn;omega
    unfold Zlength sublist
    rw [Int.toNat_zero,List.drop_zero,List.length_take,Nat.min_eq_left hl]
    simp only [Int.ofNat_eq_coe]
    omega
  refine ⟨j,by omega,?_⟩
  rw [Znth_sublist 0 0 j n a (by omega) (by omega),Int.add_zero] at hjv
  exact hjv

theorem paint_scan_state_init__scan_transitions (a : List Int) :
    PaintScanState a 0 (Znth 0 a 0) (-1) 0 0 := by
  have hz := Zlength_nonneg a
  refine ⟨by omega,rfl,by omega,by omega,rfl,by omega,?_,?_,?_,?_⟩
  · intro h;omega
  · rfl
  · intro h;omega
  · intro j hj;omega

theorem paint_scan_state_step_x__scan_transitions (a : List Int) (i x y cx cy : Int)
    (hi : 0≤i ∧ i<Zlength a) (hcur : Znth i a 0=x) (hs : PaintScanState a i x y cx cy) :
    PaintScanState a (i+1) x y (cx+1) cy := by
  obtain ⟨hib,hx,hcxb,hcyb,hsum,hsent,hdist,hcx,hcy,hcover⟩ := hs
  refine ⟨by omega,hx,by omega,by omega,by omega,hsent,hdist,?_,?_,?_⟩
  · rw [occurrences_sublist_snoc_eq__scan_transitions a i x hi hcur];omega
  · intro hy
    rw [occurrences_sublist_snoc_neq__scan_transitions a i y hi (by rw [hcur];exact Ne.symm (hdist hy))]
    exact hcy hy
  · intro j hj
    by_cases he : j=i
    · exact Or.inl (he ▸ hcur)
    · exact hcover j (by omega)

theorem paint_scan_state_step_first_y__scan_transitions (a : List Int) (i x y cx cy : Int)
    (hi : 0≤i ∧ i<Zlength a) (hpositive : 1≤Znth i a 0) (hy : y= -1)
    (hcurx : Znth i a 0≠x) (hs : PaintScanState a i x y cx cy) :
    PaintScanState a (i+1) x (Znth i a 0) cx (cy+1) := by
  obtain ⟨hib,hx,hcxb,hcyb,hsum,hsent,hdist,hcx,hcy,hcover⟩ := hs
  have hcy0 := hsent.mp hy
  have hnot : Znth i a 0∉sublist 0 i a := by
    intro hh
    obtain ⟨j,hj,hjv⟩ := sublist0_In_Znth_exists__scan_transitions a i (Znth i a 0) (by omega) hh
    obtain hh | ⟨hyn,_⟩ := hcover j hj
    · exact hcurx (hjv.symm.trans hh)
    · exact hyn hy
  have hzero : Occurrences (Znth i a 0) (sublist 0 i a)=0 := by simp [Occurrences,List.count_eq_zero.mpr hnot]
  refine ⟨by omega,hx,by omega,by omega,by omega,by omega,fun _ => hcurx,?_,?_,?_⟩
  · rw [occurrences_sublist_snoc_neq__scan_transitions a i x hi hcurx];exact hcx
  · intro hh
    rw [occurrences_sublist_snoc_eq__scan_transitions a i _ hi rfl];omega
  · intro j hj
    by_cases he : j=i
    · exact Or.inr ⟨by omega,congrArg (fun k => Znth k a 0) he⟩
    · obtain hh | ⟨hyn,_⟩ := hcover j (by omega)
      · exact Or.inl hh
      · exact False.elim (hyn hy)

theorem paint_scan_state_step_y__scan_transitions (a : List Int) (i x y cx cy : Int)
    (hi : 0≤i ∧ i<Zlength a) (hyn : y≠ -1) (hcur : Znth i a 0=y)
    (hcurx : Znth i a 0≠x) (hs : PaintScanState a i x y cx cy) :
    PaintScanState a (i+1) x y cx (cy+1) := by
  obtain ⟨hib,hx,hcxb,hcyb,hsum,hsent,hdist,hcx,hcy,hcover⟩ := hs
  refine ⟨by omega,hx,by omega,by omega,by omega,by omega,hdist,?_,?_,?_⟩
  · rw [occurrences_sublist_snoc_neq__scan_transitions a i x hi hcurx];exact hcx
  · intro hh
    rw [occurrences_sublist_snoc_eq__scan_transitions a i y hi hcur]
    have hh' := hcy hyn;omega
  · intro j hj
    by_cases he : j=i
    · exact Or.inr ⟨hyn,he ▸ hcur⟩
    · exact hcover j (by omega)

theorem good_adjacent_sums_uniform__accepted_results (a : List Int) (x : Int)
    (hall : ∀ i, (0≤i ∧ i<Zlength a) → Znth i a 0=x) : GoodAdjacentSums a := by
  refine ⟨2*x,?_⟩
  intro i hi
  rw [hall i (by omega),hall (i+1) (by omega)]
  omega


private theorem canonical_counts (l : List Int) (x y : Int) (hxy : x≠y)
    (hc : ∀ z, z∈l → z=x ∨ z=y) :
    l.Perm (List.replicate (l.count x) x++List.replicate (l.count y) y) := by
  induction l with
  | nil => exact List.Perm.nil
  | cons z l ih =>
    have ht := ih (fun v hv => hc v (List.mem_cons_of_mem z hv))
    obtain he | he := hc z List.mem_cons_self
    · simpa only [he,List.count_cons_self,List.count_cons_of_ne hxy,List.replicate_succ,List.cons_append] using ht.cons x
    · simp only [he,List.count_cons_self,List.count_cons_of_ne (Ne.symm hxy),List.replicate_succ]
      exact (ht.cons y).trans List.perm_middle.symm

private theorem equal_alternating (n : Nat) (u v : Int) :
    ∃ b, (List.replicate n u++List.replicate n v).Perm b ∧
      (n≠0 → ∃ t, b=u::t) ∧
      (∀ i, (0≤i ∧ i<Zlength b-1) → Znth i b 0+Znth (i+1) b 0=u+v) := by
  induction n with
  | zero =>
    refine ⟨[],List.Perm.nil,fun h => False.elim (h rfl),?_⟩
    intro i hi;change 0≤i ∧ i<0-1 at hi;omega
  | succ n ih =>
    obtain ⟨b,hp,hh,hadj⟩ := ih
    have hbl : b.length=2*n := by have hl:=hp.length_eq;simp only [List.length_append,List.length_replicate] at hl;omega
    refine ⟨u::v::b,?_,fun _ => ⟨v::b,rfl⟩,?_⟩
    · simp only [List.replicate_succ,List.cons_append]
      exact ((List.perm_middle : (List.replicate n u++v::List.replicate n v).Perm (v::(List.replicate n u++List.replicate n v))).trans (hp.cons v)).cons u
    · intro i hi
      simp only [Zlength_cons] at hi
      by_cases hi0 : i=0
      · subst i;change u+v=u+v;rfl
      · by_cases hi1 : i=1
        · subst i
          have hn : n≠0 := by simp only [Zlength,Int.ofNat_eq_coe] at hi;omega
          obtain ⟨t,rfl⟩ := hh hn
          change v+u=u+v;omega
        · rw [Znth_cons 0 i u (v::b) (by omega),Znth_cons 0 (i-1) v b (by omega),
            Znth_cons 0 (i+1) u (v::b) (by omega),Znth_cons 0 (i+1-1) v b (by omega)]
          rw [show i-1-1=i-2 by omega,show i+1-1-1=i-2+1 by omega]
          exact hadj (i-2) (by omega)

private theorem prepend_alternating (n : Nat) (u v : Int) (b : List Int)
    (hlen : b.length=2*n) (hh : n≠0 → ∃ t,b=v::t)
    (hadj : ∀ i, (0≤i ∧ i<Zlength b-1) → Znth i b 0+Znth (i+1) b 0=u+v) :
    GoodAdjacentSums (u::b) := by
  refine ⟨u+v,?_⟩
  intro i hi
  rw [Zlength_cons] at hi
  by_cases hi0 : i=0
  · subst i
    have hn : n≠0 := by simp only [Zlength,Int.ofNat_eq_coe] at hi;omega
    obtain ⟨t,rfl⟩ := hh hn
    rfl
  · rw [Znth_cons 0 i u b (by omega),Znth_cons 0 (i+1) u b (by omega)]
    rw [show i+1-1=i-1+1 by omega]
    exact hadj (i-1) (by omega)

theorem balanced_two_value_permutation__accepted_results (a : List Int) (x y : Int)
    (hxy : x≠y) (hcover : ∀ i, (0≤i ∧ i<Zlength a) → Znth i a 0=x ∨ Znth i a 0=y)
    (hyx : (a.count y : Int)-(a.count x : Int)≤1)
    (hxyb : (a.count x : Int)-(a.count y : Int)≤1) :
    ∃ b, a.Perm b ∧ GoodAdjacentSums b := by
  have hc : ∀ z, z∈a → z=x ∨ z=y := by
    intro z hz
    obtain ⟨i,hi,hiz⟩ := in_index a z hz
    simpa only [hiz] using hcover i hi
  have hp := canonical_counts a x y hxy hc
  have hcases : a.count x=a.count y ∨ a.count x=a.count y+1 ∨ a.count y=a.count x+1 := by omega
  rcases hcases with he | he | he
  · obtain ⟨b,hb,_,ha⟩ := equal_alternating (a.count x) x y
    refine ⟨b,?_,⟨x+y,ha⟩⟩
    rw [← he] at hp
    exact hp.trans hb
  · obtain ⟨b,hb,hh,ha⟩ := equal_alternating (a.count y) y x
    have hbl : b.length=2*a.count y := by have hl:=hb.length_eq;simp only [List.length_append,List.length_replicate] at hl;omega
    refine ⟨x::b,?_,?_⟩
    · rw [he,List.replicate_succ,List.cons_append] at hp
      exact hp.trans ((List.perm_append_comm.trans hb).cons x)
    · apply prepend_alternating (a.count y) x y b hbl hh
      intro i hi;have hh:=ha i hi;omega
  · obtain ⟨b,hb,hh,ha⟩ := equal_alternating (a.count x) x y
    have hbl : b.length=2*a.count x := by have hl:=hb.length_eq;simp only [List.length_append,List.length_replicate] at hl;omega
    refine ⟨y::b,?_,?_⟩
    · rw [he,List.replicate_succ] at hp
      exact hp.trans (List.perm_middle.trans (hb.cons y))
    · apply prepend_alternating (a.count x) y x b hbl hh
      intro i hi;have hh:=ha i hi;omega


theorem good_adjacent_sums_period_two__rejected_results (b : List Int) (j : Int)
    (hg : GoodAdjacentSums b) (hj : 0≤j) (hj2 : j+2<Zlength b) : Znth j b 0=Znth (j+2) b 0 := by
  obtain ⟨k,hs⟩ := hg
  have h1:=hs j (by omega)
  have h2:=hs (j+1) (by omega)
  rw [show j+1+1=j+2 by omega] at h2
  omega

theorem Znth_drop_two__rejected_results (j p q : Int) (l : List Int) (hj : 0≤j) :
    Znth (j+2) (p::q::l) 0=Znth j l 0 := by
  rw [Znth_cons 0 (j+2) p (q::l) (by omega),Znth_cons 0 (j+2-1) q l (by omega),show j+2-1-1=j by omega]

private theorem third_eq (tail : List Int) (p q r k : Int)
    (hs : ∀ j, (0≤j ∧ j<Zlength (p::q::r::tail)-1) →
      Znth j (p::q::r::tail) 0+Znth (j+1) (p::q::r::tail) 0=k) : r=p := by
  have hz:=Zlength_nonneg tail
  have h0:=hs 0 (by simp only [Zlength_cons];omega)
  have h1:=hs 1 (by simp only [Zlength_cons];omega)
  change p+q=k at h0
  change q+r=k at h1
  omega

private theorem fourth_eq (tail : List Int) (p q r s k : Int)
    (hs : ∀ j, (0≤j ∧ j<Zlength (p::q::r::s::tail)-1) →
      Znth j (p::q::r::s::tail) 0+Znth (j+1) (p::q::r::s::tail) 0=k) : s=q := by
  have hz:=Zlength_nonneg tail
  have h1:=hs 1 (by simp only [Zlength_cons];omega)
  have h2:=hs 2 (by simp only [Zlength_cons];omega)
  change q+r=k at h1
  change r+s=k at h2
  omega

private theorem sums_drop_pair (tail : List Int) (p q k : Int)
    (hs : ∀ j, (0≤j ∧ j<Zlength (p::q::p::q::tail)-1) →
      Znth j (p::q::p::q::tail) 0+Znth (j+1) (p::q::p::q::tail) 0=k) :
    ∀ j, (0≤j ∧ j<Zlength (p::q::tail)-1) →
      Znth j (p::q::tail) 0+Znth (j+1) (p::q::tail) 0=k := by
  intro j hj
  have hh:=hs (j+2) (by simp only [Zlength_cons] at *;omega)
  rw [show j+2+1=(j+1)+2 by omega,Znth_drop_two__rejected_results j p q _ hj.1,
    Znth_drop_two__rejected_results (j+1) p q _ (by omega)] at hh
  exact hh

theorem adjacent_sums_tail_values__rejected_results (tail : List Int) (p q k : Int)
    (hs : ∀ j, (0≤j ∧ j<Zlength (p::q::tail)-1) →
      Znth j (p::q::tail) 0+Znth (j+1) (p::q::tail) 0=k)
    (z : Int) (hz : z∈p::q::tail) : z=p ∨ z=q := by
  cases tail with
  | nil => simpa only [List.mem_cons,List.not_mem_nil,or_false] using hz
  | cons r rest =>
    have hr:=third_eq rest p q r k hs
    cases rest with
    | nil =>
      simp only [hr,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with h | h | h <;> omega
    | cons t tail =>
      have ht:=fourth_eq tail p q r t k hs
      rw [hr,ht] at hs hz
      have htail:=sums_drop_pair tail p q k hs
      apply adjacent_sums_tail_values__rejected_results tail p q k htail z
      simp only [List.mem_cons] at hz ⊢
      tauto
termination_by tail.length

theorem good_adjacent_sums_at_most_two_values__rejected_results (b : List Int) (z : Int)
    (hlen : 2≤Zlength b) (hg : GoodAdjacentSums b) (hz : z∈b) :
    z=Znth 0 b 0 ∨ z=Znth 1 b 0 := by
  cases b with
  | nil => change 2≤0 at hlen;omega
  | cons p rest => cases rest with
    | nil => change 2≤1 at hlen;omega
    | cons q tail =>
      obtain ⟨k,hs⟩:=hg
      exact adjacent_sums_tail_values__rejected_results tail p q k hs z hz

theorem occurrences_cons_distinct_pair__rejected_results (l : List Int) (p q : Int) (hpq : p≠q) :
    Occurrences p (p::q::l)-Occurrences q (p::q::l)=Occurrences p l-Occurrences q l := by
  simp only [Occurrences,List.count_cons_self,List.count_cons_of_ne hpq,List.count_cons_of_ne (Ne.symm hpq),Nat.cast_add,Nat.cast_one]
  omega

theorem adjacent_sums_count_balance_core__rejected_results (tail : List Int) (p q k : Int) (hpq : p≠q)
    (hs : ∀ j, (0≤j ∧ j<Zlength (p::q::tail)-1) →
      Znth j (p::q::tail) 0+Znth (j+1) (p::q::tail) 0=k) :
    Z.abs (((p::q::tail).count p : Int)-((p::q::tail).count q : Int))≤1 := by
  cases tail with
  | nil => simp [List.count_cons_of_ne hpq,List.count_cons_of_ne (Ne.symm hpq),Z.abs]
  | cons r rest =>
    have hr:=third_eq rest p q r k hs
    cases rest with
    | nil =>
      rw [hr]
      simp [List.count_cons_of_ne hpq,List.count_cons_of_ne (Ne.symm hpq),Z.abs]
    | cons t tail =>
      have ht:=fourth_eq tail p q r t k hs
      rw [hr,ht] at hs ⊢
      change Z.abs (Occurrences p (p::q::p::q::tail)-Occurrences q (p::q::p::q::tail))≤1
      rw [occurrences_cons_distinct_pair__rejected_results _ p q hpq]
      exact adjacent_sums_count_balance_core__rejected_results tail p q k hpq (sums_drop_pair tail p q k hs)
termination_by tail.length

theorem good_adjacent_sums_count_balance__rejected_results (a b : List Int) (x y : Int)
    (hlen : 2≤Zlength a) (hxy : x≠y) (hix : x∈a) (hiy : y∈a) (hp : a.Perm b)
    (hg : GoodAdjacentSums b) : Z.abs (Occurrences x a-Occurrences y a)≤1 := by
  have hxb := hp.mem_iff.mp hix
  have hyb := hp.mem_iff.mp hiy
  cases b with
  | nil => simp at hxb
  | cons p rest => cases rest with
    | nil => simp only [List.mem_cons,List.not_mem_nil,or_false] at hxb hyb;omega
    | cons q tail =>
      obtain ⟨k,hs⟩:=hg
      have hx:=adjacent_sums_tail_values__rejected_results tail p q k hs x hxb
      have hy:=adjacent_sums_tail_values__rejected_results tail p q k hs y hyb
      have hpq : p≠q := by omega
      have hb:=adjacent_sums_count_balance_core__rejected_results tail p q k hpq hs
      have hc : ∀ v, a.count v=(p::q::tail).count v := fun v => hp.count_eq v
      simp only [Occurrences,hc]
      have hbal : -((1 : Int))≤((p::q::tail).count p : Int)-((p::q::tail).count q : Int) ∧ ((p::q::tail).count p : Int)-((p::q::tail).count q : Int)≤1 := (Z.abs_le_iff _ _).mp hb
      apply (Z.abs_le_iff _ _).mpr
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega

theorem Znth_in_range__rejected_results (l : List Int) (j d : Int) (hj : 0≤j ∧ j<Zlength l) : Znth j l d∈l := by
  have hb : j.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hj;omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb,Option.getD_some]
  exact List.getElem_mem hb

theorem In_sublist_from_zero__rejected_results (l : List Int) (hi z : Int) (hz : z∈sublist 0 hi l) : z∈l := by
  change z∈(l.take hi.toNat).drop 0 at hz
  simp only [List.drop_zero] at hz
  exact List.mem_of_mem_take hz

theorem good_adjacent_sums_no_three_distinct__rejected_results (a b : List Int) (x y z : Int)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) (hix : x∈a) (hiy : y∈a) (hiz : z∈a)
    (hp : a.Perm b) (hg : GoodAdjacentSums b) : False := by
  have hxb:=hp.mem_iff.mp hix
  have hyb:=hp.mem_iff.mp hiy
  have hzb:=hp.mem_iff.mp hiz
  cases b with
  | nil => simp at hxb
  | cons p rest => cases rest with
    | nil => simp only [List.mem_cons,List.not_mem_nil,or_false] at hxb hyb;omega
    | cons q tail =>
      obtain ⟨k,hs⟩:=hg
      have hx:=adjacent_sums_tail_values__rejected_results tail p q k hs x hxb
      have hy:=adjacent_sums_tail_values__rejected_results tail p q k hs y hyb
      have hz:=adjacent_sums_tail_values__rejected_results tail p q k hs z hzb
      omega

theorem paint_scan_state_full_count_balance__rejected_results (input b : List Int) (n i x y cx cy : Int)
    (hn : 2≤n) (hnlen : n=Zlength input) (hin : i≥n) (hile : i≤n) (hcy0 : cy≠0)
    (hs : PaintScanState input i x y cx cy) (hp : input.Perm b) (hg : GoodAdjacentSums b) : Z.abs (cx-cy)≤1 := by
  have he : i=n := by omega
  rw [he] at hs
  obtain ⟨hb,hx,hcx,hcy,htot,hsent,hyx,hcxocc,hcyocc,hcover⟩:=hs
  have hyn : y≠ -1 := by intro hy;exact hcy0 (hsent.mp hy)
  have hyocc:=hcyocc hyn
  rw [sublist_self input n hnlen] at hcxocc hyocc
  have hxy : x≠y := Ne.symm (hyx hyn)
  have hix : x∈input := by rw [hx];exact Znth_in_range__rejected_results input 0 0 (by omega)
  have hiy : y∈input := by
    by_contra hh
    have hc : input.count y=0 := List.count_eq_zero.mpr hh
    simp only [Occurrences,hc,Nat.cast_zero] at hyocc
    exact hcy0 hyocc
  have hh:=good_adjacent_sums_count_balance__rejected_results input b x y (by omega) hxy hix hiy hp hg
  rw [hcxocc,hyocc]
  exact hh

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib
