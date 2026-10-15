import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_walk_bridge

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Dedup

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_OrbitQuotient

private theorem mod_bounds (a m : Int) (hm : 0<m) : 0≤a mod m ∧ a mod m<m := by
  exact ⟨Int.fmod_nonneg_of_pos a hm,Int.fmod_lt_of_pos a hm⟩

private theorem mod_small (a m : Int) (h : 0≤a ∧ a<m) : a mod m=a :=
  Int.fmod_eq_of_lt h.1 h.2

theorem orbit_hit_zero (m x start : Int) :
    0<m → (0≤start ∧ start<m) → OrbitHit m x start start := by
  intro hm hs
  refine ⟨0,le_refl _,?_⟩
  change start=(start*1) mod m
  rw [Int.mul_one,mod_small start m hs]

theorem catches_all_gives_orbit_hit (m x : Int) (traps : List Int) (start : Int) :
    CatchesAll m x traps → (0≤start ∧ start<m) →
    ∃ room, room∈traps ∧ OrbitHit m x start room := by
  rintro ⟨_,_,hc⟩ hs
  rcases hc start hs with ⟨time,room,ht,hr,hin⟩
  exact ⟨room,hin,time,ht,hr⟩

theorem representative_system_catches_all (m x : Int) (representatives : List Int) :
    OrbitRepresentativeSystem m x representatives → CatchesAll m x representatives := by
  rintro ⟨hn,hr,hc,_⟩
  refine ⟨hn,hr,?_⟩
  intro start hs
  rcases hc start hs with ⟨room,hin,time,ht,he⟩
  exact ⟨time,room,ht,he,hin⟩

theorem separated_witnesses_length (sources targets : List Int) (relation : Int→Int→Prop) :
    NoDup sources →
    (∀ source, source∈sources → ∃ target, target∈targets ∧ relation source target) →
    (∀ left right target, left∈sources → right∈sources → relation left target → relation right target → left=right) →
    sources.length≤targets.length := by
  intro hn
  induction sources generalizing targets with
  | nil => intros; exact Nat.zero_le _
  | cons source sources ih =>
    intro hh hs
    rcases List.nodup_cons.mp hn with ⟨hnot,htail⟩
    rcases hh source (by simp) with ⟨target,hin,hrel⟩
    have htailhit : ∀ other, other∈sources → ∃ y, y∈targets.erase target ∧ relation other y := by
      intro other ho
      rcases hh other (List.mem_cons_of_mem source ho) with ⟨y,hy,hry⟩
      refine ⟨y,?_,hry⟩
      have hne : y≠target := by
        intro he
        subst y
        have heq := hs other source target (by simp [ho]) (by simp) hry hrel
        exact hnot (heq ▸ ho)
      exact (List.mem_erase_of_ne hne).mpr hy
    have hb := ih (targets.erase target) htail htailhit (by
      intro l r t hl hr; exact hs l r t (by simp [hl]) (by simp [hr]))
    have he := List.length_erase_of_mem hin
    have hp : 0<targets.length := List.length_pos_of_mem hin
    simp only [List.length_cons]
    omega

theorem representative_system_lower_bound (m x : Int) (representatives traps : List Int) :
    OrbitRepresentativeSystem m x representatives → CatchesAll m x traps →
    representatives.length≤traps.length := by
  rintro ⟨hn,hr,_,hs⟩ hc
  exact separated_witnesses_length representatives traps (OrbitHit m x) hn
    (fun r hin => catches_all_gives_orbit_hit m x traps r hc (hr.mem hin)) hs

theorem representative_system_zlength_lower_bound (m x : Int) (representatives traps : List Int) :
    OrbitRepresentativeSystem m x representatives → CatchesAll m x traps →
    Zlength representatives≤Zlength traps := by
  intro hs hc
  exact Int.ofNat_le.mpr (representative_system_lower_bound m x representatives traps hs hc)

theorem representative_system_implies_orbit_bounds (m x cycle_count : Int) (representatives : List Int) :
    OrbitRepresentativeSystem m x representatives → Zlength representatives=cycle_count+1 →
    P090_WalkBridge.OrbitCoverUpperBound m x cycle_count ∧ P090_WalkBridge.OrbitCoverLowerBound m x cycle_count := by
  intro hs hl
  refine ⟨⟨representatives,representative_system_catches_all m x representatives hs,hl⟩,?_⟩
  intro traps ht
  rw [←hl]
  exact representative_system_zlength_lower_bound m x representatives traps hs ht

theorem representative_system_implies_spec (m x cycle_count : Int) (representatives : List Int) :
    OrbitRepresentativeSystem m x representatives → Zlength representatives=cycle_count+1 → Spec m x (cycle_count+1) := by
  intro hs hl
  have hb := representative_system_implies_orbit_bounds m x cycle_count representatives hs hl
  exact P090_WalkBridge.orbit_cover_bounds_imply_spec m x cycle_count hb.1 hb.2

theorem order_input_exact_order_criterion (x modulus phi : Int) :
    OrderInput x modulus phi → P090_WalkFoundations.ExactOrderCriterion x modulus (Ord x modulus) := by
  intro hi
  exact ⟨by have := P090_WalkFoundations.ord_positive x modulus; omega,
    OrderExact.order_input_implies_order_power_law x modulus phi hi⟩

theorem stratum_representatives_lower_bound (m x gcd_value : Int) (representatives traps : List Int) :
    StratumRepresentativeSystem m x gcd_value representatives → CatchesAll m x traps →
    representatives.length≤traps.length := by
  rintro ⟨hn,hr,_,hs⟩ hc
  exact separated_witnesses_length representatives traps (OrbitHit m x) hn
    (fun r hin => catches_all_gives_orbit_hit m x traps r hc (hr.mem hin).1) hs

theorem zero_singleton_stratum_system (m x : Int) :
    0<m → StratumRepresentativeSystem m x m [0] := by
  intro hm
  refine ⟨by simp [NoDup],?_,?_,?_⟩
  · refine Forall.cons ⟨⟨by omega,hm⟩,?_⟩ Forall.nil
    rw [Z.gcd_0_l]
    exact (Z.abs_eq_iff m).mpr (by omega)
  · intro start hs hg
    have hd := Z.gcd_divide_l start m
    rw [hg] at hd
    have hd' := (Z.divide_iff_dvd m start).mp hd
    have hz : start % m=0 := Int.emod_eq_zero_of_dvd hd'
    have he : start=0 := by rw [Int.emod_eq_of_lt hs.1 hs.2] at hz; exact hz
    subst start
    exact ⟨0,by simp,orbit_hit_zero m x 0 hm ⟨by omega,hm⟩⟩
  · intro l r room hl hr _ _
    simp only [List.mem_singleton] at hl hr
    exact hl.trans hr.symm

theorem unit_orbit_list_length (modulus x unit : Int) :
    (UnitOrbitList modulus x unit).length=(Ord x modulus).toNat := by
  simp only [UnitOrbitList,List.length_map,List.length_range']

theorem unit_orbit_list_zlength (modulus x unit phi : Int) :
    OrderInput x modulus phi → Zlength (UnitOrbitList modulus x unit)=Ord x modulus := by
  intro hi
  unfold Zlength
  rw [unit_orbit_list_length]
  exact Int.toNat_of_nonneg (by have := P090_WalkFoundations.ord_positive x modulus; omega)

theorem nodup_map_on {A B : Type} (f : A→B) (items : List A) :
    NoDup items → (∀ left right, left∈items → right∈items → f left=f right → left=right) →
    NoDup (items.map f) := by
  intro hn hi
  exact List.Nodup.map_on (fun l hl r hr => hi l r hl hr) hn

theorem find_extensional_bool (test_left test_right : Int→Bool) (items : List Int) :
    (∀ item, test_left item=test_right item) → items.find? test_left=items.find? test_right := by
  intro he
  rw [funext he]

theorem canonical_key_in_and_related (relatedb : Int→Int→Bool) (relation : Int→Int→Prop)
    («universe» : List Int) (item : Int) :
    (∀ left right, relatedb left right=true ↔ relation left right) →
    (∀ value, relation value value) → item∈«universe» →
    CanonicalKey relatedb «universe» item∈«universe» ∧ relation item (CanonicalKey relatedb «universe» item) := by
  intro hr hrefl hin
  unfold CanonicalKey
  cases he : «universe».find? (relatedb item) with
  | some key => exact ⟨List.mem_of_find?_eq_some he,(hr item key).mp (List.find?_some he)⟩
  | none => exact False.elim ((List.find?_eq_none.mp he item hin) ((hr item item).mpr (hrefl item)))

theorem canonical_key_equal_on_class (relatedb : Int→Int→Bool) (relation : Int→Int→Prop)
    («universe» : List Int) (left right : Int) :
    (∀ a b, relatedb a b=true ↔ relation a b) → EquivalenceLaws relation → relation left right →
    CanonicalKey relatedb «universe» left=CanonicalKey relatedb «universe» right := by
  rintro hr ⟨hrefl,hs,ht⟩ hrel
  have he : ∀ candidate, relatedb left candidate=relatedb right candidate := by
    intro c
    apply Bool.eq_iff_iff.mpr
    rw [hr,hr]
    exact ⟨ht right left c (hs left right hrel),ht left right c hrel⟩
  unfold CanonicalKey
  rw [find_extensional_bool _ _ «universe» he]

theorem canonical_key_idempotent (relatedb : Int→Int→Bool) (relation : Int→Int→Prop)
    («universe» : List Int) (item : Int) :
    (∀ a b, relatedb a b=true ↔ relation a b) → EquivalenceLaws relation → item∈«universe» →
    CanonicalKey relatedb «universe» (CanonicalKey relatedb «universe» item)=CanonicalKey relatedb «universe» item := by
  intro hr hl hi
  exact (canonical_key_equal_on_class relatedb relation «universe» item _ hr hl
    (canonical_key_in_and_related relatedb relation «universe» item hr hl.1 hi).2).symm

theorem finite_quotient_nodup (relatedb : Int→Int→Bool) («universe» : List Int) :
    NoDup (FiniteQuotient relatedb «universe») := List.nodup_dedup _

theorem finite_quotient_key_in (relatedb : Int→Int→Bool) («universe» : List Int) (item : Int) :
    item∈«universe» → CanonicalKey relatedb «universe» item∈FiniteQuotient relatedb «universe» := by
  intro hi
  exact List.mem_dedup.mpr (List.mem_map.mpr ⟨item,hi,rfl⟩)

theorem finite_quotient_forall_universe (relatedb : Int→Int→Bool) (relation : Int→Int→Prop)
    («universe» : List Int) :
    (∀ left right, relatedb left right=true ↔ relation left right) → (∀ value, relation value value) →
    Forall (fun representative => representative∈«universe») (FiniteQuotient relatedb «universe») := by
  intro hr hrefl
  apply Forall.iff_forall_mem.mpr
  intro r hin
  rcases List.mem_map.mp (List.mem_dedup.mp hin) with ⟨item,hi,rfl⟩
  exact (canonical_key_in_and_related relatedb relation «universe» item hr hrefl hi).1

theorem finite_quotient_covers (relatedb : Int→Int→Bool) (relation : Int→Int→Prop)
    («universe» : List Int) :
    (∀ left right, relatedb left right=true ↔ relation left right) → (∀ value, relation value value) →
    ∀ item, item∈«universe» → ∃ representative, representative∈FiniteQuotient relatedb «universe» ∧ relation item representative := by
  intro hr hrefl item hi
  exact ⟨CanonicalKey relatedb «universe» item,finite_quotient_key_in relatedb «universe» item hi,
    (canonical_key_in_and_related relatedb relation «universe» item hr hrefl hi).2⟩

theorem finite_quotient_separated (relatedb : Int→Int→Bool) (relation : Int→Int→Prop)
    («universe» : List Int) :
    (∀ left right, relatedb left right=true ↔ relation left right) → EquivalenceLaws relation →
    ∀ left right, left∈FiniteQuotient relatedb «universe» → right∈FiniteQuotient relatedb «universe» →
      relation left right → left=right := by
  intro hr hl left right hinl hinr hrel
  rcases List.mem_map.mp (List.mem_dedup.mp hinl) with ⟨sl,hsl,hkl⟩
  rcases List.mem_map.mp (List.mem_dedup.mp hinr) with ⟨sr,hsr,hkr⟩
  have hfl : CanonicalKey relatedb «universe» left=left := by
    rw [←hkl]
    exact canonical_key_idempotent relatedb relation «universe» sl hr hl hsl
  have hfr : CanonicalKey relatedb «universe» right=right := by
    rw [←hkr]
    exact canonical_key_idempotent relatedb relation «universe» sr hr hl hsr
  exact hfl.symm.trans ((canonical_key_equal_on_class relatedb relation «universe» left right hr hl hrel).trans hfr)

private theorem mul_mod_left (a b m : Int) : ((a mod m)*b) mod m=(a*b) mod m := by
  change ((a.fmod m)*b).fmod m=(a*b).fmod m
  rw [Int.mul_fmod,Int.fmod_fmod,←Int.mul_fmod]

private theorem mul_mod_right (a b m : Int) : (a*(b mod m)) mod m=(a*b) mod m := by
  change (a*(b.fmod m)).fmod m=(a*b).fmod m
  rw [Int.mul_fmod,Int.fmod_fmod,←Int.mul_fmod]

theorem orbit_advance (modulus x start first extra : Int) :
    modulus≠0 → 0≤first → 0≤extra →
    (((start*Z.pow x first) mod modulus)*Z.pow x extra) mod modulus =
    (start*Z.pow x (first+extra)) mod modulus := by
  intro hm hf he
  rw [mul_mod_left,coq_pow_add x first extra hf he,mul_assoc]

theorem unit_orbit_list_forall_range (modulus x unit phi : Int) :
    OrderInput x modulus phi →
    Forall (fun room => 0≤room ∧ room<modulus) (UnitOrbitList modulus x unit) := by
  intro hi
  apply Forall.iff_forall_mem.mpr
  intro room hin
  rcases List.mem_map.mp hin with ⟨index,_,rfl⟩
  exact mod_bounds _ modulus (by have := hi.1; omega)

theorem unit_orbit_list_forall_unit (modulus x unit phi : Int) :
    OrderInput x modulus phi → (0≤unit ∧ unit<modulus) → Z.gcd unit modulus=1 →
    Forall (fun room => Z.gcd room modulus=1) (UnitOrbitList modulus x unit) := by
  intro hi hu hg
  apply Forall.iff_forall_mem.mpr
  intro room hin
  rcases List.mem_map.mp hin with ⟨index,_,rfl⟩
  rw [P090_WalkFoundations.gcd_stratum_preserved modulus x unit (Int.ofNat index)
    (by have := hi.1; omega) (Int.natCast_nonneg _) hi.2.2.1,hg]

theorem unit_orbit_list_member_is_hit (modulus x unit phi room : Int) :
    OrderInput x modulus phi → room∈UnitOrbitList modulus x unit → OrbitHit modulus x unit room := by
  intro hi hin
  rcases List.mem_map.mp hin with ⟨index,_,he⟩
  exact ⟨Int.ofNat index,Int.natCast_nonneg _,he.symm⟩

private theorem bounded_indices_distinct (modulus x unit phi left right : Int)
    (hi : OrderInput x modulus phi) (hu : 0≤unit ∧ unit<modulus) (hg : Z.gcd unit modulus=1)
    (hl : 0≤left ∧ left<Ord x modulus) (hr : 0≤right ∧ right<Ord x modulus)
    (hlt : left<right) :
    (unit*Z.pow x left) mod modulus≠(unit*Z.pow x right) mod modulus := by
  intro he
  have hc := order_input_exact_order_criterion x modulus phi hi
  have hm : 0<modulus := by have := hi.1; omega
  let advanced := (unit*Z.pow x left) mod modulus
  have har : 0≤advanced ∧ advanced<modulus := mod_bounds _ _ hm
  have hag : Z.gcd advanced modulus=1 :=
    (P090_WalkFoundations.gcd_stratum_preserved modulus x unit left hm hl.1 hi.2.2.1).trans hg
  have hreturn : (advanced*Z.pow x (right-left)) mod modulus=advanced := by
    dsimp [advanced]
    rw [orbit_advance modulus x unit left (right-left) (by omega) hl.1 (by omega)]
    simpa only [add_sub_cancel] using he.symm
  have hd := (P090_OrbitOptimality.unit_orbit_return_iff modulus x advanced (Ord x modulus)
    (right-left) (by have := hi.1; omega) har hag (by omega) hc).mp hreturn
  have htoo := Int.le_of_dvd (by omega : 0<right-left) ((Z.divide_iff_dvd _ _).mp hd)
  omega

theorem unit_orbit_list_nodup (modulus x unit phi : Int) :
    OrderInput x modulus phi → (0≤unit ∧ unit<modulus) → Z.gcd unit modulus=1 →
    NoDup (UnitOrbitList modulus x unit) := by
  intro hi hu hg
  unfold UnitOrbitList
  apply nodup_map_on
  · exact List.nodup_range'
  · intro left right hl hr he
    have ho : 0≤Ord x modulus := by have := P090_WalkFoundations.ord_positive x modulus; omega
    have hlb : 0≤Int.ofNat left ∧ Int.ofNat left<Ord x modulus := by
      have hn := (List.mem_range'_1.mp hl).2
      have heq : Int.ofNat (Ord x modulus).toNat=Ord x modulus := Int.toNat_of_nonneg ho
      refine ⟨Int.natCast_nonneg _,?_⟩
      rw [←heq]
      exact Int.ofNat_lt.mpr (by simpa only [Nat.zero_add] using hn)
    have hrb : 0≤Int.ofNat right ∧ Int.ofNat right<Ord x modulus := by
      have hn := (List.mem_range'_1.mp hr).2
      have heq : Int.ofNat (Ord x modulus).toNat=Ord x modulus := Int.toNat_of_nonneg ho
      refine ⟨Int.natCast_nonneg _,?_⟩
      rw [←heq]
      exact Int.ofNat_lt.mpr (by simpa only [Nat.zero_add] using hn)
    rcases lt_trichotomy (Int.ofNat left) (Int.ofNat right) with hlt|heq|hgt
    · exact False.elim (bounded_indices_distinct modulus x unit phi _ _ hi hu hg hlb hrb hlt he)
    · exact Int.ofNat_inj.mp heq
    · exact False.elim (bounded_indices_distinct modulus x unit phi _ _ hi hu hg hrb hlb hgt he.symm)

theorem unit_orbit_hit_in_list (modulus x unit phi room : Int) :
    OrderInput x modulus phi → (0≤unit ∧ unit<modulus) → Z.gcd unit modulus=1 →
    OrbitHit modulus x unit room → room∈UnitOrbitList modulus x unit := by
  rintro hi hu hg ⟨time,ht,rfl⟩
  obtain ⟨ho,hc⟩ := order_input_exact_order_criterion x modulus phi hi
  have hp : Z.pow x (Ord x modulus) mod modulus=1 :=
    (hc _ (by omega)).mpr ⟨1,by ring⟩
  have hr := mod_bounds time (Ord x modulus) ho
  have hi' : Int.ofNat (time mod Ord x modulus).toNat=time mod Ord x modulus := Int.toNat_of_nonneg hr.1
  apply List.mem_map.mpr
  refine ⟨(time mod Ord x modulus).toNat,?_,?_⟩
  · apply List.mem_range'_1.mpr
    constructor
    · omega
    · have heq : Int.ofNat (Ord x modulus).toNat=Ord x modulus := Int.toNat_of_nonneg (by omega)
      have hl : Int.ofNat (time mod Ord x modulus).toNat<Int.ofNat (Ord x modulus).toNat := by omega
      simpa only [Nat.zero_add] using Int.ofNat_lt.mp hl
  · rw [hi',←mul_mod_right unit (Z.pow x (time mod Ord x modulus)) modulus,
      ←mul_mod_right unit (Z.pow x time) modulus]
    rw [OrderExact.pow_divmod_remainder x modulus (Ord x modulus) time hi.1 ho ht hp]

theorem unit_orbit_list_exact (modulus x unit phi : Int) :
    OrderInput x modulus phi → (0≤unit ∧ unit<modulus) → Z.gcd unit modulus=1 →
    NoDup (UnitOrbitList modulus x unit) ∧ Zlength (UnitOrbitList modulus x unit)=Ord x modulus ∧
    (∀ room, room∈UnitOrbitList modulus x unit ↔ OrbitHit modulus x unit room) := by
  intro hi hu hg
  exact ⟨unit_orbit_list_nodup modulus x unit phi hi hu hg,unit_orbit_list_zlength modulus x unit phi hi,
    fun room => ⟨unit_orbit_list_member_is_hit modulus x unit phi room hi,
      unit_orbit_hit_in_list modulus x unit phi room hi hu hg⟩⟩

theorem orbit_hit_transitive (modulus x start middle room : Int) :
    modulus≠0 → OrbitHit modulus x start middle → OrbitHit modulus x middle room →
    OrbitHit modulus x start room := by
  rintro hm ⟨first,hf,rfl⟩ ⟨second,hs,rfl⟩
  exact ⟨first+second,by omega,orbit_advance modulus x start first second hm hf hs⟩

theorem unit_orbit_hit_symmetric (modulus x unit phi room : Int) :
    OrderInput x modulus phi → (0≤unit ∧ unit<modulus) → Z.gcd unit modulus=1 →
    OrbitHit modulus x unit room → OrbitHit modulus x room unit := by
  intro hi hu hg hh
  have hin := unit_orbit_hit_in_list modulus x unit phi room hi hu hg hh
  rcases List.mem_map.mp hin with ⟨index,hindex,rfl⟩
  obtain ⟨ho,hc⟩ := order_input_exact_order_criterion x modulus phi hi
  have heq : Int.ofNat (Ord x modulus).toNat=Ord x modulus := Int.toNat_of_nonneg (by omega)
  have hind : Int.ofNat index<Ord x modulus := by
    rw [←heq]
    exact Int.ofNat_lt.mpr (by simpa only [Nat.zero_add] using (List.mem_range'_1.mp hindex).2)
  have hp : Z.pow x (Ord x modulus) mod modulus=1 :=
    (hc _ (by omega)).mpr ⟨1,by ring⟩
  refine ⟨Ord x modulus-Int.ofNat index,by omega,?_⟩
  rw [orbit_advance modulus x unit (Int.ofNat index) (Ord x modulus-Int.ofNat index)
    (by have := hi.1; omega) (Int.natCast_nonneg _) (by omega),add_sub_cancel,
    ←mul_mod_right unit (Z.pow x (Ord x modulus)) modulus,hp,mul_one,mod_small unit modulus hu]

theorem unit_orbit_relatedb_true_iff (modulus x left phi right : Int) :
    OrderInput x modulus phi → (0≤left ∧ left<modulus) → Z.gcd left modulus=1 →
    (UnitOrbitRelatedb modulus x left right=true ↔ OrbitHit modulus x left right) := by
  intro hi hl hg
  change (UnitOrbitList modulus x left).any (fun member => right==member)=true ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨member,hin,he⟩
    have heq : right=member := by simpa using he
    subst member
    exact unit_orbit_list_member_is_hit modulus x left phi right hi hin
  · intro hh
    exact ⟨right,unit_orbit_hit_in_list modulus x left phi right hi hl hg hh,by simp⟩

theorem unit_orbit_equivalence_on_units (modulus x phi : Int) :
    OrderInput x modulus phi →
    (∀ unit, (0≤unit ∧ unit<modulus) → Z.gcd unit modulus=1 → OrbitHit modulus x unit unit) ∧
    (∀ left right, (0≤left ∧ left<modulus) → Z.gcd left modulus=1 →
      OrbitHit modulus x left right → OrbitHit modulus x right left) ∧
    (∀ left middle right, OrbitHit modulus x left middle → OrbitHit modulus x middle right →
      OrbitHit modulus x left right) := by
  intro hi
  exact ⟨fun unit hu _ => orbit_hit_zero modulus x unit (by have := hi.1; omega) hu,
    fun left right hl hg => unit_orbit_hit_symmetric modulus x left phi right hi hl hg,
    fun left middle right => orbit_hit_transitive modulus x left middle right (by have := hi.1; omega)⟩

end P090_OrbitQuotient

export P090_OrbitQuotient (
  orbit_hit_zero
  catches_all_gives_orbit_hit
  representative_system_catches_all
  separated_witnesses_length
  representative_system_lower_bound
  representative_system_zlength_lower_bound
  representative_system_implies_orbit_bounds
  representative_system_implies_spec
  order_input_exact_order_criterion
  stratum_representatives_lower_bound
  zero_singleton_stratum_system
  unit_orbit_list_length
  unit_orbit_list_zlength
  nodup_map_on
  find_extensional_bool
  canonical_key_in_and_related
  canonical_key_equal_on_class
  canonical_key_idempotent
  finite_quotient_nodup
  finite_quotient_key_in
  finite_quotient_forall_universe
  finite_quotient_covers
  finite_quotient_separated
  orbit_advance
  unit_orbit_list_forall_range
  unit_orbit_list_forall_unit
  unit_orbit_list_member_is_hit
  unit_orbit_list_nodup
  unit_orbit_hit_in_list
  unit_orbit_list_exact
  orbit_hit_transitive
  unit_orbit_hit_symmetric
  unit_orbit_relatedb_true_iff
  unit_orbit_equivalence_on_units)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
