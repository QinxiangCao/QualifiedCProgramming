import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_orbit_quotient
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_order_input_bridge
import Mathlib.Data.List.Perm.Basic

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_UnitOrbitPartition

theorem unit_residueb_true_iff (modulus unit : Int) :
    UnitResidueb modulus unit=true ↔ UnitResidue modulus unit := by
  simp only [UnitResidueb,UnitResidue,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]

theorem unit_residues_member_iff (modulus unit : Int) :
    2≤modulus → (unit∈UnitResidues modulus ↔ UnitResidue modulus unit) := by
  intro hm
  have hcast : Int.ofNat modulus.toNat=modulus := Int.toNat_of_nonneg (by omega)
  constructor
  · intro hin
    rcases List.mem_map.mp hin with ⟨index,hi,rfl⟩
    rcases List.mem_filter.mp hi with ⟨hib,hig⟩
    have hg : Z.gcd (Int.ofNat index) modulus=1 := by simpa only [beq_iff_eq] using hig
    have hbound : Int.ofNat index≤modulus := by
      have hn := (List.mem_range'_1.mp hib).2
      rw [←hcast]
      exact Int.ofNat_le.mpr (by omega)
    have hne : Int.ofNat index≠modulus := by
      intro he
      rw [he] at hg
      simp only [Z.gcd,Int.gcd_self,Int.ofNat_eq_coe,Int.natCast_natAbs,abs_of_nonneg (by omega : 0≤modulus)] at hg
      omega
    exact ⟨⟨Int.natCast_nonneg _,by omega⟩,hg⟩
  · rintro ⟨hu,hg⟩
    have hunit : Int.ofNat unit.toNat=unit := Int.toNat_of_nonneg hu.1
    have hpos : 0<unit := by
      have hz : Z.gcd 0 modulus=modulus := by
        rw [Z.gcd_0_l]
        exact (Z.abs_eq_iff modulus).mpr (by omega)
      by_contra h
      have he : unit=0 := by omega
      rw [he,hz] at hg
      omega
    apply List.mem_map.mpr
    refine ⟨unit.toNat,?_,hunit⟩
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range'_1.mpr
      have hlo : Int.ofNat 1≤Int.ofNat unit.toNat := by
        change (1:Int)≤Int.ofNat unit.toNat
        rw [hunit]
        omega
      have hhi : Int.ofNat unit.toNat<Int.ofNat modulus.toNat := by rw [hunit,hcast]; exact hu.2
      exact ⟨Int.ofNat_le.mp hlo,by have := Int.ofNat_lt.mp hhi; omega⟩
    · simpa only [hunit,beq_iff_eq] using hg

theorem unit_residues_nodup (modulus : Int) : NoDup (UnitResidues modulus) := by
  apply nodup_map_on
  · exact List.Nodup.filter _ List.nodup_range'
  · intro l r _ _ he
    exact Int.ofNat_inj.mp he

theorem unit_residues_zlength (modulus : Int) : Zlength (UnitResidues modulus)=EulerPhi modulus := by
  unfold UnitResidues Zlength
  rw [List.length_map]
  exact (P090_WalkFoundations.coprime_count_filter modulus modulus.toNat).symm

theorem unit_orbit_equivb_true_iff (modulus x phi left right : Int) :
    OrderInput x modulus phi →
    (UnitOrbitEquivb modulus x left right=true ↔ UnitOrbitEquiv modulus x left right) := by
  intro hi
  by_cases hl : UnitResidueb modulus left=true
  · have hlu := (unit_residueb_true_iff modulus left).mp hl
    simp only [UnitOrbitEquivb,UnitOrbitEquiv,hl,↓reduceIte,Bool.and_eq_true,
      unit_residueb_true_iff,unit_orbit_relatedb_true_iff modulus x left phi right hi hlu.1 hlu.2]
  · simp [UnitOrbitEquivb,UnitOrbitEquiv,hl]

private theorem equiv_on_unit (modulus x left right : Int) (hl : UnitResidue modulus left) :
    UnitOrbitEquiv modulus x left right ↔ UnitResidue modulus right ∧ OrbitHit modulus x left right := by
  simp only [UnitOrbitEquiv,(unit_residueb_true_iff modulus left).mpr hl,↓reduceIte]

theorem unit_orbit_equiv_laws (modulus x phi : Int) :
    OrderInput x modulus phi → EquivalenceLaws (UnitOrbitEquiv modulus x) := by
  intro hi
  have hm : modulus≠0 := by have := hi.1; omega
  refine ⟨?_,?_,?_⟩
  · intro item
    by_cases hitem : UnitResidueb modulus item=true
    · have hu := (unit_residueb_true_iff modulus item).mp hitem
      exact (equiv_on_unit modulus x item item hu).mpr ⟨hu,orbit_hit_zero modulus x item (by have := hi.1; omega) hu.1⟩
    · simp [UnitOrbitEquiv,hitem]
  · intro left right he
    by_cases hl : UnitResidueb modulus left=true
    · have hlu := (unit_residueb_true_iff modulus left).mp hl
      rcases (equiv_on_unit modulus x left right hlu).mp he with ⟨hru,hh⟩
      exact (equiv_on_unit modulus x right left hru).mpr
        ⟨hlu,unit_orbit_hit_symmetric modulus x left phi right hi hlu.1 hlu.2 hh⟩
    · have heq : left=right := by simpa [UnitOrbitEquiv,hl] using he
      subst right
      simp [UnitOrbitEquiv,hl]
  · intro left middle right hleft hright
    by_cases hl : UnitResidueb modulus left=true
    · have hlu := (unit_residueb_true_iff modulus left).mp hl
      rcases (equiv_on_unit modulus x left middle hlu).mp hleft with ⟨hmu,hh1⟩
      rcases (equiv_on_unit modulus x middle right hmu).mp hright with ⟨hru,hh2⟩
      exact (equiv_on_unit modulus x left right hlu).mpr ⟨hru,orbit_hit_transitive modulus x left middle right hm hh1 hh2⟩
    · have heq : left=middle := by simpa [UnitOrbitEquiv,hl] using hleft
      subst middle
      exact hright

theorem unit_representatives_nodup (modulus x : Int) : NoDup (UnitRepresentatives modulus x) :=
  finite_quotient_nodup _ _

theorem unit_representatives_forall_unit (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi →
    Forall (UnitResidue modulus) (UnitRepresentatives modulus x) := by
  intro hm hi
  have hf := finite_quotient_forall_universe (UnitOrbitEquivb modulus x) (UnitOrbitEquiv modulus x)
    (UnitResidues modulus) (fun l r => unit_orbit_equivb_true_iff modulus x phi l r hi)
    (unit_orbit_equiv_laws modulus x phi hi).1
  apply Forall.iff_forall_mem.mpr
  intro r hr
  exact (unit_residues_member_iff modulus r hm).mp (hf.mem hr)

theorem unit_representatives_cover (modulus x phi start : Int) :
    2≤modulus → OrderInput x modulus phi → UnitResidue modulus start →
    ∃ representative, representative∈UnitRepresentatives modulus x ∧ OrbitHit modulus x start representative := by
  intro hm hi hs
  rcases finite_quotient_covers (UnitOrbitEquivb modulus x) (UnitOrbitEquiv modulus x)
    (UnitResidues modulus) (fun l r => unit_orbit_equivb_true_iff modulus x phi l r hi)
    (unit_orbit_equiv_laws modulus x phi hi).1 start ((unit_residues_member_iff modulus start hm).mpr hs)
    with ⟨r,hr,he⟩
  exact ⟨r,hr,((equiv_on_unit modulus x start r hs).mp he).2⟩

theorem unit_representatives_separated (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi → OrbitSeparated modulus x (UnitRepresentatives modulus x) := by
  intro hm hi left right room hl hr hhl hhr
  have hu := unit_representatives_forall_unit modulus x phi hm hi
  have hlu := hu.mem hl
  have hru := hu.mem hr
  have hh : OrbitHit modulus x right left := orbit_hit_transitive modulus x right room left
    (by omega) hhr (unit_orbit_hit_symmetric modulus x left phi room hi hlu.1 hlu.2 hhl)
  exact (finite_quotient_separated (UnitOrbitEquivb modulus x) (UnitOrbitEquiv modulus x)
    (UnitResidues modulus) (fun l r => unit_orbit_equivb_true_iff modulus x phi l r hi)
    (unit_orbit_equiv_laws modulus x phi hi) right left hr hl
    ((equiv_on_unit modulus x right left hru).mpr ⟨hlu,hh⟩)).symm

theorem unit_representatives_stratum_system (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi →
    StratumRepresentativeSystem modulus x 1 (UnitRepresentatives modulus x) := by
  intro hm hi
  exact ⟨unit_representatives_nodup modulus x,unit_representatives_forall_unit modulus x phi hm hi,
    fun start hs hg => unit_representatives_cover modulus x phi start hm hi ⟨hs,hg⟩,
    unit_representatives_separated modulus x phi hm hi⟩

theorem nodup_concat_map_disjoint (items : List Int) (block : Int→List Int) :
    NoDup items → (∀ item, item∈items → NoDup (block item)) →
    (∀ left right common, left∈items → right∈items → common∈block left → common∈block right → left=right) →
    NoDup ((items.map block).flatten) := by
  intro hn
  induction items with
  | nil => intros; exact List.nodup_nil
  | cons item items ih =>
    intro hb hd
    rcases List.nodup_cons.mp hn with ⟨hnot,htail⟩
    simp only [List.map_cons,List.flatten_cons]
    apply List.nodup_append.mpr
    refine ⟨hb item (by simp),ih htail (fun i hi => hb i (by simp [hi]))
      (fun l r c hl hr => hd l r c (by simp [hl]) (by simp [hr])),?_⟩
    intro l hl r hr he
    subst r
    rcases List.mem_flatten.mp hr with ⟨otherBlock,ho,hlb⟩
    rcases List.mem_map.mp ho with ⟨other,hin,rfl⟩
    have heq := hd item other l (by simp) (by simp [hin]) hl hlb
    exact hnot (heq ▸ hin)

theorem unit_orbit_blocks_nodup (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi → NoDup (UnitOrbitBlocks modulus x) := by
  intro hm hi
  apply nodup_concat_map_disjoint
  · exact unit_representatives_nodup modulus x
  · intro r hr
    have hu := (unit_representatives_forall_unit modulus x phi hm hi).mem hr
    exact unit_orbit_list_nodup modulus x r phi hi hu.1 hu.2
  · intro l r c hl hr hcl hcr
    exact unit_representatives_separated modulus x phi hm hi l r c hl hr
      (unit_orbit_list_member_is_hit modulus x l phi c hi hcl)
      (unit_orbit_list_member_is_hit modulus x r phi c hi hcr)

theorem unit_orbit_blocks_member_iff (modulus x phi room : Int) :
    2≤modulus → OrderInput x modulus phi →
    (room∈UnitOrbitBlocks modulus x ↔ room∈UnitResidues modulus) := by
  intro hm hi
  constructor
  · intro hin
    rcases List.mem_flatten.mp hin with ⟨block,hb,hr⟩
    rcases List.mem_map.mp hb with ⟨r,hinr,rfl⟩
    have hu := (unit_representatives_forall_unit modulus x phi hm hi).mem hinr
    exact (unit_residues_member_iff modulus room hm).mpr
      ⟨(unit_orbit_list_forall_range modulus x r phi hi).mem hr,
        (unit_orbit_list_forall_unit modulus x r phi hi hu.1 hu.2).mem hr⟩
  · intro hr
    have hu := (unit_residues_member_iff modulus room hm).mp hr
    rcases unit_representatives_cover modulus x phi room hm hi hu with ⟨r,hinr,hh⟩
    have hru := (unit_representatives_forall_unit modulus x phi hm hi).mem hinr
    apply List.mem_flatten.mpr
    exact ⟨UnitOrbitList modulus x r,List.mem_map.mpr ⟨r,hinr,rfl⟩,
      unit_orbit_hit_in_list modulus x r phi room hi hru.1 hru.2
        (unit_orbit_hit_symmetric modulus x room phi r hi hu.1 hu.2 hh)⟩

theorem unit_orbit_blocks_permutation (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi →
    List.Perm (UnitOrbitBlocks modulus x) (UnitResidues modulus) := by
  intro hm hi
  exact (List.perm_ext_iff_of_nodup (unit_orbit_blocks_nodup modulus x phi hm hi)
    (unit_residues_nodup modulus)).mpr (fun room => unit_orbit_blocks_member_iff modulus x phi room hm hi)

theorem concat_map_constant_length (items : List Int) (block : Int→List Int) (size : Nat) :
    (∀ item, item∈items → (block item).length=size) →
    (items.map block).flatten.length=items.length*size := by
  induction items with
  | nil => intros; simp
  | cons item items ih =>
    intro hs
    simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons]
    rw [hs item (by simp),ih (fun i hi => hs i (by simp [hi]))]
    simp only [Nat.add_mul,Nat.one_mul]
    omega

theorem unit_representatives_product_count (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi →
    Zlength (UnitRepresentatives modulus x)*Ord x modulus=EulerPhi modulus := by
  intro hm hi
  have hl := (unit_orbit_blocks_permutation modulus x phi hm hi).length_eq
  change ((UnitRepresentatives modulus x).map (UnitOrbitList modulus x)).flatten.length=(UnitResidues modulus).length at hl
  rw [concat_map_constant_length (UnitRepresentatives modulus x) (UnitOrbitList modulus x)
    (Ord x modulus).toNat (fun item _ => unit_orbit_list_length modulus x item)] at hl
  have ho : Int.ofNat (Ord x modulus).toNat=Ord x modulus :=
    Int.toNat_of_nonneg (by have := P090_WalkFoundations.ord_positive x modulus; omega)
  rw [←unit_residues_zlength modulus]
  unfold Zlength
  rw [←ho]
  change Int.ofNat ((UnitRepresentatives modulus x).length*(Ord x modulus).toNat)=_
  exact congrArg Int.ofNat hl

theorem unit_representatives_order_divides_phi (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi → (Ord x modulus ∣ᶻ EulerPhi modulus) := by
  intro hm hi
  exact ⟨Zlength (UnitRepresentatives modulus x),(unit_representatives_product_count modulus x phi hm hi).symm⟩

theorem unit_representatives_quotient_count (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi →
    Zlength (UnitRepresentatives modulus x)=EulerPhi modulus /ᶻ Ord x modulus := by
  intro hm hi
  rw [←unit_representatives_product_count modulus x phi hm hi]
  exact (Int.mul_fdiv_cancel _ (by have := P090_WalkFoundations.ord_positive x modulus; omega)).symm

theorem unit_representatives_exact_package (modulus x phi : Int) :
    2≤modulus → OrderInput x modulus phi →
    UnitOrbitRepresentativeSystem modulus x (UnitRepresentatives modulus x) ∧
    Zlength (UnitRepresentatives modulus x)=EulerPhi modulus /ᶻ Ord x modulus ∧
    List.Perm (UnitOrbitBlocks modulus x) (UnitResidues modulus) := by
  intro hm hi
  exact ⟨unit_representatives_stratum_system modulus x phi hm hi,
    unit_representatives_quotient_count modulus x phi hm hi,unit_orbit_blocks_permutation modulus x phi hm hi⟩

theorem reduced_unit_representatives_exact (x modulus : Int) :
    2≤modulus → Z.gcd x modulus=1 →
    StratumRepresentativeSystem modulus (x mod modulus) 1 (UnitRepresentatives modulus (x mod modulus)) ∧
    Zlength (UnitRepresentatives modulus (x mod modulus))=EulerPhi modulus /ᶻ Ord (x mod modulus) modulus ∧
    List.Perm (UnitOrbitBlocks modulus (x mod modulus)) (UnitResidues modulus) := by
  intro hm hg
  have hi := coprime_implies_reduced_order_input x modulus (by omega) hg
  exact unit_representatives_exact_package modulus (x mod modulus) (EulerPhi modulus) hm hi

end P090_UnitOrbitPartition

export P090_UnitOrbitPartition (
  unit_residueb_true_iff
  unit_residues_member_iff
  unit_residues_nodup
  unit_residues_zlength
  unit_orbit_equivb_true_iff
  unit_orbit_equiv_laws
  unit_representatives_nodup
  unit_representatives_forall_unit
  unit_representatives_cover
  unit_representatives_separated
  unit_representatives_stratum_system
  nodup_concat_map_disjoint
  unit_orbit_blocks_nodup
  unit_orbit_blocks_member_iff
  unit_orbit_blocks_permutation
  concat_map_constant_length
  unit_representatives_product_count
  unit_representatives_order_divides_phi
  unit_representatives_quotient_count
  unit_representatives_exact_package
  reduced_unit_representatives_exact)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
