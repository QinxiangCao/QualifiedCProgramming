import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib
open AUXLib


open MaxMinLib

def ST_LEVELS : Int := 17

def PrefixArrayPrefix (l pref : List Int) (upto : Int) : Prop :=
  0 ≤ upto ∧ upto ≤ Zlength l ∧ Zlength pref = upto + 1 ∧ Znth 0 pref 0 = 0 ∧
    ∀ i, (0 ≤ i ∧ i < upto) → Znth (i+1) pref 0 = Znth i pref 0 + Znth i l 0

def PrefixSums (l pref : List Int) : Prop := PrefixArrayPrefix l pref (Zlength l)
def SparseArgmaxBuilt (ps st_slots : List Int) (len : Int) : Prop := Zlength ps = len ∧ Zlength st_slots = len * ST_LEVELS

def RangeArgmax (ps : List Int) (lo hi best : Int) : Prop :=
  0 ≤ lo ∧ lo ≤ best ∧ best ≤ hi ∧ hi < Zlength ps ∧ ∀ idx, (lo ≤ idx ∧ idx ≤ hi) → Znth idx ps 0 ≤ Znth best ps 0

-- Coq's five-tuples are left-associated products.
def Node : Type := (((Int × Int) × Int) × Int) × Int
def default_node : Node := ((((0,0),0),0),0)
def mkNode (value start lo hi best : Int) : Node := ((((value,start),lo),hi),best)
def node_value (nd : Node) : Int := nd.1.1.1.1
def node_start (nd : Node) : Int := nd.1.1.1.2
def node_lo (nd : Node) : Int := nd.1.1.2
def node_hi (nd : Node) : Int := nd.1.2
def node_best (nd : Node) : Int := nd.2

def heap_top_node (slots : List Node) : Node := Znth 0 slots default_node
def heap_top_value (slots : List Node) : Int := node_value (heap_top_node slots)
def heap_top_start (slots : List Node) : Int := node_start (heap_top_node slots)
def heap_top_lo (slots : List Node) : Int := node_lo (heap_top_node slots)
def heap_top_hi (slots : List Node) : Int := node_hi (heap_top_node slots)
def heap_top_best (slots : List Node) : Int := node_best (heap_top_node slots)

def NodeArrays (slots : List Node) (vals starts los his bests : List Int) : Prop :=
  Zlength vals = Zlength slots ∧ Zlength starts = Zlength slots ∧ Zlength los = Zlength slots ∧
    Zlength his = Zlength slots ∧ Zlength bests = Zlength slots ∧ ∀ idx, (0 ≤ idx ∧ idx < Zlength slots) →
      Znth idx vals 0 = node_value (Znth idx slots default_node) ∧ Znth idx starts 0 = node_start (Znth idx slots default_node) ∧
      Znth idx los 0 = node_lo (Znth idx slots default_node) ∧ Znth idx his 0 = node_hi (Znth idx slots default_node) ∧
      Znth idx bests 0 = node_best (Znth idx slots default_node)

def NodeHeapState (slots : List Node) (size : Int) : Prop :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.heap_ordered
    (slots.map node_value) size ∧
  (sublist 0 size slots = [] ∨
    max_value_of_subset (LE.le (α := Int))
      (fun nd => nd ∈ sublist 0 size slots) node_value (heap_top_value slots))

def FrontierPushPrefix (slots : List Node) (size : Int) (nd : Node) (slots_out : List Node) : Prop :=
  Zlength slots_out = Zlength slots ∧ List.Perm (nd :: sublist 0 size slots) (sublist 0 (size+1) slots_out)

def FrontierPopPrefix (slots : List Node) (size : Int) (popped : Node) (slots_out : List Node) : Prop :=
  Zlength slots_out = Zlength slots ∧ popped ∈ sublist 0 size slots ∧
    List.Perm (popped :: sublist 0 (size-1) slots_out) (sublist 0 size slots)

def FrontierPushFields (slots : List Node) (size value start lo hi best : Int) (slots_out : List Node) : Prop :=
  FrontierPushPrefix slots size (mkNode value start lo hi best) slots_out

def FrontierPopTop (slots : List Node) (size : Int) (slots_out : List Node) : Prop := FrontierPopPrefix slots size (heap_top_node slots) slots_out

def ChordCode (n start finish : Int) : Int := start * (n+1) + finish
def CodeStart (n code : Int) : Int := Z.div code (n+1)
def CodeEnd (n code : Int) : Int := Z.modulo code (n+1)
def ChordValueOfCode (ps : List Int) (n code : Int) : Int := Znth (CodeEnd n code) ps 0 - Znth (CodeStart n code - 1) ps 0

def ValidChordCode (ps : List Int) (n L R code : Int) : Prop :=
  Zlength ps = n+1 ∧ 1 ≤ CodeStart n code ∧ CodeStart n code ≤ CodeEnd n code ∧ CodeEnd n code ≤ n ∧
    L ≤ CodeEnd n code - CodeStart n code + 1 ∧ CodeEnd n code - CodeStart n code + 1 ≤ R

def SongCodesSum (ps : List Int) (n : Int) (codes : List Int) (total : Int) : Prop := total = sum (codes.map (fun code => ChordValueOfCode ps n code))

def ValidSongCodes (ps : List Int) (n L R k : Int) (codes : List Int) : Prop :=
  Zlength codes = k ∧ codes.Nodup ∧ Forall (ValidChordCode ps n L R) codes

def SuperPianoAnswerByPrefix (ps : List Int) (n L R k answer : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun codes => ValidSongCodes ps n L R k codes)
    (fun codes => sum (codes.map (fun code => ChordValueOfCode ps n code))) answer

def ValidNode (ps : List Int) (n L R : Int) (nd : Node) : Prop :=
  Zlength ps = n+1 ∧ 1 ≤ node_start nd ∧ node_start nd ≤ n ∧ node_start nd + L - 1 ≤ node_lo nd ∧
    node_lo nd ≤ node_hi nd ∧ node_hi nd ≤ min n (node_start nd + R - 1) ∧
    node_lo nd ≤ node_best nd ∧ node_best nd ≤ node_hi nd ∧
    node_value nd = Znth (node_best nd) ps 0 - Znth (node_start nd - 1) ps 0 ∧
    ∀ finish, (node_lo nd ≤ finish ∧ finish ≤ node_hi nd) → Znth finish ps 0 - Znth (node_start nd - 1) ps 0 ≤ node_value nd

def ValidNodeFields (ps : List Int) (n L R value start lo hi best : Int) : Prop := ValidNode ps n L R (mkNode value start lo hi best)

def NodeCoversCode (n : Int) (nd : Node) (code : Int) : Prop :=
  CodeStart n code = node_start nd ∧ (node_lo nd ≤ CodeEnd n code ∧ CodeEnd n code ≤ node_hi nd)

def ChosenDominatesRemaining (ps : List Int) (n L R : Int) (chosen : List Int) : Prop :=
  ∀ picked rest, picked ∈ chosen → ValidChordCode ps n L R rest → rest ∉ chosen → ChordValueOfCode ps n rest ≤ ChordValueOfCode ps n picked

def DisjointClosed (lo1 hi1 lo2 hi2 : Int) : Prop := hi1 < lo2 ∨ hi2 < lo1

def NodesDisjointForSameStart (nodes : List Node) : Prop :=
  nodes.Nodup ∧ ∀ nd1 nd2, nd1 ∈ nodes → nd2 ∈ nodes → nd1 ≠ nd2 → node_start nd1 = node_start nd2 →
    DisjointClosed (node_lo nd1) (node_hi nd1) (node_lo nd2) (node_hi nd2)

def NodesCoverRemaining (ps : List Int) (n L R : Int) (chosen : List Int) (nodes : List Node) : Prop :=
  ∀ code, ValidChordCode ps n L R code → code ∉ chosen → ∃ nd, nd ∈ nodes ∧ NodeCoversCode n nd code

def NodesExcludeChosen (n : Int) (chosen : List Int) (nodes : List Node) : Prop :=
  ∀ nd code, nd ∈ nodes → NodeCoversCode n nd code → code ∉ chosen

def FrontierState (ps : List Int) (n L R : Int) (chosen : List Int) (chosen_len total : Int) (nodes : List Node) : Prop :=
  ValidSongCodes ps n L R chosen_len chosen ∧ SongCodesSum ps n chosen total ∧ ChosenDominatesRemaining ps n L R chosen ∧
    Forall (ValidNode ps n L R) nodes ∧ NodesDisjointForSameStart nodes ∧ NodesCoverRemaining ps n L R chosen nodes ∧
    NodesExcludeChosen n chosen nodes

def FrontierSplitState (ps : List Int) (n L R : Int) (chosen : List Int) (chosen_len total : Int) (pending nodes : List Node) : Prop :=
  FrontierState ps n L R chosen chosen_len total (pending ++ nodes)

def InitialFrontierState (ps : List Int) (n L R : Int) (nodes : List Node) : Prop := FrontierState ps n L R [] 0 0 nodes

theorem Forall_permutation {A : Type} (P : A → Prop) (l l' : List A) (hp : l.Perm l') (hf : Forall P l) : Forall P l' :=
  Forall.iff_forall_mem.mpr (fun x hx => hf.mem (hp.mem_iff.mpr hx))

theorem NodesDisjointForSameStart_permutation (nodes nodes' : List Node) (hp : nodes.Perm nodes')
    (hd : NodesDisjointForSameStart nodes) : NodesDisjointForSameStart nodes' :=
  ⟨hp.nodup_iff.mp hd.1,fun a b ha hb hn hs => hd.2 a b (hp.mem_iff.mpr ha) (hp.mem_iff.mpr hb) hn hs⟩

theorem NodesCoverRemaining_permutation (ps : List Int) (n L R : Int) (chosen : List Int)
    (nodes nodes' : List Node) (hp : nodes.Perm nodes') (hc : NodesCoverRemaining ps n L R chosen nodes) :
    NodesCoverRemaining ps n L R chosen nodes' := by
  intro code hv hn
  obtain ⟨nd,hm,hnd⟩ := hc code hv hn
  exact ⟨nd,hp.mem_iff.mp hm,hnd⟩

theorem NodesExcludeChosen_permutation (n : Int) (chosen : List Int) (nodes nodes' : List Node)
    (hp : nodes.Perm nodes') (he : NodesExcludeChosen n chosen nodes) : NodesExcludeChosen n chosen nodes' :=
  fun nd code hn hc => he nd code (hp.mem_iff.mpr hn) hc

theorem FrontierState_permutation (ps : List Int) (n L R : Int) (chosen : List Int) (chosen_len total : Int)
    (nodes nodes' : List Node) (hp : nodes.Perm nodes') (hs : FrontierState ps n L R chosen chosen_len total nodes) :
    FrontierState ps n L R chosen chosen_len total nodes' :=
  ⟨hs.1,hs.2.1,hs.2.2.1,Forall_permutation _ nodes nodes' hp hs.2.2.2.1,
   NodesDisjointForSameStart_permutation nodes nodes' hp hs.2.2.2.2.1,
   NodesCoverRemaining_permutation ps n L R chosen nodes nodes' hp hs.2.2.2.2.2.1,
   NodesExcludeChosen_permutation n chosen nodes nodes' hp hs.2.2.2.2.2.2⟩

theorem frontier_split_push_single_pending_forms_frontier (ps : List Int) (n L R : Int) (chosen : List Int)
    (chosen_len total : Int) (slots : List Node) (hsize : Int) (nd : Node) (slots_out : List Node)
    (hp : FrontierPushPrefix slots hsize nd slots_out)
    (hs : FrontierSplitState ps n L R chosen chosen_len total [nd] (sublist 0 hsize slots)) :
    FrontierState ps n L R chosen chosen_len total (sublist 0 (hsize+1) slots_out) :=
  FrontierState_permutation ps n L R chosen chosen_len total _ _ hp.2 hs

theorem frontier_split_push_left_keeps_right_pending (ps : List Int) (n L R : Int) (chosen : List Int)
    (chosen_len total : Int) (left right : Node) (slots : List Node) (hsize : Int) (slots_out : List Node)
    (hp : FrontierPushPrefix slots hsize left slots_out)
    (hs : FrontierSplitState ps n L R chosen chosen_len total [left,right] (sublist 0 hsize slots)) :
    FrontierSplitState ps n L R chosen chosen_len total [right] (sublist 0 (hsize+1) slots_out) :=
  FrontierState_permutation ps n L R chosen chosen_len total _ _ ((List.Perm.swap right left _).trans (hp.2.cons right)) hs

theorem PrefixArrayPrefix_entry_abs_bound (l pref : List Int) (upto i : Int)
    (hp : PrefixArrayPrefix l pref upto)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < upto) → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000)
    (hi : 0 ≤ i ∧ i ≤ upto) : -1000*i ≤ Znth i pref 0 ∧ Znth i pref 0 ≤ 1000*i := by
  have hm : ∀ k : Nat, (k : Int) ≤ upto → -1000*(k : Int) ≤ Znth (k : Int) pref 0 ∧ Znth (k : Int) pref 0 ≤ 1000*(k : Int) := by
    intro k
    induction k with
    | zero => intro hk; simpa only [Int.natCast_zero,Int.mul_zero,hp.2.2.2.1] using And.intro (le_refl (0 : Int)) (le_refl (0 : Int))
    | succ k ih =>
      intro hk
      have hkr : 0 ≤ (k : Int) ∧ (k : Int) < upto := ⟨by omega,by omega⟩
      have hh := ih (by omega)
      have hbb := hb k hkr
      rw [Int.natCast_add,Int.natCast_one,hp.2.2.2.2 k hkr]
      constructor <;> omega
  simpa only [Int.toNat_of_nonneg hi.1] using hm i.toNat (by omega)

theorem PrefixArrayPrefix_functional (l pref1 pref2 : List Int) (upto : Int)
    (h1 : PrefixArrayPrefix l pref1 upto) (h2 : PrefixArrayPrefix l pref2 upto) : pref1 = pref2 := by
  apply (ListLib.list_eq_ext pref1 pref2 0).mpr
  refine ⟨h1.2.2.1.trans h2.2.2.1.symm,?_⟩
  intro i hi
  have hm : ∀ k : Nat, (k : Int) ≤ upto → Znth (k : Int) pref1 0 = Znth (k : Int) pref2 0 := by
    intro k
    induction k with
    | zero => intro hk; exact h1.2.2.2.1.trans h2.2.2.2.1.symm
    | succ k ih =>
      intro hk
      have hkr : 0 ≤ (k : Int) ∧ (k : Int) < upto := ⟨by omega,by omega⟩
      rw [Int.natCast_add,Int.natCast_one,h1.2.2.2.2 k hkr,h2.2.2.2.2 k hkr,ih (by omega)]
  have hir : 0 ≤ i ∧ i ≤ upto := ⟨hi.1,by have hh : Zlength pref1 = upto+1 := h1.2.2.1; change 0 ≤ i ∧ i < Zlength pref1 at hi; omega⟩
  simpa only [Int.toNat_of_nonneg hir.1] using hm i.toNat (by omega)

theorem PrefixSums_functional (l ps1 ps2 : List Int) (h1 : PrefixSums l ps1) (h2 : PrefixSums l ps2) : ps1 = ps2 :=
  PrefixArrayPrefix_functional l ps1 ps2 (Zlength l) h1 h2

theorem PrefixSums_diff_int_bounds (l ps : List Int) (n i j : Int) (hp : PrefixSums l ps)
    (hl : Zlength l = n) (hn : n ≤ 100000)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < n) → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000)
    (hi : 0 ≤ i ∧ i ≤ n) (hj : 0 ≤ j ∧ j ≤ n) :
    -2147483648 ≤ Znth i ps 0-Znth j ps 0 ∧ Znth i ps 0-Znth j ps 0 ≤ 2147483647 := by
  have hp' : PrefixArrayPrefix l ps n := hl ▸ hp
  have hbi := PrefixArrayPrefix_entry_abs_bound l ps n i hp' hb hi
  have hbj := PrefixArrayPrefix_entry_abs_bound l ps n j hp' hb hj
  omega

theorem ValidNodeFields_value_int_bound (l ps : List Int) (n L R value start lo hi best : Int)
    (hp : PrefixSums l ps) (hl : Zlength l = n) (hn : n ≤ 100000) (hL : 1 ≤ L)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < n) → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000)
    (hv : ValidNodeFields ps n L R value start lo hi best) : -2147483648 ≤ value ∧ value ≤ 2147483647 := by
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  obtain ⟨hplen,hs1,hsn,hlo,hloh,hhin,hlob,hbhi,hval,hmax⟩ := hv
  change hi ≤ min n (start+R-1) at hhin
  have hin := hhin.trans (min_le_left _ _)
  change value = Znth best ps 0-Znth (start-1) ps 0 at hval
  rw [hval]
  exact PrefixSums_diff_int_bounds l ps n best (start-1) hp hl hn hb ⟨by omega,by omega⟩ ⟨by omega,by omega⟩

theorem valid_chord_value_int_bound (l ps : List Int) (n L R code : Int) (hp : PrefixSums l ps)
    (hl : Zlength l = n) (hn : n ≤ 100000)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < n) → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000)
    (hv : ValidChordCode ps n L R code) :
    -2147483648 ≤ ChordValueOfCode ps n code ∧ ChordValueOfCode ps n code ≤ 2147483647 := by
  obtain ⟨hplen,hs1,hse,hen,hL,hR⟩ := hv
  exact PrefixSums_diff_int_bounds l ps n (CodeEnd n code) (CodeStart n code-1) hp hl hn hb ⟨by omega,hen⟩ ⟨by omega,by omega⟩

theorem chord_values_sum_int64_bound (l ps : List Int) (n L R : Int) (codes : List Int)
    (hp : PrefixSums l ps) (hl : Zlength l = n) (hn : n ≤ 100000)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < n) → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000)
    (hf : Forall (ValidChordCode ps n L R) codes) :
    -2147483648*Zlength codes ≤ sum (codes.map (fun code => ChordValueOfCode ps n code)) ∧
    sum (codes.map (fun code => ChordValueOfCode ps n code)) ≤ 2147483647*Zlength codes := by
  induction hf with
  | nil => exact ⟨le_refl _,le_refl _⟩
  | @cons c cs hc hf ih =>
    have hh := valid_chord_value_int_bound l ps n L R c hp hl hn hb hc
    simp only [Zlength_cons,List.map_cons,sum,List.foldr_cons] at ih ⊢
    constructor <;> omega

theorem frontier_total_int64_bound (l ps : List Int) (n L R : Int) (chosen : List Int)
    (chosen_len total : Int) (nodes : List Node) (hp : PrefixSums l ps) (hl : Zlength l = n) (hn : n ≤ 100000)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < n) → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000)
    (hs : FrontierState ps n L R chosen chosen_len total nodes) :
    -2147483648*chosen_len ≤ total ∧ total ≤ 2147483647*chosen_len := by
  have hh := chord_values_sum_int64_bound l ps n L R chosen hp hl hn hb hs.1.2.2
  rw [hs.1.1,← hs.2.1] at hh
  exact hh

private theorem sublist_len {A : Type} (l : List A) (hi : Int) (h : 0 ≤ hi ∧ hi ≤ Zlength l) :
    Zlength (sublist 0 hi l) = hi := by
  have hh := ListLib.Zlength_sublist 0 hi l ⟨le_refl _,h.1⟩ h.2
  simpa only [Int.sub_zero] using hh

private theorem nth_mem {A : Type} (l : List A) (d : A) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l := by
  have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
  change l.getD i.toNat d ∈ l
  rw [List.getD_eq_getElem l d hn]
  exact List.getElem_mem hn

theorem frontier_state_top_node_valid (ps : List Int) (n L R : Int) (chosen : List Int)
    (chosen_len total : Int) (slots : List Node) (hsize : Int) (hh : 0 < hsize) (hhl : hsize ≤ Zlength slots)
    (hs : FrontierState ps n L R chosen chosen_len total (sublist 0 hsize slots)) :
    ValidNodeFields ps n L R (heap_top_value slots) (heap_top_start slots) (heap_top_lo slots) (heap_top_hi slots) (heap_top_best slots) := by
  have hn := nth_mem (sublist 0 hsize slots) default_node 0 ⟨by omega,by rw [sublist_len slots hsize ⟨by omega,hhl⟩]; omega⟩
  have he : Znth 0 (sublist 0 hsize slots) default_node = heap_top_node slots := by
    simpa only [Int.add_zero] using Znth_sublist default_node 0 0 hsize slots (le_refl _) (by omega)
  rw [he] at hn
  have hv := hs.2.2.2.1.mem hn
  exact hv

private theorem missing_of_longer (codes chosen : List Int) (hd : codes.Nodup)
    (hl : chosen.length < codes.length) : ∃ code, code ∈ codes ∧ code ∉ chosen := by
  classical
  by_contra hh
  have hsub : codes ⊆ chosen := by intro c hc; by_contra hn; exact hh ⟨c,hc,hn⟩
  have hlen := (List.subperm_of_subset hd hsub).length_le
  omega

theorem frontier_state_nonempty_if_more_choices_remain (ps : List Int) (n L R k ans : Int)
    (chosen : List Int) (chosen_len total : Int) (slots : List Node) (hsize : Int)
    (ha : SuperPianoAnswerByPrefix ps n L R k ans)
    (hs : FrontierState ps n L R chosen chosen_len total (sublist 0 hsize slots))
    (hn : 0 ≤ hsize) (hl : hsize ≤ Zlength slots) (hmore : chosen_len < k) : 0 < hsize := by
  obtain ⟨codes,⟨hc,hm⟩,hval⟩ := ha
  have hlong : chosen.length < codes.length := by
    have h1 := hc.1
    have h2 := hs.1.1
    change (codes.length : Int) = k at h1
    change (chosen.length : Int) = chosen_len at h2
    omega
  obtain ⟨code,hcode,hmiss⟩ := missing_of_longer codes chosen hc.2.1 hlong
  obtain ⟨nd,hnd,hcover⟩ := hs.2.2.2.2.2.1 code (hc.2.2.mem hcode) hmiss
  have hpos : 0 < (sublist 0 hsize slots).length := List.length_pos_of_mem hnd
  have hlen := sublist_len slots hsize ⟨hn,hl⟩
  change ((sublist 0 hsize slots).length : Int) = hsize at hlen
  omega

theorem sum_map_remove_split (f : Int → Int) (pre : List Int) (x : Int) (post : List Int) :
    sum ((pre++x::post).map f) = f x+sum ((pre++post).map f) := by
  rw [List.map_append,List.map_append,sum_app,sum_app]
  simp only [List.map_cons,sum,List.foldr_cons]
  omega

theorem Forall_remove_split (P : Int → Prop) (pre : List Int) (x : Int) (post : List Int)
    (hf : Forall P (pre++x::post)) : Forall P (pre++post) := by
  apply Forall.iff_forall_mem.mpr
  intro y hy
  apply hf.mem
  rcases List.mem_append.mp hy with hpre | hpost
  · exact List.mem_append_left _ hpre
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hpost)

private theorem map_sum_perm (f : Int → Int) {xs ys : List Int} (hp : xs.Perm ys) :
    sum (xs.map f) = sum (ys.map f) := by
  induction hp with
  | nil => rfl
  | cons a hp ih => simpa only [List.map_cons,sum,List.foldr_cons] using congrArg (fun z => f a+z) ih
  | swap a b l => simp only [List.map_cons,sum,List.foldr_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem topk_sum_by_dominance (valid : Int → Prop) (f : Int → Int) (chosen codes : List Int)
    (hnc : chosen.Nodup) (hnd : codes.Nodup) (hl : Zlength codes = Zlength chosen)
    (hf : Forall valid codes)
    (hd : ∀ picked rest, picked ∈ chosen → rest ∈ codes → valid rest → rest ∉ chosen → f rest ≤ f picked) :
    sum (codes.map f) ≤ sum (chosen.map f) := by
  classical
  induction chosen generalizing codes with
  | nil =>
    have he : codes = [] := by
      cases codes with
      | nil => rfl
      | cons a l => rw [Zlength_cons,Zlength_nil] at hl; have := Zlength_nonneg l; omega
    subst codes; exact le_refl _
  | cons picked chosen ih =>
    obtain ⟨hpnot,htnodup⟩ := List.nodup_cons.mp hnc
    have hchoice : ∃ x rest, codes.Perm (x::rest) ∧ picked ∉ rest ∧ f x ≤ f picked := by
      by_cases hin : picked ∈ codes
      · obtain ⟨pre,post,he⟩ := List.append_of_mem hin
        rw [he] at hnd ⊢
        have hp : (pre++picked::post).Perm (picked::(pre++post)) := List.perm_middle
        exact ⟨picked,pre++post,hp,(List.nodup_cons.mp (hp.nodup_iff.mp hnd)).1,le_refl _⟩
      · have hlen : chosen.length < codes.length := by
          change (codes.length : Int) = ((picked::chosen).length : Int) at hl
          simp only [List.length_cons] at hl; omega
        obtain ⟨x,hxin,hxnot⟩ := missing_of_longer codes chosen hnd hlen
        obtain ⟨pre,post,he⟩ := List.append_of_mem hxin
        have hp : codes.Perm (x::(pre++post)) := by rw [he]; exact List.perm_middle
        have hxnc : x ∉ picked::chosen := by
          intro hx
          rcases List.mem_cons.mp hx with heq | hm
          · exact hin (heq ▸ hxin)
          · exact hxnot hm
        refine ⟨x,pre++post,hp,?_,hd picked x (List.mem_cons_self ..) hxin (hf.mem hxin) hxnc⟩
        intro hpr
        exact hin (hp.mem_iff.mpr (List.mem_cons_of_mem _ hpr))
    obtain ⟨x,rest,hperm,hprnot,hxle⟩ := hchoice
    have hrnodup := (List.nodup_cons.mp (hperm.nodup_iff.mp hnd)).2
    have hforall := Forall_permutation valid codes (x::rest) hperm hf
    have hrfor : Forall valid rest := Forall.iff_forall_mem.mpr (fun y hy => hforall.mem (List.mem_cons_of_mem _ hy))
    have hrestlen : Zlength rest = Zlength chosen := by
      have hlen := congrArg (fun z : Nat => (z : Int)) hperm.length_eq
      change (codes.length : Int) = ((picked::chosen).length : Int) at hl
      change (rest.length : Int) = (chosen.length : Int)
      simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hlen hl
      omega
    have hdomrest : ∀ p r, p ∈ chosen → r ∈ rest → valid r → r ∉ chosen → f r ≤ f p := by
      intro p r hp hr hv hn
      apply hd p r (List.mem_cons_of_mem _ hp) (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hr)) hv
      intro hfull
      rcases List.mem_cons.mp hfull with he | hmem
      · exact hprnot (he ▸ hr)
      · exact hn hmem
    have hsum := ih rest htnodup hrnodup hrestlen hrfor hdomrest
    rw [map_sum_perm f hperm]
    simp only [List.map_cons,sum,List.foldr_cons] at hsum ⊢
    omega

theorem frontier_state_complete_implies_answer (ps : List Int) (n L R k : Int) (chosen : List Int)
    (total : Int) (nodes : List Node) (hs : FrontierState ps n L R chosen k total nodes) :
    SuperPianoAnswerByPrefix ps n L R k total := by
  refine ⟨chosen,⟨hs.1,?_⟩,hs.2.1.symm⟩
  intro codes hc
  exact topk_sum_by_dominance (ValidChordCode ps n L R) (ChordValueOfCode ps n) chosen codes hs.1.2.1 hc.2.1
    (hc.1.trans hs.1.1.symm) hc.2.2 (fun p r hp hr hv hn => hs.2.2.1 p r hp hv hn)

theorem nth_Znth {A : Type} (d : A) (l : List A) (n : Nat) (hn : n < l.length) :
    l.getD n d = Znth (n : Int) l d := rfl

theorem in_sublist0_Znth {A : Type} (d : A) (hi : Int) (l : List A) (x : A)
    (hr : 0 ≤ hi ∧ hi ≤ Zlength l) (hx : x ∈ sublist 0 hi l) :
    ∃ i, (0 ≤ i ∧ i < hi) ∧ Znth i l d = x := by
  obtain ⟨k,hk,he⟩ := List.getElem_of_mem hx
  have hlen := sublist_len l hi hr
  change ((sublist 0 hi l).length : Int) = hi at hlen
  have hki : 0 ≤ (k : Int) ∧ (k : Int) < hi := ⟨by omega,by omega⟩
  refine ⟨k,hki,?_⟩
  have hget : Znth (k : Int) (sublist 0 hi l) d = x := by
    change (sublist 0 hi l).getD k d = x
    rw [List.getD_eq_getElem _ d hk]; exact he
  have hsub := Znth_sublist d 0 (k : Int) hi l (le_refl _) (by simpa only [Int.sub_zero] using hki)
  simpa only [Int.add_zero] using hsub.symm.trans hget

theorem chord_code_eta (n code : Int) (hn : 0 ≤ n) : code = ChordCode n (CodeStart n code) (CodeEnd n code) := by
  unfold ChordCode CodeStart CodeEnd Z.div Z.modulo
  have h := Int.fdiv_add_fmod code (n+1)
  nlinarith

theorem chord_code_eq_of_start_end (n code start finish : Int) (hn : 0 ≤ n)
    (hs : CodeStart n code = start) (he : CodeEnd n code = finish) : code = ChordCode n start finish := by
  rw [chord_code_eta n code hn,hs,he]

-- Coq's sumbool equality decision has computational content, represented by Decidable.
def node_eq_dec (nd1 nd2 : Node) : Decidable (nd1 = nd2) := by
  unfold Node at *
  exact inferInstance

theorem chord_code_start_end (n start finish : Int) (hn : 0 ≤ n) (hf : 0 ≤ finish ∧ finish ≤ n) :
    CodeStart n (ChordCode n start finish) = start ∧ CodeEnd n (ChordCode n start finish) = finish := by
  unfold CodeStart CodeEnd ChordCode Z.div Z.modulo
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega),Int.fmod_eq_emod_of_nonneg _ (by omega)]
  rw [show start*(n+1)+finish = finish+start*(n+1) by ring]
  rw [Int.add_mul_ediv_right finish start (by omega : n+1 ≠ 0),Int.add_mul_emod_self_right,
      Int.ediv_eq_zero_of_lt hf.1 (by omega),Int.emod_eq_of_lt hf.1 (by omega)]
  simp only [Int.zero_add,and_self]

theorem chord_value_of_chord_code (ps : List Int) (n start finish : Int) (hn : 0 ≤ n)
    (hf : 0 ≤ finish ∧ finish ≤ n) :
    ChordValueOfCode ps n (ChordCode n start finish) = Znth finish ps 0-Znth (start-1) ps 0 := by
  obtain ⟨hs,he⟩ := chord_code_start_end n start finish hn hf
  unfold ChordValueOfCode
  rw [hs,he]

theorem heap_top_node_fields_eq (slots : List Node) (value start lo hi best : Int)
    (hv : value = heap_top_value slots) (hs : start = heap_top_start slots)
    (hl : lo = heap_top_lo slots) (hh : hi = heap_top_hi slots) (hb : best = heap_top_best slots) :
    heap_top_node slots = mkNode value start lo hi best := by
  rw [hv,hs,hl,hh,hb]
  rfl

theorem valid_node_fields_chord_valid (ps : List Int) (n L R value start lo hi best : Int)
    (hL : 1 ≤ L) (hv : ValidNodeFields ps n L R value start lo hi best) :
    ValidChordCode ps n L R (ChordCode n start best) := by
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  obtain ⟨hl,hs1,hsn,hlo,hloh,hhin,hlob,hbhi,hval,hm⟩ := hv
  have hmin1 := hhin.trans (min_le_left _ _)
  have hmin2 := hhin.trans (min_le_right _ _)
  obtain ⟨hcs,hce⟩ := chord_code_start_end n start best (by omega) ⟨by omega,by omega⟩
  unfold ValidChordCode
  rw [hcs,hce]
  exact ⟨hl,hs1,by omega,by omega,by omega,by omega⟩

theorem valid_node_fields_covers_best (ps : List Int) (n L R value start lo hi best : Int)
    (hL : 1 ≤ L) (hv : ValidNodeFields ps n L R value start lo hi best) :
    NodeCoversCode n (mkNode value start lo hi best) (ChordCode n start best) := by
  have hc := valid_node_fields_chord_valid ps n L R value start lo hi best hL hv
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  obtain ⟨hl,hs1,hsn,hlo,hloh,hhin,hlob,hbhi,hval,hm⟩ := hv
  have hmin := hhin.trans (min_le_left _ _)
  obtain ⟨hcs,hce⟩ := chord_code_start_end n start best (by omega) ⟨by omega,by omega⟩
  exact ⟨hcs,by rw [hce]; exact ⟨hlob,hbhi⟩⟩

theorem valid_node_fields_code_value (ps : List Int) (n L R value start lo hi best : Int)
    (hL : 1 ≤ L) (hv : ValidNodeFields ps n L R value start lo hi best) :
    ChordValueOfCode ps n (ChordCode n start best) = value := by
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  obtain ⟨hl,hs1,hsn,hlo,hloh,hhin,hlob,hbhi,hval,hm⟩ := hv
  have hmin := hhin.trans (min_le_left _ _)
  rw [chord_value_of_chord_code ps n start best (by omega) ⟨by omega,by omega⟩]
  exact hval.symm

theorem node_covers_code_value_le (ps : List Int) (n L R : Int) (nd : Node) (code : Int)
    (hv : ValidNode ps n L R nd) (hc : NodeCoversCode n nd code) : ChordValueOfCode ps n code ≤ node_value nd := by
  unfold ChordValueOfCode
  rw [hc.1]
  exact hv.2.2.2.2.2.2.2.2.2 _ hc.2

theorem node_heap_state_sublist_bound (slots : List Node) (size : Int) (nd : Node)
    (hp : 0 < size) (hh : NodeHeapState slots size) (hn : nd ∈ sublist 0 size slots) : node_value nd ≤ heap_top_value slots := by
  rcases hh.2 with hempty | ⟨top,⟨_,hmax⟩,heq⟩
  · rw [hempty] at hn
    exact False.elim (List.not_mem_nil hn)
  · rw [←heq]
    exact hmax nd hn

theorem in_old_of_rest_perm {A : Type} (top : A) (rest old : List A) (x : A)
    (hp : (top::rest).Perm old) (hx : x ∈ rest) : x ∈ old := hp.mem_iff.mp (List.mem_cons_of_mem _ hx)

theorem in_rest_of_old_perm_neq {A : Type} (top : A) (rest old : List A) (x : A)
    (hp : (top::rest).Perm old) (hx : x ∈ old) (hn : x ≠ top) : x ∈ rest := by
  rcases List.mem_cons.mp (hp.mem_iff.mpr hx) with he | hm
  · exact False.elim (hn he)
  · exact hm

theorem top_not_in_rest_of_perm {A : Type} (top : A) (rest old : List A)
    (hp : (top::rest).Perm old) (hn : old.Nodup) : top ∉ rest := (List.nodup_cons.mp (hp.nodup_iff.mpr hn)).1

theorem rest_nodup_of_perm {A : Type} (top : A) (rest old : List A)
    (hp : (top::rest).Perm old) (hn : old.Nodup) : rest.Nodup := (List.nodup_cons.mp (hp.nodup_iff.mpr hn)).2

theorem disjoint_closed_no_overlap (lo1 hi1 lo2 hi2 x : Int) (hd : DisjointClosed lo1 hi1 lo2 hi2)
    (h1 : lo1 ≤ x ∧ x ≤ hi1) (h2 : lo2 ≤ x ∧ x ≤ hi2) : False := by
  rcases hd with h | h <;> omega

theorem valid_node_fields_left_child (ps : List Int) (n L R value start lo hi best retval : Int)
    (hv : ValidNodeFields ps n L R value start lo hi best) (ha : RangeArgmax ps lo (best-1) retval)
    (hn : lo ≤ best-1) : ValidNodeFields ps n L R (Znth retval ps 0-Znth (start-1) ps 0) start lo (best-1) retval := by
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv ⊢
  obtain ⟨hl,hs1,hsn,hlo,hloh,hhin,hlob,hbhi,hval,hm⟩ := hv
  exact ⟨hl,hs1,hsn,hlo,hn,by omega,ha.2.1,ha.2.2.1,rfl,
    fun finish hf => sub_le_sub_right (ha.2.2.2.2 finish hf) _⟩

theorem valid_node_fields_right_child (ps : List Int) (n L R value start lo hi best retval : Int)
    (hv : ValidNodeFields ps n L R value start lo hi best) (ha : RangeArgmax ps (best+1) hi retval) :
    ValidNodeFields ps n L R (Znth retval ps 0-Znth (start-1) ps 0) start (best+1) hi retval := by
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv ⊢
  obtain ⟨hl,hs1,hsn,hlo,hloh,hhin,hlob,hbhi,hval,hm⟩ := hv
  exact ⟨hl,hs1,hsn,by omega,by have := ha.2.1; have := ha.2.2.1; omega,hhin,ha.2.1,ha.2.2.1,rfl,
    fun finish hf => sub_le_sub_right (ha.2.2.2.2 finish hf) _⟩

theorem frontier_top_value_dominates_remaining (ps : List Int) (n L R : Int) (chosen : List Int)
    (chosen_len total : Int) (slots : List Node) (size code : Int) (hp : 0 < size)
    (hh : NodeHeapState slots size) (hs : FrontierState ps n L R chosen chosen_len total (sublist 0 size slots))
    (hc : ValidChordCode ps n L R code) (hn : code ∉ chosen) : ChordValueOfCode ps n code ≤ heap_top_value slots := by
  obtain ⟨nd,hnd,hcover⟩ := hs.2.2.2.2.2.1 code hc hn
  exact (node_covers_code_value_le ps n L R nd code (hs.2.2.2.1.mem hnd) hcover).trans
    (node_heap_state_sublist_bound slots size nd hp hh hnd)

private theorem split_frontier (ps : List Int) (n L R : Int) (chosen : List Int) (t total : Int)
    (old rest children : List Node) (value start lo hi best : Int)
    (hL : 1 ≤ L) (hs : FrontierState ps n L R chosen t total old)
    (hp : (mkNode value start lo hi best::rest).Perm old)
    (hv : ValidNodeFields ps n L R value start lo hi best)
    (hmax : ∀ code, ValidChordCode ps n L R code → code ∉ chosen → ChordValueOfCode ps n code ≤ value)
    (hchild : ∀ nd, nd ∈ children → ValidNode ps n L R nd ∧ node_start nd = start ∧
      lo ≤ node_lo nd ∧ node_hi nd ≤ hi ∧ (node_hi nd < best ∨ best < node_lo nd))
    (hdis : NodesDisjointForSameStart children)
    (hcover : ∀ finish, (lo ≤ finish ∧ finish ≤ hi) → finish ≠ best →
      ∃ nd, nd ∈ children ∧ node_lo nd ≤ finish ∧ finish ≤ node_hi nd) :
    FrontierSplitState ps n L R (ChordCode n start best::chosen) (t+1) (total+value) children rest := by
  let top := mkNode value start lo hi best
  let code := ChordCode n start best
  have htop : top ∈ old := hp.mem_iff.mp (List.mem_cons_self ..)
  have htopcover : NodeCoversCode n top code := valid_node_fields_covers_best ps n L R value start lo hi best hL hv
  have hcodevalid : ValidChordCode ps n L R code := valid_node_fields_chord_valid ps n L R value start lo hi best hL hv
  have hcodevalue : ChordValueOfCode ps n code = value := valid_node_fields_code_value ps n L R value start lo hi best hL hv
  have hv' := hv
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv'
  obtain ⟨hplen,hs1,hsn,hloL,hlohi,hin,hlob,hbhi,hval,hm⟩ := hv'
  have hinin := hin.trans (min_le_left _ _)
  have hbest : 0 ≤ best ∧ best ≤ n := ⟨by omega,by omega⟩
  have hcoord : CodeStart n code = start ∧ CodeEnd n code = best := chord_code_start_end n start best (by omega) hbest
  obtain ⟨hc,hsum,hdom,hvalid,hdisold,hcovold,hexold⟩ := hs
  have hrestN := rest_nodup_of_perm top rest old hp hdisold.1
  have htopnot := top_not_in_rest_of_perm top rest old hp hdisold.1
  have hrestold (nd : Node) (hn : nd ∈ rest) : nd ∈ old := in_old_of_rest_perm top rest old nd hp hn
  have hrestne (nd : Node) (hn : nd ∈ rest) : top ≠ nd := by intro he; exact htopnot (he ▸ hn)
  have hold_dis (nd : Node) (hn : nd ∈ rest) (hsame : start = node_start nd) :
      DisjointClosed lo hi (node_lo nd) (node_hi nd) := hdisold.2 top nd htop (hrestold nd hn) (hrestne nd hn) hsame
  have hchildrest (c d : Node) (hc : c ∈ children) (hd : d ∈ rest) (hstart : node_start c = node_start d) :
      DisjointClosed (node_lo c) (node_hi c) (node_lo d) (node_hi d) := by
    obtain ⟨_,hcs,hclo,hchi,hcbest⟩ := hchild c hc
    have hh := hold_dis d hd (hcs.symm.trans hstart)
    rcases hh with h | h
    · left; omega
    · right; omega
  have hnodup : (children++rest).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hdis.1,hrestN,?_⟩
    intro c hc d hd he
    subst d
    have hsep := hchildrest c c hc hd rfl
    have hcvalid := (hchild c hc).1
    have hrange : node_lo c ≤ node_best c ∧ node_best c ≤ node_hi c := ⟨hcvalid.2.2.2.2.2.2.1,hcvalid.2.2.2.2.2.2.2.1⟩
    exact disjoint_closed_no_overlap _ _ _ _ _ hsep hrange hrange
  have hnewvalid : ValidSongCodes ps n L R (t+1) (code::chosen) := by
    exact ⟨by rw [Zlength_cons,hc.1],List.nodup_cons.mpr ⟨hexold top code htop htopcover,hc.2.1⟩,.cons hcodevalid hc.2.2⟩
  refine ⟨hnewvalid,?_,?_,?_,⟨hnodup,?_⟩,?_,?_⟩
  · change total+value = sum ((code::chosen).map (ChordValueOfCode ps n))
    simp only [List.map_cons,sum,List.foldr_cons]
    have hsum' : total = sum (chosen.map (ChordValueOfCode ps n)) := hsum
    change total = List.foldr (·+·) 0 (chosen.map (ChordValueOfCode ps n)) at hsum'
    rw [hcodevalue,hsum']; ring
  · intro picked remaining hpick hvalidrem hnrem
    have hnold : remaining ∉ chosen := fun h => hnrem (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.mp hpick with he | hchosen
    · subst picked
      rw [hcodevalue]
      exact hmax remaining hvalidrem hnold
    · exact hdom picked remaining hchosen hvalidrem hnold
  · apply Forall.iff_forall_mem.mpr
    intro nd hn
    rcases List.mem_append.mp hn with hc | hr
    · exact (hchild nd hc).1
    · exact hvalid.mem (hrestold nd hr)
  · intro nd1 nd2 h1 h2 hn he
    rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
    · exact hdis.2 nd1 nd2 h1 h2 hn he
    · exact hchildrest nd1 nd2 h1 h2 he
    · have h := hchildrest nd2 nd1 h2 h1 he.symm
      rcases h with h | h
      · right; exact h
      · left; exact h
    · exact hdisold.2 nd1 nd2 (hrestold nd1 h1) (hrestold nd2 h2) hn he
  · intro other hvother hnother
    have hnold : other ∉ chosen := fun h => hnother (List.mem_cons_of_mem _ h)
    obtain ⟨nd,hnd,hndcovers⟩ := hcovold other hvother hnold
    by_cases he : nd = top
    · subst nd
      change CodeStart n other = start ∧ lo ≤ CodeEnd n other ∧ CodeEnd n other ≤ hi at hndcovers
      have hne : CodeEnd n other ≠ best := by
        intro hend
        have heq : other = code := chord_code_eq_of_start_end n other start best (by omega) hndcovers.1 hend
        exact hnother (heq ▸ List.mem_cons_self ..)
      obtain ⟨child,hmem,hlo',hhi'⟩ := hcover (CodeEnd n other) hndcovers.2 hne
      refine ⟨child,List.mem_append_left _ hmem,?_,hlo',hhi'⟩
      exact hndcovers.1.trans (hchild child hmem).2.1.symm
    · exact ⟨nd,List.mem_append_right _ (in_rest_of_old_perm_neq top rest old nd hp hnd he),hndcovers⟩
  · intro nd other hn hothercovers hinchosen
    rcases List.mem_append.mp hn with hchildmem | hrestmem
    · obtain ⟨hcv,hcs,hclo,hchi,hcbest⟩ := hchild nd hchildmem
      rcases List.mem_cons.mp hinchosen with he | hchosenold
      · subst other
        have hrange := hothercovers.2
        rw [hcoord.2] at hrange
        rcases hcbest with h | h <;> omega
      · apply hexold top other htop _ hchosenold
        exact ⟨hothercovers.1.trans hcs,by change lo ≤ CodeEnd n other ∧ CodeEnd n other ≤ hi; have := hothercovers.2; constructor <;> omega⟩
    · rcases List.mem_cons.mp hinchosen with he | hchosenold
      · subst other
        have hh := hold_dis nd hrestmem (hcoord.1.symm.trans hothercovers.1)
        have hrange := hothercovers.2
        rw [hcoord.2] at hrange
        exact disjoint_closed_no_overlap _ _ _ _ best hh ⟨hlob,hbhi⟩ hrange
      · exact hexold nd other (hrestold nd hrestmem) hothercovers hchosenold

theorem frontier_pop_to_split_both_children (ps : List Int) (n L R : Int) (chosen : List Int) (t total : Int)
    (slots : List Node) (size : Int) (slots_out : List Node) (value start lo hi best retval retval_2 : Int)
    (hL : 1 ≤ L) (hsize : 0 < size)
    (hs : FrontierState ps n L R chosen t total (sublist 0 size slots))
    (hpop : FrontierPopTop slots size slots_out) (hheap : NodeHeapState slots size)
    (hv : ValidNodeFields ps n L R value start lo hi best)
    (hvalue : value = heap_top_value slots) (hstart : start = heap_top_start slots)
    (hlo : lo = heap_top_lo slots) (hhi : hi = heap_top_hi slots) (hbest : best = heap_top_best slots)
    (hleft : RangeArgmax ps lo (best-1) retval) (hln : lo ≤ best-1)
    (hright : RangeArgmax ps (best+1) hi retval_2) (hrn : best+1 ≤ hi) :
    FrontierSplitState ps n L R (ChordCode n start best::chosen) (t+1) (total+value)
      [mkNode (Znth retval ps 0-Znth (start-1) ps 0) start lo (best-1) retval,mkNode (Znth retval_2 ps 0-Znth (start-1) ps 0) start (best+1) hi retval_2] (sublist 0 (size-1) slots_out) := by
  have htop := heap_top_node_fields_eq slots value start lo hi best hvalue hstart hlo hhi hbest
  have hp := hpop.2.2
  rw [htop] at hp
  have hshape := hv
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hshape
  have hlv := valid_node_fields_left_child ps n L R value start lo hi best retval hv hleft hln
  have hrv := valid_node_fields_right_child ps n L R value start lo hi best retval_2 hv hright
  apply split_frontier ps n L R chosen t total (sublist 0 size slots) (sublist 0 (size-1) slots_out)
    [mkNode (Znth retval ps 0-Znth (start-1) ps 0) start lo (best-1) retval,mkNode (Znth retval_2 ps 0-Znth (start-1) ps 0) start (best+1) hi retval_2] value start lo hi best hL hs hp hv
  · intro code hc hn
    rw [hvalue]
    exact frontier_top_value_dominates_remaining ps n L R chosen t total slots size code hsize hheap hs hc hn
  · intro nd hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with he | he <;> subst nd
    · exact ⟨hlv,rfl,le_refl _,by dsimp only [node_hi,mkNode]; omega,Or.inl (by dsimp only [node_hi,mkNode]; omega)⟩
    · exact ⟨hrv,rfl,by dsimp only [node_lo,mkNode]; omega,le_refl _,Or.inr (by dsimp only [node_lo,mkNode]; omega)⟩
  · constructor
    · apply List.nodup_cons.mpr
      refine ⟨?_,by simp⟩
      intro hn
      have he := List.mem_singleton.mp hn
      have hproj := congrArg node_lo he
      dsimp only [node_lo,mkNode] at hproj
      omega
    · intro a b ha hb hne hs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst a <;> subst b
      · exact False.elim (hne rfl)
      · left; dsimp only [node_hi,node_lo,mkNode]; omega
      · right; dsimp only [node_hi,node_lo,mkNode]; omega
      · exact False.elim (hne rfl)
  · intro finish hf hn
    by_cases he : finish < best
    · refine ⟨_,List.mem_cons_self ..,?_,?_⟩ <;> dsimp only [node_hi,node_lo,mkNode] <;> omega
    · refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_,?_⟩ <;> dsimp only [node_hi,node_lo,mkNode] <;> omega

theorem frontier_pop_to_split_left_only (ps : List Int) (n L R : Int) (chosen : List Int) (t total : Int)
    (slots : List Node) (size : Int) (slots_out : List Node) (value start lo hi best retval : Int)
    (hL : 1 ≤ L) (hsize : 0 < size)
    (hs : FrontierState ps n L R chosen t total (sublist 0 size slots))
    (hpop : FrontierPopTop slots size slots_out) (hheap : NodeHeapState slots size)
    (hv : ValidNodeFields ps n L R value start lo hi best)
    (hvalue : value = heap_top_value slots) (hstart : start = heap_top_start slots)
    (hlo : lo = heap_top_lo slots) (hhi : hi = heap_top_hi slots) (hbest : best = heap_top_best slots)
    (hleft : RangeArgmax ps lo (best-1) retval) (hln : lo ≤ best-1) (hrn : hi ≤ best) :
    FrontierSplitState ps n L R (ChordCode n start best::chosen) (t+1) (total+value)
      [mkNode (Znth retval ps 0-Znth (start-1) ps 0) start lo (best-1) retval] (sublist 0 (size-1) slots_out) := by
  have htop := heap_top_node_fields_eq slots value start lo hi best hvalue hstart hlo hhi hbest
  have hp := hpop.2.2
  rw [htop] at hp
  have hshape := hv
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hshape
  have hlv := valid_node_fields_left_child ps n L R value start lo hi best retval hv hleft hln
  apply split_frontier ps n L R chosen t total (sublist 0 size slots) (sublist 0 (size-1) slots_out)
    [mkNode (Znth retval ps 0-Znth (start-1) ps 0) start lo (best-1) retval] value start lo hi best hL hs hp hv
  · intro code hc hn
    rw [hvalue]
    exact frontier_top_value_dominates_remaining ps n L R chosen t total slots size code hsize hheap hs hc hn
  · intro nd hn
    have he := List.mem_singleton.mp hn
    subst nd
    exact ⟨hlv,rfl,le_refl _,by dsimp only [node_hi,mkNode]; omega,Or.inl (by dsimp only [node_hi,mkNode]; omega)⟩
  · refine ⟨by simp,?_⟩
    intro a b ha hb hn he
    have ha := List.mem_singleton.mp ha
    have hb := List.mem_singleton.mp hb
    exact False.elim (hn (ha.trans hb.symm))
  · intro finish hf hn
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;> dsimp only [node_hi,node_lo,mkNode] <;> omega

theorem frontier_pop_to_split_right_only (ps : List Int) (n L R : Int) (chosen : List Int) (t total : Int)
    (slots : List Node) (size : Int) (slots_out : List Node) (value start lo hi best retval : Int)
    (hL : 1 ≤ L) (hsize : 0 < size)
    (hs : FrontierState ps n L R chosen t total (sublist 0 size slots))
    (hpop : FrontierPopTop slots size slots_out) (hheap : NodeHeapState slots size)
    (hv : ValidNodeFields ps n L R value start lo hi best)
    (hvalue : value = heap_top_value slots) (hstart : start = heap_top_start slots)
    (hlo : lo = heap_top_lo slots) (hhi : hi = heap_top_hi slots) (hbest : best = heap_top_best slots)
    (hright : RangeArgmax ps (best+1) hi retval) (hln : best ≤ lo) :
    FrontierSplitState ps n L R (ChordCode n start best::chosen) (t+1) (total+value)
      [mkNode (Znth retval ps 0-Znth (start-1) ps 0) start (best+1) hi retval] (sublist 0 (size-1) slots_out) := by
  have htop := heap_top_node_fields_eq slots value start lo hi best hvalue hstart hlo hhi hbest
  have hp := hpop.2.2
  rw [htop] at hp
  have hshape := hv
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hshape
  have hrv := valid_node_fields_right_child ps n L R value start lo hi best retval hv hright
  apply split_frontier ps n L R chosen t total (sublist 0 size slots) (sublist 0 (size-1) slots_out)
    [mkNode (Znth retval ps 0-Znth (start-1) ps 0) start (best+1) hi retval] value start lo hi best hL hs hp hv
  · intro code hc hn
    rw [hvalue]
    exact frontier_top_value_dominates_remaining ps n L R chosen t total slots size code hsize hheap hs hc hn
  · intro nd hn
    have he := List.mem_singleton.mp hn
    subst nd
    exact ⟨hrv,rfl,by dsimp only [node_lo,mkNode]; omega,le_refl _,Or.inr (by dsimp only [node_lo,mkNode]; omega)⟩
  · refine ⟨by simp,?_⟩
    intro a b ha hb hn he
    have ha := List.mem_singleton.mp ha
    have hb := List.mem_singleton.mp hb
    exact False.elim (hn (ha.trans hb.symm))
  · intro finish hf hn
    refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;> dsimp only [node_hi,node_lo,mkNode] <;> omega

theorem frontier_pop_to_split_singleton (ps : List Int) (n L R : Int) (chosen : List Int) (t total : Int)
    (slots : List Node) (size : Int) (slots_out : List Node) (value start lo hi best : Int)
    (hL : 1 ≤ L) (hsize : 0 < size)
    (hs : FrontierState ps n L R chosen t total (sublist 0 size slots))
    (hpop : FrontierPopTop slots size slots_out) (hheap : NodeHeapState slots size)
    (hv : ValidNodeFields ps n L R value start lo hi best)
    (hvalue : value = heap_top_value slots) (hstart : start = heap_top_start slots)
    (hlo : lo = heap_top_lo slots) (hhi : hi = heap_top_hi slots) (hbest : best = heap_top_best slots)
    (hloeq : lo = best) (hhieq : best = hi) :
    FrontierSplitState ps n L R (ChordCode n start best::chosen) (t+1) (total+value)
      [] (sublist 0 (size-1) slots_out) := by
  have htop := heap_top_node_fields_eq slots value start lo hi best hvalue hstart hlo hhi hbest
  have hp := hpop.2.2
  rw [htop] at hp
  have hshape := hv
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hshape
  apply split_frontier ps n L R chosen t total (sublist 0 size slots) (sublist 0 (size-1) slots_out)
    [] value start lo hi best hL hs hp hv
  · intro code hc hn
    rw [hvalue]
    exact frontier_top_value_dominates_remaining ps n L R chosen t total slots size code hsize hheap hs hc hn
  · intro nd hn; cases hn
  · exact ⟨by simp,fun a b ha => by cases ha⟩
  · intro finish hf hn; exact False.elim (hn (by omega))

end SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib
open AUXLib

abbrev Power2 (j : Int) : Int := Z.pow 2 j
def PianoSparseProgress (ps table : List Int) (n level upto : Int) : Prop :=
  ∀ row column : Int, 0 ≤ row → (0 ≤ column ∧ column < ST_LEVELS) →
    row + Power2 column ≤ n → (column < level ∨ (column = level ∧ row < upto)) →
    RangeArgmax ps row (row + Power2 column - 1) (Znth (row * ST_LEVELS + column) table 0)

end SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib
namespace SimpleC.EE.LLM_bench.Algorithms.super_piano
export super_piano_lib (Power2 PianoSparseProgress)
end SimpleC.EE.LLM_bench.Algorithms.super_piano

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib
open AUXLib

def PianoSparseTable (ps table : List Int) (n : Int) : Prop :=
  ∀ row column : Int, 0 ≤ row → (0 ≤ column ∧ column < ST_LEVELS) →
    row + Power2 column ≤ n →
    RangeArgmax ps row (row + Power2 column - 1) (Znth (row * ST_LEVELS + column) table 0)
def PianoSwap (slots : List Node) (a b : Int) : List Node :=
  replace_Znth b (Znth a slots default_node) (replace_Znth a (Znth b slots default_node) slots)
def PianoHeapPush (before current : List Node) (size child : Int) (nd : Node) : Prop :=
  FrontierPushPrefix before size nd current ∧
  SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.PushLoopState
    ((sublist 0 size before).map node_value ++ [node_value nd])
    ((sublist 0 (size + 1) current).map node_value) size child (node_value nd)
def PianoHeapPop (before current : List Node) (size index : Int) : Prop :=
  FrontierPopTop before size current ∧
  SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.PopLoopState
    ((sublist 0 size before).map node_value) ((sublist 0 size current).map node_value) size index
def PianoHeapSelected (current : List Node) (size index selected : Int) : Prop :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.PopSelectedChild
    ((sublist 0 (size + 1) current).map node_value) size index selected
def PianoInitialPrefix (ps : List Int) (n L R upto : Int) (nodes : List Node) : Prop :=
  Forall (fun nd => ValidNode ps n L R nd ∧ (1 ≤ node_start nd ∧ node_start nd < upto) ∧
    node_lo nd = node_start nd + L - 1 ∧ node_hi nd = min n (node_start nd + R - 1)) nodes ∧
  Permutation (nodes.map node_start) ((List.range (upto - 1).toNat).map (fun i => 1 + (i : Int)))
def PianoNodes (vals starts los his bests : List Int) : List Node :=
  (List.zip vals (List.zip starts (List.zip los (List.zip his bests)))).map
    (fun p => mkNode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib
namespace SimpleC.EE.LLM_bench.Algorithms.super_piano
export super_piano_lib (PianoSparseTable PianoSwap PianoHeapPush PianoHeapPop PianoHeapSelected PianoInitialPrefix PianoNodes)
end SimpleC.EE.LLM_bench.Algorithms.super_piano
