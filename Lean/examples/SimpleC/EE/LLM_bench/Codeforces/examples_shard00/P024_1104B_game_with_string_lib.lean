import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length
import AUXLib.ZParity

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib
open AUXLib


def OneEqualPairDeletion (before after : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength before - 1) ∧ Znth i before 0 = Znth (i + 1) before 0 ∧
    after = sublist 0 i before ++ sublist (i + 2) (Zlength before) before

def DeletionGameTrace (initial : List Int) (states : List (List Int)) : Prop :=
  0 < Zlength states ∧ Znth 0 states [] = initial ∧
  (∀ k, (0 ≤ k ∧ k < Zlength states - 1) → OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states [])) ∧
  (∀ next, ¬ OneEqualPairDeletion (Znth (Zlength states - 1) states []) next)

def FollowsDeletionStrategy (turn_parity : Bool) (strategy : List (List Int) → List Int) (states : List (List Int)) : Prop :=
  ∀ k, (0 ≤ k ∧ k < Zlength states - 1) → Z.even k = turn_parity →
    Znth (k + 1) states [] = strategy (sublist 0 (k + 1) states)

def FirstPlayerWinsDeletionGame (s : List Int) : Prop :=
  ∀ states, DeletionGameTrace s states → Z.even (Zlength states - 1) = false

def PairDeletionTraceTo (initial final : List Int) (moves : Int) : Prop :=
  0 ≤ moves ∧ ∃ states, Zlength states = moves + 1 ∧ Znth 0 states [] = initial ∧ Znth moves states [] = final ∧
    (∀ k, (0 ≤ k ∧ k < moves) → OneEqualPairDeletion (Znth k states []) (Znth (k + 1) states []))

def PairDeletionIrreducible (s : List Int) : Prop := ∀ next, ¬ OneEqualPairDeletion s next

def PrefixGameState («prefix» reduced : List Int) (moves : Int) : Prop :=
  PairDeletionTraceTo «prefix» reduced moves ∧ PairDeletionIrreducible reduced ∧
    (∀ states, DeletionGameTrace «prefix» states → Zlength states = moves + 1)

def Pre (s : List Int) : Prop :=
  (1 ≤ Zlength s ∧ Zlength s ≤ 100000) ∧ Forall (fun c => 97 ≤ c ∧ c ≤ 122) s

def Spec (s : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ FirstPlayerWinsDeletionGame s)



set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem nth_append {A : Type} (d : A) (l r : List A) (i : Int) (hi : 0≤i ∧ i<Zlength l) :
    Znth i (l++r) d=Znth i l d := ListLib.app_Znth1 d l r i hi

theorem len_prefix {A : Type} (n : Int) (l : List A) (hn : 0≤n ∧ n≤Zlength l) :
    Zlength (sublist 0 n l)=n := ListLib.Zlength_sublist0 n l hn

-- The anonymous stack transition used verbatim in the Coq fold_left interfaces.
def stackStep (st : List Int) (c : Int) : List Int :=
  match st with
  | [] => [c]
  | x::xs => if x=c then xs else c::st

theorem one_equal_pair_deletion_decompose__stack_transitions (before after : List Int)
    (hd : OneEqualPairDeletion before after) : ∃ l c r, before=l++c::c::r ∧ after=l++r := by
  obtain ⟨i,hi,he,ha⟩:=hd
  refine ⟨sublist 0 i before,Znth i before 0,sublist (i+2) (Zlength before) before,?_,ha⟩
  calc
    before = sublist 0 (Zlength before) before := (sublist_self before (Zlength before) rfl).symm
    _ = sublist 0 i before++sublist i (Zlength before) before := sublist_split _ _ _ _ (by omega) (by omega)
    _ = _ := by
      rw [sublist_split i (Zlength before) (i+1) before (by omega) (by omega),
        sublist_split (i+1) (Zlength before) (i+2) before (by omega) (by omega),
        sublist_single 0 i before (by omega)]
      rw [show i+2=(i+1)+1 by omega,sublist_single 0 (i+1) before (by omega),←he]
      rfl

theorem one_equal_pair_deletion_length__stack_transitions (before after : List Int)
    (hd : OneEqualPairDeletion before after) : Zlength after=Zlength before-2 := by
  obtain ⟨l,c,r,he,ha⟩:=one_equal_pair_deletion_decompose__stack_transitions _ _ hd
  rw [he,ha]
  simp only [Zlength_app,Zlength_cons]
  omega

theorem pair_deletion_irreducible_adjacent__stack_transitions (s : List Int) :
    PairDeletionIrreducible s ↔ ∀ i, (0≤i ∧ i<Zlength s-1) → Znth i s 0≠Znth (i+1) s 0 := by
  constructor
  · intro h i hi he;exact h _ ⟨i,hi,he,rfl⟩
  · intro h next hd;obtain ⟨i,hi,he,_⟩:=hd;exact h i hi he

theorem pair_deletion_irreducible_tail__stack_transitions (a : Int) (s : List Int)
    (hi : PairDeletionIrreducible (a::s)) : PairDeletionIrreducible s := by
  apply (pair_deletion_irreducible_adjacent__stack_transitions s).mpr
  intro i hb
  have hh := (pair_deletion_irreducible_adjacent__stack_transitions _).mp hi (i+1) (by rw [Zlength_cons];omega)
  rw [Znth_cons 0 (i+1) a s (by omega),Znth_cons 0 (i+1+1) a s (by omega)] at hh
  simpa only [show i+1-1=i by omega,show i+1+1-1=i+1 by omega] using hh

private theorem irreducible_nil : PairDeletionIrreducible [] := by
  apply (pair_deletion_irreducible_adjacent__stack_transitions _).mpr
  intro i hi;change 0≤i ∧ i< -1 at hi;omega

private theorem head_ne (a b : Int) (s : List Int) (h : PairDeletionIrreducible (a::b::s)) : a≠b :=
  (pair_deletion_irreducible_adjacent__stack_transitions _).mp h 0 (by simp only [Zlength_cons];have := Zlength_nonneg s;omega)

theorem pair_deletion_stack_step_irreducible__stack_transitions (st : List Int) (c : Int)
    (hi : PairDeletionIrreducible st) : PairDeletionIrreducible (stackStep st c) := by
  cases st with
  | nil =>
    apply (pair_deletion_irreducible_adjacent__stack_transitions _).mpr
    intro i hb;change 0≤i ∧ i<0 at hb;omega
  | cons x xs =>
    simp only [stackStep]
    split_ifs with he
    · exact pair_deletion_irreducible_tail__stack_transitions x xs hi
    · apply (pair_deletion_irreducible_adjacent__stack_transitions _).mpr
      intro i hb
      by_cases hz : i=0
      · subst i;exact Ne.symm he
      · rw [Znth_cons 0 i c (x::xs) (by omega),Znth_cons 0 (i+1) c (x::xs) (by omega)]
        have hh := (pair_deletion_irreducible_adjacent__stack_transitions _).mp hi (i-1) (by simp only [Zlength_cons] at hb ⊢;omega)
        simpa only [show i-1+1=i by omega,show i+1-1=i by omega] using hh

theorem pair_deletion_stack_step_involutive__stack_transitions (st : List Int) (c : Int)
    (hi : PairDeletionIrreducible st) : stackStep (stackStep st c) c=st := by
  cases st with
  | nil => simp [stackStep]
  | cons x xs =>
    by_cases he : x=c
    · rw [he] at hi ⊢
      cases xs with
      | nil => simp [stackStep]
      | cons y ys =>
        have hh:=head_ne c y ys hi
        simp [stackStep,Ne.symm hh]
    · simp [stackStep,he]

theorem pair_deletion_fold_irreducible__stack_transitions (input st : List Int)
    (hi : PairDeletionIrreducible st) : PairDeletionIrreducible (input.foldl stackStep st) := by
  induction input generalizing st with
  | nil => exact hi
  | cons a input ih => exact ih _ (pair_deletion_stack_step_irreducible__stack_transitions st a hi)

theorem one_equal_pair_deletion_fold_invariant__stack_transitions (before after st : List Int)
    (hd : OneEqualPairDeletion before after) (hi : PairDeletionIrreducible st) :
    before.foldl stackStep st=after.foldl stackStep st := by
  obtain ⟨l,c,r,he,ha⟩:=one_equal_pair_deletion_decompose__stack_transitions _ _ hd
  rw [he,ha,List.foldl_append,List.foldl_append]
  simp only [List.foldl_cons]
  rw [pair_deletion_stack_step_involutive__stack_transitions _ c (pair_deletion_fold_irreducible__stack_transitions l st hi)]

def stackBoundary (st s : List Int) : Prop := match st,s with | x::_,a::_=>x≠a | _,_=>True

theorem pair_deletion_fold_irreducible_word__stack_transitions (s st : List Int)
    (hi : PairDeletionIrreducible s)
    (hb : stackBoundary st s) : s.foldl stackStep st=s.reverse++st := by
  induction s generalizing st with
  | nil => rfl
  | cons a s ih =>
    have ht:=pair_deletion_irreducible_tail__stack_transitions a s hi
    have hn : stackBoundary (a::st) s := by
      cases s with
      | nil => trivial
      | cons b t => exact head_ne a b t hi
    have hstep : stackStep st a=a::st := by
      cases st with
      | nil => rfl
      | cons x xs => exact if_neg hb
    rw [List.foldl_cons,hstep,ih _ ht hn,List.reverse_cons,List.append_assoc]
    rfl

theorem pair_deletion_fold_irreducible_empty__stack_transitions (s : List Int)
    (hi : PairDeletionIrreducible s) : s.foldl stackStep []=s.reverse := by
  simpa only [List.append_nil] using pair_deletion_fold_irreducible_word__stack_transitions s [] hi (by cases s <;> trivial)

theorem pair_deletion_states_invariant_nat__stack_transitions (n : Nat) (states : List (List Int))
    (hl : Zlength states=(n:Int)+1)
    (hs : ∀ k, (0≤k ∧ k<(n:Int)) → OneEqualPairDeletion (Znth k states []) (Znth (k+1) states [])) :
    (Znth 0 states []).foldl stackStep []=(Znth (n:Int) states []).foldl stackStep [] ∧
    Zlength (Znth 0 states [])=Zlength (Znth (n:Int) states [])+2*(n:Int) := by
  induction n generalizing states with
  | zero => constructor <;> simp
  | succ n ih =>
    cases states with
    | nil => simp only [Zlength_nil,Nat.cast_succ] at hl;omega
    | cons s0 rest =>
      cases rest with
      | nil => simp only [Zlength_cons,Zlength_nil,Nat.cast_succ] at hl;omega
      | cons s1 tail =>
        have hf : OneEqualPairDeletion s0 s1 := hs 0 (by omega)
        have htl : Zlength (s1::tail)=(n:Int)+1 := by simp only [Zlength_cons,Nat.cast_succ] at hl ⊢;omega
        have hts : ∀ k, (0≤k ∧ k<(n:Int)) → OneEqualPairDeletion (Znth k (s1::tail) []) (Znth (k+1) (s1::tail) []) := by
          intro k hk
          have hh:=hs (k+1) (by omega)
          rw [Znth_cons [] (k+1) s0 _ (by omega),Znth_cons [] (k+1+1) s0 _ (by omega)] at hh
          simpa only [show k+1-1=k by omega,show k+1+1-1=k+1 by omega] using hh
        obtain ⟨hfold,hlen⟩:=ih (s1::tail) htl hts
        rw [Nat.cast_succ,Znth0_cons,Znth_cons [] (n+1) s0 _ (by omega)]
        simp only [Nat.cast_succ,add_sub_cancel_right,Znth0_cons] at hfold hlen ⊢
        refine ⟨(one_equal_pair_deletion_fold_invariant__stack_transitions s0 s1 [] hf irreducible_nil).trans hfold,?_⟩
        have hh:=one_equal_pair_deletion_length__stack_transitions _ _ hf
        omega

theorem pair_deletion_trace_invariants__stack_transitions (initial final : List Int) (moves : Int)
    (ht : PairDeletionTraceTo initial final moves) : initial.foldl stackStep []=final.foldl stackStep [] ∧
    Zlength initial=Zlength final+2*moves := by
  obtain ⟨hm,states,hl,hfirst,hlast,hs⟩:=ht
  have he : (moves.toNat:Int)=moves := Int.toNat_of_nonneg hm
  have hh:=pair_deletion_states_invariant_nat__stack_transitions moves.toNat states (by omega) (by intro k hk;exact hs k (by omega))
  rwa [hfirst,he,hlast] at hh

theorem pair_deletion_normal_form_unique__stack_transitions (initial final1 : List Int) (moves1 : Int)
    (final2 : List Int) (moves2 : Int) (ht1 : PairDeletionTraceTo initial final1 moves1)
    (hi1 : PairDeletionIrreducible final1) (ht2 : PairDeletionTraceTo initial final2 moves2)
    (hi2 : PairDeletionIrreducible final2) : final1=final2 ∧ moves1=moves2 := by
  obtain ⟨hf1,hl1⟩:=pair_deletion_trace_invariants__stack_transitions _ _ _ ht1
  obtain ⟨hf2,hl2⟩:=pair_deletion_trace_invariants__stack_transitions _ _ _ ht2
  rw [pair_deletion_fold_irreducible_empty__stack_transitions final1 hi1] at hf1
  rw [pair_deletion_fold_irreducible_empty__stack_transitions final2 hi2] at hf2
  have he : final1=final2 := List.reverse_injective (hf1.symm.trans hf2)
  rw [he] at hl1
  exact ⟨he,by omega⟩


theorem one_equal_pair_deletion_compose__stack_transitions (l : List Int) (c : Int) (r : List Int) :
    OneEqualPairDeletion (l++c::c::r) (l++r) := by
  refine ⟨Zlength l,?_,?_,?_⟩
  · simp only [Zlength_app,Zlength_cons];have := Zlength_nonneg l;have := Zlength_nonneg r;omega
  · rw [app_Znth2 0 l (c::c::r) (Zlength l) (by omega),app_Znth2 0 l (c::c::r) (Zlength l+1) (by omega)]
    simp only [Int.sub_self,add_sub_cancel_left]
    rfl
  · rw [sublist_app_exact1]
    have he : l++c::c::r=(l++[c,c])++r := by rw [List.append_assoc];rfl
    rw [he,sublist_split_app_r _ _ (Zlength l+2) (l++[c,c]) r (by simp only [Zlength_app,Zlength_cons,Zlength_nil];omega) (by simp only [Zlength_app,Zlength_cons,Zlength_nil];have := Zlength_nonneg r;omega)]
    rw [Int.sub_self,show Zlength ((l++[c,c])++r)-(Zlength l+2)=Zlength r by simp only [Zlength_app,Zlength_cons,Zlength_nil];omega,sublist_self r (Zlength r) rfl]

theorem one_equal_pair_deletion_append__stack_transitions (before after suffix : List Int)
    (hd : OneEqualPairDeletion before after) : OneEqualPairDeletion (before++suffix) (after++suffix) := by
  obtain ⟨l,c,r,he,ha⟩:=one_equal_pair_deletion_decompose__stack_transitions _ _ hd
  rw [he,ha,List.append_assoc,List.append_assoc]
  exact one_equal_pair_deletion_compose__stack_transitions l c (r++suffix)

theorem Znth_map_in_range__stack_transitions (A B : Type) (f : A→B) (l : List A) (i : Int) (da : A)
    (hi : 0≤i ∧ i<Zlength l) : Znth i (l.map f) (f da)=f (Znth i l da) := by
  have hk : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi;omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hk,Option.map_some,Option.getD_some]

private theorem nth_map {A B : Type} (f : A→B) (l : List A) (i : Int) (da : A) (db : B)
    (hi : 0≤i ∧ i<Zlength l) : Znth i (l.map f) db=f (Znth i l da) := by
  rw [Znth_indep (l.map f) i db (f da) (by simpa only [Zlength,List.length_map] using hi)]
  exact Znth_map_in_range__stack_transitions A B f l i da hi

theorem pair_deletion_trace_append__stack_transitions (initial final : List Int) (moves : Int) (suffix : List Int)
    (ht : PairDeletionTraceTo initial final moves) : PairDeletionTraceTo (initial++suffix) (final++suffix) moves := by
  obtain ⟨hm,states,hlen,hfirst,hlast,hs⟩:=ht
  refine ⟨hm,states.map (fun s=>s++suffix),?_,?_,?_,?_⟩
  · simpa only [Zlength,List.length_map] using hlen
  · rw [nth_map _ states 0 [] [] (by omega),hfirst]
  · rw [nth_map _ states moves [] [] (by omega),hlast]
  · intro k hk
    rw [nth_map _ states k [] [] (by omega),nth_map _ states (k+1) [] [] (by omega)]
    exact one_equal_pair_deletion_append__stack_transitions _ _ suffix (hs k hk)

theorem pair_deletion_trace_snoc__stack_transitions (initial middle final : List Int) (moves : Int)
    (ht : PairDeletionTraceTo initial middle moves) (hd : OneEqualPairDeletion middle final) :
    PairDeletionTraceTo initial final (moves+1) := by
  obtain ⟨hm,states,hlen,hfirst,hlast,hs⟩:=ht
  refine ⟨by omega,states++[final],?_,?_,?_,?_⟩
  · simp only [Zlength_app,Zlength_cons,Zlength_nil];omega
  · rw [nth_append [] states [final] 0 (by omega)];exact hfirst
  · rw [app_Znth2 [] states [final] (moves+1) (by omega),show moves+1-Zlength states=0 by omega];rfl
  · intro k hk
    by_cases he : k=moves
    · rw [he,nth_append [] states [final] moves (by omega),app_Znth2 [] states [final] (moves+1) (by omega),show moves+1-Zlength states=0 by omega,Znth0_cons,hlast]
      exact hd
    · rw [nth_append [] states [final] k (by omega),nth_append [] states [final] (k+1) (by omega)]
      exact hs k (by omega)

theorem deletion_game_trace_to_pair__stack_transitions (initial : List Int) (states : List (List Int))
    (ht : DeletionGameTrace initial states) :
    PairDeletionTraceTo initial (Znth (Zlength states-1) states []) (Zlength states-1) ∧
    PairDeletionIrreducible (Znth (Zlength states-1) states []) := by
  obtain ⟨hp,hf,hs,hi⟩:=ht
  exact ⟨⟨by omega,states,by omega,hf,rfl,hs⟩,hi⟩

theorem prefix_game_state_of_normal_trace__stack_transitions (initial final : List Int) (moves : Int)
    (ht : PairDeletionTraceTo initial final moves) (hi : PairDeletionIrreducible final) : PrefixGameState initial final moves := by
  refine ⟨ht,hi,?_⟩
  intro states hg
  obtain ⟨hother,hotheri⟩:=deletion_game_trace_to_pair__stack_transitions initial states hg
  have hh:=pair_deletion_normal_form_unique__stack_transitions initial final moves _ _ ht hi hother hotheri
  omega

theorem pair_deletion_irreducible_prefix__stack_transitions (l suffix : List Int)
    (hi : PairDeletionIrreducible (l++suffix)) : PairDeletionIrreducible l := by
  intro next hn
  exact hi (next++suffix) (one_equal_pair_deletion_append__stack_transitions l next suffix hn)

theorem pair_deletion_irreducible_snoc__stack_transitions (reduced : List Int) (c : Int)
    (hi : PairDeletionIrreducible reduced)
    (hb : reduced=[] ∨ (0<Zlength reduced ∧ Znth (Zlength reduced-1) reduced 0≠c)) :
    PairDeletionIrreducible (reduced++[c]) := by
  apply (pair_deletion_irreducible_adjacent__stack_transitions _).mpr
  intro i hi'
  simp only [Zlength_app,Zlength_cons,Zlength_nil] at hi'
  by_cases hii : i<Zlength reduced-1
  · rw [nth_append 0 reduced [c] i (by omega),nth_append 0 reduced [c] (i+1) (by omega)]
    exact (pair_deletion_irreducible_adjacent__stack_transitions _).mp hi i (by omega)
  · have he : i=Zlength reduced-1 := by omega
    obtain hn | ⟨hp,hn⟩:=hb
    · rw [hn,Zlength_nil] at hi';omega
    · rw [he,nth_append 0 reduced [c] _ (by omega),app_Znth2 0 reduced [c] _ (by omega),show Zlength reduced-1+1-Zlength reduced=0 by omega,Znth0_cons]
      exact hn

theorem list_snoc_as_sublist_last__stack_transitions (s : List Int) (hp : 0<Zlength s) :
    s=sublist 0 (Zlength s-1) s++[Znth (Zlength s-1) s 0] := by
  calc
    s=sublist 0 (Zlength s) s := (sublist_self _ _ rfl).symm
    _=sublist 0 (Zlength s-1) s++sublist (Zlength s-1) (Zlength s) s := sublist_split _ _ _ _ (by omega) (by omega)
    _=_ := by rw [show sublist (Zlength s-1) (Zlength s) s=[Znth (Zlength s-1) s 0] from by convert sublist_single 0 (Zlength s-1) s (by omega) using 1;congr 1;omega]

theorem prefix_game_state_push__stack_transitions («prefix» reduced : List Int) (moves c : Int)
    (hs : PrefixGameState «prefix» reduced moves)
    (hb : reduced=[] ∨ (0<Zlength reduced ∧ Znth (Zlength reduced-1) reduced 0≠c)) :
    PrefixGameState («prefix»++[c]) (reduced++[c]) moves :=
  prefix_game_state_of_normal_trace__stack_transitions _ _ _
    (pair_deletion_trace_append__stack_transitions _ _ _ [c] hs.1)
    (pair_deletion_irreducible_snoc__stack_transitions _ _ hs.2.1 hb)

theorem prefix_game_state_pop_pair__stack_transitions («prefix» reduced : List Int) (moves c : Int)
    (hs : PrefixGameState «prefix» reduced moves) (hp : 0<Zlength reduced)
    (hl : Znth (Zlength reduced-1) reduced 0=c) :
    PrefixGameState («prefix»++[c]) (sublist 0 (Zlength reduced-1) reduced) (moves+1) := by
  let short := sublist 0 (Zlength reduced-1) reduced
  have hsnoc : reduced=short++[c] := by rw [←hl];exact list_snoc_as_sublist_last__stack_transitions reduced hp
  have hdel : OneEqualPairDeletion (reduced++[c]) short := by
    rw [hsnoc,List.append_assoc]
    exact (by simpa only [List.append_nil] using one_equal_pair_deletion_compose__stack_transitions short c [])
  apply prefix_game_state_of_normal_trace__stack_transitions
  · exact pair_deletion_trace_snoc__stack_transitions _ _ _ _ (pair_deletion_trace_append__stack_transitions _ _ _ [c] hs.1) hdel
  · apply pair_deletion_irreducible_prefix__stack_transitions short [c]
    rw [←hsnoc]
    exact hs.2.1

theorem sentinel_nonzero_index_bound__stack_transitions (text : List Int) (i : Int)
    (hi : 0≤i ∧ i≤Zlength text) (hn : Znth i (text++[0]) 0≠0) : i<Zlength text := by
  by_contra hh
  have he : i=Zlength text := by omega
  rw [he,app_Znth2 0 text [0] _ (by omega),Int.sub_self,Znth0_cons] at hn
  exact hn rfl

theorem terminator_zero_index_eq_length__final_result (text : List Int) (i : Int)
    (hi : 0≤i ∧ i≤Zlength text) (hc : ∀ j, (0≤j ∧ j<Zlength text) → 97≤Znth j text 0 ∧ Znth j text 0≤122)
    (hz : Znth i (text++[0]) 0=0) : i=Zlength text := by
  by_contra hh
  rw [nth_append 0 text [0] i (by omega)] at hz
  have := hc i (by omega)
  omega

theorem prefix_game_state_spec_parity__final_result («prefix» reduced : List Int) (moves : Int)
    (hs : PrefixGameState «prefix» reduced moves) : Spec «prefix» (Z.land moves 1) := by
  obtain ⟨⟨hm,states,hlen,hfirst,hfinal,hsteps⟩,hir,hall⟩:=hs
  have hland : Z.land moves 1=moves%2 := by
    have hh:=Z.land_ones moves 1 (by omega)
    change Z.land moves 1=Int.fmod moves 2 at hh
    rw [Int.fmod_eq_emod_of_nonneg _ (by omega : (0:Int)≤2)] at hh
    exact hh
  rw [show Spec «prefix» (Z.land moves 1)=Spec «prefix» (moves%2) by rw [hland]]
  refine ⟨by omega,⟨?_,?_⟩⟩
  · intro hmod states' htrace
    have hl:=hall states' htrace
    unfold Z.even
    simp only [decide_eq_false_iff_not]
    omega
  · intro hw
    have hg : DeletionGameTrace «prefix» states := by
      refine ⟨by omega,hfirst,?_,?_⟩
      · intro k hk;exact hsteps k (by omega)
      · rw [hlen,show moves+1-1=moves by omega,hfinal]
        exact hir
    have hh:=hw states hg
    unfold Z.even at hh
    simp only [decide_eq_false_iff_not] at hh
    omega
end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib
