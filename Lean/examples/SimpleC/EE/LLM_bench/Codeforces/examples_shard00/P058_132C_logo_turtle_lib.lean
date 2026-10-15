import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import Mathlib.Data.List.Induction
import AUXLib.ZParity

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib
open AUXLib


open MaxMinLib

def ChangedExactly (commands modified : List Int) (n : Int) : Prop :=
  Zlength modified = Zlength commands ∧ ∃ counts, Zlength counts = Zlength commands ∧
    Forall (fun x => 0 ≤ x) counts ∧ counts.foldr (· + ·) 0 = n ∧
    ∀ i, (0 ≤ i ∧ i < Zlength commands) →
      (Z.even (Znth i counts 0) = true → Znth i modified 0 = Znth i commands 0) ∧
      (Z.even (Znth i counts 0) = false →
        ((Znth i commands 0 = 70 ∧ Znth i modified 0 = 84) ∨ (Znth i commands 0 = 84 ∧ Znth i modified 0 = 70)))

def TurtleEnd (c : List Int) (x : Int) : Prop :=
  ∃ states, Zlength states = Zlength c + 1 ∧ Znth 0 states (0,1) = (0,1) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength c) →
      let (p,d) := Znth i states (0,1)
      Znth (i+1) states (0,1) = if Znth i c 0 = 84 then (p,-d) else (p+d,d)) ∧
    x = (Znth (Zlength c) states (0,1)).1

def Pre (n : Int) (c : List Int) : Prop :=
  (1 ≤ Zlength c ∧ Zlength c ≤ 100) ∧ (1 ≤ n ∧ n ≤ 50) ∧ Forall (fun x => x = 70 ∨ x = 84) c

def Spec (n : Int) (c : List Int) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun candidate : List Int × Int => ChangedExactly c candidate.1 n ∧ TurtleEnd candidate.1 candidate.2)
    (fun candidate => Z.abs candidate.2) out

def PrefixChangedByFlips (commands modified : List Int) (prefix_len flips : Int) : Prop :=
  (0 ≤ prefix_len ∧ prefix_len ≤ Zlength commands) ∧ Zlength modified = prefix_len ∧
    ∃ marks, Zlength marks = prefix_len ∧ Forall (fun x => x = 0 ∨ x = 1) marks ∧ marks.foldr (· + ·) 0 = flips ∧
      ∀ j, (0 ≤ j ∧ j < prefix_len) →
        (Znth j marks 0 = 0 → Znth j modified 0 = Znth j commands 0) ∧
        (Znth j marks 0 = 1 → ((Znth j commands 0 = 70 ∧ Znth j modified 0 = 84) ∨ (Znth j commands 0 = 84 ∧ Znth j modified 0 = 70)))

def TurtleState (commands : List Int) (position direction : Int) : Prop :=
  ∃ states, Zlength states = Zlength commands+1 ∧ Znth 0 states (0,1) = (0,1) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength commands) →
      let (p,d) := Znth i states (0,1)
      Znth (i+1) states (0,1) = if Znth i commands 0 = 84 then (p,-d) else (p+d,d)) ∧
    Znth (Zlength commands) states (0,1) = (position,direction)

def PrefixReachable (commands : List Int) (prefix_len flips direction slot : Int) : Prop :=
  ∃ modified position final_direction, PrefixChangedByFlips commands modified prefix_len flips ∧
    TurtleState modified position final_direction ∧ position = slot - Zlength commands ∧
    ((direction = 0 ∧ final_direction = 1) ∨ (direction = 1 ∧ final_direction = -1))

def TurtleWidth (commands : List Int) : Int := 2 * Zlength commands + 1

def TurtleCellIndex (commands : List Int) (flips direction slot : Int) : Int :=
  (flips * 2 + direction) * TurtleWidth commands + slot

def TurtleLayerMeaning (commands : List Int) (prefix_len change_limit : Int) (table : List Int) : Prop :=
  ∀ flips direction slot, (0 ≤ flips ∧ flips ≤ change_limit) → (0 ≤ direction ∧ direction < 2) →
    (0 ≤ slot ∧ slot < TurtleWidth commands) →
    let value := Znth (TurtleCellIndex commands flips direction slot) table 0
    (value = 0 ∨ value = 1) ∧ (value = 1 ↔ PrefixReachable commands prefix_len flips direction slot)

def FlippedCommand (command flip effective : Int) : Prop :=
  (flip = 0 ∧ effective = command) ∨ (flip = 1 ∧ ((command = 70 ∧ effective = 84) ∨ (command = 84 ∧ effective = 70)))

def TurtleEncodedStep (direction slot command next_direction next_slot : Int) : Prop :=
  (command = 84 ∧ next_direction = 1 - direction ∧ next_slot = slot) ∨
    (command = 70 ∧ next_direction = direction ∧ ((direction = 0 ∧ next_slot = slot + 1) ∨ (direction = 1 ∧ next_slot = slot - 1)))

def TurtleTransitionRank (commands : List Int) (flips direction slot flip : Int) : Int :=
  2 * TurtleCellIndex commands flips direction slot + flip

def TurtleNextReachable (commands : List Int) (prefix_len change_limit done : Int) (next_flips next_direction next_slot : Int) : Prop :=
  ∃ flips direction slot flip effective, (0 ≤ flips ∧ flips ≤ change_limit) ∧ (0 ≤ direction ∧ direction < 2) ∧
    (0 ≤ slot ∧ slot < TurtleWidth commands) ∧ (0 ≤ flip ∧ flip < 2) ∧
    TurtleTransitionRank commands flips direction slot flip < done ∧ PrefixReachable commands prefix_len flips direction slot ∧
    next_flips = flips + flip ∧ next_flips ≤ change_limit ∧ FlippedCommand (Znth prefix_len commands 0) flip effective ∧
    TurtleEncodedStep direction slot effective next_direction next_slot

def TurtleNextPrefix (commands : List Int) (prefix_len change_limit done : Int) (next_table : List Int) : Prop :=
  ∀ flips direction slot, (0 ≤ flips ∧ flips ≤ change_limit) → (0 ≤ direction ∧ direction < 2) →
    (0 ≤ slot ∧ slot < TurtleWidth commands) →
    let value := Znth (TurtleCellIndex commands flips direction slot) next_table 0
    (value = 0 ∨ value = 1) ∧ (value = 1 ↔ TurtleNextReachable commands prefix_len change_limit done flips direction slot)

def TurtleTerminalEligible (commands : List Int) (change_limit flips direction slot : Int) : Prop :=
  (0 ≤ flips ∧ flips ≤ change_limit) ∧ (0 ≤ direction ∧ direction < 2) ∧ (0 ≤ slot ∧ slot < TurtleWidth commands) ∧
    Z.even (change_limit-flips) = true ∧ PrefixReachable commands (Zlength commands) flips direction slot

def TurtleAnswerPrefix (commands : List Int) (change_limit done answer : Int) : Prop :=
  0 ≤ answer ∧ (∀ flips direction slot, TurtleTerminalEligible commands change_limit flips direction slot →
    TurtleCellIndex commands flips direction slot < done → Z.abs (slot - Zlength commands) ≤ answer) ∧
    (answer = 0 ∨ ∃ flips direction slot, TurtleTerminalEligible commands change_limit flips direction slot ∧
      TurtleCellIndex commands flips direction slot < done ∧ answer = Z.abs (slot - Zlength commands))

private theorem width_pos (commands : List Int) : 0<TurtleWidth commands := by
  have := Zlength_nonneg commands
  unfold TurtleWidth
  omega

private theorem zlength_zero {A : Type} (l : List A) (h : Zlength l=0) : l=[] := by
  apply List.length_eq_zero_iff.mp
  simp only [Zlength,Int.ofNat_eq_coe] at h
  omega

private theorem zlength_snoc {A : Type} (l : List A) (x : A) : Zlength (l++[x])=Zlength l+1 := by
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

private theorem znth_app_left {A : Type} (d : A) (l l' : List A) (i : Int)
    (hi : 0≤i ∧ i<Zlength l) : Znth i (l++l') d=Znth i l d := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

private theorem znth_snoc {A : Type} (d : A) (l : List A) (x : A) : Znth (Zlength l) (l++[x]) d=x := by
  rw [app_Znth2 d l [x] (Zlength l) (le_refl _),sub_self]
  rfl

private theorem cell_bounds (commands : List Int) (limit flips direction slot : Int)
    (hf : 0≤flips ∧ flips≤limit) (hd : 0≤direction ∧ direction<2) (hs : 0≤slot ∧ slot<TurtleWidth commands) :
    0≤TurtleCellIndex commands flips direction slot ∧ TurtleCellIndex commands flips direction slot<(limit+1)*2*TurtleWidth commands := by
  have hw := width_pos commands
  have hc : 0≤flips*2+direction := by omega
  have hcu : flips*2+direction+1≤(limit+1)*2 := by omega
  have hlo := mul_nonneg hc (le_of_lt hw)
  have hhi := mul_le_mul_of_nonneg_right hcu (le_of_lt hw)
  unfold TurtleCellIndex
  constructor <;> nlinarith

theorem turtle_cell_index_same_slot__answer_position (commands : List Int) (flips1 direction1 slot1 flips2 direction2 slot2 : Int)
    (hw : 0<TurtleWidth commands) (hs1 : 0≤slot1 ∧ slot1<TurtleWidth commands) (hs2 : 0≤slot2 ∧ slot2<TurtleWidth commands)
    (he : TurtleCellIndex commands flips1 direction1 slot1=TurtleCellIndex commands flips2 direction2 slot2) : slot1=slot2 := by
  have hm := congrArg (fun v=>v%TurtleWidth commands) he
  unfold TurtleCellIndex at hm
  dsimp only at hm
  rw [Int.add_comm ((flips1*2+direction1)*TurtleWidth commands) slot1,
    Int.add_comm ((flips2*2+direction2)*TurtleWidth commands) slot2,
    Int.add_mul_emod_self_right,Int.add_mul_emod_self_right,
    Int.emod_eq_of_lt hs1.1 hs1.2,Int.emod_eq_of_lt hs2.1 hs2.2] at hm
  exact hm

private theorem cell_injective (commands : List Int) (f1 d1 s1 f2 d2 s2 : Int)
    (hd1 : 0≤d1 ∧ d1<2) (hs1 : 0≤s1 ∧ s1<TurtleWidth commands)
    (hd2 : 0≤d2 ∧ d2<2) (hs2 : 0≤s2 ∧ s2<TurtleWidth commands)
    (he : TurtleCellIndex commands f1 d1 s1=TurtleCellIndex commands f2 d2 s2) : f1=f2 ∧ d1=d2 ∧ s1=s2 := by
  have hw := width_pos commands
  have hslot := turtle_cell_index_same_slot__answer_position commands f1 d1 s1 f2 d2 s2 hw hs1 hs2 he
  unfold TurtleCellIndex at he
  have hmul : (f1*2+d1)*TurtleWidth commands=(f2*2+d2)*TurtleWidth commands := by omega
  have hc : f1*2+d1=f2*2+d2 := mul_right_cancel₀ (by omega : TurtleWidth commands≠0) hmul
  exact ⟨by omega,by omega,hslot⟩

theorem turtle_transition_rank_injective__next_noop (commands : List Int) (f1 d1 s1 b1 f2 d2 s2 b2 : Int)
    (hd1 : 0≤d1 ∧ d1<2) (hs1 : 0≤s1 ∧ s1<TurtleWidth commands) (hb1 : 0≤b1 ∧ b1<2)
    (hd2 : 0≤d2 ∧ d2<2) (hs2 : 0≤s2 ∧ s2<TurtleWidth commands) (hb2 : 0≤b2 ∧ b2<2)
    (he : TurtleTransitionRank commands f1 d1 s1 b1=TurtleTransitionRank commands f2 d2 s2 b2) :
    f1=f2 ∧ d1=d2 ∧ s1=s2 ∧ b1=b2 := by
  unfold TurtleTransitionRank at he
  have hb : b1=b2 := by omega
  have hc : TurtleCellIndex commands f1 d1 s1=TurtleCellIndex commands f2 d2 s2 := by omega
  rcases cell_injective commands f1 d1 s1 f2 d2 s2 hd1 hs1 hd2 hs2 hc with ⟨hf,hd,hs⟩
  exact ⟨hf,hd,hs,hb⟩

theorem Znth_app_left__next_noop (left right : List Int) (index default : Int)
    (hi : 0≤index ∧ index<Zlength left) : Znth index (left++right) default=Znth index left default :=
  znth_app_left default left right index hi

theorem binary_lxor_one__direction_bit (d : Int) (hd : 0≤d ∧ d<2) : Z.lxor d 1=1-d := by
  have h : d=0 ∨ d=1 := by omega
  rcases h with h | h <;> subst d <;> rfl

theorem binary_destination_bound__direction_bit (changes c flip d width pos : Int)
    (hcf : c+flip≤changes) (hd : 0≤d ∧ d<2) (hw : 0<width) (hp : 0≤pos ∧ pos<width) :
    ((c+flip)*2+Z.lxor d 1)*width+pos<((changes+1)*2)*width := by
  rw [binary_lxor_one__direction_bit d hd]
  have hb : (c+flip)*2+(1-d)+1≤(changes+1)*2 := by omega
  have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt hw)
  nlinarith

theorem fold_right_add_app_single__layer_swap (xs : List Int) (x : Int) :
    (xs++[x]).foldr (·+·) 0=xs.foldr (·+·) 0+x := by
  induction xs with
  | nil => simp
  | cons a xs ih => simpa only [List.cons_append,List.foldr_cons,ih,add_assoc]

theorem fold_right_add_nonneg__layer_swap (xs : List Int) (hf : Forall (fun x=>0≤x) xs) : 0≤xs.foldr (·+·) 0 := by
  induction hf with
  | nil => exact le_refl _
  | cons hx hf ih => exact add_nonneg hx ih

theorem fold_right_nonnegative__final_spec (values : List Int) (hf : Forall (fun x=>0≤x) values) :
    0≤values.foldr (·+·) 0 := fold_right_add_nonneg__layer_swap values hf

theorem prefix_changed_flips_nonneg__layer_swap (commands modified : List Int) (prefix_len flips : Int)
    (hp : PrefixChangedByFlips commands modified prefix_len flips) : 0≤flips := by
  rcases hp with ⟨hr,hl,marks,hm,hf,hs,hrules⟩
  have hfn : Forall (fun x=>0≤x) marks := Forall.iff_forall_mem.mpr (fun x hx=>by have := hf.mem hx; omega)
  have h := fold_right_add_nonneg__layer_swap marks hfn
  omega

theorem prefix_reachable_zero_iff__init_layer (commands : List Int) (flips direction slot : Int) :
    PrefixReachable commands 0 flips direction slot ↔ flips=0 ∧ direction=0 ∧ slot=Zlength commands := by
  constructor
  · rintro ⟨modified,p,d,⟨hr,hl,marks,hm,hf,hs,hrules⟩,⟨states,hstates,h0,hsteps,he⟩,hp,hd⟩
    have hmodified := zlength_zero modified hl
    have hmarks := zlength_zero marks hm
    subst modified
    subst marks
    change 0=flips at hs
    change Znth 0 states (0,1)=(p,d) at he
    have hpair : (p,d)=(0,1) := he.symm.trans h0
    have hpos := congrArg Prod.fst hpair
    have hdir := congrArg Prod.snd hpair
    simp only [Prod.fst,Prod.snd] at hpos hdir
    exact ⟨by omega,by rcases hd with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega,by omega⟩
  · rintro ⟨hf,hd,hs⟩
    subst flips
    subst direction
    subst slot
    have hn := Zlength_nonneg commands
    refine ⟨[],0,1,⟨by omega,rfl,[],rfl,Forall.nil,rfl,by intro j hj; omega⟩,?_,by omega,Or.inl ⟨rfl,rfl⟩⟩
    exact ⟨[(0,1)],rfl,rfl,by intro i hi; simp only [Zlength_nil] at hi; omega,rfl⟩

theorem turtle_layer_zero_table__init_layer (commands : List Int) (change_limit total : Int)
    (hn : 1≤Zlength commands) (hc : 0≤change_limit)
    (ht : total=(change_limit+1)*2*TurtleWidth commands) :
    TurtleLayerMeaning commands 0 change_limit (replace_Znth (Zlength commands) 1 («repeat» 0 total.toNat)) := by
  have hw := width_pos commands
  have hcenter : TurtleCellIndex commands 0 0 (Zlength commands)=Zlength commands := by simp [TurtleCellIndex]
  have hs : 0≤Zlength commands ∧ Zlength commands<TurtleWidth commands := by unfold TurtleWidth; omega
  have hb := cell_bounds commands change_limit 0 0 (Zlength commands) ⟨by omega,hc⟩ ⟨by omega,by omega⟩ hs
  rw [hcenter,←ht] at hb
  have hlen : Zlength («repeat» (0:Int) total.toNat)=total := by
    simp only [Zlength,«repeat»,List.length_replicate,Int.ofNat_eq_coe]
    omega
  intro f d s hf hd hs'
  dsimp only
  have hi := cell_bounds commands change_limit f d s hf hd hs'
  rw [←ht] at hi
  by_cases he : TurtleCellIndex commands f d s=Zlength commands
  · rw [he,Znth_replace_Znth_Same 0 _ _ 1 (by omega)]
    have hid := cell_injective commands f d s 0 0 (Zlength commands) hd hs' ⟨by omega,by omega⟩ hs (he.trans hcenter.symm)
    refine ⟨Or.inr rfl,?_,fun _=>rfl⟩
    intro _
    exact prefix_reachable_zero_iff__init_layer commands f d s |>.mpr hid
  · rw [Znth_replace_Znth_Diff 0 _ _ _ 1 (by omega) (by omega) (Ne.symm he),Znth_repeat]
    refine ⟨Or.inl rfl,by omega,?_⟩
    intro hr
    rcases (prefix_reachable_zero_iff__init_layer commands f d s).mp hr with ⟨rfl,rfl,rfl⟩
    exact False.elim (he hcenter)

private theorem next_mono (commands : List Int) (pre limit a b f d s : Int) (hab : a≤b)
    (h : TurtleNextReachable commands pre limit a f d s) : TurtleNextReachable commands pre limit b f d s := by
  rcases h with ⟨ofl,od,os,flip,e,hf,hd,hs,hb,hr,hrest⟩
  exact ⟨ofl,od,os,flip,e,hf,hd,hs,hb,by omega,hrest⟩

theorem turtle_next_zero_table__init_layer (commands : List Int) (prefix_len change_limit total : Int) :
    TurtleNextPrefix commands prefix_len change_limit 0 («repeat» 0 total.toNat) := by
  intro f d s hf hd hs
  dsimp only
  rw [Znth_repeat]
  refine ⟨Or.inl rfl,by omega,?_⟩
  rintro ⟨ofl,od,os,b,e,hf',hd',hs',hb,hr,hrest⟩
  have hi := cell_bounds commands change_limit ofl od os hf' hd' hs'
  unfold TurtleTransitionRank at hr
  omega

theorem turtle_next_prefix_write_one__next_update_core (commands : List Int) (pre limit done : Int) (table : List Int)
    (nf nd ns : Int) (h : TurtleNextPrefix commands pre limit done table)
    (hlen : Zlength table=(limit+1)*2*TurtleWidth commands)
    (hf : 0≤nf ∧ nf≤limit) (hd : 0≤nd ∧ nd<2) (hs : 0≤ns ∧ ns<TurtleWidth commands)
    (hn : TurtleNextReachable commands pre limit (done+1) nf nd ns)
    (hu : ∀ f d s, (0≤f ∧ f≤limit) → (0≤d ∧ d<2) → (0≤s ∧ s<TurtleWidth commands) →
      TurtleNextReachable commands pre limit (done+1) f d s → ¬TurtleNextReachable commands pre limit done f d s →
      f=nf ∧ d=nd ∧ s=ns) :
    TurtleNextPrefix commands pre limit (done+1) (replace_Znth (TurtleCellIndex commands nf nd ns) 1 table) := by
  intro f d s hf' hd' hs'
  dsimp only
  have hi := cell_bounds commands limit f d s hf' hd' hs'
  have hnidx := cell_bounds commands limit nf nd ns hf hd hs
  by_cases he : TurtleCellIndex commands nf nd ns=TurtleCellIndex commands f d s
  · have hid := cell_injective commands nf nd ns f d s hd hs hd' hs' he
    rcases hid with ⟨rfl,rfl,rfl⟩
    rw [Znth_replace_Znth_Same 0 _ _ 1 (by omega)]
    exact ⟨Or.inr rfl,fun _=>hn,fun _=>rfl⟩
  · rw [Znth_replace_Znth_Diff 0 _ _ _ 1 (by omega) (by omega) he]
    have ht := h f d s hf' hd' hs'
    refine ⟨ht.1,fun hv=>next_mono commands pre limit done (done+1) f d s (by omega) (ht.2.mp hv),?_⟩
    intro hr
    apply ht.2.mpr
    by_contra hno
    rcases hu f d s hf' hd' hs' hr hno with ⟨rfl,rfl,rfl⟩
    exact he rfl

theorem turtle_transition_new_cell_unique__next_update_core (commands : List Int) (pre limit done ofl od os b e nf nd ns : Int)
    (hf : 0≤ofl ∧ ofl≤limit) (hd : 0≤od ∧ od<2) (hs : 0≤os ∧ os<TurtleWidth commands) (hb : 0≤b ∧ b<2)
    (hr : TurtleTransitionRank commands ofl od os b=done) (hp : PrefixReachable commands pre ofl od os)
    (hnf : nf=ofl+b) (hnlim : nf≤limit) (he : FlippedCommand (Znth pre commands 0) b e)
    (hst : TurtleEncodedStep od os e nd ns) :
    ∀ f d s, (0≤f ∧ f≤limit) → (0≤d ∧ d<2) → (0≤s ∧ s<TurtleWidth commands) →
      TurtleNextReachable commands pre limit (done+1) f d s → ¬TurtleNextReachable commands pre limit done f d s →
      f=nf ∧ d=nd ∧ s=ns := by
  intro f d s hf' hd' hs' hn hno
  rcases hn with ⟨f0,d0,s0,b0,e0,hf0,hd0,hs0,hb0,hr0,hp0,hnf0,hnlim0,he0,hst0⟩
  have hre : TurtleTransitionRank commands f0 d0 s0 b0=done := by
    by_contra hne
    exact hno ⟨f0,d0,s0,b0,e0,hf0,hd0,hs0,hb0,by omega,hp0,hnf0,hnlim0,he0,hst0⟩
  rcases turtle_transition_rank_injective__next_noop commands f0 d0 s0 b0 ofl od os b hd0 hs0 hb0 hd hs hb (hre.trans hr.symm) with ⟨rfl,rfl,rfl,rfl⟩
  have hee : e0=e := by rcases he with ⟨h1,h2⟩ | ⟨h1,⟨h2,h3⟩ | ⟨h2,h3⟩⟩ <;> rcases he0 with ⟨h4,h5⟩ | ⟨h4,⟨h5,h6⟩ | ⟨h5,h6⟩⟩ <;> omega
  subst e0
  unfold TurtleEncodedStep at hst hst0
  rcases hst with ⟨h1,h2,h3⟩ | ⟨h1,h2,⟨h3,h4⟩ | ⟨h3,h4⟩⟩ <;>
    rcases hst0 with ⟨h5,h6,h7⟩ | ⟨h5,h6,⟨h7,h8⟩ | ⟨h7,h8⟩⟩ <;> omega

theorem turtle_next_prefix_write_transition__next_update_core (commands : List Int) (pre limit done : Int) (table : List Int)
    (ofl od os b e nf nd ns : Int) (h : TurtleNextPrefix commands pre limit done table)
    (hlen : Zlength table=(limit+1)*2*TurtleWidth commands)
    (hf : 0≤ofl ∧ ofl≤limit) (hd : 0≤od ∧ od<2) (hs : 0≤os ∧ os<TurtleWidth commands) (hb : 0≤b ∧ b<2)
    (hr : TurtleTransitionRank commands ofl od os b=done) (hp : PrefixReachable commands pre ofl od os)
    (hnf : nf=ofl+b) (hnlim : nf≤limit) (he : FlippedCommand (Znth pre commands 0) b e)
    (hst : TurtleEncodedStep od os e nd ns)
    (hf' : 0≤nf ∧ nf≤limit) (hd' : 0≤nd ∧ nd<2) (hs' : 0≤ns ∧ ns<TurtleWidth commands) :
    TurtleNextPrefix commands pre limit (done+1) (replace_Znth (TurtleCellIndex commands nf nd ns) 1 table) := by
  apply turtle_next_prefix_write_one__next_update_core commands pre limit done table nf nd ns h hlen hf' hd' hs'
  · exact ⟨ofl,od,os,b,e,hf,hd,hs,hb,by omega,hp,hnf,hnlim,he,hst⟩
  · exact turtle_transition_new_cell_unique__next_update_core commands pre limit done ofl od os b e nf nd ns hf hd hs hb hr hp hnf hnlim he hst

theorem turtle_next_prefix_skip_rank__next_noop (commands : List Int) (pre limit done : Int) (table : List Int)
    (h : TurtleNextPrefix commands pre limit done table)
    (hskip : ∀ f d s b e nf nd ns, (0≤f ∧ f≤limit) → (0≤d ∧ d<2) → (0≤s ∧ s<TurtleWidth commands) →
      (0≤b ∧ b<2) → TurtleTransitionRank commands f d s b=done → PrefixReachable commands pre f d s →
      nf=f+b → nf≤limit → FlippedCommand (Znth pre commands 0) b e → TurtleEncodedStep d s e nd ns →
      ¬((0≤nf ∧ nf≤limit) ∧ (0≤nd ∧ nd<2) ∧ (0≤ns ∧ ns<TurtleWidth commands))) :
    TurtleNextPrefix commands pre limit (done+1) table := by
  intro f d s hf hd hs
  have ht := h f d s hf hd hs
  refine ⟨ht.1,fun hv=>next_mono commands pre limit done (done+1) f d s (by omega) (ht.2.mp hv),?_⟩
  rintro ⟨ofl,od,os,b,e,hf',hd',hs',hb,hr,hp,hnf,hnlim,he,hst⟩
  apply ht.2.mpr
  by_cases hre : TurtleTransitionRank commands ofl od os b=done
  · exact False.elim (hskip ofl od os b e f d s hf' hd' hs' hb hre hp hnf hnlim he hst ⟨hf,hd,hs⟩)
  · exact ⟨ofl,od,os,b,e,hf',hd',hs',hb,by omega,hp,hnf,hnlim,he,hst⟩

theorem turtle_answer_prefix_zero__answer_init (commands : List Int) (limit : Int) : TurtleAnswerPrefix commands limit 0 0 := by
  refine ⟨le_refl _,?_,Or.inl rfl⟩
  intro f d s h hi
  have hb := cell_bounds commands limit f d s h.1 h.2.1 h.2.2.1
  omega

private theorem land_one_eq_mod (v : Int) : Z.land v 1=v%2 := by
  have h := Z.land_ones v 1 (by omega)
  change Z.land v 1=Int.fmod v 2 at h
  rw [Int.fmod_eq_emod_of_nonneg v (by omega : (0:Int)≤2)] at h
  exact h

theorem land_one_zero_even__answer_position (v : Int) (h : Z.land v 1=0) : Z.even v=true := by
  rw [land_one_eq_mod] at h
  exact decide_eq_true h

theorem turtle_layer_nonzero_terminal__answer_position (commands : List Int) (limit : Int) (table : List Int) (f d s : Int)
    (h : TurtleLayerMeaning commands (Zlength commands) limit table) (hf : 0≤f ∧ f≤limit)
    (hd : 0≤d ∧ d<2) (hs : 0≤s ∧ s<TurtleWidth commands) (he : Z.even (limit-f)=true)
    (hv : Znth (TurtleCellIndex commands f d s) table 0≠0) : TurtleTerminalEligible commands limit f d s := by
  have ht := h f d s hf hd hs
  exact ⟨hf,hd,hs,he,ht.2.mp (by rcases ht.1 with h0 | h1; exact False.elim (hv h0); exact h1)⟩

theorem turtle_terminal_cell_one__answer_position (commands : List Int) (limit : Int) (table : List Int) (f d s : Int)
    (h : TurtleLayerMeaning commands (Zlength commands) limit table) (ht : TurtleTerminalEligible commands limit f d s) :
    Znth (TurtleCellIndex commands f d s) table 0=1 := (h f d s ht.1 ht.2.1 ht.2.2.1).2.mpr ht.2.2.2.2

theorem turtle_answer_prefix_consume_cell__answer_position (commands : List Int) (limit done old_answer new_answer : Int)
    (h : TurtleAnswerPrefix commands limit done old_answer) (hle : old_answer≤new_answer)
    (hn : ∀ f d s, TurtleTerminalEligible commands limit f d s → TurtleCellIndex commands f d s=done → Z.abs (s-Zlength commands)≤new_answer)
    (hw : new_answer=old_answer ∨ ∃ f d s, TurtleTerminalEligible commands limit f d s ∧ TurtleCellIndex commands f d s=done ∧ new_answer=Z.abs (s-Zlength commands)) :
    TurtleAnswerPrefix commands limit (done+1) new_answer := by
  refine ⟨le_trans h.1 hle,?_,?_⟩
  · intro f d s ht hi
    by_cases he : TurtleCellIndex commands f d s=done
    · exact hn f d s ht he
    · exact le_trans (h.2.1 f d s ht (by omega)) hle
  · rcases hw with he | ⟨f,d,s,ht,hi,he⟩
    · rcases h.2.2 with hz | ⟨f,d,s,ht,hi,hv⟩
      · exact Or.inl (he.trans hz)
      · exact Or.inr ⟨f,d,s,ht,by omega,he.trans hv⟩
    · exact Or.inr ⟨f,d,s,ht,by omega,he⟩

theorem turtle_answer_prefix_skip_ineligible__answer_loop_exits (commands : List Int) (limit c answer : Int)
    (hc : 0≤c) (hcl : c≤limit) (hw : 0<TurtleWidth commands) (hne : Z.land (limit-c) 1≠0)
    (h : TurtleAnswerPrefix commands limit ((c*2)*TurtleWidth commands) answer) :
    TurtleAnswerPrefix commands limit (((c+1)*2)*TurtleWidth commands) answer := by
  have hstep : (c*2)*TurtleWidth commands<((c+1)*2)*TurtleWidth commands := by nlinarith
  refine ⟨h.1,?_,?_⟩
  · intro f d s ht hi
    have hfd := ht.1
    have hdd := ht.2.1
    have hsd := ht.2.2.1
    have hf : f≤c := by
      by_contra hn
      have hm := mul_le_mul_of_nonneg_right (by omega : (c+1)*2≤f*2+d) (le_of_lt hw)
      unfold TurtleCellIndex at hi
      nlinarith
    have hfc : f≠c := by
      intro he
      have hp := ht.2.2.2.1
      rw [he] at hp
      apply hne
      rw [land_one_eq_mod]
      exact of_decide_eq_true hp
    have hmul := mul_le_mul_of_nonneg_right (by omega : f*2+d+1≤c*2) (le_of_lt hw)
    apply h.2.1 f d s ht
    unfold TurtleCellIndex
    nlinarith
  · rcases h.2.2 with he | ⟨f,d,s,ht,hi,hv⟩
    · exact Or.inl he
    · exact Or.inr ⟨f,d,s,ht,by omega,hv⟩

theorem turtle_state_to_end__final_spec (commands : List Int) (p d : Int) (h : TurtleState commands p d) : TurtleEnd commands p := by
  rcases h with ⟨states,hl,h0,hst,he⟩
  exact ⟨states,hl,h0,hst,(congrArg Prod.fst he).symm⟩

theorem turtle_end_to_state__final_spec (commands : List Int) (p : Int) (h : TurtleEnd commands p) : ∃ d, TurtleState commands p d := by
  rcases h with ⟨states,hl,h0,hst,he⟩
  refine ⟨(Znth (Zlength commands) states (0,1)).2,states,hl,h0,hst,?_⟩
  rw [he]

theorem command_alphabet_from_Znth__final_spec (commands : List Int)
    (h : ∀ i, (0≤i ∧ i<Zlength commands) → Znth i commands 0=70 ∨ Znth i commands 0=84) : Forall (fun x=>x=70 ∨ x=84) commands := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨i,hi,he⟩
  have hz := h (i:Int) (by simp only [Zlength,Int.ofNat_eq_coe]; omega)
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he] using hz

private theorem znth_take {A : Type} (d : A) (l : List A) (n : Nat) (i : Int) (hi : 0≤i ∧ i<(n:Int)) :
    Znth i (l.take n) d=Znth i l d := by
  have hn : i.toNat<n := by omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_take_of_lt hn]

private theorem forall_snoc {A : Type} (P : A→Prop) (l : List A) (a : A) (h : Forall P l) (ha : P a) : Forall P (l++[a]) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h.mem hx
  · simpa only [List.mem_singleton.mp hx] using ha

theorem prefix_changed_extend__layer_swap (commands modified : List Int) (pre flips flip effective : Int)
    (hr : 0≤pre ∧ pre<Zlength commands) (h : PrefixChangedByFlips commands modified pre flips)
    (he : FlippedCommand (Znth pre commands 0) flip effective) :
    PrefixChangedByFlips commands (modified++[effective]) (pre+1) (flips+flip) := by
  rcases h with ⟨hpre,hl,marks,hm,hf,hs,hpoint⟩
  have hb : flip=0 ∨ flip=1 := by rcases he with h | h; exact Or.inl h.1; exact Or.inr h.1
  refine ⟨by omega,by rw [zlength_snoc,hl],marks++[flip],by rw [zlength_snoc,hm],forall_snoc _ marks flip hf hb,?_,?_⟩
  · rw [fold_right_add_app_single__layer_swap,hs]
  · intro j hj
    by_cases hjp : j<pre
    · rw [znth_app_left 0 marks [flip] j (by omega),znth_app_left 0 modified [effective] j (by omega)]
      exact hpoint j ⟨hj.1,hjp⟩
    · have hj' : j=pre := by omega
      subst j
      rw [←hm,znth_snoc,hm,←hl,znth_snoc,hl]
      rcases he with ⟨h0,hv⟩ | ⟨h1,hv⟩
      · exact ⟨fun _=>hv,by intro hh; omega⟩
      · exact ⟨by intro hh; omega,fun _=>hv⟩

private theorem state_snoc (modified : List Int) (p d effective np nd : Int) (h : TurtleState modified p d)
    (he : (np,nd)=if effective=84 then (p,-d) else (p+d,d)) : TurtleState (modified++[effective]) np nd := by
  rcases h with ⟨states,hl,h0,hsteps,hfinal⟩
  have hm := Zlength_nonneg modified
  refine ⟨states++[(np,nd)],?_,?_,?_,?_⟩
  · rw [zlength_snoc,zlength_snoc,hl]
  · rw [znth_app_left (0,1) states _ 0 (by omega)]
    exact h0
  · intro j hj
    rw [zlength_snoc] at hj
    by_cases hjm : j<Zlength modified
    · rw [znth_app_left (0,1) states _ j (by omega),znth_app_left (0,1) states _ (j+1) (by omega),znth_app_left 0 modified _ j ⟨hj.1,hjm⟩]
      exact hsteps j ⟨hj.1,hjm⟩
    · have hje : j=Zlength modified := by omega
      subst j
      rw [znth_app_left (0,1) states _ (Zlength modified) (by omega),hfinal,znth_snoc,←hl,znth_snoc]
      exact he
  · rw [zlength_snoc,←hl,znth_snoc]

theorem turtle_state_extend__layer_swap (modified : List Int) (p d effective np nd : Int) (h : TurtleState modified p d)
    (he : (effective=84 ∧ np=p ∧ nd= -d) ∨ (effective=70 ∧ np=p+d ∧ nd=d)) : TurtleState (modified++[effective]) np nd := by
  apply state_snoc modified p d effective np nd h
  rcases he with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> rfl

theorem turtle_state_endpoint_bound__layer_swap (modified : List Int) (p d : Int) (h : TurtleState modified p d) :
    (-Zlength modified≤p ∧ p≤Zlength modified) ∧ (d=1 ∨ d= -1) := by
  rcases h with ⟨states,hl,h0,hsteps,hfinal⟩
  have inv : ∀ m : Nat, (m:Int)≤Zlength modified →
      (- (m:Int)≤(Znth (m:Int) states (0,1)).1 ∧ (Znth (m:Int) states (0,1)).1≤(m:Int)) ∧
      ((Znth (m:Int) states (0,1)).2=1 ∨ (Znth (m:Int) states (0,1)).2= -1) := by
    intro m
    induction m with
    | zero => intro hm; rw [Int.natCast_zero,h0]; exact ⟨⟨le_refl _,le_refl _⟩,Or.inl rfl⟩
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have hst := hsteps (m:Int) (by omega)
      generalize hq : Znth (m:Int) states (0,1)=q at ih' hst
      rcases q with ⟨pos,dir⟩
      change (- (m:Int)≤pos ∧ pos≤(m:Int)) ∧ (dir=1 ∨ dir= -1) at ih'
      change Znth ((m:Int)+1) states (0,1)=(if Znth (m:Int) modified 0=84 then (pos,-dir) else (pos+dir,dir)) at hst
      rw [Int.natCast_succ,hst]
      split <;> dsimp only <;> rcases ih'.2 with hd | hd <;> constructor <;> omega
  have hh := inv modified.length (by simp only [Zlength,Int.ofNat_eq_coe]; omega)
  change (-Zlength modified≤(Znth (Zlength modified) states (0,1)).1 ∧ (Znth (Zlength modified) states (0,1)).1≤Zlength modified) ∧
    ((Znth (Zlength modified) states (0,1)).2=1 ∨ (Znth (Zlength modified) states (0,1)).2= -1) at hh
  rw [hfinal] at hh
  exact hh

theorem turtle_state_direction_pm1__final_spec (commands : List Int) (p d : Int) (h : TurtleState commands p d) : d=1 ∨ d= -1 :=
  (turtle_state_endpoint_bound__layer_swap commands p d h).2

theorem turtle_state_position_bound__final_spec (commands : List Int) (p d : Int) (h : TurtleState commands p d) :
    -Zlength commands≤p ∧ p≤Zlength commands := (turtle_state_endpoint_bound__layer_swap commands p d h).1

theorem turtle_state_unextend__layer_swap (modified : List Int) (effective np nd : Int) (ha : effective=70 ∨ effective=84)
    (h : TurtleState (modified++[effective]) np nd) : ∃ p d, TurtleState modified p d ∧
      ((effective=84 ∧ np=p ∧ nd= -d) ∨ (effective=70 ∧ np=p+d ∧ nd=d)) := by
  rcases h with ⟨states,hl,h0,hsteps,hfinal⟩
  rw [zlength_snoc] at hl hfinal
  have hm := Zlength_nonneg modified
  let p := (Znth (Zlength modified) states (0,1)).1
  let d := (Znth (Zlength modified) states (0,1)).2
  refine ⟨p,d,⟨states.take (modified.length+1),?_,?_,?_,?_⟩,?_⟩
  · have hn : modified.length+1≤states.length := by simp only [Zlength,Int.ofNat_eq_coe] at hl; omega
    simp only [Zlength,List.length_take_of_le hn,Int.ofNat_eq_coe,Int.natCast_add,Int.natCast_one]
  · rw [znth_take (0,1) states _ 0 (by omega)]
    exact h0
  · intro j hj
    have hr : (modified.length+1:Int)=Zlength modified+1 := rfl
    rw [znth_take (0,1) states _ j (by omega),znth_take (0,1) states _ (j+1) (by omega)]
    have hst := hsteps j (by rw [zlength_snoc]; omega)
    rw [znth_app_left 0 modified _ j hj] at hst
    exact hst
  · rw [znth_take (0,1) states _ (Zlength modified) (by simp only [Zlength,Int.ofNat_eq_coe]; omega)]
  · have hst := hsteps (Zlength modified) (by rw [zlength_snoc]; omega)
    rw [znth_snoc,hfinal] at hst
    rcases ha with rfl | rfl
    · simp only [if_false,show (70:Int)≠84 by omega] at hst
      exact Or.inr ⟨rfl,congrArg Prod.fst hst,congrArg Prod.snd hst⟩
    · simp only [if_true] at hst
      exact Or.inl ⟨rfl,congrArg Prod.fst hst,congrArg Prod.snd hst⟩

private theorem list_snoc_of_zlength {A : Type} (l : List A) (n : Int) (hn : 0≤n) (hl : Zlength l=n+1) : ∃ pre a, l=pre++[a] ∧ Zlength pre=n := by
  cases l using List.reverseRecOn with
  | nil => simp only [Zlength_nil] at hl; omega
  | append_singleton l a => exact ⟨l,a,rfl,by rw [zlength_snoc] at hl; omega⟩

theorem prefix_changed_unextend__layer_swap (commands modified : List Int) (pre total_flips : Int)
    (hr : 0≤pre ∧ pre<Zlength commands) (h : PrefixChangedByFlips commands modified (pre+1) total_flips) :
    ∃ before flips flip effective, modified=before++[effective] ∧ total_flips=flips+flip ∧
      PrefixChangedByFlips commands before pre flips ∧ FlippedCommand (Znth pre commands 0) flip effective := by
  rcases h with ⟨hp,hl,marks,hm,hf,hs,hpoint⟩
  rcases list_snoc_of_zlength modified pre hr.1 hl with ⟨before,e,he,hbl⟩
  rcases list_snoc_of_zlength marks pre hr.1 hm with ⟨beforemarks,b,hb,hbml⟩
  subst modified
  subst marks
  have hfb : Forall (fun x:Int=>x=0 ∨ x=1) beforemarks := Forall.iff_forall_mem.mpr (fun x hx=>hf.mem (List.mem_append_left _ hx))
  have hvb := hf.mem (List.mem_append_right beforemarks (List.mem_singleton_self b))
  have hlast := hpoint pre (by omega)
  rw [←hbml,znth_snoc,hbml,←hbl,znth_snoc,hbl] at hlast
  refine ⟨before,beforemarks.foldr (·+·) 0,b,e,rfl,?_,⟨by omega,hbl,beforemarks,hbml,hfb,rfl,?_⟩,?_⟩
  · rw [fold_right_add_app_single__layer_swap] at hs
    exact hs.symm
  · intro j hj
    have hh := hpoint j (by omega)
    rw [znth_app_left 0 beforemarks [b] j (by omega),znth_app_left 0 before [e] j (by omega)] at hh
    exact hh
  · rcases hvb with hz | ho
    · exact Or.inl ⟨hz,hlast.1 hz⟩
    · exact Or.inr ⟨ho,hlast.2 ho⟩

theorem turtle_state_exists__final_spec (commands : List Int) : ∃ p d, TurtleState commands p d := by
  induction commands using List.reverseRecOn with
  | nil => exact ⟨0,1,[(0,1)],rfl,rfl,by intro i hi; simp only [Zlength_nil] at hi; omega,rfl⟩
  | append_singleton commands c ih =>
    rcases ih with ⟨p,d,h⟩
    by_cases he : c=84
    · exact ⟨p,-d,state_snoc commands p d c p (-d) h (by rw [if_pos he])⟩
    · exact ⟨p+d,d,state_snoc commands p d c (p+d) d h (by rw [if_neg he])⟩

private theorem znth_mem {A : Type} (d : A) (l : List A) (i : Int) (hi : 0≤i ∧ i<Zlength l) : Znth i l d∈l := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

private theorem znth_map {A B : Type} (da : A) (db : B) (f : A→B) (l : List A) (i : Int) (hi : 0≤i ∧ i<Zlength l) :
    Znth i (l.map f) db=f (Znth i l da) := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  have hnm : i.toNat<(l.map f).length := by simpa only [List.length_map] using hn
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,List.getElem?_eq_getElem hnm,Option.getD_some,List.getElem_map]

private theorem parity_compress (counts : List Int) (hf : Forall (fun x=>0≤x) counts) :
    (counts.map (fun x=>x%2)).foldr (·+·) 0≤counts.foldr (·+·) 0 ∧
    (counts.foldr (·+·) 0-(counts.map (fun x=>x%2)).foldr (·+·) 0)%2=0 := by
  induction hf with
  | nil => exact ⟨le_refl _,rfl⟩
  | @cons x xs hx hxs ih =>
    simp only [List.map_cons,List.foldr_cons]
    constructor <;> omega

theorem change_counts_compress__final_spec (commands modified counts : List Int)
    (hl : Zlength modified=Zlength commands) (hc : Zlength counts=Zlength commands)
    (hf : Forall (fun x=>0≤x) counts)
    (hp : ∀ i, (0≤i ∧ i<Zlength commands) → (Z.even (Znth i counts 0)=true → Znth i modified 0=Znth i commands 0) ∧
      (Z.even (Znth i counts 0)=false → ((Znth i commands 0=70 ∧ Znth i modified 0=84) ∨ (Znth i commands 0=84 ∧ Znth i modified 0=70)))) :
    ∃ marks, Zlength marks=Zlength commands ∧ Forall (fun x=>x=0 ∨ x=1) marks ∧
      marks.foldr (·+·) 0≤counts.foldr (·+·) 0 ∧ Z.even (counts.foldr (·+·) 0-marks.foldr (·+·) 0)=true ∧
      ∀ i, (0≤i ∧ i<Zlength commands) → (Znth i marks 0=0 → Znth i modified 0=Znth i commands 0) ∧
        (Znth i marks 0=1 → ((Znth i commands 0=70 ∧ Znth i modified 0=84) ∨ (Znth i commands 0=84 ∧ Znth i modified 0=70))) := by
  have hpar := parity_compress counts hf
  refine ⟨counts.map (fun x=>x%2),?_,?_,hpar.1,decide_eq_true hpar.2,?_⟩
  · simpa only [Zlength,List.length_map] using hc
  · apply Forall.iff_forall_mem.mpr
    intro x hx
    rcases List.mem_map.mp hx with ⟨a,ha,rfl⟩
    omega
  · intro i hi
    rw [znth_map 0 0 _ counts i (by omega)]
    have hh := hp i hi
    refine ⟨fun he=>hh.1 (decide_eq_true he),fun he=>hh.2 ?_⟩
    apply decide_eq_false
    omega

theorem change_counts_expand__final_spec (commands modified marks : List Int) (n : Int)
    (hne : commands≠[]) (hl : Zlength modified=Zlength commands) (hm : Zlength marks=Zlength commands)
    (hf : Forall (fun x=>x=0 ∨ x=1) marks) (hle : marks.foldr (·+·) 0≤n)
    (heven : Z.even (n-marks.foldr (·+·) 0)=true)
    (hp : ∀ i, (0≤i ∧ i<Zlength commands) → (Znth i marks 0=0 → Znth i modified 0=Znth i commands 0) ∧
      (Znth i marks 0=1 → ((Znth i commands 0=70 ∧ Znth i modified 0=84) ∨ (Znth i commands 0=84 ∧ Znth i modified 0=70)))) :
    ∃ counts, Zlength counts=Zlength commands ∧ Forall (fun x=>0≤x) counts ∧ counts.foldr (·+·) 0=n ∧
      ∀ i, (0≤i ∧ i<Zlength commands) → (Z.even (Znth i counts 0)=true → Znth i modified 0=Znth i commands 0) ∧
        (Z.even (Znth i counts 0)=false → ((Znth i commands 0=70 ∧ Znth i modified 0=84) ∨ (Znth i commands 0=84 ∧ Znth i modified 0=70))) := by
  cases marks with
  | nil => exact False.elim (hne (zlength_zero commands hm.symm))
  | cons a marks =>
    have ha := hf.mem List.mem_cons_self
    have hft : Forall (fun x=>0≤x) marks := Forall.iff_forall_mem.mpr (fun x hx=>by have := hf.mem (List.mem_cons_of_mem a hx); omega)
    let padding := n-(a+marks.foldr (·+·) 0)
    have hpad : 0≤padding := by change a+marks.foldr (·+·) 0≤n at hle; dsimp only [padding]; omega
    have hpe : padding%2=0 := of_decide_eq_true heven
    refine ⟨(a+padding)::marks,?_,Forall.cons (by omega) hft,?_,?_⟩
    · simpa only [Zlength_cons] using hm
    · change a+padding+marks.foldr (·+·) 0=n
      dsimp only [padding]
      omega
    · intro i hi
      have hv := hf.mem (znth_mem 0 (a::marks) i (by omega))
      have hpar : Z.even (Znth i ((a+padding)::marks) 0)=Z.even (Znth i (a::marks) 0) := by
        by_cases hz : i=0
        · subst i
          change decide ((a+padding)%2=0)=decide (a%2=0)
          congr 1
          apply propext
          omega
        · rw [Znth_cons 0 i _ _ (by omega),Znth_cons 0 i _ _ (by omega)]
      rw [hpar]
      have hh := hp i hi
      rcases hv with hz | ho
      · rw [hz]
        exact ⟨fun _=>hh.1 hz,by intro h; contradiction⟩
      · rw [ho]
        exact ⟨by intro h; contradiction,fun _=>hh.2 ho⟩

theorem changed_exactly_exists__final_spec (commands : List Int) (n : Int) (hne : commands≠[]) (hn : 0≤n)
    (ha : Forall (fun x=>x=70 ∨ x=84) commands) : ∃ modified, ChangedExactly commands modified n := by
  cases commands with
  | nil => exact False.elim (hne rfl)
  | cons c commands =>
    let zeros : List Int := «repeat» 0 commands.length
    have hzlen : Zlength zeros=Zlength commands := by simp only [zeros,«repeat»,Zlength,List.length_replicate]
    have hzsum : zeros.foldr (·+·) 0=0 := by
      have h : ∀ m, ((«repeat» (0:Int) m).foldr (·+·) 0)=0 := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => simpa only [«repeat»,List.replicate_succ,List.foldr_cons,zero_add] using ih
      exact h commands.length
    have hzf : Forall (fun x:Int=>0≤x) zeros := by
      apply Forall.iff_forall_mem.mpr
      intro x hx
      have hx0 : x=0 := (List.mem_replicate.mp hx).2
      omega
    let effective := if Z.even n=true then c else if c=70 then 84 else 70
    refine ⟨effective::commands,⟨rfl,n::zeros,?_,Forall.cons hn hzf,?_,?_⟩⟩
    · rw [Zlength_cons,Zlength_cons,hzlen]
    · change n+zeros.foldr (·+·) 0=n
      rw [hzsum,add_zero]
    · intro i hi
      by_cases hz : i=0
      · subst i
        change (Z.even n=true → effective=c) ∧ (Z.even n=false → ((c=70 ∧ effective=84) ∨ (c=84 ∧ effective=70)))
        constructor
        · intro he
          simp only [effective,if_pos he]
        · intro he
          have hc := ha.mem List.mem_cons_self
          have hf : ¬Z.even n=true := by rw [he]; decide
          rcases hc with hc | hc
          · refine Or.inl ⟨hc,?_⟩
            dsimp only [effective]
            rw [if_neg hf,if_pos hc]
          · refine Or.inr ⟨hc,?_⟩
            dsimp only [effective]
            rw [if_neg hf,if_neg (by omega)]
      · rw [Znth_cons 0 i _ _ (by omega),Znth_cons 0 i _ _ (by omega),Znth_cons 0 i _ _ (by omega)]
        change (Z.even (Znth (i-1) («repeat» 0 commands.length) 0)=true → Znth (i-1) commands 0=Znth (i-1) commands 0) ∧ _
        rw [Znth_repeat]
        exact ⟨fun _=>rfl,by intro h; contradiction⟩

theorem turtle_next_complete_reachable_iff__layer_swap (commands : List Int) (pre limit nf nd ns : Int)
    (hpre : 0≤pre ∧ pre<Zlength commands) (hlimit : 0≤limit)
    (ha : ∀ k, (0≤k ∧ k<Zlength commands) → Znth k commands 0=70 ∨ Znth k commands 0=84)
    (hnf : 0≤nf ∧ nf≤limit) (hnd : 0≤nd ∧ nd<2) (hns : 0≤ns ∧ ns<TurtleWidth commands) :
    TurtleNextReachable commands pre limit (((limit+1)*2*TurtleWidth commands)*2) nf nd ns ↔
      PrefixReachable commands (pre+1) nf nd ns := by
  constructor
  · rintro ⟨f,d,s,b,e,hf,hd,hs,hb,hr,⟨modified,p,pd,hchanged,hstate,hp,hpd⟩,hfe,hfl,he,hst⟩
    have hchanged' : PrefixChangedByFlips commands (modified++[e]) (pre+1) nf := by
      rw [hfe]
      exact prefix_changed_extend__layer_swap commands modified pre f b e hpre hchanged he
    have hpd' : pd=1-2*d := by rcases hpd with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    refine ⟨modified++[e],ns-Zlength commands,1-2*nd,hchanged',?_,rfl,by omega⟩
    apply turtle_state_extend__layer_swap modified p pd e _ _ hstate
    rcases hst with ⟨he,hdir,hslot⟩ | ⟨he,hdir,⟨hd0,hslot⟩ | ⟨hd1,hslot⟩⟩
    · exact Or.inl ⟨he,by omega,by omega⟩
    · exact Or.inr ⟨he,by omega,by omega⟩
    · exact Or.inr ⟨he,by omega,by omega⟩
  · rintro ⟨modified,np,npd,hchanged,hstate,hp,hpd⟩
    rcases prefix_changed_unextend__layer_swap commands modified pre nf hpre hchanged with ⟨before,f,b,e,hm,hfe,hbefore,he⟩
    have hea : e=70 ∨ e=84 := by
      rcases he with ⟨hb,he⟩ | ⟨hb,⟨h1,h2⟩ | ⟨h1,h2⟩⟩
      · rw [he]; exact ha pre hpre
      · exact Or.inr h2
      · exact Or.inl h2
    rw [hm] at hstate
    rcases turtle_state_unextend__layer_swap before e np npd hea hstate with ⟨p,pd,hstate',hst⟩
    have hbound := turtle_state_endpoint_bound__layer_swap before p pd hstate'
    have hflen := hbefore.2.1
    have hfnon := prefix_changed_flips_nonneg__layer_swap commands before pre f hbefore
    have hb : 0≤b ∧ b<2 := by rcases he with hh | hh <;> have := hh.1 <;> omega
    have hf : 0≤f ∧ f≤limit := by omega
    have hs : 0≤p+Zlength commands ∧ p+Zlength commands<TurtleWidth commands := by unfold TurtleWidth; omega
    have hdir : ∃ d:Int, (0≤d ∧ d<2) ∧ ((d=0 ∧ pd=1) ∨ (d=1 ∧ pd= -1)) := by
      rcases hbound.2 with hp | hp
      · exact ⟨0,by omega,Or.inl ⟨rfl,hp⟩⟩
      · exact ⟨1,by omega,Or.inr ⟨rfl,hp⟩⟩
    rcases hdir with ⟨d,hd,hpd'⟩
    have hi := cell_bounds commands limit f d (p+Zlength commands) hf hd hs
    refine ⟨f,d,p+Zlength commands,b,e,hf,hd,hs,hb,?_,⟨before,p,pd,hbefore,hstate',by omega,hpd'⟩,hfe,hnf.2,he,?_⟩
    · unfold TurtleTransitionRank
      omega
    · unfold TurtleEncodedStep
      rcases hst with ⟨he,hpos,hdir⟩ | ⟨he,hpos,hdir⟩ <;>
        rcases hpd with ⟨hnd0,hpd0⟩ | ⟨hnd1,hpd1⟩ <;>
        rcases hpd' with ⟨hd0,hpd0'⟩ | ⟨hd1,hpd1'⟩ <;> omega

theorem turtle_next_complete_layer__layer_swap (commands : List Int) (pre limit : Int) (table : List Int)
    (hpre : 0≤pre ∧ pre<Zlength commands) (hlimit : 0≤limit)
    (ha : ∀ k, (0≤k ∧ k<Zlength commands) → Znth k commands 0=70 ∨ Znth k commands 0=84)
    (h : TurtleNextPrefix commands pre limit (((limit+1)*2*TurtleWidth commands)*2) table) :
    TurtleLayerMeaning commands (pre+1) limit table := by
  intro f d s hf hd hs
  have hh := h f d s hf hd hs
  exact ⟨hh.1,hh.2.trans (turtle_next_complete_reachable_iff__layer_swap commands pre limit f d s hpre hlimit ha hf hd hs)⟩

theorem turtle_answer_complete_spec__final_spec (commands : List Int) (limit : Int) (table : List Int) (answer : Int)
    (hpre : Pre limit commands) (hlayer : TurtleLayerMeaning commands (Zlength commands) limit table)
    (hanswer : TurtleAnswerPrefix commands limit (((limit+1)*2)*TurtleWidth commands) answer) : Spec limit commands answer := by
  rcases hpre with ⟨hlen,hlimit,ha⟩
  have hne : commands≠[] := by intro he; rw [he,Zlength_nil] at hlen; omega
  have to_terminal : ∀ modified p, ChangedExactly commands modified limit → TurtleEnd modified p →
      ∃ f d s, TurtleTerminalEligible commands limit f d s ∧ p=s-Zlength commands := by
    intro modified p hchanged hend
    rcases hchanged with ⟨hml,counts,hcl,hcf,hcs,hcp⟩
    rcases change_counts_compress__final_spec commands modified counts hml hcl hcf hcp with ⟨marks,hmlen,hmf,hmle,hmpar,hmp⟩
    have hmn : Forall (fun x:Int=>0≤x) marks := Forall.iff_forall_mem.mpr (fun x hx=>by have := hmf.mem hx; omega)
    have hsum := fold_right_nonnegative__final_spec marks hmn
    rcases turtle_end_to_state__final_spec modified p hend with ⟨pd,hstate⟩
    have hb := turtle_state_endpoint_bound__layer_swap modified p pd hstate
    have hdir : ∃ d:Int, (0≤d ∧ d<2) ∧ ((d=0 ∧ pd=1) ∨ (d=1 ∧ pd= -1)) := by
      rcases hb.2 with hp | hp
      · exact ⟨0,by omega,Or.inl ⟨rfl,hp⟩⟩
      · exact ⟨1,by omega,Or.inr ⟨rfl,hp⟩⟩
    rcases hdir with ⟨d,hd,hpd⟩
    refine ⟨marks.foldr (·+·) 0,d,p+Zlength commands,⟨by omega,hd,?_,?_,?_⟩,by omega⟩
    · unfold TurtleWidth; omega
    · rw [hcs] at hmpar
      exact hmpar
    · exact ⟨modified,p,pd,⟨by omega,hml,marks,hmlen,hmf,rfl,hmp⟩,hstate,by omega,hpd⟩
  have to_candidate : ∀ f d s, TurtleTerminalEligible commands limit f d s →
      ∃ modified p, ChangedExactly commands modified limit ∧ TurtleEnd modified p ∧ p=s-Zlength commands := by
    intro f d s ht
    rcases ht with ⟨hf,hd,hs,hpar,modified,p,pd,⟨hpr,hml,marks,hmlen,hmf,hms,hmp⟩,hstate,hp,hpd⟩
    rcases change_counts_expand__final_spec commands modified marks limit hne hml hmlen hmf (by omega) (by rw [hms]; exact hpar) hmp with ⟨counts,hcl,hcf,hcs,hcp⟩
    exact ⟨modified,p,⟨hml,counts,hcl,hcf,hcs,hcp⟩,turtle_state_to_end__final_spec modified p pd hstate,hp⟩
  have upper : ∀ modified p, ChangedExactly commands modified limit → TurtleEnd modified p → Z.abs p≤answer := by
    intro modified p hc he
    rcases to_terminal modified p hc he with ⟨f,d,s,ht,hp⟩
    rw [hp]
    exact hanswer.2.1 f d s ht (cell_bounds commands limit f d s ht.1 ht.2.1 ht.2.2.1).2
  have attained : ∃ modified p, ChangedExactly commands modified limit ∧ TurtleEnd modified p ∧ Z.abs p=answer := by
    rcases hanswer.2.2 with hz | ⟨f,d,s,ht,hi,hv⟩
    · rcases changed_exactly_exists__final_spec commands limit hne (by omega) ha with ⟨modified,hc⟩
      rcases turtle_state_exists__final_spec modified with ⟨p,d,hs⟩
      have he := turtle_state_to_end__final_spec modified p d hs
      have hu := upper modified p hc he
      have hn := Z.abs_nonneg p
      exact ⟨modified,p,hc,he,by omega⟩
    · rcases to_candidate f d s ht with ⟨modified,p,hc,he,hp⟩
      exact ⟨modified,p,hc,he,by rw [hp]; exact hv.symm⟩
  rcases attained with ⟨modified,p,hc,he,hv⟩
  refine ⟨(modified,p),⟨⟨hc,he⟩,?_⟩,hv⟩
  rintro ⟨other,q⟩ ⟨hc',he'⟩
  change Z.abs q≤Z.abs p
  rw [hv]
  exact upper other q hc' he'

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P058_132C_logo_turtle_lib
