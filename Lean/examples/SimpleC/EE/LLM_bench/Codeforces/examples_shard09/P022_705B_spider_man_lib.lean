import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import AUXLib.ZParity
import ListLib.General.Length

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_lib
open AUXLib


def SplitMove (a b : List Int) : Prop :=
  ∃ i p x, (0 ≤ i ∧ i < Zlength a) ∧ x = Znth i a 0 ∧ (1 ≤ p ∧ p < x) ∧
    List.Perm b (p :: (x - p) :: sublist 0 i a ++ sublist (i + 1) (Zlength a) a)

def SplitPlay (init : List Int) (p : List (List Int)) : Prop :=
  p ≠ [] ∧ Znth 0 p [] = init ∧
    (∀ i, (0 ≤ i ∧ i < Zlength p - 1) → SplitMove (Znth i p []) (Znth (i+1) p [])) ∧
    Forall (fun x => x = 1) (Znth (Zlength p-1) p []) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength p-1) → ∃ x, x ∈ Znth i p [] ∧ x ≥ 2)

def SplitFirstFollows (f : List (List Int) → List Int) (p : List (List Int)) : Prop :=
  ∀ i, (0 ≤ i ∧ i < Zlength p-1) → Z.even i = true → Znth (i+1) p [] = f (sublist 0 (i+1) p)

def SplitFirstWins (a : List Int) : Prop :=
  ∃ f, (∀ hist, hist ≠ [] → (∃ x, x ∈ Znth (Zlength hist-1) hist [] ∧ x ≥ 2) →
    SplitMove (Znth (Zlength hist-1) hist []) (f hist)) ∧
    ∀ p, SplitPlay a p → SplitFirstFollows f p → Z.even (Zlength p) = true

def Pre (added : List Int) : Prop := True

def Spec (added out : List Int) : Prop :=
  Zlength out = Zlength added ∧ ∀ i, (0 ≤ i ∧ i < Zlength added) →
    ((Znth i out 0 = 1 ∧ SplitFirstWins (sublist 0 (i+1) added)) ∨
      (Znth i out 0 = 2 ∧ ¬ SplitFirstWins (sublist 0 (i+1) added)))

def CycleMoveCount (added : List Int) : Int := added.foldr (· + ·) 0 - Zlength added

def SpiderWinnerCode (moves code : Int) : Prop :=
  (code = 1 ∧ Z.odd moves = true) ∨ (code = 2 ∧ Z.even moves = true)

def NextParity (par a next : Int) : Prop :=
  (0 ≤ par ∧ par ≤ 1) ∧ 1 ≤ a ∧ next = Z.rem (par + (a - 1)) 2

def SpiderPrefixState (added out : List Int) (par : Int) : Prop :=
  Zlength out = Zlength added ∧ (0 ≤ par ∧ par ≤ 1) ∧ par = Z.rem (CycleMoveCount added) 2 ∧
    ∀ i, (0 ≤ i ∧ i < Zlength added) → SpiderWinnerCode (CycleMoveCount (sublist 0 (i + 1) added)) (Znth i out 0)


theorem land_one_eq_rem_two_nonnegative__parity_foundation (z : Int) (hz : 0≤z) :
    Z.land z 1 = Z.rem z 2 := by
  have h := Z.land_ones z 1 (by omega)
  change Z.land z 1 = Z.modulo z 2 at h
  exact h.trans (rem_eq_mod z 2 hz (by omega)).symm

theorem forall_Znth_intro__prefix_evolution (P : Int → Prop) (l : List Int) (d : Int)
    (h : ∀ i, 0≤i ∧ i<Zlength l → P (Znth i l d)) : Forall P l := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    have hl := Zlength_nonneg l
    have hh := h 0 (by rw [Zlength_cons]; omega)
    apply Forall.cons hh
    apply ih
    intro i hi
    have ht := h (i+1) (by rw [Zlength_cons]; omega)
    rw [Znth_cons d (i+1) a l (by omega),add_sub_cancel_right] at ht
    exact ht

theorem cycle_move_count_nonnegative__prefix_evolution (added : List Int)
    (h : Forall (fun x => 1≤x) added) : 0≤CycleMoveCount added := by
  induction h with
  | nil => decide
  | @cons x l hx ht ih =>
    unfold CycleMoveCount at *
    rw [Zlength_cons,List.foldr_cons]
    omega

theorem fold_add_app__final_result (a b : List Int) :
    (a++b).foldr (·+·) 0 = a.foldr (·+·) 0 + b.foldr (·+·) 0 := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [List.cons_append,List.foldr_cons,ih]; omega

theorem cycle_move_count_sublist_succ__prefix_evolution (added : List Int) (i : Int)
    (hi : 0≤i ∧ i<Zlength added) :
    CycleMoveCount (sublist 0 (i+1) added) = CycleMoveCount (sublist 0 i added)+(Znth i added 0-1) := by
  rw [sublist_split 0 (i+1) i added ⟨by omega,hi.1⟩ ⟨by omega,by omega⟩,
    sublist_single 0 i added hi]
  unfold CycleMoveCount
  rw [fold_add_app__final_result,Zlength_app,Zlength_cons,Zlength_nil]
  simp only [List.foldr_cons,List.foldr_nil]
  omega

theorem permutation_sum__final_result (a b : List Int) (h : List.Perm a b) :
    a.foldr (·+·) 0=b.foldr (·+·) 0 := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [List.foldr_cons]; omega
  | swap x y l => simp only [List.foldr_cons]; omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem permutation_Zlength__final_result {A : Type} (a b : List A) (h : List.Perm a b) :
    Zlength a=Zlength b := congrArg Int.ofNat h.length_eq

theorem split_move_count_step__final_result (a b : List Int) (h : SplitMove a b) :
    CycleMoveCount b=CycleMoveCount a-1 := by
  rcases h with ⟨i,p,x,hi,hx,hp,hperm⟩
  have ha : a=(sublist 0 i a++[x])++sublist (i+1) (Zlength a) a := by
    calc
      a = sublist 0 (Zlength a) a := (sublist_self a (Zlength a) rfl).symm
      _ = sublist 0 (i+1) a ++ sublist (i+1) (Zlength a) a :=
        sublist_split 0 (Zlength a) (i+1) a ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
      _ = _ := by rw [sublist_split 0 (i+1) i a ⟨by omega,hi.1⟩ ⟨by omega,by omega⟩,
                       sublist_single 0 i a hi,←hx]
  have hs := congrArg (fun l : List Int => l.foldr (·+·) 0) ha
  have hl := congrArg (fun l : List Int => Zlength l) ha
  simp only [fold_add_app__final_result,List.foldr_cons,List.foldr_nil] at hs
  simp only [Zlength_app,Zlength_cons,Zlength_nil] at hl
  unfold CycleMoveCount
  rw [permutation_sum__final_result _ _ hperm,permutation_Zlength__final_result _ _ hperm]
  simp only [List.foldr_cons,Zlength_cons,Zlength_app,fold_add_app__final_result]
  omega

theorem Forall_firstn__final_result {A : Type} (P : A → Prop) (n : Nat) (l : List A)
    (h : Forall P l) : Forall P (firstn n l) :=
  Forall.iff_forall_mem.mpr fun x hx => h.mem (List.mem_of_mem_take hx)

theorem Forall_skipn__final_result {A : Type} (P : A → Prop) (n : Nat) (l : List A)
    (h : Forall P l) : Forall P (skipn n l) :=
  Forall.iff_forall_mem.mpr fun x hx => h.mem (List.mem_of_mem_drop hx)

theorem Forall_sublist__final_result {A : Type} (P : A → Prop) (lo hi : Int) (l : List A)
    (h : Forall P l) : Forall P (sublist lo hi l) :=
  Forall_skipn__final_result P lo.toNat _ (Forall_firstn__final_result P hi.toNat l h)

theorem split_move_positive__final_result (a b : List Int)
    (hpos : Forall (fun x => 1≤x) a) (h : SplitMove a b) : Forall (fun x => 1≤x) b := by
  rcases h with ⟨i,p,x,hi,hx,hp,hperm⟩
  apply Forall.iff_forall_mem.mpr
  intro y hy
  have hm := hperm.mem_iff.mp hy
  simp only [List.mem_cons,List.mem_append] at hm
  rcases hm with (rfl|rfl|hleft)|hright
  · omega
  · omega
  · exact (Forall_sublist__final_result _ 0 i a hpos).mem hleft
  · exact (Forall_sublist__final_result _ (i+1) (Zlength a) a hpos).mem hright

theorem cycle_count_ones__final_result (a : List Int) (h : Forall (fun x => x=1) a) :
    CycleMoveCount a=0 := by
  induction h with
  | nil => rfl
  | @cons x l hx ht ih =>
    unfold CycleMoveCount at *
    rw [Zlength_cons,List.foldr_cons]
    omega

theorem cycle_count_nonnegative__final_result (a : List Int) (h : Forall (fun x => 1≤x) a) :
    0≤CycleMoveCount a := cycle_move_count_nonnegative__prefix_evolution a h

theorem cycle_count_zero_ones__final_result (a : List Int)
    (h : Forall (fun x => 1≤x) a) (hc : CycleMoveCount a=0) : Forall (fun x => x=1) a := by
  induction h with
  | nil => exact .nil
  | @cons x l hx ht ih =>
    have hn := cycle_count_nonnegative__final_result l ht
    have hd : CycleMoveCount (x::l)=x-1+CycleMoveCount l := by
      unfold CycleMoveCount
      rw [Zlength_cons,List.foldr_cons]
      omega
    exact .cons (by omega) (ih (by omega))

theorem decrement_telescope__final_result {A : Type} (measure : A → Int) (d : A) (p : List A)
    (hne : p≠[]) (hs : ∀ i, 0≤i ∧ i<Zlength p-1 → measure (Znth (i+1) p d)=measure (Znth i p d)-1) :
    measure (Znth (Zlength p-1) p d)=measure (Znth 0 p d)-(Zlength p-1) := by
  have hl : 1≤Zlength p := by
    cases p with
    | nil => contradiction
    | cons a p => rw [Zlength_cons]; have hp := Zlength_nonneg p; omega
  have hi : ∀ n : Nat, (n:Int)<Zlength p → measure (Znth (n:Int) p d)=measure (Znth 0 p d)-(n:Int) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have he : (n.succ:Int)=(n:Int)+1 := by omega
      rw [he,hs (n:Int) (by omega),ih (by omega)]
      omega
  have he : ((Zlength p-1).toNat:Int)=Zlength p-1 := Int.toNat_of_nonneg (by omega)
  simpa only [he] using hi (Zlength p-1).toNat (by omega)

theorem split_play_move_count__final_result (init : List Int) (play : List (List Int))
    (hp : Forall (fun x => 1≤x) init) (h : SplitPlay init play) :
    Zlength play-1=CycleMoveCount init := by
  rcases h with ⟨hne,hfirst,hsteps,hfinal,hnt⟩
  have ht := decrement_telescope__final_result CycleMoveCount [] play hne
    (fun i hi => split_move_count_step__final_result _ _ (hsteps i hi))
  rw [hfirst,cycle_count_ones__final_result _ hfinal] at ht
  omega

theorem In_Znth_Zlength__final_result {A : Type} (l : List A) (x d : A) (hx : x∈l) :
    ∃ i, (0≤i ∧ i<Zlength l) ∧ Znth i l d=x := by
  rcases List.mem_iff_getElem.mp hx with ⟨i,hi,he⟩
  refine ⟨(i:Int),⟨by omega,by change (i:Int)<(l.length:Int);omega⟩,?_⟩
  change l.getD i d=x
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using he

theorem split_move_exists__final_result (a : List Int) (h : ∃ x, x∈a ∧ x≥2) : ∃ b, SplitMove a b := by
  rcases h with ⟨x,hx,hge⟩
  rcases In_Znth_Zlength__final_result a x 0 hx with ⟨i,hi,hix⟩
  exact ⟨1::(x-1)::sublist 0 i a++sublist (i+1) (Zlength a) a,i,1,x,hi,hix.symm,⟨by omega,by omega⟩,List.Perm.refl _⟩

theorem positive_cycle_nonterminal__final_result (a : List Int)
    (hp : Forall (fun x => 1≤x) a) (hc : CycleMoveCount a>0) : ∃ x, x∈a ∧ x≥2 := by
  by_contra hn
  have ho : Forall (fun x => x=1) a := Forall.iff_forall_mem.mpr (by
    intro x hx
    have hp := hp.mem hx
    have hlt : ¬x≥2 := fun hg => hn ⟨x,hx,hg⟩
    omega)
  have he := cycle_count_ones__final_result a ho
  omega


private theorem nth_app_left {A : Type} (d : A) (l r : List A) (i : Int) (hi : 0≤i ∧ i<Zlength l) :
    Znth i (l++r) d=Znth i l d := ListLib.app_Znth1 d l r i hi

private theorem sublist_app_left {A : Type} (lo hi : Int) (l r : List A)
    (hr : 0≤lo ∧ lo≤hi) (hh : hi≤Zlength l) : sublist lo hi (l++r)=sublist lo hi l :=
  ListLib.sublist_split_app_l lo hi l r hr hh

private theorem prefix_length {A : Type} (i : Int) (l : List A) (hi : 0≤i ∧ i≤Zlength l) :
    Zlength (sublist 0 i l)=i := ListLib.Zlength_sublist0 i l hi

private theorem prefix_nth {A : Type} (d : A) (i hi : Int) (l : List A) (h : 0≤i ∧ i<hi) :
    Znth i (sublist 0 hi l) d=Znth i l d := ListLib.Znth_sublist0 d i hi l h

private theorem prefix_prefix {A : Type} (i j : Int) (l : List A) (h : 0≤i ∧ i≤j) :
    sublist 0 i (sublist 0 j l)=sublist 0 i l := ListLib.Zsublist_Zsublist00 i j l h

private theorem rem_two (n : Int) (hn : 0≤n) : Z.rem n 2=n%2 := by
  rw [rem_eq_mod n 2 hn (by omega)]
  exact Int.fmod_eq_emod_of_nonneg n (by omega)

private theorem nonempty_length {A : Type} (h : List A) (hne : h≠[]) : 0<Zlength h := by
  cases h with
  | nil => contradiction
  | cons a h => rw [Zlength_cons]; have hh:=Zlength_nonneg h;omega

theorem extend_history_first__final_result {A : Type} (h : List A) (b d : A) (hne : h≠[]) :
    Znth 0 (h++[b]) d=Znth 0 h d :=
  nth_app_left d h [b] 0 ⟨by omega,nonempty_length h hne⟩

theorem extend_history_last__final_result {A : Type} (h : List A) (b d : A) :
    Znth (Zlength (h++[b])-1) (h++[b]) d=b := by
  rw [Zlength_app,Zlength_cons,Zlength_nil]
  have he : Zlength h+(0+1)-1=Zlength h := by omega
  rw [he,app_Znth2 d h [b] (Zlength h) (by omega),sub_self]
  rfl

theorem extend_history_steps__final_result (h : List (List Int)) (b : List Int)
    (hne : h≠[]) (hs : ∀ i, 0≤i ∧ i<Zlength h-1 → SplitMove (Znth i h []) (Znth (i+1) h []))
    (hl : SplitMove (Znth (Zlength h-1) h []) b) :
    ∀ i, 0≤i ∧ i<Zlength (h++[b])-1 → SplitMove (Znth i (h++[b]) []) (Znth (i+1) (h++[b]) []) := by
  intro i hi
  rw [Zlength_app,Zlength_cons,Zlength_nil] at hi
  by_cases ho : i<Zlength h-1
  · rw [nth_app_left [] h [b] i (by omega),nth_app_left [] h [b] (i+1) (by omega)]
    exact hs i ⟨hi.1,ho⟩
  · have he : i=Zlength h-1 := by omega
    subst i
    rw [nth_app_left [] h [b] (Zlength h-1) (by omega),sub_add_cancel,
        app_Znth2 [] h [b] (Zlength h) (by omega),sub_self]
    exact hl

theorem extend_history_nonterminal__final_result (h : List (List Int)) (b : List Int)
    (hne : h≠[]) (ho : ∀ i, 0≤i ∧ i<Zlength h-1 → ∃ x, x∈Znth i h [] ∧ x≥2)
    (hl : ∃ x, x∈Znth (Zlength h-1) h [] ∧ x≥2) :
    ∀ i, 0≤i ∧ i<Zlength (h++[b])-1 → ∃ x, x∈Znth i (h++[b]) [] ∧ x≥2 := by
  intro i hi
  rw [Zlength_app,Zlength_cons,Zlength_nil] at hi
  rw [nth_app_left [] h [b] i (by omega)]
  by_cases hold : i<Zlength h-1
  · exact ho i ⟨hi.1,hold⟩
  · have he : i=Zlength h-1 := by omega
    simpa only [he] using hl

theorem extend_history_follows__final_result (f : List (List Int) → List Int) (h : List (List Int))
    (hne : h≠[]) (hf : SplitFirstFollows f h) : SplitFirstFollows f (h++[f h]) := by
  intro i hi heven
  rw [Zlength_app,Zlength_cons,Zlength_nil] at hi
  by_cases ho : i<Zlength h-1
  · rw [nth_app_left [] h [f h] (i+1) (by omega),
        sublist_app_left 0 (i+1) h [f h] ⟨by omega,by omega⟩ (by omega)]
    exact hf i ⟨hi.1,ho⟩ heven
  · have he : i+1=Zlength h := by omega
    rw [he,app_Znth2 [] h [f h] (Zlength h) (by omega),sub_self,sublist_app_exact1]
    rfl

theorem strategy_play_exists_from_history__final_result (n : Nat) (init : List Int)
    (f : List (List Int) → List Int) (h : List (List Int))
    (hl : ∀ hist, hist≠[] → (∃ x, x∈Znth (Zlength hist-1) hist [] ∧ x≥2) →
      SplitMove (Znth (Zlength hist-1) hist []) (f hist))
    (hne : h≠[]) (hfirst : Znth 0 h []=init)
    (hsteps : ∀ i, 0≤i ∧ i<Zlength h-1 → SplitMove (Znth i h []) (Znth (i+1) h []))
    (hfollow : SplitFirstFollows f h)
    (hnt : ∀ i, 0≤i ∧ i<Zlength h-1 → ∃ x, x∈Znth i h [] ∧ x≥2)
    (hpos : Forall (fun x => 1≤x) (Znth (Zlength h-1) h []))
    (hc : CycleMoveCount (Znth (Zlength h-1) h [])=(n:Int)) :
    ∃ p, SplitPlay init p ∧ SplitFirstFollows f p := by
  induction n generalizing h with
  | zero =>
    exact ⟨h,⟨hne,hfirst,hsteps,cycle_count_zero_ones__final_result _ hpos hc,hnt⟩,hfollow⟩
  | succ n ih =>
    have hcur := positive_cycle_nonterminal__final_result _ hpos (by omega)
    have hm := hl h hne hcur
    apply ih (h++[f h])
    · intro hz
      have hz := List.append_eq_nil_iff.mp hz
      exact hne hz.1
    · rw [extend_history_first__final_result h (f h) [] hne]
      exact hfirst
    · exact extend_history_steps__final_result h (f h) hne hsteps hm
    · exact extend_history_follows__final_result f h hne hfollow
    · exact extend_history_nonterminal__final_result h (f h) hne hnt hcur
    · rw [extend_history_last__final_result]
      exact split_move_positive__final_result _ _ hpos hm
    · rw [extend_history_last__final_result,split_move_count_step__final_result _ _ hm,hc]
      omega

theorem even_successor_iff_odd__final_result (n : Int) : Z.even (n+1)=true ↔ Z.odd n=true := by
  simp only [Z.even,Z.odd,decide_eq_true_eq]
  omega

theorem strategy_play_exists__final_result (init : List Int) (f : List (List Int) → List Int)
    (hne : init≠[]) (hpos : Forall (fun x => 1≤x) init)
    (hl : ∀ hist, hist≠[] → (∃ x, x∈Znth (Zlength hist-1) hist [] ∧ x≥2) →
      SplitMove (Znth (Zlength hist-1) hist []) (f hist)) :
    ∃ p, SplitPlay init p ∧ SplitFirstFollows f p := by
  have hn := cycle_count_nonnegative__final_result init hpos
  apply strategy_play_exists_from_history__final_result (CycleMoveCount init).toNat init f [init] hl
  · simp
  · rfl
  · intro i hi
    change 0≤i ∧ i<1-1 at hi
    omega
  · intro i hi he
    change 0≤i ∧ i<1-1 at hi
    omega
  · intro i hi
    change 0≤i ∧ i<1-1 at hi
    omega
  · exact hpos
  · change CycleMoveCount init=((CycleMoveCount init).toNat:Int)
    omega

theorem split_first_wins_iff_odd__final_result (init : List Int)
    (hne : init≠[]) (hpos : Forall (fun x => 1≤x) init) :
    SplitFirstWins init ↔ Z.odd (CycleMoveCount init)=true := by
  classical
  constructor
  · rintro ⟨f,hl,hw⟩
    rcases strategy_play_exists__final_result init f hne hpos hl with ⟨p,hp,hf⟩
    have he := hw p hp hf
    have hc := split_play_move_count__final_result init p hpos hp
    rw [show Zlength p=CycleMoveCount init+1 by omega] at he
    exact (even_successor_iff_odd__final_result _).mp he
  · intro hodd
    have ht : ∀ hist : List (List Int), ∃ b, hist≠[] →
        (∃ x, x∈Znth (Zlength hist-1) hist [] ∧ x≥2) →
        SplitMove (Znth (Zlength hist-1) hist []) b := by
      intro hist
      by_cases h : ∃ x, x∈Znth (Zlength hist-1) hist [] ∧ x≥2
      · rcases split_move_exists__final_result _ h with ⟨b,hb⟩
        exact ⟨b,fun _ _ => hb⟩
      · exact ⟨[],fun _ hx => False.elim (h hx)⟩
    let f := fun hist => Classical.choose (ht hist)
    have hl : ∀ hist, hist≠[] → (∃ x, x∈Znth (Zlength hist-1) hist [] ∧ x≥2) →
        SplitMove (Znth (Zlength hist-1) hist []) (f hist) :=
      fun hist => Classical.choose_spec (ht hist)
    refine ⟨f,hl,?_⟩
    intro p hp hf
    have hc := split_play_move_count__final_result init p hpos hp
    rw [show Zlength p=CycleMoveCount init+1 by omega]
    exact (even_successor_iff_odd__final_result _).mpr hodd


theorem spider_prefix_state_extend__prefix_evolution (added written : List Int) (par i next code : Int)
    (hi : 0≤i ∧ i<Zlength added) (hp : ∀ j, 0≤j ∧ j<Zlength added → 1≤Znth j added 0)
    (hn : NextParity par (Znth i added 0) next)
    (hs : SpiderPrefixState (sublist 0 i added) written par)
    (hc : (code=1 ∧ next=1) ∨ (code=2 ∧ next=0)) :
    SpiderPrefixState (sublist 0 (i+1) added) (written++[code]) next := by
  rcases hs with ⟨hl,hpar,hmod,hw⟩
  rcases hn with ⟨hpar',ha,hn⟩
  have hli := prefix_length i added ⟨hi.1,by omega⟩
  have hls := prefix_length (i+1) added ⟨by omega,by omega⟩
  have hwlen : Zlength written=i := hl.trans hli
  have hpos : Forall (fun x => 1≤x) (sublist 0 i added) := by
    apply forall_Znth_intro__prefix_evolution _ _ 0
    intro j hj
    rw [hli] at hj
    rw [prefix_nth 0 j i added hj]
    exact hp j (by omega)
  have hold := cycle_move_count_nonnegative__prefix_evolution _ hpos
  have hstep := cycle_move_count_sublist_succ__prefix_evolution added i hi
  have hnew : 0≤CycleMoveCount (sublist 0 (i+1) added) := by omega
  rw [rem_two _ (by omega)] at hn
  rw [rem_two _ hold] at hmod
  have hnewpar : next=Z.rem (CycleMoveCount (sublist 0 (i+1) added)) 2 := by
    rw [rem_two _ hnew]
    omega
  refine ⟨?_,⟨by omega,by omega⟩,hnewpar,?_⟩
  · rw [Zlength_app,Zlength_cons,Zlength_nil,hls,hwlen]
    omega
  · intro k hk
    rw [hls] at hk
    by_cases hki : k<i
    · have hwk := hw k (by rw [hli];omega)
      rw [prefix_prefix (k+1) i added (by omega)] at hwk
      rw [prefix_prefix (k+1) (i+1) added (by omega),nth_app_left 0 written [code] k (by omega)]
      exact hwk
    · have he : k=i := by omega
      subst k
      rw [prefix_prefix (i+1) (i+1) added (by omega),app_Znth2 0 written [code] i (by omega),hwlen,sub_self]
      change (code=1 ∧ Z.odd (CycleMoveCount (sublist 0 (i+1) added))=true) ∨
             (code=2 ∧ Z.even (CycleMoveCount (sublist 0 (i+1) added))=true)
      rw [rem_two _ hnew] at hnewpar
      simp only [Z.odd,Z.even,decide_eq_true_eq]
      rcases hc with ⟨hc,hn⟩|⟨hc,hn⟩
      · exact Or.inl ⟨hc,by omega⟩
      · exact Or.inr ⟨hc,by omega⟩

theorem spider_prefix_state_implies_spec__final_result (added out : List Int) (par : Int)
    (hp : ∀ i, 0≤i ∧ i<Zlength added → 1≤Znth i added 0)
    (hs : SpiderPrefixState added out par) : Spec added out := by
  rcases hs with ⟨hl,hpar,hmod,hw⟩
  have hpos := forall_Znth_intro__prefix_evolution _ added 0 hp
  refine ⟨hl,?_⟩
  intro i hi
  have hpp := Forall_sublist__final_result _ 0 (i+1) added hpos
  have hne : sublist 0 (i+1) added≠[] := by
    intro he
    have hh := prefix_length (i+1) added ⟨by omega,by omega⟩
    rw [he,Zlength_nil] at hh
    omega
  have he := split_first_wins_iff_odd__final_result _ hne hpp
  rcases hw i hi with ⟨hc,ho⟩|⟨hc,hv⟩
  · exact Or.inl ⟨hc,he.mpr ho⟩
  · refine Or.inr ⟨hc,?_⟩
    intro hwin
    have ho := he.mp hwin
    simp only [Z.even,Z.odd,decide_eq_true_eq] at hv ho
    omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_lib
