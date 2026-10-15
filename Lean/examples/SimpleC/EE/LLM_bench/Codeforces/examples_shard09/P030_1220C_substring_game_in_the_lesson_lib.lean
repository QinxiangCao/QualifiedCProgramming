import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Presuffix
import AUXLib.ZParity

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_lib
open AUXLib


def LexLt (a b : List Int) : Prop :=
  (∃ i, (0 ≤ i ∧ i < min (Zlength a) (Zlength b)) ∧
    (∀ j, (0 ≤ j ∧ j < i) → Znth j a 0 = Znth j b 0) ∧ Znth i a 0 < Znth i b 0) ∨
  (Zlength a < Zlength b ∧ ListLib.is_prefix a b)

def IntervalMove (s : List Int) (a b : Int × Int) : Prop :=
  b.1 ≤ a.1 ∧ a.2 ≤ b.2 ∧ (0 ≤ b.1 ∧ b.1 ≤ b.2) ∧ b.2 < Zlength s ∧
    LexLt (sublist b.1 (b.2+1) s) (sublist a.1 (a.2+1) s)

def IntervalPlay (s : List Int) (k : Int) (p : List (Int × Int)) : Prop :=
  p ≠ [] ∧ Znth 0 p (0,0) = (k,k) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength p - 1) → IntervalMove s (Znth i p (0,0)) (Znth (i+1) p (0,0))) ∧
    ¬ ∃ q, IntervalMove s (Znth (Zlength p-1) p (0,0)) q

def AnnFollows (f : List (Int × Int) → Int × Int) (p : List (Int × Int)) : Prop :=
  ∀ i, (0 ≤ i ∧ i < Zlength p - 1) → Z.even i = true → Znth (i+1) p (0,0) = f (sublist 0 (i+1) p)

def AnnWins (s : List Int) (k : Int) : Prop :=
  ∃ f, (∀ hist, hist ≠ [] → (∃ q, IntervalMove s (Znth (Zlength hist-1) hist (0,0)) q) →
    IntervalMove s (Znth (Zlength hist-1) hist (0,0)) (f hist)) ∧
    ∀ p, IntervalPlay s k p → AnnFollows f p → Z.even (Zlength p) = true

def Pre (s : List Int) : Prop := True

def Spec (s : List Int) (out : List Int) : Prop :=
  Zlength out = Zlength s ∧ ∀ k, (0 ≤ k ∧ k < Zlength s) →
    ((Znth k out 0 = 1 ∧ AnnWins s k) ∨ (Znth k out 0 = 0 ∧ ¬ AnnWins s k))

def PrefixMinimum (s : List Int) (k mn : Int) : Prop :=
  (0 ≤ k ∧ k ≤ Zlength s) ∧ ((k = 0 ∧ mn = 123) ∨
    (0 < k ∧ (∃ j, (0 ≤ j ∧ j < k) ∧ mn = Znth j s 0) ∧ ∀ j, (0 ≤ j ∧ j < k) → mn ≤ Znth j s 0))

def SpecPrefix (s : List Int) (k : Int) (out : List Int) : Prop :=
  Zlength out = k ∧ ∀ i, (0 ≤ i ∧ i < k) →
    ((Znth i out 0 = 1 ∧ AnnWins s i) ∨ (Znth i out 0 = 0 ∧ ¬ AnnWins s i))


theorem Znth_app_left__prefix_transitions (A : Type) (l1 l2 : List A) (d : A) (i : Int)
    (hi : 0≤i ∧ i<Zlength l1) : Znth i (l1++l2) d=Znth i l1 d :=
  ListLib.app_Znth1 d l1 l2 i hi

theorem Znth_app_last__prefix_transitions (A : Type) (l : List A) (d x : A) :
    Znth (Zlength l) (l++[x]) d=x := by
  rw [app_Znth2 d l [x] (Zlength l) (by omega),sub_self]
  rfl

theorem prefix_minimum_step__prefix_transitions (s : List Int) (k mn : Int)
    (hk : 0≤k ∧ k<Zlength s) (hc : Znth k s 0≤122) (hm : PrefixMinimum s k mn) :
    PrefixMinimum s (k+1) (min mn (Znth k s 0)) := by
  rcases hm with ⟨hkb,⟨hk0,hmn⟩|⟨hkpos,⟨j,hj,hmn⟩,hall⟩⟩
  · subst k mn
    refine ⟨⟨by omega,by omega⟩,Or.inr ⟨by omega,⟨0,⟨by omega,by omega⟩,by omega⟩,?_⟩⟩
    intro j hj
    have he : j=0 := by omega
    subst j
    exact min_le_right _ _
  · refine ⟨⟨by omega,by omega⟩,Or.inr ⟨by omega,?_,?_⟩⟩
    · by_cases he : mn≤Znth k s 0
      · exact ⟨j,⟨hj.1,by omega⟩,by rw [min_eq_left he];exact hmn⟩
      · exact ⟨k,⟨hk.1,by omega⟩,min_eq_right (by omega)⟩
    · intro j' hj'
      by_cases he : j'=k
      · subst j';exact min_le_right _ _
      · exact le_trans (min_le_left _ _) (hall j' (by omega))

theorem spec_prefix_snoc__prefix_transitions (s : List Int) (k : Int) (out : List Int) (b : Int)
    (hs : SpecPrefix s k out) (hk : 0≤k)
    (hc : (b=1 ∧ AnnWins s k) ∨ (b=0 ∧ ¬AnnWins s k)) : SpecPrefix s (k+1) (out++[b]) := by
  rcases hs with ⟨hl,hall⟩
  refine ⟨?_,?_⟩
  · rw [Zlength_app,Zlength_cons,Zlength_nil,hl]
    omega
  · intro i hi
    by_cases he : i<k
    · rw [Znth_app_left__prefix_transitions Int out [b] 0 i (by omega)]
      exact hall i ⟨hi.1,he⟩
    · have he : i=Zlength out := by omega
      rw [he,Znth_app_last__prefix_transitions,hl]
      exact hc

theorem LexLt_cons_iff__prefix_transitions (x : Int) (xs : List Int) (y : Int) (ys : List Int) :
    LexLt (x::xs) (y::ys) ↔ x<y ∨ (x=y ∧ LexLt xs ys) := by
  constructor
  · rintro (⟨i,hi,he,ht⟩|⟨hl,tail,hpre⟩)
    · by_cases hz : i=0
      · subst i;exact Or.inl ht
      · have hxy := he 0 (by omega)
        refine Or.inr ⟨hxy,Or.inl ⟨i-1,?_,?_,?_⟩⟩
        · rw [Zlength_cons,Zlength_cons] at hi
          omega
        · intro j hj
          have hej := he (j+1) (by omega)
          rw [Znth_cons 0 (j+1) x xs (by omega),Znth_cons 0 (j+1) y ys (by omega),add_sub_cancel_right] at hej
          exact hej
        · rw [Znth_cons 0 i x xs (by omega),Znth_cons 0 i y ys (by omega)] at ht
          exact ht
    · change y::ys=x::(xs++tail) at hpre
      have hh := List.cons.inj hpre
      refine Or.inr ⟨hh.1.symm,Or.inr ⟨?_,tail,hh.2⟩⟩
      rw [Zlength_cons,Zlength_cons] at hl
      omega
  · rintro (hxy|⟨rfl,ht⟩)
    · refine Or.inl ⟨0,?_,fun j hj => False.elim (by omega),hxy⟩
      rw [Zlength_cons,Zlength_cons]
      have hx := Zlength_nonneg xs
      have hy := Zlength_nonneg ys
      omega
    · rcases ht with ⟨i,hi,he,ht⟩|⟨hl,tail,hpre⟩
      · refine Or.inl ⟨i+1,?_,?_,?_⟩
        · rw [Zlength_cons,Zlength_cons]
          omega
        · intro j hj
          by_cases hz : j=0
          · subst j;rfl
          · rw [Znth_cons 0 j x xs (by omega),Znth_cons 0 j x ys (by omega)]
            exact he (j-1) (by omega)
        · rw [Znth_cons 0 (i+1) x xs (by omega),Znth_cons 0 (i+1) x ys (by omega),add_sub_cancel_right]
          exact ht
      · refine Or.inr ⟨?_,tail,?_⟩
        · rw [Zlength_cons,Zlength_cons]
          omega
        · change x::ys=x::(xs++tail)
          rw [hpre]

-- Exact case-local expansion of Coq's polymorphic list_compare: an equal head
-- comparison continues on the tails; a non-equal comparison is returned directly.
def list_compare {A : Type} (cmp : A → A → Ordering) : List A → List A → Ordering
  | [], [] => .eq
  | [], _::_ => .lt
  | _::_, [] => .gt
  | x::xs, y::ys => match cmp x y with | .eq => list_compare cmp xs ys | c => c

private theorem lex_nil_right (a : List Int) : ¬LexLt a [] := by
  rintro (⟨i,hi,he,ht⟩|⟨hl,hp⟩)
  · rw [Zlength_nil] at hi
    omega
  · rw [Zlength_nil] at hl
    have ha := Zlength_nonneg a
    omega

private theorem lex_nil_cons (y : Int) (ys : List Int) : LexLt [] (y::ys) := by
  refine Or.inr ⟨?_,y::ys,rfl⟩
  rw [Zlength_nil,Zlength_cons]
  have hy := Zlength_nonneg ys
  omega

theorem LexLt_iff_list_compare__prefix_transitions (a b : List Int) :
    LexLt a b ↔ list_compare compare a b=Ordering.lt := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact iff_of_false (lex_nil_right []) (by decide)
    | cons y ys => exact iff_of_true (lex_nil_cons y ys) rfl
  | cons x xs ih =>
    cases b with
    | nil => exact iff_of_false (lex_nil_right (x::xs)) (by change ¬Ordering.gt=Ordering.lt;decide)
    | cons y ys =>
      rw [LexLt_cons_iff__prefix_transitions]
      change x<y ∨ (x=y ∧ LexLt xs ys) ↔ (match compare x y with | .eq => list_compare compare xs ys | c => c)=.lt
      cases hcmp : compare x y with
      | lt =>
        have ht := compare_lt_iff_lt.mp hcmp
        simp [ht]
      | eq =>
        have he := compare_eq_iff_eq.mp hcmp
        subst y
        simpa using ih ys
      | gt =>
        have ht := compare_gt_iff_gt.mp hcmp
        simp [show ¬x<y by omega,show x≠y by omega]

theorem Z_compare_same_trans__prefix_transitions (x y z : Int) (c : Ordering)
    (hxy : compare x y=c) (hyz : compare y z=c) : compare x z=c := by
  cases c with
  | lt => apply compare_lt_iff_lt.mpr;have h1:=compare_lt_iff_lt.mp hxy;have h2:=compare_lt_iff_lt.mp hyz;omega
  | eq => apply compare_eq_iff_eq.mpr;have h1:=compare_eq_iff_eq.mp hxy;have h2:=compare_eq_iff_eq.mp hyz;omega
  | gt => apply compare_gt_iff_gt.mpr;have h1:=compare_gt_iff_gt.mp hxy;have h2:=compare_gt_iff_gt.mp hyz;omega

theorem LexLt_trans__prefix_transitions (a b c : List Int) (hab : LexLt a b) (hbc : LexLt b c) : LexLt a c := by
  induction a generalizing b c with
  | nil =>
    cases c with
    | nil => exact False.elim (lex_nil_right b hbc)
    | cons z zs => exact lex_nil_cons z zs
  | cons x xs ih =>
    cases b with
    | nil => exact False.elim (lex_nil_right (x::xs) hab)
    | cons y ys =>
      cases c with
      | nil => exact False.elim (lex_nil_right (y::ys) hbc)
      | cons z zs =>
        rw [LexLt_cons_iff__prefix_transitions] at hab hbc ⊢
        rcases hab with hab|⟨hxy,hab⟩ <;> rcases hbc with hbc|⟨hyz,hbc⟩
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr ⟨hxy.trans hyz,ih ys zs hab hbc⟩

theorem LexLt_irrefl__prefix_transitions (a : List Int) : ¬LexLt a a := by
  rintro (⟨i,hi,he,ht⟩|⟨hl,hp⟩) <;> omega


private theorem segment_length {A : Type} (lo hi : Int) (s : List A)
    (hr : 0≤lo ∧ lo≤hi) (hh : hi≤Zlength s) : Zlength (sublist lo hi s)=hi-lo :=
  ListLib.Zlength_sublist lo hi s hr hh

theorem move_from_singleton_iff_earlier_smaller__prefix_transitions (s : List Int) (k : Int)
    (hk : 0≤k ∧ k<Zlength s) : (∃ b, IntervalMove s (k,k) b) ↔
    ∃ j, (0≤j ∧ j<k) ∧ Znth j s 0<Znth k s 0 := by
  constructor
  · rintro ⟨⟨l,r⟩,hlk,hkr,hl,hr,hlex⟩
    rw [sublist_single 0 k s hk] at hlex
    have hlen := segment_length l (r+1) s ⟨hl.1,by omega⟩ (by omega)
    generalize he : sublist l (r+1) s=seg at hlex hlen
    cases seg with
    | nil => rw [Zlength_nil] at hlen;omega
    | cons x xs =>
      rw [LexLt_cons_iff__prefix_transitions] at hlex
      rcases hlex with hlt|⟨hxy,ht⟩
      · have hhead := Znth_sublist 0 l 0 (r+1) s hl.1 (by omega)
        rw [he,zero_add] at hhead
        change x=Znth l s 0 at hhead
        rw [hhead] at hlt
        have hlk' : l<k := by
          by_contra hn
          have hh : l=k := by omega
          rw [hh] at hlt
          omega
        exact ⟨l,⟨hl.1,hlk'⟩,hlt⟩
      · exact False.elim (lex_nil_right xs ht)
  · rintro ⟨j,hj,hlt⟩
    refine ⟨(j,k),by omega,by omega,⟨hj.1,by omega⟩,hk.2,Or.inl ⟨0,?_,?_,?_⟩⟩
    · rw [segment_length j (k+1) s ⟨hj.1,by omega⟩ (by omega),segment_length k (k+1) s ⟨hk.1,by omega⟩ (by omega)]
      omega
    · intro i hi
      omega
    · rw [Znth_sublist 0 j 0 (k+1) s hj.1 (by omega),Znth_sublist 0 k 0 (k+1) s hk.1 (by omega),zero_add,zero_add]
      exact hlt

theorem IntervalMove_trans__prefix_transitions (s : List Int) (a b c : Int×Int)
    (hab : IntervalMove s a b) (hbc : IntervalMove s b c) : IntervalMove s a c := by
  rcases hab with ⟨hab1,hab2,hb,hbn,habl⟩
  rcases hbc with ⟨hbc1,hbc2,hc,hcn,hbcl⟩
  exact ⟨by omega,by omega,hc,hcn,LexLt_trans__prefix_transitions _ _ _ hbcl habl⟩

theorem IntervalMove_capacity_lt__prefix_transitions (s : List Int) (a b : Int×Int)
    (hm : IntervalMove s a b) : b.1+(Zlength s-1-b.2)<a.1+(Zlength s-1-a.2) := by
  rcases hm with ⟨hba,hab,hb,hbn,hl⟩
  have hne : b.1≠a.1 ∨ a.2≠b.2 := by
    by_contra hn
    have h1 : b.1=a.1 := by tauto
    have h2 : a.2=b.2 := by tauto
    rw [h1,h2] at hl
    exact LexLt_irrefl__prefix_transitions _ hl
  omega

theorem interval_valid_capacity_nonneg__prefix_transitions (s : List Int) (a : Int×Int)
    (ha : 0≤a.1 ∧ a.1≤a.2) (hn : a.2<Zlength s) : 0≤a.1+(Zlength s-1-a.2) := by omega

theorem terminal_move_from_valid__prefix_transitions (s : List Int) (a : Int×Int)
    (ha : 0≤a.1 ∧ a.1≤a.2) (han : a.2<Zlength s) (hm : ∃ b, IntervalMove s a b) :
    ∃ b, IntervalMove s a b ∧ ¬∃ c, IntervalMove s b c := by
  classical
  have h : ∀ n : Nat, ∀ a : Int×Int, (a.1+(Zlength s-1-a.2)).toNat=n →
      (0≤a.1 ∧ a.1≤a.2) → a.2<Zlength s → (∃ b, IntervalMove s a b) →
      ∃ b, IntervalMove s a b ∧ ¬∃ c, IntervalMove s b c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a he ha han hm
      rcases hm with ⟨b,hab⟩
      by_cases hb : ∃ c, IntervalMove s b c
      · have hbn := interval_valid_capacity_nonneg__prefix_transitions s b hab.2.2.1 hab.2.2.2.1
        have han' := interval_valid_capacity_nonneg__prefix_transitions s a ha han
        have hlt := IntervalMove_capacity_lt__prefix_transitions s a b hab
        rcases ih (b.1+(Zlength s-1-b.2)).toNat (by omega) b rfl hab.2.2.1 hab.2.2.2.1 hb with ⟨d,hbd,hd⟩
        exact ⟨d,IntervalMove_trans__prefix_transitions s a b d hab hbd,hd⟩
      · exact ⟨b,hab,hb⟩
  exact h _ a rfl ha han hm

theorem terminal_move__prefix_transitions (s : List Int) (a : Int×Int)
    (hm : ∃ b, IntervalMove s a b) : ∃ b, IntervalMove s a b ∧ ¬∃ c, IntervalMove s b c := by
  classical
  rcases hm with ⟨b,hab⟩
  by_cases hb : ∃ c, IntervalMove s b c
  · rcases terminal_move_from_valid__prefix_transitions s b hab.2.2.1 hab.2.2.2.1 hb with ⟨d,hbd,hd⟩
    exact ⟨d,IntervalMove_trans__prefix_transitions s a b d hab hbd,hd⟩
  · exact ⟨b,hab,hb⟩

theorem AnnWins_iff_move_from_singleton__prefix_transitions (s : List Int) (k : Int) :
    AnnWins s k ↔ ∃ b, IntervalMove s (k,k) b := by
  classical
  constructor
  · rintro ⟨f,hl,hw⟩
    by_contra hn
    have hp : IntervalPlay s k [(k,k)] := by
      refine ⟨by simp,rfl,?_,hn⟩
      intro i hi
      change 0≤i ∧ i<1-1 at hi
      omega
    have hf : AnnFollows f [(k,k)] := by
      intro i hi he
      change 0≤i ∧ i<1-1 at hi
      omega
    have he := hw [(k,k)] hp hf
    change false=true at he
    contradiction
  · intro hini
    have hc : ∀ a : Int×Int, ∃ b : Int×Int, (∃ q, IntervalMove s a q) →
        IntervalMove s a b ∧ ¬∃ c, IntervalMove s b c := by
      intro a
      by_cases ha : ∃ q, IntervalMove s a q
      · rcases terminal_move__prefix_transitions s a ha with ⟨b,hb⟩
        exact ⟨b,fun _ => hb⟩
      · exact ⟨(0,0),fun hq => False.elim (ha hq)⟩
    let F := fun a => Classical.choose (hc a)
    have hF : ∀ a, (∃ q, IntervalMove s a q) → IntervalMove s a (F a) ∧ ¬∃ c, IntervalMove s (F a) c :=
      fun a => Classical.choose_spec (hc a)
    refine ⟨fun hist => F (Znth (Zlength hist-1) hist (0,0)),?_,?_⟩
    · intro hist hne hm
      exact (hF _ hm).1
    · intro p hp hf
      rcases hp with ⟨hne,hstart,hsteps,hlast⟩
      have hlen : 0<Zlength p := by
        cases p with
        | nil => contradiction
        | cons x xs => rw [Zlength_cons];have hh:=Zlength_nonneg xs;omega
      by_cases hlong : 1<Zlength p
      · have hm := hsteps 0 (by omega)
        have hh := hf 0 (by omega) (by decide)
        change Znth 1 p (0,0)=F (Znth (Zlength (sublist 0 1 p)-1) (sublist 0 1 p) (0,0)) at hh
        rw [segment_length 0 1 p ⟨by omega,by omega⟩ (by omega)] at hh
        change Znth 1 p (0,0)=F (Znth 0 (sublist 0 1 p) (0,0)) at hh
        rw [Znth_sublist (0,0) 0 0 1 p (by omega) (by omega)] at hh
        have hterm := (hF _ ⟨Znth 1 p (0,0),hm⟩).2
        rw [←hh] at hterm
        have hle : Zlength p≤2 := by
          by_contra hn
          exact hterm ⟨Znth 2 p (0,0),hsteps 1 (by omega)⟩
        rw [show Zlength p=2 by omega]
        decide
      · have he : Zlength p=1 := by omega
        rw [he] at hlast
        change ¬∃ q, IntervalMove s (Znth 0 p (0,0)) q at hlast
        rw [hstart] at hlast
        exact False.elim (hlast hini)

theorem ann_wins_iff_prefix_min_lt__prefix_transitions (s : List Int) (k mn : Int)
    (hk : 0≤k ∧ k<Zlength s) (hc : Znth k s 0≤122) (hm : PrefixMinimum s k mn) :
    AnnWins s k ↔ mn<Znth k s 0 := by
  rw [AnnWins_iff_move_from_singleton__prefix_transitions,move_from_singleton_iff_earlier_smaller__prefix_transitions s k hk]
  rcases hm with ⟨hb,⟨hk0,hmn⟩|⟨hkpos,⟨j,hj,hmn⟩,hall⟩⟩
  · subst k mn
    constructor
    · rintro ⟨j,hj,ht⟩;omega
    · intro ht;omega
  · constructor
    · rintro ⟨j',hj',ht⟩
      have hh:=hall j' hj'
      omega
    · intro ht
      exact ⟨j,hj,by omega⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_lib
