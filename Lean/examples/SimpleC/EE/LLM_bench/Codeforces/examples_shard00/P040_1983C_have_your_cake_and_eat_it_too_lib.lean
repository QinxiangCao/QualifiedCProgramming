import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length
import Mathlib.Data.List.GetD

set_option linter.unusedVariables false
set_option maxRecDepth 600
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib
open AUXLib


def CakeSumboolIf {P Q : Prop} {T : Type} (c : PSum P Q) (x y : T) : T :=
  match c with | .inl _ => x | .inr _ => y
abbrev Some {A : Type} (x : A) : Option A := .some x
abbrev None {A : Type} : Option A := .none

def DisjointIntervals (l1 r1 l2 r2 : Int) : Prop := r1 < l2 ∨ r2 < l1

def ValidCakeDivision (a b c bounds : List Int) : Prop :=
  ∃ la ra lb rb lc rc total, bounds = [la,ra,lb,rb,lc,rc] ∧ total = a.foldr (· + ·) 0 ∧
    (0 ≤ la ∧ la ≤ ra) ∧ ra < Zlength a ∧ (0 ≤ lb ∧ lb ≤ rb) ∧ rb < Zlength b ∧
    (0 ≤ lc ∧ lc ≤ rc) ∧ rc < Zlength c ∧
    DisjointIntervals la ra lb rb ∧ DisjointIntervals la ra lc rc ∧ DisjointIntervals lb rb lc rc ∧
    3 * (sublist la (ra+1) a).foldr (· + ·) 0 ≥ total ∧
    3 * (sublist lb (rb+1) b).foldr (· + ·) 0 ≥ total ∧
    3 * (sublist lc (rc+1) c).foldr (· + ·) 0 ≥ total

def Pre (a b c : List Int) : Prop :=
  (3 ≤ Zlength a ∧ Zlength a ≤ 200000) ∧ Zlength b = Zlength a ∧ Zlength c = Zlength a ∧
    Forall (fun x => 1 ≤ x ∧ x ≤ 1000000) a ∧ Forall (fun x => 1 ≤ x ∧ x ≤ 1000000) b ∧
    Forall (fun x => 1 ≤ x ∧ x ≤ 1000000) c ∧ a.foldr (· + ·) 0 = b.foldr (· + ·) 0 ∧ a.foldr (· + ·) 0 = c.foldr (· + ·) 0

def Spec (a b c : List Int) (out : Option (List Int)) : Prop :=
  (∃ bounds, out = some bounds ∧ ValidCakeDivision a b c bounds) ∨ (out = none ∧ ∀ bounds, ¬ ValidCakeDivision a b c bounds)

def CakeSum (l : List Int) : Int := l.foldr (· + ·) 0
def CakeOrder (ord : List Int) : Prop :=
  ord = [0,1,2] ∨ ord = [0,2,1] ∨ ord = [1,0,2] ∨ ord = [1,2,0] ∨ ord = [2,0,1] ∨ ord = [2,1,0]
def BoundLeft (bounds : List Int) (who : Int) : Int := Znth (2*who) bounds 0
def BoundRight (bounds : List Int) (who : Int) : Int := Znth (2*who+1) bounds 0

def OrderedBy (ord bounds : List Int) : Prop :=
  CakeOrder ord ∧ BoundRight bounds (Znth 0 ord 0) < BoundLeft bounds (Znth 1 ord 0) ∧
    BoundRight bounds (Znth 1 ord 0) < BoundLeft bounds (Znth 2 ord 0)

def TryOrderSpec (a b c ord : List Int) (out : Option (List Int)) : Prop :=
  match out with
  | some bounds => ValidCakeDivision a b c bounds ∧ OrderedBy ord bounds
  | none => ∀ bounds, ValidCakeDivision a b c bounds → ¬ OrderedBy ord bounds

def SearchState (rows : List (List Int)) (who start pos need acc : Int) : Prop :=
  let row := Znth who rows []
  0 ≤ start ∧ start ≤ pos ∧ pos ≤ Zlength row ∧ acc = CakeSum (sublist start pos row) ∧
    (∀ q, (start ≤ q ∧ q < pos) → CakeSum (sublist start (q+1) row) < need)

def SuffixSumState (rows : List (List Int)) (who start pos acc : Int) : Prop :=
  let row := Znth who rows []
  0 ≤ start ∧ start ≤ pos ∧ pos ≤ Zlength row ∧ acc = CakeSum (sublist start pos row)

def GreedyPrefixState (rows : List (List Int)) (ord : List Int) (need part pos : Int) (left right : List Int) : Prop :=
  CakeOrder ord ∧ Zlength left = 3 ∧ Zlength right = 3 ∧ (0 ≤ part ∧ part ≤ 2) ∧ (0 ≤ pos ∧ pos ≤ Zlength (Znth 0 rows [])) ∧
    (∀ k, (0 ≤ k ∧ k < part) →
      let who := Znth k ord 0
      let lo := Znth who left 0
      let hi := Znth who right 0
      (0 ≤ who ∧ who < 3) ∧ 0 ≤ lo ∧ lo ≤ hi ∧ hi < Zlength (Znth who rows []) ∧
        lo = (if k = 0 then 0 else Znth (Znth (k-1) ord 0) right 0 + 1) ∧
        need ≤ CakeSum (sublist lo (hi+1) (Znth who rows [])) ∧
        (∀ q, (lo ≤ q ∧ q < hi) → CakeSum (sublist lo (q+1) (Znth who rows [])) < need)) ∧
    pos = (if part = 0 then 0 else Znth (Znth (part-1) ord 0) right 0 + 1)

def OutputBounds (left right : List Int) : List Int :=
  [Znth 0 left 0 - 1, Znth 0 right 0 - 1, Znth 1 left 0 - 1, Znth 1 right 0 - 1, Znth 2 left 0 - 1, Znth 2 right 0 - 1]

def OrderAt (z : Int) (ord : List Int) : Prop :=
  (z = 0 ∧ ord = [0,1,2]) ∨ (z = 1 ∧ ord = [0,2,1]) ∨ (z = 2 ∧ ord = [1,0,2]) ∨
  (z = 3 ∧ ord = [1,2,0]) ∨ (z = 4 ∧ ord = [2,0,1]) ∨ (z = 5 ∧ ord = [2,1,0])

def OrderTable (table : List Int) : Prop := table = [0,1,2,0,2,1,1,0,2,1,2,0,2,0,1,2,1,0]

def OrderFor (z : Int) : List Int :=
  if z = 0 then [0,1,2] else if z = 1 then [0,2,1] else if z = 2 then [1,0,2] else
  if z = 3 then [1,2,0] else if z = 4 then [2,0,1] else [2,1,0]

def FailedOrders (a b c : List Int) (z : Int) : Prop :=
  ∀ k, (0 ≤ k ∧ k < z) → ∃ ord, OrderAt k ord ∧ TryOrderSpec a b c ord none

def SearchPrefixState (rows : List (List Int)) (who start pos need acc : Int) : Prop :=
  let row := Znth who rows []
  0 ≤ start ∧ start ≤ pos ∧ pos ≤ Zlength row ∧ acc = CakeSum (sublist start pos row) ∧
    (∀ q, (start ≤ q ∧ q < pos) → CakeSum (sublist start q row) < need)

def GreedyRawState (rows : List (List Int)) (ord : List Int) (need part pos : Int) (left right : List Int) : Prop :=
  CakeOrder ord ∧ Zlength left = 3 ∧ Zlength right = 3 ∧ (0 ≤ part ∧ part ≤ 2) ∧ (0 ≤ pos ∧ pos ≤ Zlength (Znth 0 rows [])) ∧
    (∀ k, (0 ≤ k ∧ k < part) →
      let who := Znth k ord 0
      let lo := Znth who left 0
      let hi := Znth who right 0
      (0 ≤ who ∧ who < 3) ∧ 1 ≤ lo ∧ lo ≤ hi ∧ hi ≤ Zlength (Znth who rows []) ∧
        lo = (if k = 0 then 1 else Znth (Znth (k-1) ord 0) right 0 + 1) ∧
        need ≤ CakeSum (sublist (lo-1) hi (Znth who rows [])) ∧
        (∀ q, (lo-1 ≤ q ∧ q < hi) → CakeSum (sublist (lo-1) q (Znth who rows [])) < need)) ∧
    pos = (if part = 0 then 0 else Znth (Znth (part-1) ord 0) right 0)

private theorem sum_cons (h : Int) (t : List Int) : CakeSum (h::t)=h+CakeSum t := rfl
private theorem sum_append (a b : List Int) : CakeSum (a++b)=CakeSum a+CakeSum b := by
  induction a with
  | nil => change CakeSum b=0+CakeSum b; omega
  | cons h t ih => simp only [List.cons_append,sum_cons,ih]; omega
private theorem length_sublist (lo hi : Int) (a : List Int) (hl : 0≤lo ∧ lo≤hi) (hh : hi≤Zlength a) :
    Zlength (sublist lo hi a)=hi-lo := ListLib.Zlength_sublist lo hi a hl hh

theorem Forall_Znth__solver_order_iteration {A : Type} (P : A→Prop) (d : A) (l : List A) :
    Forall P l ↔ ∀ i,(0≤i ∧ i<Zlength l) → P (Znth i l d) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h i hi
    apply h
    have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
    simpa only [Znth,List.getD_eq_getElem l d hn] using List.getElem_mem hn
  · intro h x hx
    rcases List.getElem_of_mem hx with ⟨i,hi,he⟩
    have hh := h (i:Int) ⟨by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega⟩
    simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem l d hi,he] using hh

theorem cake_sum_bounds_from_forall__try_initialization (xs : List Int)
    (h : Forall (fun x=>1≤x ∧ x≤1000000) xs) : Zlength xs≤CakeSum xs ∧ CakeSum xs≤Zlength xs*1000000 := by
  induction h with
  | nil => exact ⟨le_refl _,le_refl _⟩
  | @cons x xs hx hxs ih => rw [Zlength_cons,sum_cons]; constructor <;> omega

theorem sum_nonnegative_pointwise__try_terminal_semantics (xs : List Int)
    (h : ∀ k,(0≤k ∧ k<Zlength xs) → 0≤Znth k xs 0) : 0≤CakeSum xs := by
  have hh := (Forall_Znth__solver_order_iteration (fun x=>0≤x) 0 xs).mpr h
  clear h
  induction hh with
  | nil => exact le_refl _
  | @cons x xs hx hxs ih => rw [sum_cons]; omega

theorem sum_sublist_nonnegative__try_terminal_semantics (xs : List Int) (lo hi : Int)
    (h : ∀ k,(0≤k ∧ k<Zlength xs) → 0≤Znth k xs 0) (hl : 0≤lo ∧ lo≤hi) (hh : hi≤Zlength xs) :
    0≤CakeSum (sublist lo hi xs) := by
  apply sum_nonnegative_pointwise__try_terminal_semantics
  intro k hk
  rw [length_sublist lo hi xs hl hh] at hk
  rw [Znth_sublist 0 lo k hi xs hl.1 hk]
  exact h (k+lo) ⟨by omega,by omega⟩

theorem sum_sublist_inclusion__try_terminal_semantics (xs : List Int) (outer_lo inner_lo inner_hi outer_hi : Int)
    (h : ∀ k,(0≤k ∧ k<Zlength xs) → 0≤Znth k xs 0)
    (hl : 0≤outer_lo ∧ outer_lo≤inner_lo) (hr : inner_lo≤inner_hi ∧ inner_hi≤outer_hi) (hb : outer_hi≤Zlength xs) :
    CakeSum (sublist inner_lo inner_hi xs)≤CakeSum (sublist outer_lo outer_hi xs) := by
  rw [sublist_split outer_lo outer_hi inner_lo xs hl ⟨by omega,hb⟩,
    sublist_split inner_lo outer_hi inner_hi xs ⟨by omega,hr.1⟩ ⟨hr.2,hb⟩,sum_append,sum_append]
  have h₁ := sum_sublist_nonnegative__try_terminal_semantics xs outer_lo inner_lo h hl (by omega)
  have h₂ := sum_sublist_nonnegative__try_terminal_semantics xs inner_hi outer_hi h ⟨by omega,hr.2⟩ hb
  omega

theorem ceil_third_threshold__try_terminal_semantics (total need s : Int) (ht : 0≤total)
    (hn : need=Z.div (total+2) 3) : need≤s ↔ total≤3*s := by
  have hd : Z.div (total+2) 3=(total+2)/3 := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  rw [hd] at hn
  omega

theorem sublist_full__try_terminal_semantics (A : Type) (xs : List A) : sublist 0 (Zlength xs) xs=xs := sublist_self xs _ rfl

theorem greedy_terminal_exclusion_chain__try_terminal_semantics (x y z : List Int)
    (need n g1 g2 acc l1 u1 l2 u2 l3 u3 : Int)
    (hx : Zlength x=n) (hy : Zlength y=n) (hz : Zlength z=n)
    (hxn : ∀ k,(0≤k ∧ k<n) → 0≤Znth k x 0) (hyn : ∀ k,(0≤k ∧ k<n) → 0≤Znth k y 0)
    (hzn : ∀ k,(0≤k ∧ k<n) → 0≤Znth k z 0) (hg : 0≤g1 ∧ g1≤g2) (hgn : g2≤n)
    (hm1 : ∀ q,(0≤q ∧ q<g1) → CakeSum (sublist 0 q x)<need)
    (hm2 : ∀ q,(g1≤q ∧ q<g2) → CakeSum (sublist g1 q y)<need)
    (ha : acc=CakeSum (sublist g2 n z)) (han : acc<need)
    (hl1 : 0≤l1 ∧ l1≤u1) (hu1 : u1<n) (hl2 : 0≤l2 ∧ l2≤u2) (hu2 : u2<n)
    (hl3 : 0≤l3 ∧ l3≤u3) (hu3 : u3<n) (ho12 : u1<l2) (ho23 : u2<l3)
    (hv1 : need≤CakeSum (sublist l1 (u1+1) x)) (hv2 : need≤CakeSum (sublist l2 (u2+1) y))
    (hv3 : need≤CakeSum (sublist l3 (u3+1) z)) : False := by
  have hg1 : g1≤u1+1 := by
    by_contra hn
    have hm := hm1 (u1+1) ⟨by omega,by omega⟩
    have hi := sum_sublist_inclusion__try_terminal_semantics x 0 l1 (u1+1) (u1+1)
      (fun k hk=>hxn k (by omega)) ⟨by omega,hl1.1⟩ ⟨by omega,le_refl _⟩ (by omega)
    omega
  have hg2 : g2≤u2+1 := by
    by_contra hn
    have hm := hm2 (u2+1) ⟨by omega,by omega⟩
    have hi := sum_sublist_inclusion__try_terminal_semantics y g1 l2 (u2+1) (u2+1)
      (fun k hk=>hyn k (by omega)) ⟨hg.1,by omega⟩ ⟨by omega,le_refl _⟩ (by omega)
    omega
  have hi := sum_sublist_inclusion__try_terminal_semantics z g2 l3 (u3+1) n
    (fun k hk=>hzn k (by omega)) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega)
  omega

theorem suffix_sum_empty__try_terminal_semantics (rows : List (List Int)) (who pos : Int)
    (hp : 0≤pos) (hl : pos≤Zlength (Znth who rows [])) : SuffixSumState rows who pos pos 0 := by
  refine ⟨hp,le_refl _,hl,?_⟩
  rw [Zsublist_nil _ pos pos (le_refl _)]
  rfl

theorem selected_row_length__try_terminal_semantics (a b c ord : List Int) (who : Int)
    (ho : CakeOrder ord) (hw : who=Znth 2 ord 0) (hb : Zlength b=Zlength a) (hc : Zlength c=Zlength a) :
    Zlength (Znth who [a,b,c] [])=Zlength a := by
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> subst who <;> first | exact hb | exact hc | rfl

private theorem sum_snoc (row : List Int) (start i : Int) (hs : 0≤start ∧ start≤i) (hi : i<Zlength row) :
    CakeSum (sublist start (i+1) row)=CakeSum (sublist start i row)+Znth i row 0 := by
  rw [sublist_split start (i+1) i row hs ⟨by omega,by omega⟩,sublist_single 0 i row ⟨by omega,hi⟩,sum_append]
  change _+(Znth i row 0+0)=_
  omega

theorem suffix_sum_extend__try_terminal_semantics (rows : List (List Int)) (who start i acc : Int)
    (hs : SuffixSumState rows who start i acc) (hi : i<Zlength (Znth who rows [])) :
    SuffixSumState rows who start (i+1) (acc+Znth i (Znth who rows []) 0) := by
  refine ⟨hs.1,by have h:=hs.2.1; omega,by omega,?_⟩
  rw [sum_snoc _ start i ⟨hs.1,hs.2.1⟩ hi,hs.2.2.2]

theorem sum_upper_pointwise__try_terminal_semantics (xs : List Int) (b : Int)
    (h : ∀ k,(0≤k ∧ k<Zlength xs) → Znth k xs 0≤b) : CakeSum xs≤Zlength xs*b := by
  have hh := (Forall_Znth__solver_order_iteration (fun x=>x≤b) 0 xs).mpr h
  clear h
  induction hh with
  | nil => change 0≤0*b; omega
  | @cons x xs hx hxs ih => rw [sum_cons,Zlength_cons]; nlinarith

theorem suffix_sum_upper__try_terminal_semantics (rows : List (List Int)) (who start i acc : Int)
    (hs : SuffixSumState rows who start i acc) :
    let row := Znth who rows []
    i<Zlength row → (∀ k,(0≤k ∧ k<Zlength row) → 0≤Znth k row 0 ∧ Znth k row 0≤1000000) →
    Zlength row≤200000 → acc+Znth i row 0≤200000000000 := by
  intro row hi hv hl
  have hinc := sum_sublist_inclusion__try_terminal_semantics row 0 start (i+1) (Zlength row)
    (fun k hk=>(hv k hk).1) ⟨by omega,hs.1⟩ ⟨by have h:=hs.2.1; omega,by omega⟩ (le_refl _)
  rw [sublist_full__try_terminal_semantics,sum_snoc row start i ⟨hs.1,hs.2.1⟩ hi,← hs.2.2.2] at hinc
  have hu := sum_upper_pointwise__try_terminal_semantics row 1000000 (fun k hk=>(hv k hk).2)
  omega

theorem Znth_app_left__try_output_materialization (l1 l2 : List Int) (d i : Int) (hi : 0≤i ∧ i<Zlength l1) :
    Znth i (l1++l2) d=Znth i l1 d := ListLib.app_Znth1 d l1 l2 i hi

theorem Znth_app_last__try_output_materialization (l : List Int) (d x : Int) : Znth (Zlength l) (l++[x]) d=x := by
  have hh : Znth (Zlength l) (l++[x]) d=Znth (Zlength l-Zlength l) [x] d := ListLib.app_Znth2 d l [x] (Zlength l) (le_refl _)
  simpa only [Int.sub_self] using hh

theorem bounded_values_sum_lower__solver_order_setup (xs : List Int) (h : Forall (fun x=>1≤x ∧ x≤1000000) xs) :
    Zlength xs≤CakeSum xs := (cake_sum_bounds_from_forall__try_initialization xs h).1

theorem order_table_decomposition__solver_order_setup (table : List Int) (z : Int) (ht : OrderTable table) (hz : 0≤z ∧ z<6) :
    table=sublist 0 (3*z) table++OrderFor z++sublist (3*(z+1)) 18 table ∧
    Zlength (sublist 0 (3*z) table)=3*z ∧ Zlength (OrderFor z)=3 ∧ Zlength (sublist (3*(z+1)) 18 table)=18-3*(z+1) ∧
    OrderAt z (OrderFor z) ∧ CakeOrder (OrderFor z) ∧ sublist (3*z) (3*(z+1)) table=OrderFor z ∧
    sublist 0 (3*(z+1)-3*z) (sublist (3*z) 18 table)=OrderFor z ∧
    sublist (3*(z+1)-3*z) (18-3*z) (sublist (3*z) 18 table)=sublist (3*(z+1)) 18 table := by
  rcases show z=0 ∨ z=1 ∨ z=2 ∨ z=3 ∨ z=4 ∨ z=5 by omega with rfl|rfl|rfl|rfl|rfl|rfl <;> subst table <;> unfold OrderAt CakeOrder <;> decide

theorem failed_six_orders_spec_none__solver_final_results (a b c : List Int) (hf : FailedOrders a b c 6) : Spec a b c none := by
  refine Or.inr ⟨rfl,?_⟩
  intro bounds hv
  have hvcopy := hv
  obtain ⟨la,ra,lb,rb,lc,rc,total,hbeq,ht,ha,hra,hb,hrb,hc,hrc,hab,hac,hbc,hsa,hsb,hsc⟩ := hv
  subst bounds
  have hn : ∀k,(0≤k ∧ k<6) → ¬OrderedBy (OrderFor k) [la,ra,lb,rb,lc,rc] := by
    intro k hk
    rcases hf k hk with ⟨ord,ho,hn⟩
    have he : ord=OrderFor k := by
      rcases ho with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl
    rw [← he]
    exact hn _ hvcopy
  have h0 : ¬(ra<lb ∧ rb<lc) := by
    intro ho
    apply hn 0 ⟨by omega,by omega⟩
    exact ⟨by unfold CakeOrder OrderFor; simp,ho⟩
  have h1 : ¬(ra<lc ∧ rc<lb) := by
    intro ho
    apply hn 1 ⟨by omega,by omega⟩
    exact ⟨by unfold CakeOrder OrderFor; simp,ho⟩
  have h2 : ¬(rb<la ∧ ra<lc) := by
    intro ho
    apply hn 2 ⟨by omega,by omega⟩
    exact ⟨by unfold CakeOrder OrderFor; simp,ho⟩
  have h3 : ¬(rb<lc ∧ rc<la) := by
    intro ho
    apply hn 3 ⟨by omega,by omega⟩
    exact ⟨by unfold CakeOrder OrderFor; simp,ho⟩
  have h4 : ¬(rc<la ∧ ra<lb) := by
    intro ho
    apply hn 4 ⟨by omega,by omega⟩
    exact ⟨by unfold CakeOrder OrderFor; simp,ho⟩
  have h5 : ¬(rc<lb ∧ rb<la) := by
    intro ho
    apply hn 5 ⟨by omega,by omega⟩
    exact ⟨by unfold CakeOrder OrderFor; simp,ho⟩
  unfold DisjointIntervals at hab hac hbc
  rcases hab with h|h <;> rcases hac with h'|h' <;> rcases hbc with h''|h'' <;> omega

private theorem triple0 {A : Type} (a b c d : A) : Znth 0 [a,b,c] d=a := rfl
private theorem triple1 {A : Type} (a b c d : A) : Znth 1 [a,b,c] d=b := rfl
private theorem triple2 {A : Type} (a b c d : A) : Znth 2 [a,b,c] d=c := rfl
private theorem nth_update (l : List Int) (i v j : Int) (hi : 0≤i ∧ i<Zlength l) (hj : 0≤j ∧ j<Zlength l) :
    Znth j (replace_Znth i v l) 0=if j=i then v else Znth j l 0 := by
  by_cases he:j=i
  · subst j; rw [if_pos rfl,Znth_replace_Znth_Same 0 l i v hi]
  · rw [if_neg he,Znth_replace_Znth_Diff 0 l i j v hi hj (Ne.symm he)]

theorem greedy_terminal_success__try_terminal_semantics (a b c ord : List Int) (need n pos who acc : Int) (left right : List Int)
    (hp : Pre a b c)
    (hv : ∀ row col,((0≤row ∧ row<3) ∧ 0≤col) ∧ col<Zlength a → 1≤Znth col (Znth row [a,b,c] []) 0 ∧ Znth col (Znth row [a,b,c] []) 0≤1000000)
    (hn : n=Zlength a) (hneed : need=Z.div (CakeSum a+2) 3) (ho : CakeOrder ord) (hw : who=Znth 2 ord 0)
    (hg : GreedyRawState [a,b,c] ord need 2 pos left right) (hsuf : SuffixSumState [a,b,c] who pos n acc) (hacc : need≤acc) :
    TryOrderSpec a b c ord (some (OutputBounds (replace_Znth who (pos+1) left) (replace_Znth who n right))) := by
  have htot := cake_sum_bounds_from_forall__try_initialization a hp.2.2.2.1
  have ht : 0≤CakeSum a := by have h:=hp.1.1; omega
  have hpneed : 0<need := by
    have hh := ceil_third_threshold__try_terminal_semantics (CakeSum a) need 0 ht hneed
    have h:=hp.1.1
    omega
  obtain ⟨hlen,hblen,hclen,hfa,hfb,hfc,hab,hac⟩ := hp
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
  · change who=2 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength c ∧ acc=CakeSum (sublist pos n c) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    have hposlt : pos<n := by
      by_contra hnot
      have he : pos=n := by omega
      rw [he,Zsublist_nil _ n n (le_refl _)] at hasum
      change acc=0 at hasum
      omega
    have hfv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hfs
    have hsv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hss
    have htv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need acc ht hneed).mp hacc
    rw [hasum] at htv
    have hout : OutputBounds (replace_Znth 2 (pos+1) left) (replace_Znth 2 n right)=
      [Znth 0 left 0-1,Znth 0 right 0-1,Znth 1 left 0-1,Znth 1 right 0-1,pos,n-1] := by
      unfold OutputBounds
      rw [nth_update left 2 (pos+1) 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 2 n 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 2 (pos+1) 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 2 n 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 2 (pos+1) 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 2 n 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      simp only [show (0:Int)≠2 by decide, show (1:Int)≠2 by decide, ite_false, ite_true, Int.add_sub_cancel]
    change ValidCakeDivision a b c _ ∧ OrderedBy _ _
    rw [hout]
    constructor
    · refine ⟨_,_,_,_,_,_,_,rfl,rfl,?_⟩
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a
      simp only [Int.sub_add_cancel]
      unfold DisjointIntervals
      repeat' apply And.intro
      all_goals first | omega | (first | left; omega | right; omega)
    · unfold OrderedBy
      refine ⟨by unfold CakeOrder; simp,?_,?_⟩
      · change Znth 0 right 0-1 < Znth 1 left 0-1
        omega
      · change Znth 1 right 0-1 < pos
        omega
  · change who=1 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength b ∧ acc=CakeSum (sublist pos n b) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    have hposlt : pos<n := by
      by_contra hnot
      have he : pos=n := by omega
      rw [he,Zsublist_nil _ n n (le_refl _)] at hasum
      change acc=0 at hasum
      omega
    have hfv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hfs
    have hsv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hss
    have htv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need acc ht hneed).mp hacc
    rw [hasum] at htv
    have hout : OutputBounds (replace_Znth 1 (pos+1) left) (replace_Znth 1 n right)=
      [Znth 0 left 0-1,Znth 0 right 0-1,pos,n-1,Znth 2 left 0-1,Znth 2 right 0-1] := by
      unfold OutputBounds
      rw [nth_update left 1 (pos+1) 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 1 n 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 1 (pos+1) 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 1 n 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 1 (pos+1) 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 1 n 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      simp only [show (0:Int)≠1 by decide, show (2:Int)≠1 by decide, ite_false, ite_true, Int.add_sub_cancel]
    change ValidCakeDivision a b c _ ∧ OrderedBy _ _
    rw [hout]
    constructor
    · refine ⟨_,_,_,_,_,_,_,rfl,rfl,?_⟩
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a
      simp only [Int.sub_add_cancel]
      unfold DisjointIntervals
      repeat' apply And.intro
      all_goals first | omega | (first | left; omega | right; omega)
    · unfold OrderedBy
      refine ⟨by unfold CakeOrder; simp,?_,?_⟩
      · change Znth 0 right 0-1 < Znth 2 left 0-1
        omega
      · change Znth 2 right 0-1 < pos
        omega
  · change who=2 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength c ∧ acc=CakeSum (sublist pos n c) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    have hposlt : pos<n := by
      by_contra hnot
      have he : pos=n := by omega
      rw [he,Zsublist_nil _ n n (le_refl _)] at hasum
      change acc=0 at hasum
      omega
    have hfv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hfs
    have hsv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hss
    have htv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need acc ht hneed).mp hacc
    rw [hasum] at htv
    have hout : OutputBounds (replace_Znth 2 (pos+1) left) (replace_Znth 2 n right)=
      [Znth 0 left 0-1,Znth 0 right 0-1,Znth 1 left 0-1,Znth 1 right 0-1,pos,n-1] := by
      unfold OutputBounds
      rw [nth_update left 2 (pos+1) 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 2 n 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 2 (pos+1) 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 2 n 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 2 (pos+1) 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 2 n 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      simp only [show (0:Int)≠2 by decide, show (1:Int)≠2 by decide, ite_false, ite_true, Int.add_sub_cancel]
    change ValidCakeDivision a b c _ ∧ OrderedBy _ _
    rw [hout]
    constructor
    · refine ⟨_,_,_,_,_,_,_,rfl,rfl,?_⟩
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a
      simp only [Int.sub_add_cancel]
      unfold DisjointIntervals
      repeat' apply And.intro
      all_goals first | omega | (first | left; omega | right; omega)
    · unfold OrderedBy
      refine ⟨by unfold CakeOrder; simp,?_,?_⟩
      · change Znth 1 right 0-1 < Znth 0 left 0-1
        omega
      · change Znth 0 right 0-1 < pos
        omega
  · change who=0 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength a ∧ acc=CakeSum (sublist pos n a) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    have hposlt : pos<n := by
      by_contra hnot
      have he : pos=n := by omega
      rw [he,Zsublist_nil _ n n (le_refl _)] at hasum
      change acc=0 at hasum
      omega
    have hfv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hfs
    have hsv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hss
    have htv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need acc ht hneed).mp hacc
    rw [hasum] at htv
    have hout : OutputBounds (replace_Znth 0 (pos+1) left) (replace_Znth 0 n right)=
      [pos,n-1,Znth 1 left 0-1,Znth 1 right 0-1,Znth 2 left 0-1,Znth 2 right 0-1] := by
      unfold OutputBounds
      rw [nth_update left 0 (pos+1) 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 0 n 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 0 (pos+1) 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 0 n 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 0 (pos+1) 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 0 n 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      simp only [show (1:Int)≠0 by decide, show (2:Int)≠0 by decide, ite_false, ite_true, Int.add_sub_cancel]
    change ValidCakeDivision a b c _ ∧ OrderedBy _ _
    rw [hout]
    constructor
    · refine ⟨_,_,_,_,_,_,_,rfl,rfl,?_⟩
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a
      simp only [Int.sub_add_cancel]
      unfold DisjointIntervals
      repeat' apply And.intro
      all_goals first | omega | (first | left; omega | right; omega)
    · unfold OrderedBy
      refine ⟨by unfold CakeOrder; simp,?_,?_⟩
      · change Znth 1 right 0-1 < Znth 2 left 0-1
        omega
      · change Znth 2 right 0-1 < pos
        omega
  · change who=1 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength b ∧ acc=CakeSum (sublist pos n b) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    have hposlt : pos<n := by
      by_contra hnot
      have he : pos=n := by omega
      rw [he,Zsublist_nil _ n n (le_refl _)] at hasum
      change acc=0 at hasum
      omega
    have hfv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hfs
    have hsv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hss
    have htv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need acc ht hneed).mp hacc
    rw [hasum] at htv
    have hout : OutputBounds (replace_Znth 1 (pos+1) left) (replace_Znth 1 n right)=
      [Znth 0 left 0-1,Znth 0 right 0-1,pos,n-1,Znth 2 left 0-1,Znth 2 right 0-1] := by
      unfold OutputBounds
      rw [nth_update left 1 (pos+1) 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 1 n 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 1 (pos+1) 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 1 n 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 1 (pos+1) 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 1 n 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      simp only [show (0:Int)≠1 by decide, show (2:Int)≠1 by decide, ite_false, ite_true, Int.add_sub_cancel]
    change ValidCakeDivision a b c _ ∧ OrderedBy _ _
    rw [hout]
    constructor
    · refine ⟨_,_,_,_,_,_,_,rfl,rfl,?_⟩
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a
      simp only [Int.sub_add_cancel]
      unfold DisjointIntervals
      repeat' apply And.intro
      all_goals first | omega | (first | left; omega | right; omega)
    · unfold OrderedBy
      refine ⟨by unfold CakeOrder; simp,?_,?_⟩
      · change Znth 2 right 0-1 < Znth 0 left 0-1
        omega
      · change Znth 0 right 0-1 < pos
        omega
  · change who=0 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength a ∧ acc=CakeSum (sublist pos n a) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    have hposlt : pos<n := by
      by_contra hnot
      have he : pos=n := by omega
      rw [he,Zsublist_nil _ n n (le_refl _)] at hasum
      change acc=0 at hasum
      omega
    have hfv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hfs
    have hsv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need _ ht hneed).mp hss
    have htv := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need acc ht hneed).mp hacc
    rw [hasum] at htv
    have hout : OutputBounds (replace_Znth 0 (pos+1) left) (replace_Znth 0 n right)=
      [pos,n-1,Znth 1 left 0-1,Znth 1 right 0-1,Znth 2 left 0-1,Znth 2 right 0-1] := by
      unfold OutputBounds
      rw [nth_update left 0 (pos+1) 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 0 n 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 0 (pos+1) 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 0 n 1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update left 0 (pos+1) 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      rw [nth_update right 0 n 2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
      simp only [show (1:Int)≠0 by decide, show (2:Int)≠0 by decide, ite_false, ite_true, Int.add_sub_cancel]
    change ValidCakeDivision a b c _ ∧ OrderedBy _ _
    rw [hout]
    constructor
    · refine ⟨_,_,_,_,_,_,_,rfl,rfl,?_⟩
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a ∧ 3*CakeSum _≥CakeSum a
      simp only [Int.sub_add_cancel]
      unfold DisjointIntervals
      repeat' apply And.intro
      all_goals first | omega | (first | left; omega | right; omega)
    · unfold OrderedBy
      refine ⟨by unfold CakeOrder; simp,?_,?_⟩
      · change Znth 2 right 0-1 < Znth 1 left 0-1
        omega
      · change Znth 1 right 0-1 < pos
        omega

theorem greedy_terminal_failure__try_terminal_semantics (a b c ord : List Int) (need n pos who acc : Int) (left right : List Int)
    (hp : Pre a b c)
    (hv : ∀ row col,((0≤row ∧ row<3) ∧ 0≤col) ∧ col<Zlength a → 1≤Znth col (Znth row [a,b,c] []) 0 ∧ Znth col (Znth row [a,b,c] []) 0≤1000000)
    (hn : n=Zlength a) (hneed : need=Z.div (CakeSum a+2) 3) (ho : CakeOrder ord) (hw : who=Znth 2 ord 0)
    (hg : GreedyRawState [a,b,c] ord need 2 pos left right) (hsuf : SuffixSumState [a,b,c] who pos n acc) (hacc : acc<need) : TryOrderSpec a b c ord none := by
  have htot := cake_sum_bounds_from_forall__try_initialization a hp.2.2.2.1
  have ht : 0≤CakeSum a := by have h:=hp.1.1; omega
  have hpneed : 0<need := by
    have hh := ceil_third_threshold__try_terminal_semantics (CakeSum a) need 0 ht hneed
    have h:=hp.1.1
    omega
  obtain ⟨hlen,hblen,hclen,hfa,hfb,hfc,hab,hac⟩ := hp
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl
  · change who=2 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength c ∧ acc=CakeSum (sublist pos n c) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    intro bounds hb hord
    rcases hb with ⟨la,ra,lb,rb,lc,rc,total,hbeq,htotal,hla,hra,hlb,hrb,hlc,hrc,hdab,hdac,hdbc,hva,hvb,hvc⟩
    subst bounds
    subst total
    have hva' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist la (ra+1) a)) ht hneed).mpr hva
    have hvb' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lb (rb+1) b)) ht hneed).mpr hvb
    have hvc' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lc (rc+1) c)) ht hneed).mpr hvc
    obtain ⟨_,ho12,ho23⟩ := hord
    change ra<lb at ho12
    change rb<lc at ho23
    have hna : ∀t,(0≤t ∧ t<n) → 0≤Znth t a 0 := by
      intro t htr
      have hh := hv 0 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t a 0 ∧ Znth t a 0≤1000000 at hh
      omega
    have hnb : ∀t,(0≤t ∧ t<n) → 0≤Znth t b 0 := by
      intro t htr
      have hh := hv 1 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t b 0 ∧ Znth t b 0≤1000000 at hh
      omega
    have hnc : ∀t,(0≤t ∧ t<n) → 0≤Znth t c 0 := by
      intro t htr
      have hh := hv 2 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t c 0 ∧ Znth t c 0≤1000000 at hh
      omega
    apply greedy_terminal_exclusion_chain__try_terminal_semantics a b c need n (Znth 0 right 0) pos acc la ra lb rb lc rc
    all_goals try first | assumption | omega
    · intro q hq
      have he : Znth 0 left 0-1=0 := by omega
      rw [he] at hfm
      exact hfm q ⟨by omega,hq.2⟩
    · intro q hq
      have he : Znth 1 left 0-1=Znth 0 right 0 := by omega
      rw [he] at hsm
      exact hsm q ⟨hq.1,by omega⟩
  · change who=1 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength b ∧ acc=CakeSum (sublist pos n b) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    intro bounds hb hord
    rcases hb with ⟨la,ra,lb,rb,lc,rc,total,hbeq,htotal,hla,hra,hlb,hrb,hlc,hrc,hdab,hdac,hdbc,hva,hvb,hvc⟩
    subst bounds
    subst total
    have hva' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist la (ra+1) a)) ht hneed).mpr hva
    have hvb' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lb (rb+1) b)) ht hneed).mpr hvb
    have hvc' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lc (rc+1) c)) ht hneed).mpr hvc
    obtain ⟨_,ho12,ho23⟩ := hord
    change ra<lc at ho12
    change rc<lb at ho23
    have hna : ∀t,(0≤t ∧ t<n) → 0≤Znth t a 0 := by
      intro t htr
      have hh := hv 0 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t a 0 ∧ Znth t a 0≤1000000 at hh
      omega
    have hnb : ∀t,(0≤t ∧ t<n) → 0≤Znth t b 0 := by
      intro t htr
      have hh := hv 1 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t b 0 ∧ Znth t b 0≤1000000 at hh
      omega
    have hnc : ∀t,(0≤t ∧ t<n) → 0≤Znth t c 0 := by
      intro t htr
      have hh := hv 2 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t c 0 ∧ Znth t c 0≤1000000 at hh
      omega
    apply greedy_terminal_exclusion_chain__try_terminal_semantics a c b need n (Znth 0 right 0) pos acc la ra lc rc lb rb
    all_goals try first | assumption | omega
    · intro q hq
      have he : Znth 0 left 0-1=0 := by omega
      rw [he] at hfm
      exact hfm q ⟨by omega,hq.2⟩
    · intro q hq
      have he : Znth 2 left 0-1=Znth 0 right 0 := by omega
      rw [he] at hsm
      exact hsm q ⟨hq.1,by omega⟩
  · change who=2 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength c ∧ acc=CakeSum (sublist pos n c) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    intro bounds hb hord
    rcases hb with ⟨la,ra,lb,rb,lc,rc,total,hbeq,htotal,hla,hra,hlb,hrb,hlc,hrc,hdab,hdac,hdbc,hva,hvb,hvc⟩
    subst bounds
    subst total
    have hva' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist la (ra+1) a)) ht hneed).mpr hva
    have hvb' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lb (rb+1) b)) ht hneed).mpr hvb
    have hvc' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lc (rc+1) c)) ht hneed).mpr hvc
    obtain ⟨_,ho12,ho23⟩ := hord
    change rb<la at ho12
    change ra<lc at ho23
    have hna : ∀t,(0≤t ∧ t<n) → 0≤Znth t a 0 := by
      intro t htr
      have hh := hv 0 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t a 0 ∧ Znth t a 0≤1000000 at hh
      omega
    have hnb : ∀t,(0≤t ∧ t<n) → 0≤Znth t b 0 := by
      intro t htr
      have hh := hv 1 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t b 0 ∧ Znth t b 0≤1000000 at hh
      omega
    have hnc : ∀t,(0≤t ∧ t<n) → 0≤Znth t c 0 := by
      intro t htr
      have hh := hv 2 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t c 0 ∧ Znth t c 0≤1000000 at hh
      omega
    apply greedy_terminal_exclusion_chain__try_terminal_semantics b a c need n (Znth 1 right 0) pos acc lb rb la ra lc rc
    all_goals try first | assumption | omega
    · intro q hq
      have he : Znth 1 left 0-1=0 := by omega
      rw [he] at hfm
      exact hfm q ⟨by omega,hq.2⟩
    · intro q hq
      have he : Znth 0 left 0-1=Znth 1 right 0 := by omega
      rw [he] at hsm
      exact hsm q ⟨hq.1,by omega⟩
  · change who=0 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength a ∧ acc=CakeSum (sublist pos n a) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    intro bounds hb hord
    rcases hb with ⟨la,ra,lb,rb,lc,rc,total,hbeq,htotal,hla,hra,hlb,hrb,hlc,hrc,hdab,hdac,hdbc,hva,hvb,hvc⟩
    subst bounds
    subst total
    have hva' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist la (ra+1) a)) ht hneed).mpr hva
    have hvb' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lb (rb+1) b)) ht hneed).mpr hvb
    have hvc' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lc (rc+1) c)) ht hneed).mpr hvc
    obtain ⟨_,ho12,ho23⟩ := hord
    change rb<lc at ho12
    change rc<la at ho23
    have hna : ∀t,(0≤t ∧ t<n) → 0≤Znth t a 0 := by
      intro t htr
      have hh := hv 0 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t a 0 ∧ Znth t a 0≤1000000 at hh
      omega
    have hnb : ∀t,(0≤t ∧ t<n) → 0≤Znth t b 0 := by
      intro t htr
      have hh := hv 1 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t b 0 ∧ Znth t b 0≤1000000 at hh
      omega
    have hnc : ∀t,(0≤t ∧ t<n) → 0≤Znth t c 0 := by
      intro t htr
      have hh := hv 2 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t c 0 ∧ Znth t c 0≤1000000 at hh
      omega
    apply greedy_terminal_exclusion_chain__try_terminal_semantics b c a need n (Znth 1 right 0) pos acc lb rb lc rc la ra
    all_goals try first | assumption | omega
    · intro q hq
      have he : Znth 1 left 0-1=0 := by omega
      rw [he] at hfm
      exact hfm q ⟨by omega,hq.2⟩
    · intro q hq
      have he : Znth 2 left 0-1=Znth 1 right 0 := by omega
      rw [he] at hsm
      exact hsm q ⟨hq.1,by omega⟩
  · change who=1 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength b ∧ acc=CakeSum (sublist pos n b) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    intro bounds hb hord
    rcases hb with ⟨la,ra,lb,rb,lc,rc,total,hbeq,htotal,hla,hra,hlb,hrb,hlc,hrc,hdab,hdac,hdbc,hva,hvb,hvc⟩
    subst bounds
    subst total
    have hva' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist la (ra+1) a)) ht hneed).mpr hva
    have hvb' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lb (rb+1) b)) ht hneed).mpr hvb
    have hvc' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lc (rc+1) c)) ht hneed).mpr hvc
    obtain ⟨_,ho12,ho23⟩ := hord
    change rc<la at ho12
    change ra<lb at ho23
    have hna : ∀t,(0≤t ∧ t<n) → 0≤Znth t a 0 := by
      intro t htr
      have hh := hv 0 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t a 0 ∧ Znth t a 0≤1000000 at hh
      omega
    have hnb : ∀t,(0≤t ∧ t<n) → 0≤Znth t b 0 := by
      intro t htr
      have hh := hv 1 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t b 0 ∧ Znth t b 0≤1000000 at hh
      omega
    have hnc : ∀t,(0≤t ∧ t<n) → 0≤Znth t c 0 := by
      intro t htr
      have hh := hv 2 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t c 0 ∧ Znth t c 0≤1000000 at hh
      omega
    apply greedy_terminal_exclusion_chain__try_terminal_semantics c a b need n (Znth 2 right 0) pos acc lc rc la ra lb rb
    all_goals try first | assumption | omega
    · intro q hq
      have he : Znth 2 left 0-1=0 := by omega
      rw [he] at hfm
      exact hfm q ⟨by omega,hq.2⟩
    · intro q hq
      have he : Znth 0 left 0-1=Znth 2 right 0 := by omega
      rw [he] at hsm
      exact hsm q ⟨hq.1,by omega⟩
  · change who=0 at hw
    subst who
    rcases hg with ⟨_,hll,hrl,_,hpos,hdone,hpeq⟩
    have hf := hdone 0 ⟨by omega,by omega⟩
    have hs := hdone 1 ⟨by omega,by omega⟩
    norm_num only [triple0,triple1,triple2] at hf hs hpeq
    rcases hf with ⟨_,hfl,hfr,hfn,hfst,hfs,hfm⟩
    rcases hs with ⟨_,hsl,hsr,hsn,hsst,hss,hsm⟩
    simp only [ite_true,ite_false] at hfst hsst hpeq
    change 0≤pos ∧ pos≤n ∧ n≤Zlength a ∧ acc=CakeSum (sublist pos n a) at hsuf
    rcases hsuf with ⟨hp0,hpn,hnrow,hasum⟩
    intro bounds hb hord
    rcases hb with ⟨la,ra,lb,rb,lc,rc,total,hbeq,htotal,hla,hra,hlb,hrb,hlc,hrc,hdab,hdac,hdbc,hva,hvb,hvc⟩
    subst bounds
    subst total
    have hva' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist la (ra+1) a)) ht hneed).mpr hva
    have hvb' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lb (rb+1) b)) ht hneed).mpr hvb
    have hvc' := (ceil_third_threshold__try_terminal_semantics (CakeSum a) need (CakeSum (sublist lc (rc+1) c)) ht hneed).mpr hvc
    obtain ⟨_,ho12,ho23⟩ := hord
    change rc<lb at ho12
    change rb<la at ho23
    have hna : ∀t,(0≤t ∧ t<n) → 0≤Znth t a 0 := by
      intro t htr
      have hh := hv 0 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t a 0 ∧ Znth t a 0≤1000000 at hh
      omega
    have hnb : ∀t,(0≤t ∧ t<n) → 0≤Znth t b 0 := by
      intro t htr
      have hh := hv 1 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t b 0 ∧ Znth t b 0≤1000000 at hh
      omega
    have hnc : ∀t,(0≤t ∧ t<n) → 0≤Znth t c 0 := by
      intro t htr
      have hh := hv 2 t ⟨⟨by omega,by omega⟩,by omega⟩
      change 1≤Znth t c 0 ∧ Znth t c 0≤1000000 at hh
      omega
    apply greedy_terminal_exclusion_chain__try_terminal_semantics c b a need n (Znth 2 right 0) pos acc lc rc lb rb la ra
    all_goals try first | assumption | omega
    · intro q hq
      have he : Znth 2 left 0-1=0 := by omega
      rw [he] at hfm
      exact hfm q ⟨by omega,hq.2⟩
    · intro q hq
      have he : Znth 1 left 0-1=Znth 2 right 0 := by omega
      rw [he] at hsm
      exact hsm q ⟨hq.1,by omega⟩

theorem greedy_terminal_try_order__try_terminal_semantics (a b c ord : List Int) (need n pos who acc : Int) (left right : List Int)
    (hp : Pre a b c)
    (hv : ∀ row col,((0≤row ∧ row<3) ∧ 0≤col) ∧ col<Zlength a → 1≤Znth col (Znth row [a,b,c] []) 0 ∧ Znth col (Znth row [a,b,c] []) 0≤1000000)
    (hn : n=Zlength a) (hneed : need=Z.div (CakeSum a+2) 3) (ho : CakeOrder ord) (hw : who=Znth 2 ord 0)
    (hg : GreedyRawState [a,b,c] ord need 2 pos left right) (hsuf : SuffixSumState [a,b,c] who pos n acc) :
    (acc<need → TryOrderSpec a b c ord none) ∧
    (need≤acc → TryOrderSpec a b c ord (some (OutputBounds (replace_Znth who (pos+1) left) (replace_Znth who n right)))) := by
  exact ⟨greedy_terminal_failure__try_terminal_semantics a b c ord need n pos who acc left right hp hv hn hneed ho hw hg hsuf,
    greedy_terminal_success__try_terminal_semantics a b c ord need n pos who acc left right hp hv hn hneed ho hw hg hsuf⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib
