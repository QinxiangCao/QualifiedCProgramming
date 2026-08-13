import AUXLib.BinaryTree
import SimpleC.SL.SeparationLogic
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace SimpleC.EE.QCP_demos_LLM.bst_base_lib

open AUXLib
open AUXLib.BinaryTree
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance bst_libSacContext : SacContext := ⟨naive_C_Rules⟩

abbrev key := Int
abbrev value := Int
abbrev tree := Tree key value
abbrev mapping := Mapping key value

def empty : tree := .empty
def make_tree (l : tree) (k : key) (v : value) (r : tree) : tree :=
  .make_tree l k v r

namespace Key

inductive Decision (x y : Int) : Type where
  | lt (h : x < y)
  | gt (h : x > y)
  | eq (h : x = y)

def dec (x y : Int) : Decision x y :=
  if hlt : x < y then
    .lt hlt
  else if hgt : x > y then
    .gt hgt
  else
    .eq (by omega)

end Key

abbrev SearchTree : tree -> Prop := AUXLib.BinaryTree.SearchTree
abbrev Abs : tree -> mapping -> Prop := AUXLib.BinaryTree.Abs
abbrev tree_kv : tree -> key -> value -> Prop := AUXLib.BinaryTree.tree_kv
abbrev key_set : tree -> KeySet key := AUXLib.BinaryTree.key_set

namespace Map

abbrev empty : mapping := AUXLib.BinaryTree.Map.empty
abbrev singleton := AUXLib.BinaryTree.Map.singleton (Key := key) (Value := value)
abbrev merge := AUXLib.BinaryTree.Map.merge (Key := key) (Value := value)
abbrev filter_lt := AUXLib.BinaryTree.Map.filter_lt (Key := key) (Value := value)
abbrev filter_gt := AUXLib.BinaryTree.Map.filter_gt (Key := key) (Value := value)
abbrev insert := AUXLib.BinaryTree.Map.insert (Key := key) (Value := value)
abbrev delete := AUXLib.BinaryTree.Map.delete (Key := key) (Value := value)
abbrev domain := AUXLib.BinaryTree.Map.domain (Key := key) (Value := value)

end Map

inductive half_tree : Type where
  | LH (k : key) (v : value) (right : tree)
  | RH (k : key) (v : value) (left : tree)
  deriving Repr

export half_tree (LH RH)

abbrev partial_tree := List half_tree

def combine_tree : partial_tree -> tree -> tree
  | [], tr => tr
  | LH k v r :: pt, tr => combine_tree pt (make_tree tr k v r)
  | RH k v l :: pt, tr => combine_tree pt (make_tree l k v tr)

def empty_partial_tree : partial_tree := []

theorem combine_tree_make_tree (pt : partial_tree) (k : key) (v : value)
    (l tr : tree) :
    combine_tree (pt ++ [RH k v l]) tr = make_tree l k v (combine_tree pt tr) := by
  induction pt generalizing tr with
  | nil => rfl
  | cons h pt ih =>
      cases h <;> simp only [List.cons_append, combine_tree] <;> apply ih

def tree_insert (x : key) (v : value) : tree -> tree :=
  AUXLib.BinaryTree.insert x v

def tree_pre_merge : tree -> tree -> tree := AUXLib.BinaryTree.tree_pre_merge

def tree_delete (x : key) : tree -> tree := AUXLib.BinaryTree.delete x

namespace get_right_most

structure result : Type where
  pt : partial_tree
  k : key
  v : value
  l_tree : tree
  deriving Repr

end get_right_most

def find_pre (t_left : tree) (k0 : key) (v0 : value) : tree ->
    get_right_most.result
  | .empty => ⟨[], k0, v0, t_left⟩
  | .make_tree a y w b =>
      let res := find_pre a y w b
      ⟨res.pt ++ [RH k0 v0 t_left], res.k, res.v, res.l_tree⟩

def tree_delete' (x : key) : tree -> tree
  | .empty => .empty
  | .make_tree a y v b =>
      if x < y then .make_tree (tree_delete' x a) y v b
      else if x = y then
        match a with
        | .empty => b
        | .make_tree c z w d =>
            let res := find_pre c z w d
            .make_tree (combine_tree res.pt res.l_tree) res.k res.v b
      else .make_tree a y v (tree_delete' x b)

theorem tree_insert_same_def (x : key) (v : value) :
    tree_insert x v = AUXLib.BinaryTree.insert x v := rfl

theorem tree_pre_merge_same_def (tl tr : tree) :
    tree_pre_merge tl tr = AUXLib.BinaryTree.tree_pre_merge tl tr := rfl

theorem tree_delete_same_def (x : key) (tr : tree) :
    tree_delete x tr = AUXLib.BinaryTree.delete x tr := rfl

abbrev map_insert := Map.insert
abbrev map_delete := Map.delete

noncomputable abbrev tree_key_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "key")

noncomputable abbrev tree_value_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "value")

noncomputable abbrev tree_left_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "left")

noncomputable abbrev tree_right_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "tree")) "right")

def store_tree (p : addr) : tree -> Assertion
  | .empty => “ p = NULL ” && emp
  | .make_tree l k v r =>
      “ p ≠ NULL ” && “ INT_MIN <= k /\ k <= INT_MAX ” &&
      (EX pl : addr, EX pr : addr,
        store_int naive_C_Rules (tree_key_addr p) k **
        store_int naive_C_Rules (tree_value_addr p) v **
        store_ptr naive_C_Rules (tree_left_addr p) pl **
        store_ptr naive_C_Rules (tree_right_addr p) pr **
        store_tree pl l ** store_tree pr r)

def store_ptb (p2 p2_root : addr) : partial_tree -> Assertion
  | [] => “ p2 = p2_root ” && emp
  | LH k v tr :: pt =>
      EX p_fa : addr, EX p2_fa : addr, EX p_bro : addr,
        “ p_fa ≠ NULL ” && “ INT_MIN <= k /\ k <= INT_MAX ” &&
        “ tree_left_addr p_fa = p2 ” &&
        store_ptr naive_C_Rules p2_fa p_fa **
        store_int naive_C_Rules (tree_key_addr p_fa) k **
        store_int naive_C_Rules (tree_value_addr p_fa) v **
        store_ptr naive_C_Rules (tree_right_addr p_fa) p_bro **
        store_tree p_bro tr ** store_ptb p2_fa p2_root pt
  | RH k v tr :: pt =>
      EX p_fa : addr, EX p2_fa : addr, EX p_bro : addr,
        “ p_fa ≠ NULL ” && “ INT_MIN <= k /\ k <= INT_MAX ” &&
        “ tree_right_addr p_fa = p2 ” &&
        store_ptr naive_C_Rules p2_fa p_fa **
        store_int naive_C_Rules (tree_key_addr p_fa) k **
        store_int naive_C_Rules (tree_value_addr p_fa) v **
        store_ptr naive_C_Rules (tree_left_addr p_fa) p_bro **
        store_tree p_bro tr ** store_ptb p2_fa p2_root pt

def store_pt (p p_root : addr) : partial_tree -> Assertion
  | [] => “ p = p_root ” && emp
  | LH k v tr :: pt =>
      EX p_fa : addr, EX p_bro : addr,
        “ p_fa ≠ NULL ” && “ INT_MIN <= k /\ k <= INT_MAX ” &&
        store_ptr naive_C_Rules (tree_left_addr p_fa) p **
        store_int naive_C_Rules (tree_key_addr p_fa) k **
        store_int naive_C_Rules (tree_value_addr p_fa) v **
        store_ptr naive_C_Rules (tree_right_addr p_fa) p_bro **
        store_tree p_bro tr ** store_pt p_fa p_root pt
  | RH k v tr :: pt =>
      EX p_fa : addr, EX p_bro : addr,
        “ p_fa ≠ NULL ” && “ INT_MIN <= k /\ k <= INT_MAX ” &&
        store_ptr naive_C_Rules (tree_right_addr p_fa) p **
        store_int naive_C_Rules (tree_key_addr p_fa) k **
        store_int naive_C_Rules (tree_value_addr p_fa) v **
        store_ptr naive_C_Rules (tree_left_addr p_fa) p_bro **
        store_tree p_bro tr ** store_pt p_fa p_root pt

attribute [irreducible] store_tree store_ptb store_pt

namespace Bst

def store_map (p : addr) (m : mapping) : Assertion :=
  EX tr : tree, “ SearchTree tr ” && “ Abs tr m ” && store_tree p tr

end Bst

theorem insert_SearchTree (tr : tree) (k v : Int) (h : SearchTree tr) :
    SearchTree (tree_insert k v tr) :=
  IntFacts.insert_SearchTree tr k v h

theorem insert_Abs (tr : tree) (m : mapping) (k v : Int)
    (hst : SearchTree tr) (habs : Abs tr m) :
    Abs (tree_insert k v tr) (map_insert k v m) :=
  IntFacts.insert_Abs tr m k v hst habs

theorem delete_SearchTree (tr : tree) (k : Int) (h : SearchTree tr) :
    SearchTree (tree_delete k tr) :=
  IntFacts.delete_SearchTree tr k h

theorem delete_Abs (tr : tree) (m : mapping) (k : Int)
    (hst : SearchTree tr) (habs : Abs tr m) :
    Abs (tree_delete k tr) (map_delete k m) :=
  IntFacts.delete_Abs tr m k hst habs

theorem find_pre_tree_kv_split (tl : tree) (k : key) (v : value) (tr : tree)
    (q : key) (w : value) :
    let res := find_pre tl k v tr
    tree_kv (make_tree tl k v tr) q w <->
      tree_kv (combine_tree res.pt res.l_tree) q w ∨
        (q = res.k /\ w = res.v) := by
  induction tr generalizing tl k v with
  | empty =>
      simp only [find_pre, make_tree, combine_tree]
      change
        AUXLib.BinaryTree.tree_kv (.make_tree tl k v .empty) q w <->
          AUXLib.BinaryTree.tree_kv tl q w \/ (q = k /\ w = v)
      rw [tree_kv_make_tree_iff, tree_kv_empty_iff]
      simp only [AUXLib.int_setoidEq_iff, or_false]
  | make_tree a y z b iha ihb =>
      simp only [find_pre]
      let res := find_pre a y z b
      change tree_kv (make_tree tl k v (.make_tree a y z b)) q w <->
        tree_kv (combine_tree (res.pt ++ [RH k v tl]) res.l_tree) q w ∨
          (q = res.k /\ w = res.v)
      rw [combine_tree_make_tree]
      change
        (tree_kv tl q w \/ (q = k /\ w = v) \/
          tree_kv (.make_tree a y z b) q w) <->
        (tree_kv tl q w \/ (q = k /\ w = v) \/
          tree_kv (combine_tree res.pt res.l_tree) q w) \/
          (q = res.k /\ w = res.v)
      have hinner :
          tree_kv (.make_tree a y z b) q w <->
            tree_kv (combine_tree res.pt res.l_tree) q w ∨
              (q = res.k /\ w = res.v) := by
        simpa only [res] using (ihb a y z)
      rw [hinner]
      constructor
      · rintro (ha | hb | hc | hd)
        · exact Or.inl (Or.inl ha)
        · exact Or.inl (Or.inr (Or.inl hb))
        · exact Or.inl (Or.inr (Or.inr hc))
        · exact Or.inr hd
      · rintro (habc | hd)
        · rcases habc with ha | hb | hc
          · exact Or.inl ha
          · exact Or.inr (Or.inl hb)
          · exact Or.inr (Or.inr (Or.inl hc))
        · exact Or.inr (Or.inr (Or.inr hd))

theorem find_pre_key_mem (tl : tree) (k : key) (v : value) (tr : tree) :
    let res := find_pre tl k v tr
    tree_kv (make_tree tl k v tr) res.k res.v := by
  dsimp only
  apply (find_pre_tree_kv_split tl k v tr _ _).2
  exact Or.inr ⟨rfl, rfl⟩

theorem find_pre_remaining_key_subset (tl : tree) (k : key) (v : value)
    (tr : tree) (q : key) :
    let res := find_pre tl k v tr
    key_set (combine_tree res.pt res.l_tree) q ->
      key_set (make_tree tl k v tr) q := by
  dsimp only
  intro hq
  rcases key_set_tree_kv_exists.mp hq with ⟨w, hkv⟩
  apply key_set_tree_kv_exists.mpr
  exact ⟨w, (find_pre_tree_kv_split tl k v tr q w).2 (Or.inl hkv)⟩

theorem find_pre_remaining_SearchTree (tl : tree) (k : key) (v : value)
    (tr : tree) (hst : SearchTree (make_tree tl k v tr)) :
    let res := find_pre tl k v tr
    SearchTree (combine_tree res.pt res.l_tree) := by
  induction tr generalizing tl k v with
  | empty =>
      exact hst.2.2.1
  | make_tree a y z b iha ihb =>
      simp only [find_pre]
      let res := find_pre a y z b
      rw [combine_tree_make_tree]
      rcases hst with ⟨hlt, hkr, hsl, hsr⟩
      change SearchTree (make_tree tl k v (combine_tree res.pt res.l_tree))
      refine ⟨hlt, ?_, hsl, ihb a y z hsr⟩
      intro q hq
      exact hkr q (find_pre_remaining_key_subset a y z b q hq)

theorem find_pre_remaining_lt_key (tl : tree) (k : key) (v : value)
    (tr : tree) (hst : SearchTree (make_tree tl k v tr)) :
    let res := find_pre tl k v tr
    keys_key_lt (key_set (combine_tree res.pt res.l_tree)) res.k := by
  induction tr generalizing tl k v with
  | empty =>
      exact hst.1
  | make_tree a y z b iha ihb =>
      simp only [find_pre]
      let res := find_pre a y z b
      rw [combine_tree_make_tree]
      rcases hst with ⟨hlt, hkr, hsl, hsr⟩
      have hresRight : key_set (.make_tree a y z b) res.k :=
        tree_kv_key_set (find_pre_key_mem a y z b)
      have hkres : k < res.k := hkr res.k hresRight
      have hinner := ihb a y z hsr
      intro q hq
      rcases hq with hq | hq | hq
      · exact Int.lt_trans (hlt q hq) hkres
      · subst q
        exact hkres
      · exact hinner q hq

theorem tree_delete'_tree_kv (tr : tree) (x q : key) (w : value)
    (hst : SearchTree tr) :
    tree_kv (tree_delete' x tr) q w <-> q ≠ x /\ tree_kv tr q w := by
  induction tr with
  | empty =>
      simp only [tree_delete']
      change
        AUXLib.BinaryTree.tree_kv (.empty : Tree Int Int) q w <->
          q ≠ x /\ AUXLib.BinaryTree.tree_kv .empty q w
      rw [tree_kv_empty_iff]
      simp
  | make_tree l k v r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      by_cases hlt : x < k
      · simp only [tree_delete', hlt, if_pos]
        change
          (tree_kv (tree_delete' x l) q w ∨ (q = k /\ w = v) ∨
            tree_kv r q w) <->
          q ≠ x /\ (tree_kv l q w ∨ (q = k /\ w = v) ∨ tree_kv r q w)
        rw [ihl hsl]
        constructor
        · rintro (⟨hne, hl⟩ | hroot | hr)
          · exact ⟨hne, Or.inl hl⟩
          · rcases hroot with ⟨hq, hw⟩
            subst q
            refine ⟨?_, Or.inr (Or.inl ⟨rfl, hw⟩)⟩
            intro hkx
            subst x
            exact (Int.lt_irrefl k hlt).elim
          · have hkq := hkr q (tree_kv_key_set hr)
            refine ⟨?_, Or.inr (Or.inr hr)⟩
            intro hqx
            subst q
            exact (Int.lt_irrefl x (Int.lt_trans hlt hkq)).elim
        · rintro ⟨hne, hl | hroot | hr⟩
          · exact Or.inl ⟨hne, hl⟩
          · exact Or.inr (Or.inl hroot)
          · exact Or.inr (Or.inr hr)
      · by_cases heq : x = k
        · subst x
          cases l with
          | empty =>
              simp only [tree_delete', Int.lt_irrefl, if_false, if_pos]
              change BinaryTree.tree_kv r q w <-> q ≠ k /\
                BinaryTree.tree_kv (.make_tree .empty k v r) q w
              rw [tree_kv_make_tree_iff]
              simp only [tree_kv_empty_iff, false_or]
              constructor
              · intro hr
                have hkq := hkr q (tree_kv_key_set hr)
                refine ⟨?_, Or.inr hr⟩
                intro hqk
                subst q
                exact (Int.lt_irrefl k hkq).elim
              · rintro ⟨hne, hroot | hr⟩
                · exact (hne hroot.1).elim
                · exact hr
          | make_tree ll lk lv lr =>
              let res := find_pre ll lk lv lr
              simp only [tree_delete', Int.lt_irrefl, if_false, if_pos]
              change
                (tree_kv (combine_tree res.pt res.l_tree) q w ∨
                  (q = res.k /\ w = res.v) ∨ tree_kv r q w) <->
                q ≠ k /\
                  (tree_kv (.make_tree ll lk lv lr) q w ∨
                    (q = k /\ w = v) ∨ tree_kv r q w)
              have hsplit := find_pre_tree_kv_split ll lk lv lr q w
              have hleft :
                  tree_kv (.make_tree ll lk lv lr) q w <->
                    tree_kv (combine_tree res.pt res.l_tree) q w ∨
                      (q = res.k /\ w = res.v) := by
                simpa only [res] using hsplit
              constructor
              · rintro (hrem | hpre | hr)
                · have hold := hleft.mpr (Or.inl hrem)
                  have hqk := hlk q (tree_kv_key_set hold)
                  refine ⟨?_, Or.inl hold⟩
                  intro heq
                  subst q
                  exact (Int.lt_irrefl k hqk).elim
                · have hold := hleft.mpr (Or.inr hpre)
                  have hqk := hlk q (tree_kv_key_set hold)
                  refine ⟨?_, Or.inl hold⟩
                  intro heq
                  subst q
                  exact (Int.lt_irrefl k hqk).elim
                · have hkq := hkr q (tree_kv_key_set hr)
                  refine ⟨?_, Or.inr (Or.inr hr)⟩
                  intro heq
                  subst q
                  exact (Int.lt_irrefl k hkq).elim
              · rintro ⟨hne, hleftOld | hroot | hr⟩
                · rcases hleft.mp hleftOld with hrem | hpre
                  · exact Or.inl hrem
                  · exact Or.inr (Or.inl hpre)
                · exact (hne hroot.1).elim
                · exact Or.inr (Or.inr hr)
        · have hkx : k < x := by
            rcases Int.lt_trichotomy x k with hxk | hxk | hkx
            · exact (hlt hxk).elim
            · exact (heq hxk).elim
            · exact hkx
          simp only [tree_delete', hlt, heq, if_false]
          change
            (tree_kv l q w ∨ (q = k /\ w = v) ∨
              tree_kv (tree_delete' x r) q w) <->
            q ≠ x /\ (tree_kv l q w ∨ (q = k /\ w = v) ∨ tree_kv r q w)
          rw [ihr hsr]
          constructor
          · rintro (hl | hroot | ⟨hne, hr⟩)
            · have hqk := hlk q (tree_kv_key_set hl)
              refine ⟨?_, Or.inl hl⟩
              intro hqx
              subst q
              exact (Int.lt_irrefl x (Int.lt_trans hqk hkx)).elim
            · rcases hroot with ⟨hq, hw⟩
              subst q
              refine ⟨?_, Or.inr (Or.inl ⟨rfl, hw⟩)⟩
              intro hk
              subst x
              exact (Int.lt_irrefl k hkx).elim
            · exact ⟨hne, Or.inr (Or.inr hr)⟩
          · rintro ⟨hne, hl | hroot | hr⟩
            · exact Or.inl hl
            · exact Or.inr (Or.inl hroot)
            · exact Or.inr (Or.inr ⟨hne, hr⟩)

theorem tree_delete'_key_set (tr : tree) (x q : key)
    (hst : SearchTree tr) :
    key_set (tree_delete' x tr) q <-> q ≠ x /\ key_set tr q := by
  constructor
  · intro hq
    rcases key_set_tree_kv_exists.mp hq with ⟨w, hkv⟩
    have h := (tree_delete'_tree_kv tr x q w hst).mp hkv
    exact ⟨h.1, tree_kv_key_set h.2⟩
  · rintro ⟨hne, hq⟩
    rcases key_set_tree_kv_exists.mp hq with ⟨w, hkv⟩
    apply key_set_tree_kv_exists.mpr
    exact ⟨w, (tree_delete'_tree_kv tr x q w hst).mpr ⟨hne, hkv⟩⟩

theorem delete'_SearchTree (tr : tree) (x : key) (hst : SearchTree tr) :
    SearchTree (tree_delete' x tr) := by
  induction tr with
  | empty => exact hst
  | make_tree l k v r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      by_cases hlt : x < k
      · simp only [tree_delete', hlt, if_pos]
        change SearchTree (.make_tree (tree_delete' x l) k v r)
        refine ⟨?_, hkr, ihl hsl, hsr⟩
        intro q hq
        exact hlk q ((tree_delete'_key_set l x q hsl).mp hq).2
      · by_cases heq : x = k
        · subst x
          cases l with
          | empty =>
              simpa only [tree_delete', Int.lt_irrefl, if_false, if_pos] using hsr
          | make_tree ll lk lv lr =>
              let res := find_pre ll lk lv lr
              simp only [tree_delete', Int.lt_irrefl, if_false, if_pos]
              change SearchTree
                (.make_tree (combine_tree res.pt res.l_tree) res.k res.v r)
              have hleft : SearchTree (.make_tree ll lk lv lr) := hsl
              have hresMem : key_set (.make_tree ll lk lv lr) res.k :=
                tree_kv_key_set (find_pre_key_mem ll lk lv lr)
              have hresRoot : res.k < k := hlk res.k hresMem
              refine ⟨find_pre_remaining_lt_key ll lk lv lr hleft, ?_,
                find_pre_remaining_SearchTree ll lk lv lr hleft, hsr⟩
              intro q hq
              exact Int.lt_trans hresRoot (hkr q hq)
        · have hkx : k < x := by
            rcases Int.lt_trichotomy x k with hxk | hxk | hkx
            · exact (hlt hxk).elim
            · exact (heq hxk).elim
            · exact hkx
          simp only [tree_delete', hlt, heq, if_false]
          change SearchTree (.make_tree l k v (tree_delete' x r))
          refine ⟨hlk, ?_, hsl, ihr hsr⟩
          intro q hq
          exact hkr q ((tree_delete'_key_set r x q hsr).mp hq).2

theorem delete'_Abs (tr : tree) (m : mapping) (x : key)
    (hst : SearchTree tr) (habs : Abs tr m) :
    Abs (tree_delete' x tr) (map_delete x m) := by
  intro q w
  rw [AUXLib.BinaryTree.Map.delete_iff, habs]
  exact (tree_delete'_tree_kv tr x q w hst).symm

theorem store_ptb_LH (p2_fa p_fa p_bro k v : Int) (tr : tree)
    (hp : p_fa ≠ NULL) (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_ptr naive_C_Rules p2_fa p_fa **
      store_int naive_C_Rules (tree_key_addr p_fa) k **
      store_int naive_C_Rules (tree_value_addr p_fa) v **
      store_ptr naive_C_Rules (tree_right_addr p_fa) p_bro **
      store_tree p_bro tr |--
    store_ptb (tree_left_addr p_fa) p2_fa [LH k v tr] := by
  simp only [store_ptb]
  Exists p_fa p2_fa p_bro
  entailer!

theorem store_ptb_RH (p2_fa p_fa p_bro k v : Int) (tr : tree)
    (hp : p_fa ≠ NULL) (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_ptr naive_C_Rules p2_fa p_fa **
      store_int naive_C_Rules (tree_key_addr p_fa) k **
      store_int naive_C_Rules (tree_value_addr p_fa) v **
      store_ptr naive_C_Rules (tree_left_addr p_fa) p_bro **
      store_tree p_bro tr |--
    store_ptb (tree_right_addr p_fa) p2_fa [RH k v tr] := by
  simp only [store_ptb]
  Exists p_fa p2_fa p_bro
  entailer!

theorem store_pt_LH (p p_fa p_bro k v : Int) (tr : tree)
    (hp : p_fa ≠ NULL) (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_int naive_C_Rules (tree_key_addr p_fa) k **
      store_int naive_C_Rules (tree_value_addr p_fa) v **
      store_ptr naive_C_Rules (tree_left_addr p_fa) p **
      store_ptr naive_C_Rules (tree_right_addr p_fa) p_bro **
      store_tree p_bro tr |-- store_pt p p_fa [LH k v tr] := by
  simp only [store_pt]
  Exists p_fa p_bro
  entailer!

theorem store_pt_RH (p p_fa p_bro k v : Int) (tr : tree)
    (hp : p_fa ≠ NULL) (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_int naive_C_Rules (tree_key_addr p_fa) k **
      store_int naive_C_Rules (tree_value_addr p_fa) v **
      store_ptr naive_C_Rules (tree_right_addr p_fa) p **
      store_ptr naive_C_Rules (tree_left_addr p_fa) p_bro **
      store_tree p_bro tr |-- store_pt p p_fa [RH k v tr] := by
  simp only [store_pt]
  Exists p_fa p_bro
  entailer!

theorem store_ptb_app (p2 p2_mid p2_root : Int) (pt1 pt2 : partial_tree) :
    store_ptb p2 p2_mid pt1 ** store_ptb p2_mid p2_root pt2 |--
      store_ptb p2 p2_root (pt1 ++ pt2) := by
  induction pt1 generalizing p2 with
  | nil =>
      simp only [store_ptb, List.nil_append]
      Intros
      subst p2
      entailer!
  | cons h pt ih =>
      cases h with
      | LH k v tr =>
          simp only [store_ptb, List.cons_append]
          Intros p_fa p2_fa p_bro
          Exists p_fa p2_fa p_bro
          entailer!
      | RH k v tr =>
          simp only [store_ptb, List.cons_append]
          Intros p_fa p2_fa p_bro
          Exists p_fa p2_fa p_bro
          entailer!

theorem store_pt_app (p2 p2_mid p2_root : Int) (pt1 pt2 : partial_tree) :
    store_pt p2 p2_mid pt1 ** store_pt p2_mid p2_root pt2 |--
      store_pt p2 p2_root (pt1 ++ pt2) := by
  induction pt1 generalizing p2 with
  | nil =>
      simp only [store_pt, List.nil_append]
      Intros
      subst p2
      entailer!
  | cons h pt ih =>
      cases h with
      | LH k v tr =>
          simp only [store_pt, List.cons_append]
          Intros p_fa p_bro
          Exists p_fa p_bro
          entailer!
      | RH k v tr =>
          simp only [store_pt, List.cons_append]
          Intros p_fa p_bro
          Exists p_fa p_bro
          entailer!

theorem store_tree_zero (p : Int) (tr : tree) (hp : p = 0) :
    store_tree p tr |-- “ tr = empty ” && emp := by
  subst p
  cases tr with
  | empty => simp only [store_tree, empty]; entailer!
  | make_tree l k v r =>
      simp only [store_tree]
      entailer!

theorem store_tree_not_zero (p : Int) (tr : tree) (hp : p ≠ 0) :
    store_tree p tr |--
      EX l : tree, EX k : Int, EX v : Int, EX r : tree,
      EX pl : Int, EX pr : Int,
        “ tr = make_tree l k v r ” &&
        “ INT_MIN <= k /\ k <= INT_MAX ” && “ p ≠ NULL ” &&
        “ INT_MIN <= k /\ k <= INT_MAX ” &&
        store_int naive_C_Rules (tree_key_addr p) k **
        store_int naive_C_Rules (tree_value_addr p) v **
        store_ptr naive_C_Rules (tree_left_addr p) pl **
        store_ptr naive_C_Rules (tree_right_addr p) pr **
        store_tree pl l ** store_tree pr r := by
  cases tr with
  | empty => simp only [store_tree]; entailer!
  | make_tree l k v r =>
      simp only [store_tree]
      Intros pl pr
      Exists l k v r pl pr
      entailer!

theorem store_tree_size_1 (p k v : Int) (hp : p ≠ 0)
    (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_int naive_C_Rules (tree_key_addr p) k **
      store_int naive_C_Rules (tree_value_addr p) v **
      store_ptr naive_C_Rules (tree_left_addr p) 0 **
      store_ptr naive_C_Rules (tree_right_addr p) 0 |--
    store_tree p (make_tree empty k v empty) := by
  simp only [store_tree, make_tree, empty]
  Exists (0 : Int) (0 : Int)
  entailer!

theorem store_tree_make_tree (p k v pl pr : Int) (l r : tree)
    (hp : p ≠ 0) (hk : INT_MIN <= k /\ k <= INT_MAX) :
    store_int naive_C_Rules (tree_key_addr p) k **
      store_int naive_C_Rules (tree_value_addr p) v **
      store_ptr naive_C_Rules (tree_left_addr p) pl **
      store_ptr naive_C_Rules (tree_right_addr p) pr **
      store_tree pl l ** store_tree pr r |--
    store_tree p (make_tree l k v r) := by
  simp only [store_tree, make_tree]
  Exists pl pr
  entailer!

theorem store_ptb_store_tree (p2_root p2 p : Int) (pt : partial_tree)
    (tr : tree) :
    store_ptb p2 p2_root pt ** store_ptr naive_C_Rules p2 p **
      store_tree p tr |--
    EX p_root : Int,
      store_ptr naive_C_Rules p2_root p_root **
        store_tree p_root (combine_tree pt tr) := by
  induction pt generalizing p2 p tr with
  | nil =>
      simp only [store_ptb, combine_tree]
      Intros
      subst p2
      Exists p
      entailer!
  | cons h pt ih =>
      cases h with
      | LH k v sibling =>
          simp only [store_ptb, combine_tree]
          Intros p_fa p2_fa p_bro
          subst p2
          sep_apply (store_tree_make_tree p_fa k v p p_bro tr sibling) <;>
            try assumption
          sep_apply (ih p2_fa p_fa (make_tree tr k v sibling))
          Intros p_root
          Exists p_root
          entailer!
      | RH k v sibling =>
          simp only [store_ptb, combine_tree]
          Intros p_fa p2_fa p_bro
          subst p2
          sep_apply (store_tree_make_tree p_fa k v p_bro p sibling tr) <;>
            try assumption
          sep_apply (ih p2_fa p_fa (make_tree sibling k v tr))
          Intros p_root
          Exists p_root
          entailer!

theorem combine_tree_pt_assoc (pt1 pt2 : partial_tree) (tr : tree) :
    combine_tree pt1 (combine_tree pt2 tr) = combine_tree (pt2 ++ pt1) tr := by
  induction pt2 generalizing tr with
  | nil => rfl
  | cons h pt ih => cases h <;> simp only [combine_tree, List.cons_append] <;> apply ih

theorem store_combine (p1 p2 : Int) (pt : partial_tree) (tr : tree) :
    store_tree p2 tr ** store_pt p2 p1 pt |--
      store_tree p1 (combine_tree pt tr) := by
  induction pt generalizing p2 tr with
  | nil =>
      simp only [store_pt, combine_tree]
      Intros
      subst p2
      entailer!
  | cons h pt ih =>
      cases h with
      | LH k v sibling =>
          simp only [store_pt, combine_tree]
          Intros p_fa p_bro
          sep_apply (store_tree_make_tree p_fa k v p2 p_bro tr sibling) <;>
            try assumption
          exact ih p_fa (make_tree tr k v sibling)
      | RH k v sibling =>
          simp only [store_pt, combine_tree]
          Intros p_fa p_bro
          sep_apply (store_tree_make_tree p_fa k v p_bro p2 sibling tr) <;>
            try assumption
          exact ih p_fa (make_tree sibling k v tr)

end SimpleC.EE.QCP_demos_LLM.bst_base_lib
