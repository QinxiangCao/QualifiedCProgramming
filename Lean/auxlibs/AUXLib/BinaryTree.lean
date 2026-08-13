import AUXLib.OrdersDecFact
import Lean.Elab.Tactic.Omega
import Std.Tactic

namespace AUXLib.BinaryTree

universe u v

/-!
This file is the dependency slice of `AUXLib/BinaryTree.v` used by the
annotated-simple-C binary-search-tree examples.  Coq packages this theory as
a family of module types and functors.  Lean exposes the same transparent
definitions over an explicit `Tree Key Value`; no theorem is stored in a
structure field.
-/

inductive Tree (Key : Type u) (Value : Type v) : Type (max u v) where
  | empty
  | make_tree (left : Tree Key Value) (key : Key) (value : Value)
      (right : Tree Key Value)
  deriving Repr

namespace Tree

def t_case {Key : Type u} {Value : Type v} {P : Tree Key Value -> Sort w}
    (emptyCase : P .empty)
    (nodeCase : forall (l : Tree Key Value) (k : Key) (v : Value)
      (r : Tree Key Value), P (Tree.make_tree l k v r)) :
    (tr : Tree Key Value) -> P tr
  | .empty => emptyCase
  | .make_tree l k v r => nodeCase l k v r

theorem t_case_empty {Key : Type u} {Value : Type v}
    {P : Tree Key Value -> Sort w} (f1 : P .empty)
    (f2 : forall (l : Tree Key Value) (k : Key) (v : Value)
      (r : Tree Key Value), P (Tree.make_tree l k v r)) :
    t_case f1 f2 .empty = f1 := rfl

theorem t_case_make_tree {Key : Type u} {Value : Type v}
    {P : Tree Key Value -> Sort w} (f1 : P .empty)
    (f2 : forall (l : Tree Key Value) (k : Key) (v : Value)
      (r : Tree Key Value), P (Tree.make_tree l k v r))
    (l : Tree Key Value) (k : Key) (v : Value)
    (r : Tree Key Value) :
    t_case f1 f2 (.make_tree l k v r) = f2 l k v r := rfl

end Tree

abbrev KeySet (Key : Type u) := Key -> Prop

def Sets_singleton_setoid [DecidableSetoid Key] (k : Key) : KeySet Key :=
  fun k0 => setoidEq k0 k

def set_equiv (s1 s2 : KeySet Key) : Prop := forall k, s1 k <-> s2 k

def set_union (s1 s2 : KeySet Key) : KeySet Key := fun k => s1 k \/ s2 k

def set_intersect (s1 s2 : KeySet Key) : KeySet Key := fun k => s1 k /\ s2 k

def set_complement (s : KeySet Key) : KeySet Key := fun k => Not (s k)

def empty_set : KeySet Key := fun _ => False

def key_keys_lt [LT Key] (k1 : Key) (ks2 : KeySet Key) : Prop :=
  forall k2, ks2 k2 -> k1 < k2

def keys_key_lt [LT Key] (ks1 : KeySet Key) (k2 : Key) : Prop :=
  forall k1, ks1 k1 -> k1 < k2

def keys_keys_lt [LT Key] (ks1 ks2 : KeySet Key) : Prop :=
  forall k1 k2, ks1 k1 -> ks2 k2 -> k1 < k2

def keys_union (kss : List (KeySet Key)) : KeySet Key :=
  fun k => exists ks, ks ∈ kss /\ ks k

def keys_list_lt [LT Key] : List (KeySet Key) -> Prop
  | [] => True
  | ks :: rest => keys_keys_lt ks (keys_union rest) /\ keys_list_lt rest

theorem keys_union_iff (kss : List (KeySet Key)) (k : Key) :
    keys_union kss k <-> exists ks, ks ∈ kss /\ ks k := Iff.rfl

theorem empty_set_keys_keys_lt [LT Key] (ks : KeySet Key) :
    keys_keys_lt empty_set ks := by
  intro _ _ h
  exact h.elim

theorem keys_keys_lt_empty_set [LT Key] (ks : KeySet Key) :
    keys_keys_lt ks empty_set := by
  intro _ _ _ h
  exact h.elim

theorem keys_keys_lt_union [LT Key] (ks1 ks2 ks3 : KeySet Key) :
    keys_keys_lt ks1 (set_union ks2 ks3) <->
      keys_keys_lt ks1 ks2 /\ keys_keys_lt ks1 ks3 := by
  constructor
  · intro h
    exact ⟨fun a b ha hb => h a b ha (Or.inl hb),
      fun a b ha hb => h a b ha (Or.inr hb)⟩
  · rintro ⟨h12, h13⟩ a b ha (hb | hb)
    · exact h12 a b ha hb
    · exact h13 a b ha hb

theorem union_keys_keys_lt [LT Key] (ks1 ks2 ks3 : KeySet Key) :
    keys_keys_lt (set_union ks1 ks2) ks3 <->
      keys_keys_lt ks1 ks3 /\ keys_keys_lt ks2 ks3 := by
  constructor
  · intro h
    exact ⟨fun a b ha hb => h a b (Or.inl ha) hb,
      fun a b ha hb => h a b (Or.inr ha) hb⟩
  · rintro ⟨h13, h23⟩ a b (ha | ha) hb
    · exact h13 a b ha hb
    · exact h23 a b ha hb

theorem keys_keys_lt_intersect [LT Key] (ks1 ks2 ks3 : KeySet Key)
    (h : keys_keys_lt ks1 ks2 \/ keys_keys_lt ks1 ks3) :
    keys_keys_lt ks1 (set_intersect ks2 ks3) := by
  rcases h with h | h
  · exact fun a b ha hb => h a b ha hb.1
  · exact fun a b ha hb => h a b ha hb.2

theorem intersect_keys_keys_lt_l [LT Key] (ks1 ks2 ks3 : KeySet Key)
    (h : keys_keys_lt ks1 ks3) :
    keys_keys_lt (set_intersect ks1 ks2) ks3 :=
  fun a b ha hb => h a b ha.1 hb

theorem intersect_keys_keys_lt_r [LT Key] (ks1 ks2 ks3 : KeySet Key)
    (h : keys_keys_lt ks2 ks3) :
    keys_keys_lt (set_intersect ks1 ks2) ks3 :=
  fun a b ha hb => h a b ha.2 hb

def elements : Tree Key Value -> List (Key × Value)
  | .empty => []
  | .make_tree l k v r => (k, v) :: elements l ++ elements r

theorem elements_empty : elements (Tree.empty : Tree Key Value) = [] := rfl

theorem elements_make_tree (l : Tree Key Value) (k : Key) (v : Value)
    (r : Tree Key Value) :
    elements (.make_tree l k v r) = (k, v) :: elements l ++ elements r := rfl

def In (n : Key × Value) (tr : Tree Key Value) : Prop := n ∈ elements tr

theorem in_empty_iff (n : Key × Value) :
    In n (Tree.empty : Tree Key Value) <-> False := by
  simp [In, elements]

theorem in_make_tree_iff (n : Key × Value) (l : Tree Key Value)
    (k : Key) (v : Value) (r : Tree Key Value) :
    In n (.make_tree l k v r) <->
      (k, v) = n \/ In n l \/ In n r := by
  simp [In, elements, eq_comm]

def key_set [DecidableSetoid Key] : Tree Key Value -> KeySet Key
  | .empty => empty_set
  | .make_tree l k _ r =>
      set_union (key_set l) (set_union (Sets_singleton_setoid k) (key_set r))

theorem key_set_empty [DecidableSetoid Key] (k : Key) :
    key_set (Tree.empty : Tree Key Value) k <-> False := Iff.rfl

theorem key_set_make_tree [DecidableSetoid Key] (q : Key) (l : Tree Key Value)
    (k : Key) (v : Value) (r : Tree Key Value) :
    key_set (.make_tree l k v r) q <->
      key_set l q \/ setoidEq q k \/ key_set r q := Iff.rfl

def SearchTree [DecidableSetoid Key] [LT Key] : Tree Key Value -> Prop
  | .empty => True
  | .make_tree l k _ r =>
      keys_key_lt (key_set l) k /\ key_keys_lt k (key_set r) /\
      SearchTree l /\ SearchTree r

theorem SearchTree_empty [DecidableSetoid Key] [LT Key] :
    SearchTree (Tree.empty : Tree Key Value) := trivial

theorem SearchTree_make_tree [DecidableSetoid Key] [LT Key]
    (l : Tree Key Value)
    (k : Key) (v : Value) (r : Tree Key Value) :
    SearchTree (.make_tree l k v r) <->
      keys_key_lt (key_set l) k /\ key_keys_lt k (key_set r) /\
      SearchTree l /\ SearchTree r := Iff.rfl

def tree_kv [DecidableSetoid Key] : Tree Key Value -> Key -> Value -> Prop
  | .empty, _, _ => False
  | .make_tree l k v r, q, w =>
      tree_kv l q w \/ (setoidEq q k /\ w = v) \/ tree_kv r q w

theorem tree_kv_empty [DecidableSetoid Key] (k : Key) (v : Value) :
    Not (tree_kv (Tree.empty : Tree Key Value) k v) := by simp [tree_kv]

theorem tree_kv_empty_iff [DecidableSetoid Key] (k : Key) (v : Value) :
    tree_kv (Tree.empty : Tree Key Value) k v <-> False := Iff.rfl

theorem tree_kv_make_tree_iff [DecidableSetoid Key]
    (l : Tree Key Value) (k : Key)
    (v : Value) (r : Tree Key Value) (q : Key) (w : Value) :
    tree_kv (.make_tree l k v r) q w <->
      tree_kv l q w \/ (setoidEq q k /\ w = v) \/ tree_kv r q w := Iff.rfl

theorem tree_kv_key_set [DecidableSetoid Key]
    {tr : Tree Key Value} {k : Key} {v : Value}
    (h : tree_kv tr k v) : key_set tr k := by
  induction tr with
  | empty => exact h.elim
  | make_tree l k0 v0 r ihl ihr =>
      rcases h with h | h | h
      · exact Or.inl (ihl h)
      · exact Or.inr (Or.inl h.1)
      · exact Or.inr (Or.inr (ihr h))

theorem key_set_tree_kv_exists [DecidableSetoid Key]
    {tr : Tree Key Value} {k : Key} :
    key_set tr k <-> exists v, tree_kv tr k v := by
  induction tr with
  | empty => simp [key_set, empty_set, tree_kv]
  | make_tree l k0 v0 r ihl ihr =>
      simp only [key_set, set_union, Sets_singleton_setoid, tree_kv]
      rw [ihl, ihr]
      constructor
      · rintro (⟨v, hv⟩ | hk | ⟨v, hv⟩)
        · exact ⟨v, Or.inl hv⟩
        · exact ⟨v0, Or.inr (Or.inl ⟨hk, rfl⟩)⟩
        · exact ⟨v, Or.inr (Or.inr hv)⟩
      · rintro ⟨v, hv | hv | hv⟩
        · exact Or.inl ⟨v, hv⟩
        · exact Or.inr (Or.inl hv.1)
        · exact Or.inr (Or.inr ⟨v, hv⟩)

abbrev Mapping (Key : Type u) (Value : Type v) := Key -> Option Value

namespace Map

def equiv (m1 m2 : Mapping Key Value) : Prop := forall k, m1 k = m2 k

def empty : Mapping Key Value := fun _ => none

def singleton [DecidableSetoid Key] (k0 : Key) (v0 : Value) :
    Mapping Key Value :=
  fun k => if setoidEq k k0 then some v0 else none

def merge [DecidableEq Value] (m1 m2 : Mapping Key Value) : Mapping Key Value :=
  fun k =>
    match m1 k, m2 k with
    | some v, none => some v
    | none, some v => some v
    | some v1, some v2 => if v1 = v2 then some v1 else none
    | none, none => none

def filter_lt [LT Key] [DecidableLT Key] (k0 : Key) (m : Mapping Key Value) :
    Mapping Key Value := fun k => if k < k0 then m k else none

def filter_gt [LT Key] [DecidableLT Key] (k0 : Key) (m : Mapping Key Value) :
    Mapping Key Value := fun k => if k0 < k then m k else none

def insert [DecidableSetoid Key] (k0 : Key) (v0 : Value)
    (m : Mapping Key Value) : Mapping Key Value :=
  fun k => if setoidEq k k0 then some v0 else m k

def delete [DecidableSetoid Key] (k0 : Key) (m : Mapping Key Value) :
    Mapping Key Value := fun k => if setoidEq k k0 then none else m k

def domain (m : Mapping Key Value) : KeySet Key := fun k => exists v, m k = some v

theorem empty_iff (k : Key) (v : Value) : empty k = some v <-> False := by
  simp [empty]

theorem single_iff [DecidableSetoid Key] (k : Key) (v : Value)
    (k0 : Key) (v0 : Value) :
    singleton k v k0 = some v0 <-> setoidEq k0 k /\ v0 = v := by
  by_cases h : setoidEq k0 k <;> simp [singleton, h, eq_comm]

theorem filter_lt_iff [LT Key] [DecidableLT Key] (m : Mapping Key Value)
    (k0 k : Key) (v : Value) :
    filter_lt k0 m k = some v <-> m k = some v /\ k < k0 := by
  by_cases h : k < k0 <;> simp [filter_lt, h]

theorem filter_gt_iff [LT Key] [DecidableLT Key] (m : Mapping Key Value)
    (k0 k : Key) (v : Value) :
    filter_gt k0 m k = some v <-> m k = some v /\ k0 < k := by
  by_cases h : k0 < k <;> simp [filter_gt, h]

theorem filter_lt_eq [LT Key] [DecidableLT Key] (m : Mapping Key Value)
    (k0 k : Key) (h : k < k0) : filter_lt k0 m k = m k := by
  simp [filter_lt, h]

theorem filter_gt_eq [LT Key] [DecidableLT Key] (m : Mapping Key Value)
    (k0 k : Key) (h : k0 < k) : filter_gt k0 m k = m k := by
  simp [filter_gt, h]

theorem insert_iff [DecidableSetoid Key] (k : Key) (v : Value)
    (m : Mapping Key Value) (k0 : Key) (v0 : Value) :
    insert k v m k0 = some v0 <->
      (setoidEq k0 k /\ v0 = v) \/
        (setoidNe k0 k /\ m k0 = some v0) := by
  by_cases h : setoidEq k0 k <;> simp [insert, setoidNe, h, eq_comm]

theorem delete_iff [DecidableSetoid Key] (k : Key) (m : Mapping Key Value)
    (k0 : Key) (v0 : Value) :
    delete k m k0 = some v0 <->
      setoidNe k0 k /\ m k0 = some v0 := by
  by_cases h : setoidEq k0 k <;> simp [delete, setoidNe, h]

theorem empty_domain (k : Key) : domain (empty : Mapping Key Value) k <-> False := by
  simp [domain, empty]

theorem singleton_domain [DecidableSetoid Key]
    (k : Key) (v : Value) (q : Key) :
    domain (singleton k v) q <-> setoidEq q k := by
  by_cases h : setoidEq q k <;> simp [domain, singleton, h]

theorem insert_domain [DecidableSetoid Key] (k : Key) (v : Value)
    (m : Mapping Key Value) (q : Key) :
    domain (insert k v m) q <-> setoidEq q k \/ domain m q := by
  by_cases h : setoidEq q k <;> simp [domain, insert, h]

theorem delete_domain [DecidableSetoid Key] (k : Key) (m : Mapping Key Value)
    (q : Key) :
    domain (delete k m) q <-> domain m q /\ setoidNe q k := by
  by_cases h : setoidEq q k <;> simp [domain, delete, setoidNe, h]

end Map

def Abs [DecidableSetoid Key] (tr : Tree Key Value)
    (m : Mapping Key Value) : Prop :=
  forall k v, m k = some v <-> tree_kv tr k v

theorem Abs_empty [DecidableSetoid Key] :
    Abs (Tree.empty : Tree Key Value) Map.empty := by
  intro k v
  simp [Map.empty, tree_kv]

theorem Abs_empty_inv [DecidableSetoid Key] {m : Mapping Key Value}
    (h : Abs (Tree.empty : Tree Key Value) m) : Map.equiv m Map.empty := by
  intro k
  cases hmk : m k with
  | none => rfl
  | some v =>
      have := (h k v).mp hmk
      exact this.elim

def look_up [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (key : Key) : Tree Key Value -> Option Value
  | .empty => none
  | .make_tree l k v r =>
      if key < k then look_up key l
      else if setoidEq key k then some v
      else look_up key r

theorem look_up_empty [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (key : Key) : look_up key (Tree.empty : Tree Key Value) = none := rfl

theorem look_up_make_tree_lt [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (key k : Key) (v : Value) (l r : Tree Key Value) (h : key < k) :
    look_up key (.make_tree l k v r) = look_up key l := by simp [look_up, h]

theorem look_up_make_tree_eq [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (key k : Key) (v : Value) (l r : Tree Key Value)
    (hlt : Not (key < k)) (heq : setoidEq key k) :
    look_up key (.make_tree l k v r) = some v := by
  simp [look_up, hlt, heq]

def insert [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (key : Key) (value : Value) : Tree Key Value -> Tree Key Value
  | .empty => .make_tree .empty key value .empty
  | .make_tree l k v r =>
      if key < k then .make_tree (insert key value l) k v r
      else if setoidEq key k then .make_tree l key value r
      else .make_tree l k v (insert key value r)

theorem insert_empty [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k : Key) (v : Value) :
    insert k v (.empty : Tree Key Value) = .make_tree .empty k v .empty := rfl

theorem insert_make_tree_lt [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k0 k : Key) (v0 v : Value) (l r : Tree Key Value) (h : k0 < k) :
    insert k0 v0 (.make_tree l k v r) =
      .make_tree (insert k0 v0 l) k v r := by simp [insert, h]

theorem insert_make_tree_eq [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k0 k : Key) (v0 v : Value) (l r : Tree Key Value)
    (hlt : Not (k0 < k)) (heq : setoidEq k0 k) :
    insert k0 v0 (.make_tree l k v r) = .make_tree l k0 v0 r := by
  simp [insert, hlt, heq]

theorem insert_make_tree_gt [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k0 k : Key) (v0 v : Value) (l r : Tree Key Value)
    (hlt : Not (k0 < k)) (hne : setoidNe k0 k) :
    insert k0 v0 (.make_tree l k v r) =
      .make_tree l k v (insert k0 v0 r) := by
  have hne' : Not (setoidEq k0 k) := hne
  simp [insert, hlt, hne']

def tree_pre_merge : Tree Key Value -> Tree Key Value -> Tree Key Value
  | .empty, tr => tr
  | .make_tree l k v r, tr => .make_tree l k v (tree_pre_merge r tr)

def delete [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (key : Key) : Tree Key Value -> Tree Key Value
  | .empty => .empty
  | .make_tree l k v r =>
      if key < k then .make_tree (delete key l) k v r
      else if setoidEq key k then tree_pre_merge l r
      else .make_tree l k v (delete key r)

theorem tree_pre_merge_empty (tr : Tree Key Value) :
    tree_pre_merge .empty tr = tr := rfl

theorem tree_pre_merge_maketree (l : Tree Key Value) (k : Key)
    (v : Value) (r tr : Tree Key Value) :
    tree_pre_merge (.make_tree l k v r) tr =
      .make_tree l k v (tree_pre_merge r tr) := rfl

theorem delete_empty [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k : Key) : delete k (Tree.empty : Tree Key Value) = .empty := rfl

theorem delete_make_tree_lt [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k0 k : Key) (v : Value) (l r : Tree Key Value) (h : k0 < k) :
    delete k0 (.make_tree l k v r) = .make_tree (delete k0 l) k v r := by
  simp [delete, h]

theorem delete_make_tree_eq [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k0 k : Key) (v : Value) (l r : Tree Key Value)
    (hlt : Not (k0 < k)) (heq : setoidEq k0 k) :
    delete k0 (.make_tree l k v r) = tree_pre_merge l r := by
  simp [delete, hlt, heq]

theorem delete_make_tree_gt [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k0 k : Key) (v : Value) (l r : Tree Key Value)
    (hlt : Not (k0 < k)) (hne : setoidNe k0 k) :
    delete k0 (.make_tree l k v r) = .make_tree l k v (delete k0 r) := by
  have hne' : Not (setoidEq k0 k) := hne
  simp [delete, hlt, hne']

def delete_min : Tree Key Value -> Tree Key Value
  | .empty => .empty
  | .make_tree .empty _ _ r => r
  | .make_tree (.make_tree ll lk lv lr) k v r =>
      .make_tree (delete_min (.make_tree ll lk lv lr)) k v r

def min_node (default : Key × Value) : Tree Key Value -> Key × Value
  | .empty => default
  | .make_tree .empty k v _ => (k, v)
  | .make_tree (.make_tree ll lk lv lr) _ _ _ =>
      min_node default (.make_tree ll lk lv lr)

def swap_delete [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (key : Key) : Tree Key Value -> Tree Key Value
  | .empty => .empty
  | .make_tree l k v r =>
      if key < k then .make_tree (swap_delete key l) k v r
      else if setoidEq key k then
        match l, r with
        | _, .empty => l
        | .empty, _ => r
        | .make_tree ll lk lv lr, .make_tree rl rk rv rr =>
            let n := min_node (k, v) (.make_tree rl rk rv rr)
            .make_tree (.make_tree ll lk lv lr) n.1 n.2
              (delete_min (.make_tree rl rk rv rr))
      else .make_tree l k v (swap_delete key r)

theorem delete_min_empty :
    delete_min (Tree.empty : Tree Key Value) = .empty := rfl

theorem min_node_empty (n : Key × Value) :
    min_node n (Tree.empty : Tree Key Value) = n := rfl

theorem delete_min_size_1 (k : Key) (v : Value)
    (r : Tree Key Value) : delete_min (.make_tree .empty k v r) = r := rfl

theorem min_node_size_1 (n : Key × Value) (k : Key) (v : Value)
    (r : Tree Key Value) : min_node n (.make_tree .empty k v r) = (k, v) := rfl

theorem delete_min_make_tree (ll : Tree Key Value) (lk : Key)
    (lv : Value) (lr : Tree Key Value) (k : Key) (v : Value)
    (r : Tree Key Value) :
    delete_min (.make_tree (.make_tree ll lk lv lr) k v r) =
      .make_tree (delete_min (.make_tree ll lk lv lr)) k v r := rfl

theorem min_node_make_tree (n : Key × Value) (ll : Tree Key Value)
    (lk : Key) (lv : Value) (lr : Tree Key Value) (k : Key) (v : Value)
    (r : Tree Key Value) :
    min_node n (.make_tree (.make_tree ll lk lv lr) k v r) =
      min_node n (.make_tree ll lk lv lr) := rfl

theorem swap_delete_empty [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (k : Key) : swap_delete k (Tree.empty : Tree Key Value) = .empty := rfl

theorem swap_delete_make_tree_lt [LT Key] [DecidableSetoid Key]
    [DecidableLT Key]
    (k0 k : Key) (v : Value) (l r : Tree Key Value) (h : k0 < k) :
    swap_delete k0 (.make_tree l k v r) =
      .make_tree (swap_delete k0 l) k v r := by simp [swap_delete, h]

theorem swap_delete_make_tree_eq_r_empty [LT Key] [DecidableSetoid Key]
    [DecidableLT Key] (k0 k : Key) (v : Value) (l : Tree Key Value)
    (hlt : Not (k0 < k)) (heq : setoidEq k0 k) :
    swap_delete k0 (.make_tree l k v .empty) = l := by
  simp [swap_delete, hlt, heq]

theorem swap_delete_make_tree_eq_l_empty [LT Key] [DecidableSetoid Key]
    [DecidableLT Key] (k0 k : Key) (v : Value) (r : Tree Key Value)
    (hlt : Not (k0 < k)) (heq : setoidEq k0 k) :
    swap_delete k0 (.make_tree .empty k v r) = r := by
  cases r <;> simp [swap_delete, hlt, heq]

theorem swap_delete_make_tree_eq [LT Key] [DecidableSetoid Key]
    [DecidableLT Key]
    (k0 k : Key) (v : Value)
    (ll : Tree Key Value) (lk : Key) (lv : Value) (lr : Tree Key Value)
    (rl : Tree Key Value) (rk : Key) (rv : Value) (rr : Tree Key Value)
    (hlt : Not (k0 < k)) (heq : setoidEq k0 k) :
    swap_delete k0
        (.make_tree (.make_tree ll lk lv lr) k v (.make_tree rl rk rv rr)) =
      let n := min_node (k, v) (.make_tree rl rk rv rr)
      .make_tree (.make_tree ll lk lv lr) n.1 n.2
        (delete_min (.make_tree rl rk rv rr)) := by
  simp [swap_delete, hlt, heq]

theorem swap_delete_make_tree_gt [LT Key] [DecidableSetoid Key]
    [DecidableLT Key]
    (k0 k : Key) (v : Value) (l r : Tree Key Value)
    (hlt : Not (k0 < k)) (hne : setoidNe k0 k) :
    swap_delete k0 (.make_tree l k v r) =
      .make_tree l k v (swap_delete k0 r) := by
  have hne' : Not (setoidEq k0 k) := hne
  simp [swap_delete, hlt, hne']

def pushdown_left (tl : Tree Key Value) : Tree Key Value -> Tree Key Value
  | .empty => tl
  | .make_tree l k v r => .make_tree (pushdown_left tl l) k v r

def pushdown_delete [LT Key] [DecidableSetoid Key] [DecidableLT Key]
    (key : Key) : Tree Key Value -> Tree Key Value
  | .empty => .empty
  | .make_tree l k v r =>
      if key < k then .make_tree (pushdown_delete key l) k v r
      else if setoidEq key k then pushdown_left l r
      else .make_tree l k v (pushdown_delete key r)

theorem pushdown_left_empty (tl : Tree Key Value) :
    pushdown_left tl .empty = tl := rfl

theorem pushdown_delete_empty [LT Key] [DecidableSetoid Key]
    [DecidableLT Key]
    (k : Key) : pushdown_delete k (Tree.empty : Tree Key Value) = .empty := rfl

theorem pushdown_left_make_tree (tl l : Tree Key Value) (k : Key)
    (v : Value) (r : Tree Key Value) :
    pushdown_left tl (.make_tree l k v r) =
      .make_tree (pushdown_left tl l) k v r := rfl

/- Semantic lemmas independent of ordering. -/

theorem tree_pre_merge_tree_kv [DecidableSetoid Key]
    (tl tr : Tree Key Value) (k : Key) (v : Value) :
    tree_kv tl k v \/ tree_kv tr k v <->
      tree_kv (tree_pre_merge tl tr) k v := by
  symm
  induction tl with
  | empty => simp [tree_pre_merge, tree_kv]
  | make_tree l k0 v0 r ihl ihr =>
      simp only [tree_pre_merge, tree_kv]
      rw [ihr]
      constructor
      · rintro (hl | hroot | hr | ht)
        · exact Or.inl (Or.inl hl)
        · exact Or.inl (Or.inr (Or.inl hroot))
        · exact Or.inl (Or.inr (Or.inr hr))
        · exact Or.inr ht
      · rintro (hold | ht)
        · rcases hold with hl | hroot | hr
          · exact Or.inl hl
          · exact Or.inr (Or.inl hroot)
          · exact Or.inr (Or.inr (Or.inl hr))
        · exact Or.inr (Or.inr (Or.inr ht))

theorem pushdown_left_tree_kv [DecidableSetoid Key]
    (tl tr : Tree Key Value) (k : Key) (v : Value) :
    tree_kv (pushdown_left tl tr) k v <-> tree_kv tl k v \/ tree_kv tr k v := by
  induction tr with
  | empty => simp [pushdown_left, tree_kv]
  | make_tree l k0 v0 r ihl ihr =>
      simp only [pushdown_left, tree_kv]
      rw [ihl]
      constructor
      · rintro ((ht | hl) | hroot | hr)
        · exact Or.inl ht
        · exact Or.inr (Or.inl hl)
        · exact Or.inr (Or.inr (Or.inl hroot))
        · exact Or.inr (Or.inr (Or.inr hr))
      · rintro (ht | hl | hroot | hr)
        · exact Or.inl (Or.inl ht)
        · exact Or.inl (Or.inr hl)
        · exact Or.inr (Or.inl hroot)
        · exact Or.inr (Or.inr hr)

theorem min_node_same_def (d1 d2 : Key × Value) (l : Tree Key Value)
    (k : Key) (v : Value) (r : Tree Key Value) :
    min_node d1 (.make_tree l k v r) = min_node d2 (.make_tree l k v r) := by
  induction l generalizing d1 d2 k v r with
  | empty => rfl
  | make_tree ll lk lv lr ihl ihr =>
      simp only [min_node]
      exact ihl d1 d2 lk lv lr

theorem min_node_tree_kv [DecidableSetoid Key]
    (d : Key × Value) (l : Tree Key Value)
    (k : Key) (v : Value) (r : Tree Key Value) :
    let n := min_node d (.make_tree l k v r)
    tree_kv (.make_tree l k v r) n.1 n.2 := by
  induction l generalizing d k v r with
  | empty =>
      simp only [min_node, tree_kv, false_or]
      exact Or.inl ⟨setoidEq_refl k, True.intro⟩
  | make_tree ll lk lv lr ihl ihr =>
      simp only [min_node, tree_kv]
      exact Or.inl (ihl d lk lv lr)

theorem min_node_key_in [DecidableSetoid Key]
    (d : Key × Value) (l : Tree Key Value)
    (k : Key) (v : Value) (r : Tree Key Value) :
    key_set (.make_tree l k v r) (min_node d (.make_tree l k v r)).1 :=
  tree_kv_key_set (min_node_tree_kv d l k v r)

theorem delete_min_tree_kv [DecidableSetoid Key]
    (l : Tree Key Value) (k : Key) (v : Value)
    (r : Tree Key Value) (q : Key) (w : Value) :
    let n := min_node (k, v) (.make_tree l k v r)
    tree_kv (.make_tree l k v r) q w <->
      (setoidEq q n.1 /\ w = n.2) \/
        tree_kv (delete_min (.make_tree l k v r)) q w := by
  induction l generalizing k v r with
  | empty => simp [min_node, delete_min, tree_kv]
  | make_tree ll lk lv lr ihl ihr =>
      simp only [min_node, delete_min, tree_kv]
      rw [min_node_same_def (k, v) (lk, lv) ll lk lv lr]
      have hih := ihl lk lv lr
      dsimp only at hih
      change
        (tree_kv (.make_tree ll lk lv lr) q w \/
          (setoidEq q k /\ w = v) \/
          tree_kv r q w) <->
        (setoidEq q (min_node (lk, lv) (.make_tree ll lk lv lr)).1 /\
            w = (min_node (lk, lv) (.make_tree ll lk lv lr)).2) \/
          tree_kv (delete_min (.make_tree ll lk lv lr)) q w \/
          (setoidEq q k /\ w = v) \/ tree_kv r q w
      rw [hih]
      constructor
      · rintro ((hmin | hdel) | hroot | hr)
        · exact Or.inl hmin
        · exact Or.inr (Or.inl hdel)
        · exact Or.inr (Or.inr (Or.inl hroot))
        · exact Or.inr (Or.inr (Or.inr hr))
      · rintro (hmin | hdel | hroot | hr)
        · exact Or.inl (Or.inl hmin)
        · exact Or.inl (Or.inr hdel)
        · exact Or.inr (Or.inl hroot)
        · exact Or.inr (Or.inr hr)

namespace IntFacts

attribute [local simp] int_setoidEq_iff int_setoidNe_iff

theorem insert_key_set (k : Int) (v : Value) (tr : Tree Int Value) (q : Int) :
    key_set (insert k v tr) q <-> q = k \/ key_set tr q := by
  induction tr with
  | empty =>
      simp [insert, key_set, set_union, Sets_singleton_setoid, empty_set]
  | make_tree l k0 v0 r ihl ihr =>
      rcases Int.lt_trichotomy k k0 with h | h | h
      · simp [insert, key_set, set_union, Sets_singleton_setoid, h, ihl,
          or_assoc, or_left_comm]
      · subst k0
        simp [insert, key_set, set_union, Sets_singleton_setoid,
          or_left_comm]
      · have hnlt : Not (k < k0) := by omega
        have hne : k ≠ k0 := by omega
        simp [insert, key_set, set_union, Sets_singleton_setoid, hnlt, hne, ihr,
          or_left_comm]

theorem tree_pre_merge_key_set (tl tr : Tree Int Value) (q : Int) :
    key_set (tree_pre_merge tl tr) q <-> key_set tl q \/ key_set tr q := by
  induction tl with
  | empty => simp [tree_pre_merge, key_set, empty_set]
  | make_tree l k v r ihl ihr =>
      simp only [tree_pre_merge, key_set, set_union, Sets_singleton_setoid, ihr,
        int_setoidEq_iff]
      constructor
      · rintro (hl | hk | hr | htr)
        · exact Or.inl (Or.inl hl)
        · exact Or.inl (Or.inr (Or.inl hk))
        · exact Or.inl (Or.inr (Or.inr hr))
        · exact Or.inr htr
      · rintro ((hl | hk | hr) | htr)
        · exact Or.inl hl
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr (Or.inl hr))
        · exact Or.inr (Or.inr (Or.inr htr))

theorem insert_SearchTree (tr : Tree Int Value) (k : Int) (v : Value)
    (hst : SearchTree tr) : SearchTree (insert k v tr) := by
  induction tr with
  | empty => simp [insert, SearchTree, keys_key_lt, key_keys_lt, key_set, empty_set]
  | make_tree l k0 v0 r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      rcases Int.lt_trichotomy k k0 with h | h | h
      · simp only [insert, h, if_pos, SearchTree, int_setoidEq_iff]
        refine ⟨?_, hkr, ihl hsl, hsr⟩
        intro q hq
        rw [insert_key_set] at hq
        rcases hq with rfl | hq
        · exact h
        · exact hlk q hq
      · subst k0
        simp [insert, SearchTree, hlk, hkr, hsl, hsr]
      · have hnlt : Not (k < k0) := by omega
        have hne : k ≠ k0 := by omega
        simp only [insert, hnlt, hne, if_false, SearchTree, int_setoidEq_iff]
        refine ⟨hlk, ?_, hsl, ihr hsr⟩
        intro q hq
        rw [insert_key_set] at hq
        rcases hq with rfl | hq
        · exact h
        · exact hkr q hq

theorem insert_tree_kv (tr : Tree Int Value) (k : Int) (v : Value)
    (hst : SearchTree tr) (q : Int) (w : Value) :
    tree_kv (insert k v tr) q w <->
      (q = k /\ w = v) \/ (q ≠ k /\ tree_kv tr q w) := by
  induction tr with
  | empty => simp [insert, tree_kv]
  | make_tree l k0 v0 r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      rcases Int.lt_trichotomy k k0 with h | h | h
      · have hk0 : k ≠ k0 := by omega
        have hr_ne : tree_kv r q w -> q ≠ k := by
          intro hkv heq
          subst q
          have hkey := tree_kv_key_set hkv
          have := hkr k hkey
          omega
        simp only [insert, h, if_pos, tree_kv, int_setoidEq_iff]
        rw [ihl hsl]
        constructor <;> intro hgoal
        · rcases hgoal with hnew | hold | hr
          · exact hnew.elim Or.inl (fun hx => Or.inr ⟨hx.1, Or.inl hx.2⟩)
          · exact Or.inr ⟨by omega, Or.inr (Or.inl hold)⟩
          · exact Or.inr ⟨hr_ne hr, Or.inr (Or.inr hr)⟩
        · rcases hgoal with hnew | ⟨hne, hold⟩
          · exact Or.inl (Or.inl hnew)
          · rcases hold with hl | hroot | hr
            · exact Or.inl (Or.inr ⟨hne, hl⟩)
            · exact Or.inr (Or.inl hroot)
            · exact Or.inr (Or.inr hr)
      · subst k0
        simp only [insert, Int.lt_irrefl, if_false, if_pos, tree_kv,
          int_setoidEq_iff]
        have hl_ne : tree_kv l q w -> q ≠ k := by
          intro hkv heq
          subst q
          have hkey := tree_kv_key_set hkv
          have := hlk k hkey
          omega
        have hr_ne : tree_kv r q w -> q ≠ k := by
          intro hkv heq
          subst q
          have hkey := tree_kv_key_set hkv
          have := hkr k hkey
          omega
        constructor <;> intro hgoal
        · rcases hgoal with hl | hroot | hr
          · exact Or.inr ⟨hl_ne hl, Or.inl hl⟩
          · exact Or.inl hroot
          · exact Or.inr ⟨hr_ne hr, Or.inr (Or.inr hr)⟩
        · rcases hgoal with hroot | ⟨hne, hold⟩
          · exact Or.inr (Or.inl hroot)
          · rcases hold with hl | hroot | hr
            · exact Or.inl hl
            · exact (hne hroot.1).elim
            · exact Or.inr (Or.inr hr)
      · have hnlt : Not (k < k0) := by omega
        have hne0 : k ≠ k0 := by omega
        have hl_ne : tree_kv l q w -> q ≠ k := by
          intro hkv heq
          subst q
          have hkey := tree_kv_key_set hkv
          have := hlk k hkey
          omega
        simp only [insert, hnlt, hne0, if_false, tree_kv, int_setoidEq_iff]
        rw [ihr hsr]
        constructor <;> intro hgoal
        · rcases hgoal with hl | hroot | hnew
          · exact Or.inr ⟨hl_ne hl, Or.inl hl⟩
          · exact Or.inr ⟨by omega, Or.inr (Or.inl hroot)⟩
          · exact hnew.elim Or.inl (fun hx => Or.inr ⟨hx.1, Or.inr (Or.inr hx.2)⟩)
        · rcases hgoal with hnew | ⟨hne, hold⟩
          · exact Or.inr (Or.inr (Or.inl hnew))
          · rcases hold with hl | hroot | hr
            · exact Or.inl hl
            · exact Or.inr (Or.inl hroot)
            · exact Or.inr (Or.inr (Or.inr ⟨hne, hr⟩))

theorem insert_Abs (tr : Tree Int Value) (m : Mapping Int Value)
    (k : Int) (v : Value) (hst : SearchTree tr) (habs : Abs tr m) :
    Abs (insert k v tr) (Map.insert k v m) := by
  intro q w
  rw [Map.insert_iff, habs, insert_tree_kv tr k v hst q w]
  simp only [int_setoidEq_iff, int_setoidNe_iff]

theorem delete_tree_kv (tr : Tree Int Value) (k : Int)
    (hst : SearchTree tr) (q : Int) (w : Value) :
    tree_kv (delete k tr) q w <-> q ≠ k /\ tree_kv tr q w := by
  induction tr with
  | empty => simp [delete, tree_kv]
  | make_tree l k0 v0 r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      rcases Int.lt_trichotomy k k0 with h | h | h
      · have hroot_ne : q = k0 -> q ≠ k := by omega
        have hr_ne : tree_kv r q w -> q ≠ k := by
          intro hkv heq
          subst q
          have hkey := tree_kv_key_set hkv
          have := hkr k hkey
          omega
        simp only [delete, h, if_pos, tree_kv, int_setoidEq_iff]
        rw [ihl hsl]
        constructor
        · rintro (⟨hne, hl⟩ | hroot | hr)
          · exact ⟨hne, Or.inl hl⟩
          · exact ⟨hroot_ne hroot.1, Or.inr (Or.inl hroot)⟩
          · exact ⟨hr_ne hr, Or.inr (Or.inr hr)⟩
        · rintro ⟨hne, hl | hroot | hr⟩
          · exact Or.inl ⟨hne, hl⟩
          · exact Or.inr (Or.inl hroot)
          · exact Or.inr (Or.inr hr)
      · subst k0
        have hl_ne : tree_kv l q w -> q ≠ k := by
          intro hkv heq
          subst q
          have hkey := tree_kv_key_set hkv
          have := hlk k hkey
          omega
        have hr_ne : tree_kv r q w -> q ≠ k := by
          intro hkv heq
          subst q
          have hkey := tree_kv_key_set hkv
          have := hkr k hkey
          omega
        simp only [delete, Int.lt_irrefl, if_false, if_pos, int_setoidEq_iff]
        rw [← tree_pre_merge_tree_kv]
        constructor
        · rintro (hl | hr)
          · exact ⟨hl_ne hl, Or.inl hl⟩
          · exact ⟨hr_ne hr, Or.inr (Or.inr hr)⟩
        · rintro ⟨hne, hl | hroot | hr⟩
          · exact Or.inl hl
          · exact (hne hroot.1).elim
          · exact Or.inr hr
      · have hnlt : Not (k < k0) := by omega
        have hne0 : k ≠ k0 := by omega
        have hl_ne : tree_kv l q w -> q ≠ k := by
          intro hkv heq
          subst q
          have hkey := tree_kv_key_set hkv
          have := hlk k hkey
          omega
        have hroot_ne : q = k0 -> q ≠ k := by omega
        simp only [delete, hnlt, hne0, if_false, tree_kv, int_setoidEq_iff]
        rw [ihr hsr]
        constructor
        · rintro (hl | hroot | ⟨hne, hr⟩)
          · exact ⟨hl_ne hl, Or.inl hl⟩
          · exact ⟨hroot_ne hroot.1, Or.inr (Or.inl hroot)⟩
          · exact ⟨hne, Or.inr (Or.inr hr)⟩
        · rintro ⟨hne, hl | hroot | hr⟩
          · exact Or.inl hl
          · exact Or.inr (Or.inl hroot)
          · exact Or.inr (Or.inr ⟨hne, hr⟩)

theorem delete_key_set (tr : Tree Int Value) (k : Int) (hst : SearchTree tr)
    (q : Int) : key_set (delete k tr) q <-> q ≠ k /\ key_set tr q := by
  constructor
  · intro hq
    rcases key_set_tree_kv_exists.mp hq with ⟨w, hkv⟩
    rw [delete_tree_kv tr k hst q w] at hkv
    exact ⟨hkv.1, tree_kv_key_set hkv.2⟩
  · rintro ⟨hne, hq⟩
    rcases key_set_tree_kv_exists.mp hq with ⟨w, hkv⟩
    apply key_set_tree_kv_exists.mpr
    exact ⟨w, (delete_tree_kv tr k hst q w).mpr ⟨hne, hkv⟩⟩

theorem tree_pre_merge_SearchTree (tl tr : Tree Int Value)
    (hall : keys_keys_lt (key_set tl) (key_set tr))
    (hstl : SearchTree tl) (hstr : SearchTree tr) :
    SearchTree (tree_pre_merge tl tr) := by
  induction tl with
  | empty => simpa [tree_pre_merge] using hstr
  | make_tree l k v r ihl ihr =>
      rcases hstl with ⟨hlk, hkr, hsl, hsr⟩
      simp only [tree_pre_merge, SearchTree]
      refine ⟨hlk, ?_, hsl, ?_⟩
      · intro q hq
        rw [tree_pre_merge_key_set] at hq
        rcases hq with hq | hq
        · exact hkr q hq
        · exact hall k q (Or.inr (Or.inl rfl)) hq
      · apply ihr
        · intro a b ha hb
          exact hall a b (Or.inr (Or.inr ha)) hb
        · exact hsr

theorem delete_SearchTree (tr : Tree Int Value) (k : Int)
    (hst : SearchTree tr) : SearchTree (delete k tr) := by
  induction tr with
  | empty => simpa [delete] using (SearchTree_empty (Key := Int) (Value := Value))
  | make_tree l k0 v0 r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      rcases Int.lt_trichotomy k k0 with h | h | h
      · simp only [delete, h, if_pos, SearchTree, int_setoidEq_iff]
        refine ⟨?_, hkr, ihl hsl, hsr⟩
        intro q hq
        rw [delete_key_set l k hsl] at hq
        exact hlk q hq.2
      · subst k0
        simp only [delete, Int.lt_irrefl, if_false, if_pos, int_setoidEq_iff]
        apply tree_pre_merge_SearchTree l r
        · intro a b ha hb
          have hal := hlk a ha
          have hbr := hkr b hb
          omega
        · exact hsl
        · exact hsr
      · have hnlt : Not (k < k0) := by omega
        have hne : k ≠ k0 := by omega
        simp only [delete, hnlt, hne, if_false, SearchTree, int_setoidEq_iff]
        refine ⟨hlk, ?_, hsl, ihr hsr⟩
        intro q hq
        rw [delete_key_set r k hsr] at hq
        exact hkr q hq.2

theorem delete_Abs (tr : Tree Int Value) (m : Mapping Int Value)
    (k : Int) (hst : SearchTree tr) (habs : Abs tr m) :
    Abs (delete k tr) (Map.delete k m) := by
  intro q w
  rw [Map.delete_iff, habs, delete_tree_kv tr k hst q w]
  simp only [int_setoidNe_iff]

theorem delete_min_key_set_subset (l : Tree Int Value) (k : Int) (v : Value)
    (r : Tree Int Value) (q : Int)
    (hq : key_set (delete_min (.make_tree l k v r)) q) :
    key_set (.make_tree l k v r) q := by
  rcases key_set_tree_kv_exists.mp hq with ⟨w, hkv⟩
  apply key_set_tree_kv_exists.mpr
  exact ⟨w, (delete_min_tree_kv l k v r q w).mpr (Or.inr hkv)⟩

theorem delete_min_Searchtree (tr : Tree Int Value) (hst : SearchTree tr) :
    SearchTree (delete_min tr) := by
  induction tr with
  | empty => exact hst
  | make_tree l k v r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      cases l with
      | empty => simpa [delete_min] using hsr
      | make_tree ll lk lv lr =>
          simp only [delete_min, SearchTree]
          refine ⟨?_, hkr, ihl hsl, hsr⟩
          intro q hq
          apply hlk q
          exact delete_min_key_set_subset ll lk lv lr q hq

theorem min_node_lt (l : Tree Int Value) (k : Int) (v : Value)
    (r : Tree Int Value) (hst : SearchTree (.make_tree l k v r)) :
    key_keys_lt (min_node (k, v) (.make_tree l k v r)).1
      (key_set (delete_min (.make_tree l k v r))) := by
  induction l generalizing k v r with
  | empty =>
      simpa [min_node, delete_min] using hst.2.1
  | make_tree ll lk lv lr ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      have hsame := min_node_same_def (k, v) (lk, lv) ll lk lv lr
      simp only [min_node, delete_min]
      rw [hsame]
      intro q hq
      rcases hq with hq | hq | hq
      · exact ihl lk lv lr hsl q hq
      · subst q
        apply hlk
        exact min_node_key_in (lk, lv) ll lk lv lr
      · have hminroot : (min_node (lk, lv) (.make_tree ll lk lv lr)).1 < k :=
          hlk _ (min_node_key_in (lk, lv) ll lk lv lr)
        have hrootq := hkr q hq
        omega

theorem swap_delete_tree_kv (tr : Tree Int Value) (k : Int)
    (hst : SearchTree tr) (q : Int) (w : Value) :
    tree_kv (swap_delete k tr) q w <-> q ≠ k /\ tree_kv tr q w := by
  induction tr with
  | empty => simp [swap_delete, tree_kv]
  | make_tree l k0 v0 r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      rcases Int.lt_trichotomy k k0 with h | h | h
      · have hroot_ne : q = k0 -> q ≠ k := by omega
        have hr_ne : tree_kv r q w -> q ≠ k := by
          intro hkv heq
          subst q
          have := hkr k (tree_kv_key_set hkv)
          omega
        simp only [swap_delete, h, if_pos, tree_kv, int_setoidEq_iff]
        rw [ihl hsl]
        constructor
        · rintro (⟨hne, hl⟩ | hroot | hr)
          · exact ⟨hne, Or.inl hl⟩
          · exact ⟨hroot_ne hroot.1, Or.inr (Or.inl hroot)⟩
          · exact ⟨hr_ne hr, Or.inr (Or.inr hr)⟩
        · rintro ⟨hne, hl | hroot | hr⟩
          · exact Or.inl ⟨hne, hl⟩
          · exact Or.inr (Or.inl hroot)
          · exact Or.inr (Or.inr hr)
      · subst k0
        have hl_ne : tree_kv l q w -> q ≠ k := by
          intro hkv heq
          subst q
          have := hlk k (tree_kv_key_set hkv)
          omega
        have hr_ne : tree_kv r q w -> q ≠ k := by
          intro hkv heq
          subst q
          have := hkr k (tree_kv_key_set hkv)
          omega
        cases l with
        | empty =>
            cases r with
            | empty =>
                simp only [swap_delete, Int.lt_irrefl, if_false, if_pos,
                  int_setoidEq_iff]
                rw [tree_kv_empty_iff]
                rw [tree_kv_make_tree_iff]
                simp only [tree_kv_empty_iff, false_or, or_false,
                  int_setoidEq_iff]
                change False <-> q ≠ k /\ (q = k /\ w = v0)
                constructor
                · exact False.elim
                · rintro ⟨hne, heq, _⟩
                  exact (hne heq).elim
            | make_tree rl rk rv rr =>
                simp only [swap_delete, Int.lt_irrefl, if_false, if_pos,
                  int_setoidEq_iff]
                rw [tree_kv_make_tree_iff (l := Tree.empty) (k := k)
                  (v := v0) (r := .make_tree rl rk rv rr)]
                simp only [tree_kv_empty_iff, false_or, int_setoidEq_iff]
                change tree_kv (.make_tree rl rk rv rr) q w <->
                  q ≠ k /\ ((q = k /\ w = v0) \/
                    tree_kv (.make_tree rl rk rv rr) q w)
                constructor
                · intro hnew
                  exact ⟨hr_ne hnew, Or.inr hnew⟩
                · rintro ⟨hne, hroot | hright⟩
                  · exact (hne hroot.1).elim
                  · exact hright
        | make_tree ll lk lv lr =>
            cases r with
            | empty =>
                simp only [swap_delete, Int.lt_irrefl, if_false, if_pos,
                  int_setoidEq_iff]
                rw [tree_kv_make_tree_iff (l := .make_tree ll lk lv lr)
                  (k := k) (v := v0) (r := Tree.empty)]
                simp only [tree_kv_empty_iff, or_false, int_setoidEq_iff]
                change tree_kv (.make_tree ll lk lv lr) q w <->
                  q ≠ k /\ (tree_kv (.make_tree ll lk lv lr) q w \/
                    (q = k /\ w = v0))
                constructor
                · intro hnew
                  exact ⟨hl_ne hnew, Or.inl hnew⟩
                · rintro ⟨hne, hleft | hroot⟩
                  · exact hleft
                  · exact (hne hroot.1).elim
            | make_tree rl rk rv rr =>
                have hsame := min_node_same_def (k, v0) (rk, rv) rl rk rv rr
                simp only [swap_delete, Int.lt_irrefl, if_false, if_pos,
                  int_setoidEq_iff]
                rw [hsame]
                have hdm := delete_min_tree_kv rl rk rv rr q w
                dsimp only at hdm
                rw [tree_kv_make_tree_iff
                  (l := .make_tree ll lk lv lr)
                  (k := (min_node (rk, rv) (.make_tree rl rk rv rr)).1)
                  (v := (min_node (rk, rv) (.make_tree rl rk rv rr)).2)
                  (r := delete_min (.make_tree rl rk rv rr))]
                rw [tree_kv_make_tree_iff (l := .make_tree ll lk lv lr)
                  (k := k) (v := v0) (r := .make_tree rl rk rv rr)]
                change
                  (tree_kv (.make_tree ll lk lv lr) q w \/
                    (q = (min_node (rk, rv) (.make_tree rl rk rv rr)).1 /\
                      w = (min_node (rk, rv) (.make_tree rl rk rv rr)).2) \/
                    tree_kv (delete_min (.make_tree rl rk rv rr)) q w) <->
                  q ≠ k /\
                    (tree_kv (.make_tree ll lk lv lr) q w \/
                      (q = k /\ w = v0) \/
                      tree_kv (.make_tree rl rk rv rr) q w)
                constructor
                · rintro (hleft | hmin | hdel)
                  · exact ⟨hl_ne hleft, Or.inl hleft⟩
                  · have hright := hdm.mpr (Or.inl hmin)
                    exact ⟨hr_ne hright, Or.inr (Or.inr hright)⟩
                  · have hright := hdm.mpr (Or.inr hdel)
                    exact ⟨hr_ne hright, Or.inr (Or.inr hright)⟩
                · rintro ⟨hne, hleft | hroot | hright⟩
                  · exact Or.inl hleft
                  · exact (hne hroot.1).elim
                  · rcases hdm.mp hright with hmin | hdel
                    · exact Or.inr (Or.inl hmin)
                    · exact Or.inr (Or.inr hdel)
      · have hnlt : Not (k < k0) := by omega
        have hne0 : k ≠ k0 := by omega
        have hl_ne : tree_kv l q w -> q ≠ k := by
          intro hkv heq
          subst q
          have := hlk k (tree_kv_key_set hkv)
          omega
        have hroot_ne : q = k0 -> q ≠ k := by omega
        simp only [swap_delete, hnlt, hne0, if_false, tree_kv,
          int_setoidEq_iff]
        rw [ihr hsr]
        constructor
        · rintro (hl | hroot | ⟨hne, hr⟩)
          · exact ⟨hl_ne hl, Or.inl hl⟩
          · exact ⟨hroot_ne hroot.1, Or.inr (Or.inl hroot)⟩
          · exact ⟨hne, Or.inr (Or.inr hr)⟩
        · rintro ⟨hne, hl | hroot | hr⟩
          · exact Or.inl hl
          · exact Or.inr (Or.inl hroot)
          · exact Or.inr (Or.inr ⟨hne, hr⟩)

theorem swap_delete_key_set (tr : Tree Int Value) (k : Int)
    (hst : SearchTree tr) (q : Int) :
    key_set (swap_delete k tr) q <-> q ≠ k /\ key_set tr q := by
  constructor
  · intro hq
    rcases key_set_tree_kv_exists.mp hq with ⟨w, hkv⟩
    rw [swap_delete_tree_kv tr k hst q w] at hkv
    exact ⟨hkv.1, tree_kv_key_set hkv.2⟩
  · rintro ⟨hne, hq⟩
    rcases key_set_tree_kv_exists.mp hq with ⟨w, hkv⟩
    apply key_set_tree_kv_exists.mpr
    exact ⟨w, (swap_delete_tree_kv tr k hst q w).mpr ⟨hne, hkv⟩⟩

theorem swap_delete_SearchTree (tr : Tree Int Value) (k : Int)
    (hst : SearchTree tr) : SearchTree (swap_delete k tr) := by
  induction tr with
  | empty => exact hst
  | make_tree l k0 v0 r ihl ihr =>
      rcases hst with ⟨hlk, hkr, hsl, hsr⟩
      rcases Int.lt_trichotomy k k0 with h | h | h
      · simp only [swap_delete, h, if_pos, SearchTree, int_setoidEq_iff]
        refine ⟨?_, hkr, ihl hsl, hsr⟩
        intro q hq
        rw [swap_delete_key_set l k hsl] at hq
        exact hlk q hq.2
      · subst k0
        cases l with
        | empty =>
            cases r <;> simp [swap_delete] at hsr ⊢ <;> assumption
        | make_tree ll lk lv lr =>
            cases r with
            | empty => simpa [swap_delete] using hsl
            | make_tree rl rk rv rr =>
                have hsame := min_node_same_def (k, v0) (rk, rv) rl rk rv rr
                simp only [swap_delete, Int.lt_irrefl, if_false, if_pos,
                  SearchTree, int_setoidEq_iff]
                rw [hsame]
                refine ⟨?_, min_node_lt rl rk rv rr hsr, hsl,
                  delete_min_Searchtree _ hsr⟩
                intro q hq
                have hleftroot := hlk q hq
                have hminright := hkr _ (min_node_key_in (rk, rv) rl rk rv rr)
                omega
      · have hnlt : Not (k < k0) := by omega
        have hne : k ≠ k0 := by omega
        simp only [swap_delete, hnlt, hne, if_false, SearchTree,
          int_setoidEq_iff]
        refine ⟨hlk, ?_, hsl, ihr hsr⟩
        intro q hq
        rw [swap_delete_key_set r k hsr] at hq
        exact hkr q hq.2

theorem swap_delete_Abs (tr : Tree Int Value) (m : Mapping Int Value)
    (k : Int) (hst : SearchTree tr) (habs : Abs tr m) :
    Abs (swap_delete k tr) (Map.delete k m) := by
  intro q w
  rw [Map.delete_iff, habs, swap_delete_tree_kv tr k hst q w]
  simp only [int_setoidNe_iff]

end IntFacts

end AUXLib.BinaryTree
