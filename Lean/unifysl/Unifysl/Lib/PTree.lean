universe u

namespace PTree

inductive positive : Type where
  | xH : positive
  | xO : positive -> positive
  | xI : positive -> positive
deriving DecidableEq, Repr

export positive (xH xO xI)

inductive tree (A : Type u) : Type u where
  | Leaf : tree A
  | Node : tree A -> Option A -> tree A -> tree A
deriving Repr

export tree (Leaf Node)

def empty {A : Type u} : tree A :=
  Leaf

def get_rec' (A : Type u) : positive -> tree A -> (tree A -> tree A) -> tree A
  | xH, m, f => f m
  | xO ii, m, f =>
      get_rec' A ii m (fun m0 =>
        match f m0 with
        | Leaf => Leaf
        | Node l _ _ => l)
  | xI ii, m, f =>
      get_rec' A ii m (fun m0 =>
        match f m0 with
        | Leaf => Leaf
        | Node _ _ r => r)

def get_rec (A : Type u) (i : positive) (m : tree A) : Option A :=
  match get_rec' A i m (fun m0 => m0) with
  | Leaf => none
  | Node _ o _ => o

def set_rec' (A : Type u) : positive -> A -> tree A -> (tree A -> tree A) -> tree A
  | xH, v, Leaf, f => f (Node Leaf (some v) Leaf)
  | xO ii, v, Leaf, f =>
      set_rec' A ii v Leaf (fun hole => f (Node hole none Leaf))
  | xI ii, v, Leaf, f =>
      set_rec' A ii v Leaf (fun hole => f (Node Leaf none hole))
  | xH, v, Node l _ r, f => f (Node l (some v) r)
  | xO ii, v, Node l o r, f =>
      set_rec' A ii v l (fun hole => f (Node hole o r))
  | xI ii, v, Node l o r, f =>
      set_rec' A ii v r (fun hole => f (Node l o hole))

def set_rec (A : Type u) (i : positive) (v : A) (m : tree A) : tree A :=
  set_rec' A i v m (fun hole => hole)

def xelements (A : Type u) : tree A -> List A -> List A
  | Leaf, k => k
  | Node l none r, k => xelements A l (xelements A r k)
  | Node l (some x) r, k => xelements A l (x :: xelements A r k)

def elements (A : Type u) (m : tree A) : List A :=
  xelements A m []

private theorem get_rec'_apply :
    forall (A : Type u) (p : positive) (m : tree A) (f : tree A -> tree A),
      get_rec' A p m f = get_rec' A p (f m) (fun m0 => m0) := by
  intro A p
  induction p with
  | xH =>
      intro m f
      rfl
  | xO p ih =>
      intro m f
      calc
        get_rec' A (xO p) m f
            = get_rec' A p m
                (fun m0 =>
                  match f m0 with
                  | Leaf => Leaf
                  | Node l _ _ => l) := rfl
        _ = get_rec' A p
              ((fun m0 =>
                match f m0 with
                | Leaf => Leaf
                | Node l _ _ => l) m)
              (fun m0 => m0) := ih _ _
        _ = get_rec' A p (f m)
              (fun m0 =>
                match m0 with
                | Leaf => Leaf
                | Node l _ _ => l) := by
              rw [ih (f m)
                (fun m0 =>
                  match m0 with
                  | Leaf => Leaf
                  | Node l _ _ => l)]
        _ = get_rec' A (xO p) (f m) (fun m0 => m0) := rfl
  | xI p ih =>
      intro m f
      calc
        get_rec' A (xI p) m f
            = get_rec' A p m
                (fun m0 =>
                  match f m0 with
                  | Leaf => Leaf
                  | Node _ _ r => r) := rfl
        _ = get_rec' A p
              ((fun m0 =>
                match f m0 with
                | Leaf => Leaf
                | Node _ _ r => r) m)
              (fun m0 => m0) := ih _ _
        _ = get_rec' A p (f m)
              (fun m0 =>
                match m0 with
                | Leaf => Leaf
                | Node _ _ r => r) := by
              rw [ih (f m)
                (fun m0 =>
                  match m0 with
                  | Leaf => Leaf
                  | Node _ _ r => r)]
        _ = get_rec' A (xI p) (f m) (fun m0 => m0) := rfl

private theorem get_rec'_empty :
    forall (A : Type u) (p : positive) (f : tree A -> tree A),
      f Leaf = Leaf ->
      get_rec' A p Leaf f = Leaf := by
  intro A p
  induction p with
  | xH =>
      intro f hf
      exact hf
  | xO p ih =>
      intro f hf
      apply ih
      rw [hf]
  | xI p ih =>
      intro f hf
      apply ih
      rw [hf]

private theorem set_rec'_apply :
    forall (A : Type u) (p : positive) (x : A) (m : tree A) (f : tree A -> tree A),
      set_rec' A p x m f = f (set_rec A p x m) := by
  intro A p
  induction p with
  | xH =>
      intro x m f
      cases m <;> rfl
  | xO p ih =>
      intro x m f
      cases m with
      | Leaf =>
          calc
            set_rec' A (xO p) x Leaf f
                = set_rec' A p x Leaf (fun hole => f (Node hole none Leaf)) := rfl
            _ = f (Node (set_rec A p x Leaf) none Leaf) := ih _ _ _
            _ = f (set_rec A (xO p) x Leaf) := by
                  rw [show set_rec A (xO p) x Leaf =
                    set_rec' A p x Leaf (fun hole => Node hole none Leaf) from rfl]
                  rw [ih]
      | Node l o r =>
          calc
            set_rec' A (xO p) x (Node l o r) f
                = set_rec' A p x l (fun hole => f (Node hole o r)) := rfl
            _ = f (Node (set_rec A p x l) o r) := ih _ _ _
            _ = f (set_rec A (xO p) x (Node l o r)) := by
                  rw [show set_rec A (xO p) x (Node l o r) =
                    set_rec' A p x l (fun hole => Node hole o r) from rfl]
                  rw [ih]
  | xI p ih =>
      intro x m f
      cases m with
      | Leaf =>
          calc
            set_rec' A (xI p) x Leaf f
                = set_rec' A p x Leaf (fun hole => f (Node Leaf none hole)) := rfl
            _ = f (Node Leaf none (set_rec A p x Leaf)) := ih _ _ _
            _ = f (set_rec A (xI p) x Leaf) := by
                  rw [show set_rec A (xI p) x Leaf =
                    set_rec' A p x Leaf (fun hole => Node Leaf none hole) from rfl]
                  rw [ih]
      | Node l o r =>
          calc
            set_rec' A (xI p) x (Node l o r) f
                = set_rec' A p x r (fun hole => f (Node l o hole)) := rfl
            _ = f (Node l o (set_rec A p x r)) := ih _ _ _
            _ = f (set_rec A (xI p) x (Node l o r)) := by
                  rw [show set_rec A (xI p) x (Node l o r) =
                    set_rec' A p x r (fun hole => Node l o hole) from rfl]
                  rw [ih]

theorem get_empty :
    forall (A : Type u) (p : positive),
      get_rec A p (empty : tree A) = none := by
  intro A p
  unfold get_rec empty
  rw [get_rec'_empty]
  rfl

theorem elements_set_empty :
    forall (A : Type u) (p : positive) (x : A),
      elements A (set_rec A p x empty) = x :: [] := by
  intro A p
  induction p with
  | xH =>
      intro x
      rfl
  | xO p ih =>
      intro x
      unfold empty
      change elements A (set_rec' A p x Leaf (fun hole => Node hole none Leaf)) = x :: []
      rw [set_rec'_apply]
      change elements A (set_rec A p x Leaf) = x :: []
      exact ih x
  | xI p ih =>
      intro x
      unfold empty
      change elements A (set_rec' A p x Leaf (fun hole => Node Leaf none hole)) = x :: []
      rw [set_rec'_apply]
      change elements A (set_rec A p x Leaf) = x :: []
      exact ih x

theorem get_node0 :
    forall (A : Type u) (p : positive) (m1 : tree A) (o : Option A) (m2 : tree A),
      get_rec A (xO p) (Node m1 o m2) = get_rec A p m1 := by
  intro A p m1 o m2
  unfold get_rec
  change (match get_rec' A p (Node m1 o m2)
      (fun m0 =>
        match m0 with
        | Leaf => Leaf
        | Node l _ _ => l) with
    | Leaf => none
    | Node _ o _ => o) =
    match get_rec' A p m1 (fun m0 => m0) with
    | Leaf => none
    | Node _ o _ => o
  rw [get_rec'_apply]

theorem get_node1 :
    forall (A : Type u) (p : positive) (m1 : tree A) (o : Option A) (m2 : tree A),
      get_rec A (xI p) (Node m1 o m2) = get_rec A p m2 := by
  intro A p m1 o m2
  unfold get_rec
  change (match get_rec' A p (Node m1 o m2)
      (fun m0 =>
        match m0 with
        | Leaf => Leaf
        | Node _ _ r => r) with
    | Leaf => none
    | Node _ o _ => o) =
    match get_rec' A p m2 (fun m0 => m0) with
    | Leaf => none
    | Node _ o _ => o
  rw [get_rec'_apply]

theorem set_node0 :
    forall (A : Type u) (p : positive) (x : A) (m1 : tree A) (o : Option A) (m2 : tree A),
      set_rec A (xO p) x (Node m1 o m2) = Node (set_rec A p x m1) o m2 := by
  intro A p x m1 o m2
  change set_rec' A p x m1 (fun hole => Node hole o m2) =
    Node (set_rec A p x m1) o m2
  rw [set_rec'_apply]

theorem set_node1 :
    forall (A : Type u) (p : positive) (x : A) (m1 : tree A) (o : Option A) (m2 : tree A),
      set_rec A (xI p) x (Node m1 o m2) = Node m1 o (set_rec A p x m2) := by
  intro A p x m1 o m2
  change set_rec' A p x m2 (fun hole => Node m1 o hole) =
    Node m1 o (set_rec A p x m2)
  rw [set_rec'_apply]

theorem xelements_append :
    forall (A : Type u) (m : tree A) (l1 l2 : List A),
      xelements A m (l1 ++ l2) = xelements A m l1 ++ l2 := by
  intro A m
  induction m with
  | Leaf =>
      intro l1 l2
      rfl
  | Node l o r ihl ihr =>
      intro l1 l2
      cases o with
      | none =>
          calc
            xelements A (Node l none r) (l1 ++ l2)
                = xelements A l (xelements A r (l1 ++ l2)) := rfl
            _ = xelements A l (xelements A r l1 ++ l2) := by rw [ihr]
            _ = xelements A l (xelements A r l1) ++ l2 := ihl _ _
            _ = xelements A (Node l none r) l1 ++ l2 := rfl
      | some x =>
          calc
            xelements A (Node l (some x) r) (l1 ++ l2)
                = xelements A l (x :: xelements A r (l1 ++ l2)) := rfl
            _ = xelements A l (x :: (xelements A r l1 ++ l2)) := by rw [ihr]
            _ = xelements A l ((x :: xelements A r l1) ++ l2) := rfl
            _ = xelements A l (x :: xelements A r l1) ++ l2 := ihl _ _
            _ = xelements A (Node l (some x) r) l1 ++ l2 := rfl

private theorem xelements_elements_append :
    forall (A : Type u) (m : tree A) (l : List A),
      xelements A m l = elements A m ++ l := by
  intro A m l
  unfold elements
  simpa using (xelements_append A m [] l)

private theorem elements_node_none :
    forall (A : Type u) (l r : tree A),
      elements A (Node l none r) = elements A l ++ elements A r := by
  intro A l r
  change xelements A l (elements A r) = elements A l ++ elements A r
  rw [xelements_elements_append]

private theorem elements_node_some :
    forall (A : Type u) (l : tree A) (x : A) (r : tree A),
      elements A (Node l (some x) r) = elements A l ++ x :: elements A r := by
  intro A l x r
  change xelements A l (x :: elements A r) = elements A l ++ x :: elements A r
  rw [xelements_elements_append]

theorem elements_set_none :
    forall (A : Type u) (p : positive) (x : A) (m : tree A),
      get_rec A p m = none ->
      exists l1 l2 : List A,
        elements A m = l1 ++ l2 /\
        elements A (set_rec A p x m) = l1 ++ (x :: l2) := by
  intro A p
  induction p with
  | xH =>
      intro x m h
      cases m with
      | Leaf =>
          exists []
          exists []
      | Node l o r =>
          cases o with
          | none =>
              exists elements A l
              exists elements A r
              constructor
              · exact elements_node_none A l r
              · change elements A (Node l (some x) r) = elements A l ++ x :: elements A r
                exact elements_node_some A l x r
          | some y =>
              cases h
  | xO p ih =>
      intro x m h
      cases m with
      | Leaf =>
          exists []
          exists []
          constructor
          · rfl
          · exact elements_set_empty A (xO p) x
      | Node l o r =>
          have hleft : get_rec A p l = none := by
            rw [get_node0] at h
            exact h
          rcases ih x l hleft with ⟨l1, l2, hm, hset⟩
          cases o with
          | none =>
              exists l1
              exists l2 ++ elements A r
              constructor
              · calc
                  elements A (Node l none r)
                      = elements A l ++ elements A r := elements_node_none A l r
                  _ = (l1 ++ l2) ++ elements A r := by rw [hm]
                  _ = l1 ++ (l2 ++ elements A r) := by rw [List.append_assoc]
              · calc
                  elements A (set_rec A (xO p) x (Node l none r))
                      = elements A (Node (set_rec A p x l) none r) := by rw [set_node0]
                  _ = elements A (set_rec A p x l) ++ elements A r :=
                      elements_node_none A (set_rec A p x l) r
                  _ = (l1 ++ x :: l2) ++ elements A r := by rw [hset]
                  _ = l1 ++ x :: (l2 ++ elements A r) := by
                      simp [List.append_assoc]
          | some y =>
              exists l1
              exists l2 ++ y :: elements A r
              constructor
              · calc
                  elements A (Node l (some y) r)
                      = elements A l ++ y :: elements A r := elements_node_some A l y r
                  _ = (l1 ++ l2) ++ y :: elements A r := by rw [hm]
                  _ = l1 ++ (l2 ++ y :: elements A r) := by
                      simp [List.append_assoc]
              · calc
                  elements A (set_rec A (xO p) x (Node l (some y) r))
                      = elements A (Node (set_rec A p x l) (some y) r) := by rw [set_node0]
                  _ = elements A (set_rec A p x l) ++ y :: elements A r :=
                      elements_node_some A (set_rec A p x l) y r
                  _ = (l1 ++ x :: l2) ++ y :: elements A r := by rw [hset]
                  _ = l1 ++ x :: (l2 ++ y :: elements A r) := by
                      simp [List.append_assoc]
  | xI p ih =>
      intro x m h
      cases m with
      | Leaf =>
          exists []
          exists []
          constructor
          · rfl
          · exact elements_set_empty A (xI p) x
      | Node l o r =>
          have hright : get_rec A p r = none := by
            rw [get_node1] at h
            exact h
          rcases ih x r hright with ⟨l1, l2, hm, hset⟩
          cases o with
          | none =>
              exists elements A l ++ l1
              exists l2
              constructor
              · calc
                  elements A (Node l none r)
                      = elements A l ++ elements A r := elements_node_none A l r
                  _ = elements A l ++ (l1 ++ l2) := by rw [hm]
                  _ = (elements A l ++ l1) ++ l2 := by rw [List.append_assoc]
              · calc
                  elements A (set_rec A (xI p) x (Node l none r))
                      = elements A (Node l none (set_rec A p x r)) := by rw [set_node1]
                  _ = elements A l ++ elements A (set_rec A p x r) :=
                      elements_node_none A l (set_rec A p x r)
                  _ = elements A l ++ (l1 ++ x :: l2) := by rw [hset]
                  _ = (elements A l ++ l1) ++ x :: l2 := by
                      simp [List.append_assoc]
          | some y =>
              exists elements A l ++ y :: l1
              exists l2
              constructor
              · calc
                  elements A (Node l (some y) r)
                      = elements A l ++ y :: elements A r := elements_node_some A l y r
                  _ = elements A l ++ y :: (l1 ++ l2) := by rw [hm]
                  _ = (elements A l ++ y :: l1) ++ l2 := by
                      simp [List.append_assoc]
              · calc
                  elements A (set_rec A (xI p) x (Node l (some y) r))
                      = elements A (Node l (some y) (set_rec A p x r)) := by rw [set_node1]
                  _ = elements A l ++ y :: elements A (set_rec A p x r) :=
                      elements_node_some A l y (set_rec A p x r)
                  _ = elements A l ++ y :: (l1 ++ x :: l2) := by rw [hset]
                  _ = (elements A l ++ y :: l1) ++ x :: l2 := by
                      simp [List.append_assoc]

theorem elements_set_some :
    forall (A : Type u) (p : positive) (x x' : A) (m : tree A),
      get_rec A p m = some x ->
      exists l1 l2 : List A,
        elements A m = l1 ++ (x :: l2) /\
        elements A (set_rec A p x' m) = l1 ++ (x' :: l2) := by
  intro A p
  induction p with
  | xH =>
      intro x x' m h
      cases m with
      | Leaf =>
          have hnone : get_rec A xH Leaf = none := get_empty A xH
          rw [hnone] at h
          cases h
      | Node l o r =>
          cases o with
          | none =>
              cases h
          | some y =>
              cases h
              exists elements A l
              exists elements A r
              constructor
              · exact elements_node_some A l x r
              · change elements A (Node l (some x') r) = elements A l ++ x' :: elements A r
                exact elements_node_some A l x' r
  | xO p ih =>
      intro x x' m h
      cases m with
      | Leaf =>
          have hnone : get_rec A (xO p) Leaf = none := get_empty A (xO p)
          rw [hnone] at h
          cases h
      | Node l o r =>
          have hleft : get_rec A p l = some x := by
            rw [get_node0] at h
            exact h
          rcases ih x x' l hleft with ⟨l1, l2, hm, hset⟩
          cases o with
          | none =>
              exists l1
              exists l2 ++ elements A r
              constructor
              · calc
                  elements A (Node l none r)
                      = elements A l ++ elements A r := elements_node_none A l r
                  _ = (l1 ++ x :: l2) ++ elements A r := by rw [hm]
                  _ = l1 ++ x :: (l2 ++ elements A r) := by
                      simp [List.append_assoc]
              · calc
                  elements A (set_rec A (xO p) x' (Node l none r))
                      = elements A (Node (set_rec A p x' l) none r) := by rw [set_node0]
                  _ = elements A (set_rec A p x' l) ++ elements A r :=
                      elements_node_none A (set_rec A p x' l) r
                  _ = (l1 ++ x' :: l2) ++ elements A r := by rw [hset]
                  _ = l1 ++ x' :: (l2 ++ elements A r) := by
                      simp [List.append_assoc]
          | some y =>
              exists l1
              exists l2 ++ y :: elements A r
              constructor
              · calc
                  elements A (Node l (some y) r)
                      = elements A l ++ y :: elements A r := elements_node_some A l y r
                  _ = (l1 ++ x :: l2) ++ y :: elements A r := by rw [hm]
                  _ = l1 ++ x :: (l2 ++ y :: elements A r) := by
                      simp [List.append_assoc]
              · calc
                  elements A (set_rec A (xO p) x' (Node l (some y) r))
                      = elements A (Node (set_rec A p x' l) (some y) r) := by rw [set_node0]
                  _ = elements A (set_rec A p x' l) ++ y :: elements A r :=
                      elements_node_some A (set_rec A p x' l) y r
                  _ = (l1 ++ x' :: l2) ++ y :: elements A r := by rw [hset]
                  _ = l1 ++ x' :: (l2 ++ y :: elements A r) := by
                      simp [List.append_assoc]
  | xI p ih =>
      intro x x' m h
      cases m with
      | Leaf =>
          have hnone : get_rec A (xI p) Leaf = none := get_empty A (xI p)
          rw [hnone] at h
          cases h
      | Node l o r =>
          have hright : get_rec A p r = some x := by
            rw [get_node1] at h
            exact h
          rcases ih x x' r hright with ⟨l1, l2, hm, hset⟩
          cases o with
          | none =>
              exists elements A l ++ l1
              exists l2
              constructor
              · calc
                  elements A (Node l none r)
                      = elements A l ++ elements A r := elements_node_none A l r
                  _ = elements A l ++ (l1 ++ x :: l2) := by rw [hm]
                  _ = (elements A l ++ l1) ++ x :: l2 := by
                      simp [List.append_assoc]
              · calc
                  elements A (set_rec A (xI p) x' (Node l none r))
                      = elements A (Node l none (set_rec A p x' r)) := by rw [set_node1]
                  _ = elements A l ++ elements A (set_rec A p x' r) :=
                      elements_node_none A l (set_rec A p x' r)
                  _ = elements A l ++ (l1 ++ x' :: l2) := by rw [hset]
                  _ = (elements A l ++ l1) ++ x' :: l2 := by
                      simp [List.append_assoc]
          | some y =>
              exists elements A l ++ y :: l1
              exists l2
              constructor
              · calc
                  elements A (Node l (some y) r)
                      = elements A l ++ y :: elements A r := elements_node_some A l y r
                  _ = elements A l ++ y :: (l1 ++ x :: l2) := by rw [hm]
                  _ = (elements A l ++ y :: l1) ++ x :: l2 := by
                      simp [List.append_assoc]
              · calc
                  elements A (set_rec A (xI p) x' (Node l (some y) r))
                      = elements A (Node l (some y) (set_rec A p x' r)) := by rw [set_node1]
                  _ = elements A l ++ y :: elements A (set_rec A p x' r) :=
                      elements_node_some A l y (set_rec A p x' r)
                  _ = elements A l ++ y :: (l1 ++ x' :: l2) := by rw [hset]
                  _ = (elements A l ++ y :: l1) ++ x' :: l2 := by
                      simp [List.append_assoc]

end PTree
