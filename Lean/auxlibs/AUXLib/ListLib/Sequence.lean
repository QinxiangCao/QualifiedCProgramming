import AUXLib.ListLib.NPerm

namespace AUXLib

universe u v

private theorem getD_eq_getElem_of_lt {A : Type u} (l : List A) (d : A)
    (n : Nat) (h : n < l.length) : l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

def swap_nperm (n1 n2 n3 : Nat) : List Nat :=
  seq 0 n1 ++ (1 + n1 + n2) :: seq (1 + n1) n2 ++
    n1 :: seq (2 + n1 + n2) n3

private theorem seq_app_nat (start len1 len2 : Nat) :
    seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2 := by
  exact (List.range'_append_1 (s := start) (m := len1) (n := len2)).symm

private theorem seq_three_parts (n1 n2 n3 : Nat) :
    seq 0 (n1 + (1 + n2 + (1 + n3))) =
      seq 0 n1 ++ n1 :: seq (1 + n1) n2 ++
        (1 + n1 + n2) :: seq (2 + n1 + n2) n3 := by
  rw [seq_app_nat 0 n1]
  simp only [Nat.zero_add]
  have htail1 : 1 + n2 + (1 + n3) = 1 + (n2 + (1 + n3)) := by omega
  rw [htail1]
  rw [seq_app_nat n1 1]
  rw [seq_app_nat (n1 + 1) n2]
  rw [seq_app_nat (n1 + 1 + n2) 1]
  simp only [seq, List.range'_one, List.append_assoc]
  have hs1 : n1 + 1 = 1 + n1 := by omega
  have hs2 : n1 + 1 + n2 = 1 + n1 + n2 := by omega
  have hs3 : n1 + 1 + n2 + 1 = 2 + n1 + n2 := by omega
  rw [hs3, hs2, hs1]
  simp only [List.cons_append, List.nil_append]

private theorem perm_swap_separated {A : Type u} (pfx middle suffix : List A)
    (x y : A) :
    Permutation (pfx ++ x :: middle ++ y :: suffix)
      (pfx ++ y :: middle ++ x :: suffix) := by
  have hcore : Permutation (x :: middle ++ y :: suffix)
      (y :: middle ++ x :: suffix) :=
    (List.perm_append_comm_assoc [x] middle (y :: suffix)).trans
      ((List.Perm.swap y x suffix).append_left middle |>.trans List.perm_middle)
  simpa only [List.append_assoc] using hcore.append_left pfx

theorem swap_nperm_nperm (n1 n2 n3 : Nat) :
    nperm (swap_nperm n1 n2 n3) := by
  unfold nperm swap_nperm
  simp only [List.length_append, List.length_cons, List.length_range']
  have hlen : n1 + (n2 + 1) + (n3 + 1) = n1 + (1 + n2 + (1 + n3)) := by omega
  rw [hlen, seq_three_parts]
  exact perm_swap_separated (seq 0 n1) (seq (1 + n1) n2)
    (seq (2 + n1 + n2) n3) n1 (1 + n1 + n2)

private theorem map_seq_nth_slice {A : Type u} (pre mid post : List A) (d : A) :
    (seq pre.length mid.length).map
      (fun n => nth n (pre ++ mid ++ post) d) = mid := by
  apply List.ext_getElem
  · simp [seq]
  · intro k hkmap hkmid
    simp only [List.getElem_map]
    rw [List.getElem_range']
    simp only [Nat.one_mul]
    change nth (pre.length + k) (pre ++ mid ++ post) d = mid[k]
    change (pre ++ mid ++ post).getD (pre.length + k) d = mid[k]
    have hvalid : pre.length + k < (pre ++ mid ++ post).length := by
      simp only [List.length_append]
      omega
    rw [getD_eq_getElem_of_lt _ _ _ hvalid]
    have hleft : pre.length + k < (pre ++ mid).length := by
      simp only [List.length_append]
      omega
    rw [List.getElem_append_left hleft]
    rw [List.getElem_append_right (Nat.le_add_right pre.length k)]
    simp only [Nat.add_sub_cancel_left]

private theorem nth_length_append_cons {A : Type u}
    (pre : List A) (x d : A) (post : List A) :
    nth pre.length (pre ++ x :: post) d = x := by
  induction pre with
  | nil => rfl
  | cons y ys ih =>
      change nth ys.length (ys ++ x :: post) d = x
      exact ih

theorem swap_nperm_do_nperm (A : Type u) (l1 : List A) (i : A)
    (l2 : List A) (j : A) (l3 : List A) (d : A) :
    do_nperm (swap_nperm l1.length l2.length l3.length)
        (l1 ++ i :: l2 ++ j :: l3) d =
      l1 ++ j :: l2 ++ i :: l3 := by
  unfold do_nperm swap_nperm
  simp only [List.map_append, List.map_cons]
  have h1 :
      (seq 0 l1.length).map
        (fun n => nth n (l1 ++ i :: l2 ++ j :: l3) d) = l1 := by
    simpa only [List.nil_append, List.cons_append, List.append_assoc] using
      map_seq_nth_slice [] l1 (i :: l2 ++ j :: l3) d
  have hj : nth (1 + l1.length + l2.length)
      (l1 ++ i :: l2 ++ j :: l3) d = j := by
    have hbase := nth_length_append_cons (l1 ++ i :: l2) j d l3
    have hlen : (l1 ++ i :: l2).length = 1 + l1.length + l2.length := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [hlen] at hbase
    exact hbase
  have h2 :
      (seq (1 + l1.length) l2.length).map
        (fun n => nth n (l1 ++ i :: l2 ++ j :: l3) d) = l2 := by
    have hbase := map_seq_nth_slice (l1 ++ [i]) l2 (j :: l3) d
    have hshape : (l1 ++ [i]) ++ l2 ++ j :: l3 = l1 ++ i :: l2 ++ j :: l3 := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hshape] at hbase
    have hlen : (l1 ++ [i]).length = 1 + l1.length := by simp; omega
    rw [hlen] at hbase
    exact hbase
  have hi : nth l1.length (l1 ++ i :: l2 ++ j :: l3) d = i := by
    simpa only [List.cons_append, List.append_assoc] using
      nth_length_append_cons l1 i d (l2 ++ j :: l3)
  have h3 :
      (seq (2 + l1.length + l2.length) l3.length).map
        (fun n => nth n (l1 ++ i :: l2 ++ j :: l3) d) = l3 := by
    have hbase := map_seq_nth_slice (l1 ++ i :: l2 ++ [j]) l3 [] d
    have hshape : (l1 ++ i :: l2 ++ [j]) ++ l3 ++ [] =
        l1 ++ i :: l2 ++ j :: l3 := by
      simp only [List.append_assoc, List.cons_append, List.append_nil, List.nil_append]
    rw [hshape] at hbase
    have hlen : (l1 ++ i :: l2 ++ [j]).length = 2 + l1.length + l2.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hlen] at hbase
    exact hbase
  rw [h1, hj, h2, hi, h3]

def list_swap_nperm (n1 n2 : Nat) : List Nat :=
  seq n1 n2 ++ seq 0 n1

theorem list_swap_nperm_nperm (n1 n2 : Nat) :
    nperm (list_swap_nperm n1 n2) := by
  unfold nperm list_swap_nperm
  simp only [List.length_append, List.length_range']
  have hcomm : n2 + n1 = n1 + n2 := Nat.add_comm n2 n1
  rw [hcomm]
  rw [seq_app_nat 0 n1 n2]
  simp only [Nat.zero_add]
  exact List.perm_append_comm

theorem list_swap_nperm_do_nperm (A : Type u) (l1 l2 : List A) (d : A) :
    do_nperm (list_swap_nperm l1.length l2.length) (l1 ++ l2) d =
      l2 ++ l1 := by
  unfold do_nperm list_swap_nperm
  simp only [List.map_append]
  have h2 : (seq l1.length l2.length).map
      (fun n => nth n (l1 ++ l2) d) = l2 := by
    have hbase := map_seq_nth_slice l1 l2 [] d
    simp only [List.append_nil] at hbase
    exact hbase
  have h1 : (seq 0 l1.length).map
      (fun n => nth n (l1 ++ l2) d) = l1 := by
    exact map_seq_nth_slice [] l1 l2 d
  rw [h2, h1]

theorem NoDup_map_fst (A : Type u) (B : Type v) (l : List (A × B))
    (x : A) (y y' : B) (hnd : NoDup (l.map Prod.fst))
    (hy : In (x, y) l) (hy' : In (x, y') l) : y = y' := by
  induction l with
  | nil => simp at hy
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      have hparts : a ∉ ps.map Prod.fst ∧ NoDup (ps.map Prod.fst) := by
        change (a :: ps.map Prod.fst).Nodup at hnd
        exact List.nodup_cons.mp hnd
      simp only [List.mem_cons] at hy hy'
      rcases hy with hxy | hy
      · rcases hy' with hxy' | hy'
        · exact (Prod.mk.inj hxy).2.trans (Prod.mk.inj hxy').2.symm
        · have hmem : a ∈ ps.map Prod.fst := by
            apply List.mem_map.mpr
            exact ⟨(x, y'), hy', (Prod.mk.inj hxy).1⟩
          exact False.elim (hparts.1 hmem)
      · rcases hy' with hxy' | hy'
        · have hmem : a ∈ ps.map Prod.fst := by
            apply List.mem_map.mpr
            exact ⟨(x, y), hy, (Prod.mk.inj hxy').1⟩
          exact False.elim (hparts.1 hmem)
        · exact ih hparts.2 hy hy'

def Zseq : Int -> Nat -> List Int
  | _, 0 => []
  | start, len + 1 => start :: Zseq (start + 1) len

theorem Zseq_length (start : Int) (len : Nat) :
    (Zseq start len).length = len := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih => simp [Zseq, ih]

theorem Zseq_app (start : Int) (len1 len2 : Nat) :
    Zseq start (len1 + len2) =
      Zseq start len1 ++ Zseq (start + Int.ofNat len1) len2 := by
  induction len1 generalizing start with
  | zero => simp [Zseq]
  | succ len ih =>
      simp only [Nat.succ_add, Zseq, List.cons_append]
      rw [ih]
      congr 2
      ac_rfl

def nat_list_insert (i : Nat) : List Nat -> List Nat
  | [] => [i]
  | h :: t => if i <= h then i :: h :: t else h :: nat_list_insert i t

def nat_sort : List Nat -> List Nat
  | [] => []
  | h :: t => nat_list_insert h (nat_sort t)

theorem nat_list_insert_perm (x : Nat) (l : List Nat) :
    Permutation (x :: l) (nat_list_insert x l) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
      simp only [nat_list_insert]
      split
      · exact .refl _
      · exact (List.Perm.swap a x l).trans (ih.cons a)

theorem nat_sort_perm (l : List Nat) : Permutation l (nat_sort l) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
      exact (ih.cons a).trans (nat_list_insert_perm a (nat_sort l))

theorem nat_sort_nperm (s : List Nat)
    (h : nat_sort s = seq 0 s.length) : nperm s := by
  unfold nperm
  rw [← h]
  exact (nat_sort_perm s).symm

def list_update_nth {A : Type u} (l : List A) (n : Nat) (v : A) : List A :=
  firstn n l ++ v :: skipn (n + 1) l

theorem list_eq_nth (A : Type u) (l1 l2 : List A) (d : A)
    (hlen : l1.length = l2.length)
    (hget : forall n, n < l1.length -> nth n l1 d = nth n l2 d) :
    l1 = l2 := by
  apply List.ext_getElem
  · exact hlen
  · intro n hn1 hn2
    rw [← getD_eq_getElem_of_lt l1 d n hn1]
    rw [← getD_eq_getElem_of_lt l2 d n hn2]
    exact hget n hn1

theorem Zseq_nth (start : Int) (len n : Nat) (h : n < len) :
    nth n (Zseq start len) 0 = start + Int.ofNat n := by
  induction n generalizing start len with
  | zero =>
      cases len with
      | zero => omega
      | succ len => simp [Zseq, nth]
  | succ n ih =>
      cases len with
      | zero => omega
      | succ len =>
          change nth n (Zseq (start + 1) len) 0 = start + Int.ofNat (n + 1)
          rw [ih (start := start + 1) (len := len) (by omega)]
          have hcast : Int.ofNat (n + 1) = Int.ofNat n + 1 := by
            rw [show n + 1 = Nat.succ n by omega]
            exact (Int.ofNat_add_one_out n).symm
          rw [hcast]
          ac_rfl

theorem combine_skipn (A : Type u) (B : Type v) (l : List A) (l' : List B)
    (n : Nat) :
    skipn n (combine l l') = combine (skipn n l) (skipn n l') := by
  induction n generalizing l l' with
  | zero => rfl
  | succ n ih =>
      cases l <;> cases l' <;> simp [skipn, combine, ih]

theorem Zseq_firstn (start : Int) (len n : Nat) (h : n <= len) :
    firstn n (Zseq start len) = Zseq start n := by
  induction n generalizing start len with
  | zero => rfl
  | succ n ih =>
      cases len with
      | zero => omega
      | succ len =>
          simp only [Zseq, firstn, List.take_succ_cons]
          congr 1
          exact ih (start := start + 1) (len := len) (by omega)

theorem Zseq_skipn (start : Int) (len n : Nat) :
    skipn n (Zseq start len) =
      Zseq (start + Int.ofNat n) (len - n) := by
  induction n generalizing start len with
  | zero => simp [skipn]
  | succ n ih =>
      cases len with
      | zero => simp [skipn, Zseq]
      | succ len =>
          change List.drop n (Zseq (start + 1) len) =
            Zseq (start + Int.ofNat (n + 1)) ((len + 1) - (n + 1))
          rw [Nat.succ_sub_succ]
          change skipn n (Zseq (start + 1) len) =
            Zseq (start + Int.ofNat (n + 1)) (len - n)
          rw [ih (start := start + 1) (len := len)]
          apply congrArg (fun z => Zseq z (len - n))
          have hcast : Int.ofNat (n + 1) = Int.ofNat n + 1 := by
            rw [show n + 1 = Nat.succ n by omega]
            exact (Int.ofNat_add_one_out n).symm
          rw [hcast]
          ac_rfl
