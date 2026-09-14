Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.
Require Import Logic.LogicGenerator.demo932.Interface.
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

(** ********* Hash and finite-map model ********* *)

Definition hash_string (l : list Z) : Z :=
  fold_left (fun acc c => acc * 33 + c) l 5381 mod 4294967296.

Definition hash_string_k : list Z -> Z := hash_string.

Lemma hash_string_in_range :
  forall l, 0 <= hash_string l <= Int.max_unsigned.
Proof.
  intros l.
  unfold hash_string.
  pose proof (Z.mod_pos_bound
                (fold_left (fun acc c => acc * 33 + c) l 5381)
                4294967296) as Hbound.
  change Int.max_unsigned with 4294967295.
  lia.
Qed.

Module KP.
Definition insert_map
           (m : list Z -> option addr)
           (k : list Z)
           (v : addr) : list Z -> option addr :=
  fun k' => if list_eq_dec Z.eq_dec k' k then Some v else m k'.

Lemma insert_map_same :
  forall m k v, insert_map m k v k = Some v.
Proof.
  intros.
  unfold insert_map.
  destruct (list_eq_dec Z.eq_dec k k); congruence.
Qed.

Lemma insert_map_diff :
  forall m k1 k2 v, k1 <> k2 -> insert_map m k1 v k2 = m k2.
Proof.
  intros.
  unfold insert_map.
  destruct (list_eq_dec Z.eq_dec k2 k1); congruence.
Qed.

Definition remove_map
           (m : list Z -> option addr)
           (k : list Z) : list Z -> option addr :=
  fun k' => if list_eq_dec Z.eq_dec k' k then None else m k'.

Lemma remove_map_same :
  forall m k, remove_map m k k = None.
Proof.
  intros.
  unfold remove_map.
  destruct (list_eq_dec Z.eq_dec k k); congruence.
Qed.

Lemma remove_map_diff :
  forall m k1 k2, k1 <> k2 -> remove_map m k1 k2 = m k2.
Proof.
  intros.
  unfold remove_map.
  destruct (list_eq_dec Z.eq_dec k2 k1); congruence.
Qed.

Fixpoint remove_keys
         (m: list Z -> option addr)
         (ks: list (list Z)): list Z -> option addr :=
  match ks with
  | nil => m
  | k :: ks' => remove_keys (remove_map m k) ks'
  end.
End KP.

Module PV.
Definition insert_map
           (m : addr -> option Z)
           (k v : Z) : addr -> option Z :=
  fun k' => if Z.eq_dec k' k then Some v else m k'.

Lemma insert_map_same :
  forall m k v, insert_map m k v k = Some v.
Proof.
  intros.
  unfold insert_map.
  destruct (Z.eq_dec k k); congruence.
Qed.

Lemma insert_map_diff :
  forall m k1 k2 v, k1 <> k2 -> insert_map m k1 v k2 = m k2.
Proof.
  intros.
  unfold insert_map.
  destruct (Z.eq_dec k2 k1); congruence.
Qed.

Definition remove_map
           (m : addr -> option Z)
           (k : addr) : addr -> option Z :=
  fun k' => if Z.eq_dec k' k then None else m k'.

Lemma remove_map_same :
  forall m k, remove_map m k k = None.
Proof.
  intros.
  unfold remove_map.
  destruct (Z.eq_dec k k); congruence.
Qed.

Lemma remove_map_diff :
  forall m k1 k2, k1 <> k2 -> remove_map m k1 k2 = m k2.
Proof.
  intros.
  unfold remove_map.
  destruct (Z.eq_dec k2 k1); congruence.
Qed.

Fixpoint remove_addrs
         (m : addr -> option Z)
         (ps : list addr) : addr -> option Z :=
  match ps with
  | nil => m
  | p :: ps' => remove_addrs (remove_map m p) ps'
  end.
End PV.

(** ********* Definitions ********* *)

Definition NBUCK: Z := 211.

Definition bucket_cells_nonnull (bucks : addr) : Prop :=
  forall i, 0 <= i < NBUCK ->
    bucks + i * sizeof(PTR) <> NULL.

Fixpoint sll (x: addr) (l: list addr): Assertion :=
  match l with
    | nil      => “ x = NULL ” && emp
    | x0 :: l0 => “ x <> NULL ” && “ x = x0 ” &&
                  “ &(x # "blist" ->ₛ "next") <> NULL ” &&
                  EX y: addr,
                   &(x # "blist" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

Fixpoint sllseg (x y: addr) (l: list addr): Assertion :=
  match l with
    | nil      => “ x = y ” && emp
    | x0 :: l0 => “ x <> NULL ” && “ x = x0 ” &&
                  “ &(x # "blist" ->ₛ "next") <> NULL ” &&
                  EX z: addr,
                    &(x # "blist" ->ₛ "next") # Ptr |-> z **
                    sllseg z y l0
  end.

Fixpoint sllbseg (x y: addr) (l: list addr): Assertion :=
  match l with
    | nil      => “ x <> NULL ” && “ x = y ” && emp
    | x0 :: l0 => “ x <> NULL ” && “ x0 <> NULL ” &&
                    x # Ptr |-> x0 **
                    sllbseg (&(x0 # "blist" ->ₛ "next")) y l0
  end.

Fixpoint dll (x x_up: addr) (l: list addr): Assertion :=
  match l with
    | nil      => “ x = NULL ” && emp
    | x0 :: l0 => “ x <> NULL ” && “ x = x0 ” &&
                  EX x_down: addr,
                    &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
                    &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
                    dll x_down x l0
  end.

Fixpoint dllseg (x y x_up y_up: addr) (l: list addr): Assertion :=
  match l with
    | nil      => “ x = y ” && “ x_up = y_up ” &&
                  emp
    | x0 :: l0 => “ x <> NULL ” && “ x = x0 ” &&
                  EX x_down: addr,
                    &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
                    &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
                    dllseg x_down y x y_up l0
  end.

Definition not_key (k: list Z) (l_prev: list Z) (m: list Z -> option Z) : Prop :=
  forall (p: addr) (k1: list Z),
    In p l_prev ->
    m k1 = Some p -> k1 <> k.

Definition store_sll (n: Z): addr * list addr -> Assertion :=
  fun '(p, l) => sll p l.

Definition store_map_missing_first_i_Z {B: Type}
           (P: Z -> B -> Assertion)
           (m: Z -> option B)
           (i: Z): Assertion :=
  EX l: list Z,
    “ forall a, In a l <-> (exists b, m a = Some b) /\ i < a ” &&
    “ NoDup l ” &&
    iter_sepcon
      (map (fun a => match m a with Some b => P a b | None => emp end) l).

Definition store_name (k: list Z) (p: addr): Assertion :=
  EX key_addr: addr,
    &(p # "blist" ->ₛ "key") # Ptr |-> key_addr **
    store_string key_addr k.

Definition store_val (p v: Z): Assertion :=
  &(p # "blist" ->ₛ "val") # UInt |-> v.

Lemma ptr_string_name:
  forall p key_addr k,
    &(p # "blist" ->ₛ "key") # Ptr |-> key_addr **
    store_string key_addr k |-- store_name k p.
Proof.
  intros.
  unfold store_name.
  Exists key_addr.
  repeat cancel.
Qed.

Definition contain_all_addrs (m: list Z -> option addr) (l: list addr) :=
  forall p: addr,
    (exists key: list Z, m key = Some p) <-> In p l.

Fixpoint key_list_for_addrs
         (m: list Z -> option addr)
         (l: list addr)
         (ks: list (list Z)): Prop :=
  match l, ks with
  | nil, nil => True
  | p :: l', k :: ks' =>
      m k = Some p /\ key_list_for_addrs (KP.remove_map m k) l' ks'
  | _, _ => False
  end.

Definition keys_exact_bucket
           (m: list Z -> option addr)
           (i: Z)
           (ks: list (list Z)): Prop :=
  forall k p,
    m k = Some p -> (In k ks <-> hash_string k mod NBUCK = i).

Definition remaining_after_bucket_index
           (m m_rem: list Z -> option addr)
           (i: Z): Prop :=
  forall k p,
    m_rem k = Some p <-> m k = Some p /\ i <= hash_string k mod NBUCK.

Definition current_bucket_key_list
           (m: list Z -> option addr)
           (b: Z -> option (addr * list addr))
           (i: Z)
           (li: list addr)
           (ks: list (list Z)): Prop :=
  key_list_for_addrs m li ks /\
  (exists buck, b i = Some (buck, li)) /\
  keys_exact_bucket m i ks /\
  (forall m0,
      remaining_after_bucket_index m0 m i ->
      remaining_after_bucket_index m0 (KP.remove_keys m ks) (i + 1)).

Definition repr_all_heads
             (lh: list addr)
             (b: Z -> option (addr * list addr)): Prop :=
  forall i p,
    (exists l, b i = Some (p, l)) <->
    (0 <= i < Zlength lh /\ Znth i lh 0 = p).

Definition contain_all_correct_addrs
             (m: list Z -> option addr)
             (b: Z -> option (addr * list addr)): Prop :=
  forall i p,
    (exists key, hash_string key mod NBUCK = i /\ m key = Some p) <->
    (exists ph l, b i = Some (ph, l) /\ In p l).

Definition current_bucket_suffix
             (m: list Z -> option addr)
             (b: Z -> option (addr * list addr))
             (i: Z)
             (l_prev l_res: list addr): Prop :=
  contain_all_correct_addrs m b /\
  exists buck, b i = Some (buck, app l_prev l_res).

Definition map_fun {A B C: Type} (m: A -> option B) (f: B -> C): A -> option C :=
  fun a =>
    match m a with
      | None => None
      | Some b => Some (f b)
  end.

Definition node_value_map
             (m_node: list Z -> option addr)
             (m_value: list Z -> option addr): Prop :=
  m_value = map_fun m_node (fun p => &(p # "blist" ->ₛ "val")).

Definition store_hash_skeleton (x: addr) (m: list Z -> option addr): Assertion :=
  EX (m0: list Z -> option addr) (l lh: list addr)
     (top bucks: addr) (b: Z -> option (addr * list addr)),
    “ node_value_map m0 m ” &&
    “ contain_all_addrs m0 l ” &&
    “ repr_all_heads lh b ” &&
    “ contain_all_correct_addrs m0 b ” &&
    “ bucket_cells_nonnull bucks ” &&
    &(x # "hashtbl" ->ₛ "top") # Ptr |-> top **
    dll top NULL l **  (** permission of top & down*)
    &(x # "hashtbl" ->ₛ "bucks") # Ptr |-> bucks ** (** permission of bucks pointer *)
    PtrArray.full bucks NBUCK lh ** (** permission of bucks array *)
    store_map store_sll b **  (** permission of next *)
    store_map store_name m0.  (** permission of key *)

Definition map_compose
             {A B C: Type}
             (m1: A -> option B)
             (m2: B -> option C)
             (m: A -> option C): Prop :=
  (forall a,
    (m1 a = None /\ m a = None) \/
    (exists b c, m1 a = Some b /\ m2 b = Some c /\ m a = Some c)) /\
  (forall b,
    m2 b = None /\ (forall a, m1 a <> Some b) \/
    exists a c, m1 a = Some b /\ m2 b = Some c).

Definition map_composable
             {A B C: Type}
             (m1: A -> option B)
             (m2: B -> option C): Prop :=
  (forall a,
    m1 a = None \/
    (exists b c, m1 a = Some b /\ m2 b = Some c)) /\
  (forall b,
    m2 b = None /\ (forall a, m1 a <> Some b) \/
    exists a c, m1 a = Some b /\ m2 b = Some c).

Definition store_hashtbl (x: addr) (m: list Z -> option Z): Assertion :=
  EX (m1: list Z -> option addr) (m2: addr -> option Z),
    “ map_compose m1 m2 m ” &&
    store_hash_skeleton x m1 **
    store_map store_uint m2. (** permission of val *)

Definition empty_map {Key Value: Type}: Key -> option Value := fun _ => None.

Definition update_b0_at (b0: Z -> option (Z * list Z)) (ind: Z) (new_head: Z) (new_l: list Z) : Z -> option (Z * list Z) :=
  fun i => if Z.eq_dec i ind then Some (new_head, new_l) else b0 i.

Fixpoint update_nth {A} (l : list A) (n : nat) (x : A) : list A :=
  match l with
  | [] => []
  | h :: t => match n with
               | 0%nat => x :: t
               | S n' => h :: update_nth t n' x
               end
  end.

Definition update_nth_Z {A} (l : list A) (ind : Z) (x : A) : list A :=
  update_nth l (Z.to_nat ind) x.

(** ********* Proofs ********* *)

Lemma sll_zero: forall x l,
  x = NULL ->
  sll x l |-- “ l = nil ” && emp.
Proof.
  intros x l Hx.
  destruct l as [|a l].
  - simpl sll.
    Intros_p Hnull.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - simpl sll.
    Intros y.
    contradiction.
Qed.

Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y l0,
      “ l = x :: l0 ” &&
      &(x # "blist" ->ₛ "next") # Ptr |-> y **
      sll y l0.
Proof.
  intros x l Hx.
  destruct l as [|a l].
  - simpl sll.
    Intros_p Hnull.
    contradiction.
  - simpl sll.
    Intros.
    Intros y.
    Exists y l.
    split_pure_spatial.
    + repeat cancel.
    + dump_pre_spatial.
      subst a.
      reflexivity.
Qed.

Lemma sll_not_zero': forall x l,
  x <> NULL ->
  sll x l |-- “ l <> nil ”.
Proof.
  intros x l Hx.
  destruct l as [|a l].
  - simpl sll.
    Intros_p Hnull.
    contradiction.
  - simpl sll.
    Intros.
    Intros y.
    dump_pre_spatial.
    discriminate.
Qed.

Lemma sllseg_nil_equiv: forall x,
  sllseg x x nil --||-- emp.
Proof.
  intros x.
  split.
  - simpl sllseg.
    Intros_p Heq.
    cancel.
  - simpl sllseg.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma sllseg_len1: forall x y,
  x <> NULL ->
  &(x # "blist" ->ₛ "next") <> NULL ->
  &(x # "blist" ->ₛ "next") # Ptr |-> y |--
  sllseg x y [x].
Proof.
  intros x y Hx Hnext.
  simpl sllseg.
  Exists y.
  fold (sllseg y y nil).
  rewrite sllseg_nil_equiv.
  normalize.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; auto.
Qed.

Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
Proof.
  intros x y z l1 l2.
  revert x; induction l1 as [|a l1 IH]; simpl sllseg; intros x.
  - Intros_p Hxy.
    subst x.
    cancel.
  - Intros.
    Intros z0.
    Exists z0.
    sep_apply IH.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: assumption.
Qed.

Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
Proof.
  intros x y l1 l2.
  revert x; induction l1 as [|a l1 IH]; simpl sllseg; simpl sll; intros x.
  - Intros_p Hxy.
    subst x.
    cancel.
  - Intros.
    Intros z0.
    Exists z0.
    sep_apply IH.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: assumption.
Qed.

Lemma sllbseg_start_nonnull : forall x y l,
  sllbseg x y l |-- “ x <> NULL ”.
Proof.
  intros x y [|a l]; simpl sllbseg.
  - Intros_p Hx.
    dump_pre_spatial.
    exact Hx.
  - Intros_p Hx.
    dump_pre_spatial.
    exact Hx.
Qed.

Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.
Proof.
  intros x y z l.
  revert x; induction l as [|a l IH]; intros x; simpl.
  - Intros.
    subst x.
    Exists z.
    simpl sllseg.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - Intros.
    prop_apply_p
      (sllbseg_start_nonnull (&(a # "blist" ->ₛ "next")) y l).
    Intros_p Hnext.
    sep_apply_l_atomic (IH (&(a # "blist" ->ₛ "next"))).
    Intros y'.
    Exists a y'.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial. reflexivity.
      * dump_pre_spatial. exact Hnext.
Qed.

Lemma sllbseg_len1: forall (x y: addr),
  x <> NULL ->
  y <> 0 ->
  &(y # "blist" ->ₛ "next") <> NULL ->
  x # Ptr |-> y  |--
  sllbseg x (&( y # "blist" ->ₛ "next")) [y].
Proof.
  intros x y Hx Hy Hnext.
  simpl.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact Hx.
    + dump_pre_spatial. exact Hy.
    + dump_pre_spatial. exact Hnext.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma sllbseg_sllbseg: forall x y z l1 l2,
  sllbseg x y l1 ** sllbseg y z l2 |--
  sllbseg x z (l1 ++ l2).
Proof.
  intros x y z l1 l2.
  revert x; induction l1 as [|a l1 IH]; simpl; intros x.
  - Intros_p Hx.
    Intros_p Hxy.
    subst x.
    cancel.
  - Intros_p Hx.
    Intros_p Ha.
    sep_apply IH.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      * dump_pre_spatial. exact Hx.
      * dump_pre_spatial. exact Ha.
Qed.

Lemma sllseg_0_sll: forall x l,
  sllseg x 0 l |-- sll x l.
Proof.
  intros x l.
  revert x; induction l as [|a l IH]; simpl; intros x.
  - Intros_p Hx.
    subst x.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - Intros z.
    Exists z.
    sep_apply IH.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: assumption.
Qed.

Lemma sll2sllseg: forall x l,
  sll x l |-- sllseg x NULL l.
Proof.
  intros x l.
  revert x; induction l as [|a l IH]; simpl; intros x.
  - cancel.
  - Intros y.
    Exists y.
    sep_apply IH.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: assumption.
Qed.

Lemma sll_in: forall x l,
  “x <> 0” && sll x l |--
  “In x l”.
Proof.
  intros x l.
  induction l as [|a l]; simpl.
  - Intros_p Hx.
    Intros_p Hnull.
    rewrite Hnull in Hx.
    contradiction.
  - Intros y.
    dump_pre_spatial.
    subst a.
    left.
    reflexivity.
Qed.


Lemma sllseg_not_in: forall x x' y z l,
  &(x # "blist" ->ₛ "next") # Ptr |-> x' **
  sllseg y z l |--
  “ ~ In x l ”.
Proof.
  intros x x' y z l.
  revert y; induction l as [|a l IH]; intros y; simpl.
  - dump_pre_spatial.
    intros Hin.
    inversion Hin.
  - Intros y'.
    subst a.
    prop_apply (IH y').
    Intros_p Htail.
    destruct (Z.eq_dec y x) as [Heq | Hneq].
    + subst y.
      prop_apply (dup_store_ptr (&(x # "blist" ->ₛ "next")) x' y').
      Intros_p Hfalse.
      contradiction.
    + dump_pre_spatial.
      intros [Heq | Hin].
      * apply Hneq.
        exact Heq.
      * apply Htail.
        exact Hin.
Qed.

Lemma sllseg_nodup: forall x y l,
  sllseg x y l |-- “ NoDup l ”.
Proof.
  intros x y l.
  revert x; induction l as [|a l IH]; intros x; simpl.
  - dump_pre_spatial.
    constructor.
  - Intros x'.
    prop_apply (IH x').
    Intros_p Hnodup.
    prop_apply (sllseg_not_in x x' x' y l).
    Intros_p Hnotin.
    dump_pre_spatial.
    subst a.
    constructor; assumption.
Qed.

Lemma sll_nodup: forall x l,
  sll x l |-- “ NoDup l ”.
Proof.
  intros x l.
  sep_apply sll2sllseg.
  prop_apply sllseg_nodup.
  Intros_p Hnodup.
  dump_pre_spatial.
  exact Hnodup.
Qed.

Lemma dllseg_nil_equiv: forall x x_up,
  dllseg x x x_up x_up nil --||-- emp.
Proof.
  intros x x_up.
  split.
  - simpl dllseg.
    Intros_p Hx.
    Intros_p Hup.
    cancel.
  - simpl dllseg.
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial. reflexivity.
      * dump_pre_spatial. reflexivity.
Qed.

Lemma dllseg_len1: forall (x x_up x_down: addr),
  x <> NULL ->
  &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
  &(x # "blist" ->ₛ "up") # Ptr |-> x_up |--
  dllseg x x_down x_up x [x].
Proof.
  intros x x_up x_down Hx.
  simpl dllseg.
  Exists x_down.
  fold (dllseg x_down x_down x x nil).
  rewrite dllseg_nil_equiv.
  normalize.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; auto.
Qed.

Lemma dllseg_dllseg: forall (x y z x_up y_up z_up: addr) l1 l2,
  dllseg x y x_up y_up l1 **
  dllseg y z y_up z_up l2 |--
  dllseg x z x_up z_up (l1 ++ l2).
Proof.
  intros x y z x_up y_up z_up l1 l2.
  revert x x_up; induction l1 as [|a l1 IH]; intros x x_up; simpl.
  - Intros_p Hxy.
    Intros_p Hup.
    subst x.
    subst x_up.
    cancel.
  - Intros u.
    Exists u.
    sep_apply IH.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      all: dump_pre_spatial; assumption.
Qed.

Lemma dllseg_head_zero: forall x y x_up y_up l,
  x = 0 ->
  dllseg x y x_up y_up l |--
  “ y = 0 ” && “ x_up = y_up ” && “ l = nil ” && emp.
Proof.
  intros x y x_up y_up l Hx.
  destruct l as [|a l].
  - simpl dllseg.
    subst x.
    repeat (split_pure_spatial || split_pures).
    + Intros_p Hxy.
      Intros_p Hup.
      cancel.
    + Intros_p Hxy.
      dump_pre_spatial.
      symmetry; exact Hxy.
    + Intros_p Hxy.
      Intros_p Hup.
      dump_pre_spatial.
      exact Hup.
    + dump_pre_spatial.
      reflexivity.
  - simpl dllseg.
    subst x.
    Intros x_down.
    contradiction.
Qed.

Lemma dllseg_head_neq: forall x y x_up y_up l,
  x <> y ->
  dllseg x y x_up y_up l |--
  EX z l0,
    “ l = x :: l0 ” &&
    &(x # "blist" ->ₛ "down") # Ptr |-> z **
    &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
    dllseg z y x y_up l0.
Proof.
  intros x y x_up y_up l Hxy.
  destruct l as [|a l].
  - simpl dllseg.
    Intros_p Heq.
    contradiction.
  - simpl dllseg.
    Intros z0.
    Exists z0 l.
    split_pure_spatial.
    + repeat cancel.
    + dump_pre_spatial.
      subst a.
      reflexivity.
Qed.

Lemma dllseg_head_neq_destruct_tail_aux: forall x y x_up y_up l,
  dllseg x y x_up y_up l |--
  “ x = y ” && “ x_up = y_up ” && “ l = nil ” && emp ||
  EX z l0,
    “ y_up <> 0 ” &&
    “ l = (l0 ++ y_up :: nil)%list ” &&
    dllseg x y_up x_up z l0 **
    &(y_up # "blist" ->ₛ "down") # Ptr |-> y **
    &(y_up # "blist" ->ₛ "up") # Ptr |-> z.
Proof.
  intros x y x_up y_up l.
  revert x x_up; induction l as [|a l IH]; intros x x_up; simpl.
  - Left.
    repeat (split_pure_spatial || split_pures).
    + Intros_p Hxy.
      Intros_p Hup.
      cancel.
    + Intros_p Hxy.
      dump_pre_spatial. exact Hxy.
    + Intros_p Hxy.
      Intros_p Hup.
      dump_pre_spatial. exact Hup.
    + dump_pre_spatial. reflexivity.
  - Intros z0.
    sep_apply IH.
    Split.
    + Right.
      Exists x_up (@nil addr).
      repeat (split_pure_spatial || split_pures).
      * Intros_p Hz0y.
        Intros_p Hxyup.
        Intros_p Hl.
        subst y.
        subst y_up.
        simpl dllseg.
        repeat (split_pure_spatial || split_pures).
        -- repeat cancel.
        -- dump_pre_spatial. reflexivity.
        -- dump_pre_spatial. reflexivity.
      * Intros_p Hz0y.
        Intros_p Hxyup.
        Intros_p Hl.
        dump_pre_spatial.
        subst y_up.
        assumption.
      * Intros_p Hz0y.
        Intros_p Hxyup.
        Intros_p Hl.
        dump_pre_spatial.
        subst l.
        subst a.
        subst y_up.
        reflexivity.
    + Intros z.
      Intros l0.
      Right.
      Exists z (a :: l0).
      repeat (split_pure_spatial || split_pures).
      * cancel (&(y_up # "blist" ->ₛ "down") # Ptr |-> y).
        cancel (&(y_up # "blist" ->ₛ "up") # Ptr |-> z).
        simpl dllseg.
        Exists z0.
        split_pure_spatial.
        -- repeat cancel.
        -- split_pures.
           all: dump_pre_spatial; assumption.
      * dump_pre_spatial. assumption.
      * dump_pre_spatial.
        subst l.
        reflexivity.
Qed.

Lemma dllseg_head_neq_destruct_tail: forall x y x_up y_up l,
  x <> y ->
  dllseg x y x_up y_up l |--
  EX z l0,
    “ y_up <> 0 ” &&
    “ l = (l0 ++ y_up :: nil)%list ” &&
    dllseg x y_up x_up z l0 **
    &(y_up # "blist" ->ₛ "down") # Ptr |-> y **
    &(y_up # "blist" ->ₛ "up") # Ptr |-> z.
Proof.
  intros x y x_up y_up l Hxy.
  sep_apply dllseg_head_neq_destruct_tail_aux.
  normalize.
  Split.
  - Intros_p Heq.
    contradiction.
  - cancel.
Qed.

Lemma dll_zero : forall (x x_up : addr) (l : list Z),
  x = NULL ->
  dll x x_up l |-- “ l = nil” && emp.
Proof.
  intros x x_up l Hx.
  destruct l as [|a l].
  - simpl dll.
    subst x.
    split_pure_spatial.
    + Intros_p Hnull. cancel.
    + dump_pre_spatial. reflexivity.
  - simpl dll.
    subst x.
    Intros x_down.
    contradiction.
Qed.

Lemma dll_not_zero: forall x x_up l,
  x <> NULL ->
  dll x x_up l |--
    EX y l0,
      “ l = x :: l0 ” &&
      &(x # "blist" ->ₛ "down") # Ptr |-> y **
      &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
      dll y x l0.
Proof.
  intros x x_up l Hx.
  destruct l as [|a l].
  - simpl dll.
    Intros_p Hnull.
    contradiction.
  - simpl dll.
    Intros y.
    Exists y l.
    split_pure_spatial.
    + repeat cancel.
    + dump_pre_spatial.
      subst a.
      reflexivity.
Qed.

Lemma dllseg_dll : forall x y x_up y_up l1 l2,
  dllseg x y x_up y_up l1 ** dll y y_up l2 |-- dll x x_up (l1 ++ l2).
Proof.
  intros x y x_up y_up l1 l2.
  revert x x_up; induction l1 as [|a l1 IH]; intros x x_up; simpl.
  - Intros_p Hxy.
    Intros_p Hup.
    subst x.
    subst x_up.
    cancel.
  - Intros z.
    Exists z.
    split_pure_spatial.
    + cancel (&(x # "blist" ->ₛ "down") # Ptr |-> z).
      cancel (&(x # "blist" ->ₛ "up") # Ptr |-> x_up).
      apply IH.
    + split_pures.
      all: dump_pre_spatial; assumption.
Qed.

Lemma dllseg_0_dll: forall x x_up y_up l,
  dllseg x NULL x_up y_up l |-- dll x x_up l.
Proof.
  intros x x_up y_up l.
  revert x x_up y_up; induction l as [|a l IH]; intros x x_up y_up; simpl.
  - Intros_p Hnull.
    Intros_p Hup.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. exact Hnull.
  - Intros x_down.
    Exists x_down.
    sep_apply IH.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      all: dump_pre_spatial; assumption.
Qed.

Lemma dll2dllseg: forall x x_up l,
  dll x x_up l |-- EX y_up, dllseg x NULL x_up y_up l.
Proof.
  intros x x_up l.
  revert x x_up; induction l as [|a l IH]; intros x x_up; simpl.
  - Intros_p Hnull.
    Exists x_up.
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial. exact Hnull.
      * dump_pre_spatial. reflexivity.
  - Intros x_down.
    sep_apply IH.
    Intros y_up.
    Exists y_up x_down.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      all: dump_pre_spatial; assumption.
Qed.

Lemma dllseg_not_in: forall x x_down y z y_up z_up l,
  &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
  dllseg y z y_up z_up l |--
  “ ~ In x l ”.
Proof.
  intros x x_down y z y_up z_up l.
  revert y y_up; induction l as [|a l IH]; intros y y_up; simpl.
  - dump_pre_spatial.
    intros Hin.
    inversion Hin.
  - Intros y_down.
    subst a.
    destruct (Z.eq_dec y x) as [Heq | Hneq].
    + subst y.
      prop_apply
        (dup_store_ptr (&(x # "blist" ->ₛ "down")) x_down y_down).
      Intros_p Hfalse.
      contradiction.
    + prop_apply (IH y_down y).
      Intros_p Htail.
      dump_pre_spatial.
      intros [Heq | Hin].
      * apply Hneq. exact Heq.
      * apply Htail. exact Hin.
Qed.

Lemma dllseg_nodup: forall x y x_up y_up l,
  dllseg x y x_up y_up l |-- “ NoDup l ”.
Proof.
  intros x y x_up y_up l.
  revert x x_up; induction l as [|a l IH]; intros x x_up; simpl.
  - dump_pre_spatial. constructor.
  - Intros x_down.
    prop_apply (IH x_down x).
    Intros_p Hnodup.
    prop_apply (dllseg_not_in x x_down x_down y x y_up l).
    Intros_p Hnotin.
    dump_pre_spatial.
    subst a.
    constructor; assumption.
Qed.

Lemma dll_nodup: forall x x_up l,
  dll x x_up l |-- “ NoDup l ”.
Proof.
  intros x x_up l.
  sep_apply dll2dllseg.
  Intros y_up.
  prop_apply dllseg_nodup.
  Intros_p Hnodup.
  dump_pre_spatial. exact Hnodup.
Qed.


Lemma sllseg_nil_emp : forall p,
  sllseg p p nil |-- emp.
Proof.
  intros p.
  rewrite sllseg_nil_equiv.
  cancel.
Qed.

Lemma b_sll (b: Z -> option (addr * list addr)):
  forall i p l, 
    store_map store_sll b &&
    “b i = Some(p, l)” |--
    store_map_missing_i (fun (_ : Z) '(p0, l0) => sll p0 l0) b i **
    sll p l.
Proof.
  intros i p l.
  andp_lift (“ b i = Some (p, l) ”).
  Intros_p Hlookup.
  sep_apply (store_map_split store_sll i (p, l) b Hlookup).
  unfold store_sll.
  cancel.
Qed.

Lemma sll_b (b: Z -> option (addr * list addr)):
  forall i p l,
    store_map_missing_i (fun (_ : Z) '(p0, l0) => sll p0 l0) b i **
    sll p l &&
    “b i = Some(p, l)” |--
    store_map store_sll b.
Proof.
  intros i p l.
  andp_lift (“ b i = Some (p, l) ”).
  Intros_p Hlookup.
  unfold store_sll.
  sep_apply (store_map_merge store_sll i (p, l) b Hlookup).
  unfold store_sll.
  cancel.
Qed.

Lemma sllseg_head (p q: Z)(l: list Z):
    q = NULL -> 
    sllseg p q l 
    |-- 
    “ l = nil \/ In p l” && sllseg p q l.
Proof.
  intros Hq.
  split_pure_spatial.
  - cancel.
  - destruct l as [|a l].
    + dump_pre_spatial.
      left; reflexivity.
    + simpl sllseg.
      Intros next.
      dump_pre_spatial.
      subst a.
      right; left; reflexivity.
Qed.

Lemma sll_head : 
    forall p l,
        p <> 0 -> sll p l 
        |-- EX l_resres,  “ l = p :: l_resres ” && sll p l.
Proof.
  intros p l Hp.
  destruct l as [|a l].
  - simpl sll.
    Intros_p Hnull.
    contradiction.
  -
    Exists l.
    split_pure_spatial.
    + cancel.
    + simpl sll.
      Intros next.
      dump_pre_spatial.
      subst a.
      reflexivity.
Qed. 

Lemma sllbseg_sll:
  forall p i l_prev i_v l_res,
    sllbseg p i l_prev **
    i # Ptr |-> i_v **
    sll i_v l_res 
    |--
    EX p0,
    p # Ptr |-> p0 **
    sll p0 (l_prev++l_res).
Proof.
  intros p i l_prev.
  revert p i.
  induction l_prev as [|a l_prev IH]; intros p i i_v l_res.
  - simpl sllbseg.
    simpl.
    Intros_p Hp.
    Intros_p Hpi.
    subst p.
    Exists i_v.
    cancel.
  - simpl sllbseg.
    simpl.
    Intros_p Hp.
    Intros_p Ha.
    prop_apply_p
      (sllbseg_start_nonnull
        (&(a # "blist" ->ₛ "next")) i l_prev).
    Intros_p Hnext.
    sep_apply_l_atomic
      (IH (&(a # "blist" ->ₛ "next")) i i_v l_res).
    Intros p_tail.
    Exists a.
    Exists p_tail.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact Ha.
      * dump_pre_spatial.
        reflexivity.
      * dump_pre_spatial.
        exact Hnext.
Qed.

Lemma sll_head_append: 
forall head p0 l,
  head <> 0 ->
  &(head # "blist" ->ₛ "next") <> NULL ->
  &( head # "blist" ->ₛ "next") # Ptr |-> p0 **
  sll p0 l
  |-- sll head (head::l).
Proof.
  intros head p0 l Hhead Hnext.
  simpl sll.
  Exists p0.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact Hhead.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. exact Hnext.
Qed.

(* ---------------------------------------------------------------------- *)
(* Helper lemmas about lists                                               *)
(* ---------------------------------------------------------------------- *)

Lemma firstn_replace_nth_nat {A} (n: nat) (v: A) (l: list A) :
  firstn n (replace_nth n l v) = firstn n l.
Proof.
  (* 对 n 做归纳：替换第 n 位不会影响前 n 个元素 *)
  revert l v.
  induction n; intros; destruct l; simpl; auto; f_equal; apply IHn.
Qed.

Lemma length_replace_nth {A} (n: nat) (v: A) (l: list A) :
  List.length (replace_nth n l v) = List.length l.
Proof.
  (* replace_nth 不改变长度 *)
  revert v l.
  induction n; intros v l.
  - destruct l; simpl; auto.
  - destruct l; simpl.
    + reflexivity.
    + f_equal. apply IHn.
Qed.

Lemma nth_replace_nth {A} (n: nat) (v d: A) (l: list A) :
  (n < List.length l)%nat ->
  nth n (replace_nth n l v) d = v.
Proof.
  (* 在合法索引处取到新值 *)
  revert l.
  induction n; intros l Hlen; destruct l; simpl in *; try lia; auto.
  apply IHn; lia.
Qed.

Lemma nth_replace_nth_neq {A} (i j: nat) (v d: A) (l: list A) :
  i <> j ->
  nth j (replace_nth i l v) d = nth j l d.
Proof.
  (* 非目标索引处保持不变 *)
  revert i l.
  induction j; intros i l Hneq; destruct l; simpl;
    try (destruct i; simpl; try congruence; reflexivity).
  - destruct i; simpl; try reflexivity.
    apply IHj. congruence.
Qed.


Lemma sublist_replace_prefix {A} (l: list A) (i: Z) (v: A) :
  0 <= i ->
  sublist 0 i (replace_Znth i v l) = sublist 0 i l.
Proof.
  intros.
  (* 前缀子串只依赖前 i 项 *)
  unfold sublist, replace_Znth.
  rewrite firstn_replace_nth_nat.
  reflexivity.
Qed.

Lemma Zlength_replace_Znth {A} (l: list A) (i: Z) (v: A) :
  Zlength (replace_Znth i v l) = Zlength l.
Proof.
  (* Zlength 与 list length 对齐 *)
  unfold replace_Znth.
  rewrite !Zlength_correct, length_replace_nth.
  reflexivity.
Qed.

Lemma Znth_replace_eq {A} (l: list A) (i: Z) (v d: A) :
  0 <= i < Zlength l ->
  Znth i (replace_Znth i v l) d = v.
Proof.
  intros [Hi0 Hi1].
  (* 转换到 nat 索引后使用 nth_replace_nth *)
  unfold replace_Znth, Znth.
  replace (Z.to_nat i) with (Z.to_nat i + 0)%nat by lia.
  apply nth_replace_nth.
  rewrite Zlength_correct in Hi1.
  apply Z2Nat.inj_lt in Hi1; lia.
Qed.

Lemma Znth_replace_neq {A} (l: list A) (i j: Z) (v d: A) :
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  i <> j ->
  Znth j (replace_Znth i v l) d = Znth j l d.
Proof.
  intros Hi Hj Hneq.
  (* 不同索引时结果保持不变 *)
  unfold replace_Znth, Znth.
  apply nth_replace_nth_neq.
  intros Heq.
  apply Hneq.
  apply Z2Nat.inj; lia.
Qed.

Lemma zeros_succ : forall n, 0 <= n -> zeros (n + 1) = (zeros n ++ (0 :: nil))%list.
Proof.
  intros.
  (* zeros 定义为 repeat 0：用 repeat_app 展开 *)
  unfold zeros.
  rewrite Z2Nat.inj_add by lia.
  simpl.
  rewrite repeat_app.
  simpl.
  reflexivity.
Qed.

Definition store_map_pointwise_emp := @store_map_empty.

Lemma store_map_empty :
  forall {A B} (P: A -> B -> Assertion),
    store_map P (@empty_map A B) --||-- emp.
Proof.
  intros A B P.
  unfold store_map, empty_map.
  unfold logic_equiv, derivable1.
  unfold exp, andp, coq_prop, iter_sepcon, emp.
  split.
  (* 从 store_map empty_map 推出 iter_sepcon 为空列表，因此是 emp *)
  - intros st H.
    destruct H as [l [[HIn HNoDup] HIter]].
    destruct l.
    + exact HIter.
    + exfalso.
      match goal with
      | HIn0: (forall x, In x (?hd :: ?tl) <-> exists b, None = Some b) |- _ =>
          pose proof (HIn0 hd) as Hhd;
          assert (In hd (hd :: tl)) as Hin by (simpl; auto);
          apply Hhd in Hin;
          destruct Hin as [b Hb];
          discriminate Hb
      end.
  (* 反向：由 emp 构造空列表作为 store_map 的见证 *)
  - intros st Hemp.
    exists (@nil A).
    split.
    + split.
      * intros a; split; intros Hin.
        { inversion Hin. }
        { destruct Hin as [b Hb]. discriminate Hb. }
      * constructor.
    + exact Hemp.
Qed.

(* -------- init_hashtbl -------- *)
Definition b_init (x : Z) : option (Z * list Z):= 
  if (Z.geb x 0 && Z.ltb x 211)%bool then Some (0, nil) 
  else None.

Lemma Zlength_zeros : forall n, 0 <= n -> Zlength (zeros n) = n.
Proof.
  intros n Hn.
  (* zeros = repeat 0：Zlength 与 repeat_length 对应 *)
  unfold zeros.
  rewrite Zlength_correct.
  rewrite repeat_length.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma Znth_zeros : forall n i d,
  0 <= i < n ->
  Znth i (zeros n) d = 0.
Proof.
  intros n i d Hi.
  (* 把 Znth 化为 nth_repeat *)
  assert (Hrange : 0 <= i < Zlength (zeros n)).
  { rewrite Zlength_zeros by lia. lia. }
  rewrite (Znth_indep (zeros n) i d 0) by exact Hrange.
  unfold Znth, zeros.
  rewrite nth_repeat by (apply Z2Nat.inj_lt; lia).
  reflexivity.
Qed.

Lemma Zlength_zeros_211 : Zlength (zeros 211) = 211.
Proof.
  apply Zlength_zeros; lia.
Qed.

Lemma empty_contain_all_addrs : contain_all_addrs empty_map nil.
Proof. 
  unfold contain_all_addrs, empty_map. 
  (* 空映射只包含空地址集合 *)
  intros; split; intros; simpl in *; [destruct H; discriminate | tauto]. 
Qed.

Lemma empty_contain_all_correct_addrs: contain_all_correct_addrs empty_map b_init.
Proof.
  unfold contain_all_correct_addrs, empty_map, b_init. split; intros.
  - destruct H as [key [? ?]].
    discriminate.
  (* 反向：b_init 的每个桶是空链表，因此不可能包含地址 *)
  - exfalso.
    destruct H as [ph [l [Hb Hin]]].
    destruct (((Z.geb i 0) && (Z.ltb i 211))%bool) eqn:Hi.
    + (* case true *)
      simpl in *.
      inversion Hb; subst.     (* 得到 l = nil *)
      simpl in Hin.            (* H0 : In p nil *)
      contradiction.          (* 或者: inversion H0. *)
    + (* case false *)
      discriminate.
Qed.


Lemma empty_repr_all_heads : repr_all_heads (zeros 211) b_init.
Proof.
  unfold repr_all_heads, b_init. intros.
  split; intros.
  (* 正向：从 b_init 的 Some 推出范围与数组对应为 0 *)
  - destruct H as [l Hl].
    remember (((Z.geb i 0) && (Z.ltb i 211))%bool) as b eqn:Hb.
    destruct b.
    + inversion Hl; subst; clear Hl.
      assert (Hb' : ((Z.geb i 0) && (Z.ltb i 211))%bool = true).
      { now symmetry. }
      (* 通过 apply 和 destruct 继续推理 *)
      apply andb_true_iff in Hb'.
      destruct Hb' as [Hi0 Hi211].
      apply Z.geb_le in Hi0.
      apply Z.ltb_lt in Hi211.
      split.
      * split; [exact Hi0 | unfold zeros; rewrite Zlength_correct;
          rewrite repeat_length; rewrite Z2Nat.id by lia; lia].
      * assert (Hz : Znth i (zeros 211) 0 = 0) by (apply Znth_zeros; lia).
        exact Hz.
    + discriminate.
  (* 反向：从数组位置为 0 反推 b_init i = Some (0, nil) *)
  - destruct H as [Hi Hnth].
    destruct Hi as [Hi0 Hi1].
    assert (Hrange : 0 <= i < 211).
    { split.
      - exact Hi0.
      - rewrite <- Zlength_zeros_211. exact Hi1. }
    assert (Hz : Znth i (zeros 211) 0 = 0) by (apply Znth_zeros; exact Hrange).
    assert (Hp : p = 0) by (eapply eq_trans; [exact (eq_sym Hnth) | exact Hz]).
    clear Hnth.
    subst p.
    exists nil.
    unfold b_init.
    assert (Hge : Z.geb i 0 = true) by (apply Z.geb_le; lia).
    assert (Hlt : Z.ltb i 211 = true) by (apply Z.ltb_lt; lia).
    rewrite Hge, Hlt.
    reflexivity.
Qed.

Lemma In_Zseq_iff :
  forall s len a,
    In a (Zseq s len) <-> exists n, (n < len)%nat /\ a = s + Z.of_nat n.
Proof.
  intros s len; revert s.
  (* 对 len 归纳，逐步拆分 Zseq 的 head/tail *)
  induction len; intros s a; simpl.
  - split; intros H.
    + contradiction.
    + destruct H as [n [Hlt _]]. lia.
  - split; intros H.
    + destruct H as [Heq | Hin].
      * exists 0%nat. split; [lia | subst; simpl; lia].
      * apply IHlen in Hin.
        destruct Hin as [n [Hlt Heq]].
        exists (S n). split; [lia | subst; simpl; lia].
    + destruct H as [n [Hlt Heq]].
      destruct n.
      * simpl in Heq. left. subst. lia.
      * right. apply IHlen.
        exists n. split; [lia | subst; simpl; lia].
Qed.

Lemma In_Zseq_0_iff : forall a len,
  In a (Zseq 0 len) <-> 0 <= a < Z.of_nat len.
Proof.
  intros a len; split; intros H.
  (* 0 起始时可以转成整数范围判断 *)
  - apply In_Zseq_iff in H.
    destruct H as [n [Hlt Heq]].
    subst. split.
    + lia.
    + apply Nat2Z.inj_lt in Hlt. lia.
  - destruct H as [Hge Hlt].
    apply In_Zseq_iff.
    exists (Z.to_nat a). split.
    + rewrite <- Nat2Z.id.
      apply Z2Nat.inj_lt; lia.
    + rewrite Z2Nat.id by lia. lia.
Qed.

Lemma Zseq_NoDup : forall s len, NoDup (Zseq s len).
Proof.
  intros s len; revert s.
  (* Zseq 是严格递增序列，因此无重复 *)
  induction len; intros s; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply In_Zseq_iff in Hin.
      destruct Hin as [n [Hlt Heq]]. lia.
    + apply IHlen.
Qed.

Lemma dll_nil_equiv: forall x_up,
  dll NULL x_up nil --||-- emp.
Proof.
  intros x_up.
  split.
  - simpl dll.
    Intros_p Hnull.
    cancel.
  - simpl dll.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma dll_null: dll 0 NULL nil --||-- emp.
Proof.
  apply dll_nil_equiv.
Qed.

Lemma store_sll_null: emp |-- store_map store_sll b_init.
Proof.
  refine (proj2
    (@store_map_pointwise_emp
       Z (addr * list addr) store_sll b_init _ _)).
  - exists (Zseq 0 211%nat).
    split.
    + intros a; split; intros Hin.
      * exists (0, @nil addr).
        unfold b_init.
        apply In_Zseq_0_iff in Hin.
        destruct Hin as [Hge Hlt].
        assert (Hgeb : Z.geb a 0 = true) by (apply Z.geb_le; lia).
        assert (Hltb : Z.ltb a 211 = true) by (apply Z.ltb_lt; lia).
        rewrite Hgeb, Hltb. reflexivity.
      * destruct Hin as [bucket Hb].
        unfold b_init in Hb.
        destruct ((Z.geb a 0 && Z.ltb a 211)%bool) eqn:Hrange;
          try discriminate.
        apply andb_true_iff in Hrange as [Hge Hlt].
        apply Z.geb_le in Hge.
        apply Z.ltb_lt in Hlt.
        apply In_Zseq_0_iff. lia.
    + apply Zseq_NoDup.
  - intros a.
    unfold b_init.
    destruct ((Z.geb a 0 && Z.ltb a 211)%bool) eqn:Hrange.
    + right.
      intros bucket Hb.
      injection Hb as Hb.
      subst bucket.
      unfold store_sll.
      split.
      * simpl sll.
        Intros_p Hnull.
        cancel.
      * simpl sll.
        split_pure_spatial.
        -- cancel.
        -- dump_pre_spatial. reflexivity.
    + left. reflexivity.
Qed.


Lemma store_name_null: emp |-- store_map store_name empty_map.
Proof.
  (* 空映射的 store_map 与 emp 等价 *)
  setoid_rewrite <- (store_map_empty store_name).
  cancel.
Qed.

Lemma KP_insert_map_ext_same :
  forall (m: list Z -> option addr) k p,
    m k = Some p ->
    (forall key, KP.insert_map m k p key = m key).
Proof.
  intros m k p Hmk key.
  (* key 等于 k 或不等于 k 的两种情况 *)
  destruct (list_eq_dec Z.eq_dec key k) as [Heq|Hneq].
  - subst. rewrite KP.insert_map_same. rewrite Hmk. reflexivity.
  - rewrite KP.insert_map_diff by (intro Heq; apply Hneq; symmetry; exact Heq).
    reflexivity.
Qed.

Definition b' (b : Z -> option (addr * list addr)) (idx new : Z)
  : Z -> option (addr * list addr) :=
  fun j =>
    if Z.eq_dec j idx then
      match b j with
      | Some (_old_head, l_old) => Some (new, new :: l_old)
      | None => Some (new, new :: nil)
      end
    else b j.

Lemma contain_all_addrs_insert_cons :
  forall (m : list Z -> option addr) (l : list addr) (k : list Z) (p : addr),
    contain_all_addrs m l ->
    m k = None ->
    contain_all_addrs (KP.insert_map m k p) (p :: l).
Proof.
  intros m l k p Hcontain Hmk.
  unfold contain_all_addrs in *.
  intro p0.
  split; intros H.
  (* 正向：在新 map 中出现的地址要么是新插入的 p，要么来自旧 l *)
  - destruct H as [key Hkey].
    destruct (list_eq_dec Z.eq_dec key k) as [Heq|Hneq].
    + subst key.
      rewrite KP.insert_map_same in Hkey.
      inversion Hkey; subst.
      simpl; auto.
    + rewrite KP.insert_map_diff in Hkey
        by (intro Heq; apply Hneq; symmetry; exact Heq).
      specialize (Hcontain p0).
      assert (Hinl : In p0 l).
      { apply (proj1 Hcontain). exists key; exact Hkey. }
      simpl; right; exact Hinl.
  (* 反向：列表中地址存在则可构造对应 key *)
  - simpl in H.
    destruct H as [Hp | Hin].
    + subst p0.
      exists k.
      rewrite KP.insert_map_same.
      reflexivity.
    + specialize (Hcontain p0).
      apply (proj2 Hcontain) in Hin.
      destruct Hin as [key Hkey].
      exists key.
      destruct (list_eq_dec Z.eq_dec key k) as [Heq|Hneq].
      * subst. rewrite Hmk in Hkey. discriminate.
      * rewrite KP.insert_map_diff
          by (intro Heq; apply Hneq; symmetry; exact Heq).
        exact Hkey.
Qed.

Lemma repr_all_heads_update :
  forall lh b idx new,
    0 <= idx < Zlength lh ->
    repr_all_heads lh b ->
    (* 需要从旧 repr_all_heads 推出 b idx = Some(old_head, l_old) 的存在性 *)
    repr_all_heads (replace_Znth idx new lh) (b' b idx new).
Proof.
  intros lh b idx new Hidx Hrepr.
  unfold repr_all_heads in *.
  intros j p; split; intros H.
  (* 正向：从 b' 的 Some 推回数组范围与 Znth 等式 *)
  - destruct (Z.eq_dec j idx) as [Heq|Hneq].
    + subst j.
      (* j=idx：b' 直接更新头结点 *)
      destruct H as [l Hb].
      unfold b' in Hb.
      destruct (Z.eq_dec idx idx) as [_|Hneq].
      * simpl in Hb.
        destruct (b idx) as [pl | ] eqn:Hbidx.
        -- destruct pl as [ph l_old].
           inversion Hb; subst; clear Hb.
           split.
           ++ rewrite Zlength_replace_Znth. exact Hidx.
           ++ rewrite (Znth_replace_eq lh idx p 0) by exact Hidx. reflexivity.
        -- inversion Hb; subst; clear Hb.
           split.
           ++ rewrite Zlength_replace_Znth. exact Hidx.
           ++ rewrite (Znth_replace_eq lh idx p 0) by exact Hidx. reflexivity.
      * exfalso. apply Hneq. reflexivity.
    + (* j<>idx：继承旧的 repr_all_heads *)
      destruct H as [l Hb].
      unfold b' in Hb.
      destruct (Z.eq_dec j idx) as [Heq|Hneq'].
      * exfalso. apply Hneq. exact Heq.
      * simpl in Hb.
      specialize (Hrepr j p) as Hreprj.
      destruct (proj1 Hreprj (ex_intro _ l Hb)) as [Hrange Hnth].
      split;
        [rewrite Zlength_replace_Znth; exact Hrange
        |rewrite (Znth_replace_neq lh idx j new 0)
           by (try exact Hidx; try exact Hrange;
               intro Heq; apply Hneq; symmetry; exact Heq);
         exact Hnth].
  (* 反向：从数组范围与 Znth 等式构造 b' 的 Some 见证 *)
  - destruct (Z.eq_dec j idx) as [Heq|Hneq].
    + subst j.
      (* j=idx：构造 new::l_old 或 new::nil *)
      destruct H as [Hrange Hnth].
      pose proof (Znth_replace_eq lh idx new 0 Hidx) as Hz.
      rewrite Hz in Hnth. subst p.
      destruct (b idx) as [pl | ] eqn:Hbidx.
      * destruct pl as [ph l_old].
        exists (new :: l_old).
        unfold b'. destruct (Z.eq_dec idx idx) as [_|Hneq].
        -- rewrite Hbidx. reflexivity.
        -- exfalso. apply Hneq. reflexivity.
      * exists (new :: nil).
        unfold b'. destruct (Z.eq_dec idx idx) as [_|Hneq].
        -- rewrite Hbidx. reflexivity.
        -- exfalso. apply Hneq. reflexivity.
    + (* j<>idx：回退到旧 b 的见证 *)
      destruct H as [Hrange Hnth].
      rewrite Zlength_replace_Znth in Hrange.
      assert (Hnth' : Znth j lh 0 = p).
      { rewrite (Znth_replace_neq lh idx j new 0) in Hnth
          by (try exact Hidx; try exact Hrange;
              intro Heq; apply Hneq; symmetry; exact Heq).
        exact Hnth. }
      specialize (Hrepr j p) as Hreprj.
      destruct (proj2 Hreprj (conj Hrange Hnth')) as [l Hb].
      exists l.
      unfold b'.
      destruct (Z.eq_dec j idx) as [Heq|Hneq'].
      * exfalso. apply Hneq. exact Heq.
      * simpl. exact Hb.
Qed.

Lemma dll_singleton_from_fields :
  forall x,
    x <> NULL ->
    &(x # "blist" ->ₛ "down") # Ptr |-> NULL **
    &(x # "blist" ->ₛ "up") # Ptr |-> NULL
    |-- dll x NULL (x :: nil).
Proof.
  intros x Hx.
  simpl dll.
  Exists NULL.
  fold (dll NULL x nil).
  rewrite dll_nil_equiv.
  normalize.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact Hx.
    + dump_pre_spatial. reflexivity.
Qed.

(* ------------------ store_map store_sll update (admit for now) ------------------ *)


Lemma contain_all_correct_addrs_insert_update :
  forall (m: list Z -> option addr) (b: Z -> option (addr * list addr))
         (k: list Z) (p: addr) (idx: Z),
    m k = None ->
    idx = hash_string k mod NBUCK ->
    contain_all_correct_addrs m b ->
    contain_all_correct_addrs (KP.insert_map m k p) (b' b idx p).
Proof.
  intros m b k p idx Hmk Hidx Hcorr.
  (* 新 key 的哈希值固定为 idx，更新 b 的对应桶 *)
  pose proof Hidx as Hidx0.
  unfold contain_all_correct_addrs in *.
  intros.
  split ; intros.
  (* 正向：新插入的 key 映射到 idx 桶，旧 key 保持一致 *)
  - destruct H as [key [? ?]].
    destruct (list_eq_dec Z.eq_dec key k) as [Heq|Hneq].
    + subst key.
      rewrite KP.insert_map_same in H0.
      inversion H0; subst p0.
      unfold b'.
      destruct (Z.eq_dec i idx) ; try lia.
      destruct (b i) as [[ph l] | ] eqn:Hbidx.
      * exists p, (p :: l). split ; auto. left. auto.
      * simpl. exists p. exists (p :: nil). split; [reflexivity | simpl; auto].
    + rewrite KP.insert_map_diff in H0 ; auto.
      specialize (Hcorr i p0).
      unfold b'.
      assert (exists key, hash_string key mod NBUCK = i /\ m key = Some p0).
      { exists key. split; tauto. }
      rewrite Hcorr in H1.
      destruct H1 as [ph [l [? ?]]].
      rewrite H1.    
      destruct (Z.eq_dec i idx).
      * exists p, (p :: l). split; [reflexivity | simpl; auto].
      * simpl. exists ph, l. split ; tauto.
  (* 反向：从桶中的元素反推 key；新插入的元素只能来自 k *)
  - unfold b' in H.
    destruct (Z.eq_dec i idx).
    + subst i.
      specialize (Hcorr idx p0).
      destruct (b idx).
      * destruct H as [ph [l [? ?]]].
        destruct p1.
        inversion H. subst ph l.
        destruct H0 ; try lia.
        -- exists k. split ; auto.
          rewrite KP.insert_map_same. subst. auto.
        -- assert (exists ph l, Some (a, l0) = Some (ph, l) /\ In p0 l).
           { exists a, l0. split ; tauto. }
           rewrite <- Hcorr in H1.
           destruct H1 as [key' [? ?]].
           exists key'. split ; auto.
           destruct (list_eq_dec Z.eq_dec k key').
           ++ subst. congruence.
           ++ rewrite KP.insert_map_diff ; auto.
      * destruct H as [ph [l [? ?]]].
        inversion H. subst ph l.
        destruct H0 ; try lia.
        -- exists k. split ; auto.
           rewrite KP.insert_map_same. subst. auto.
        -- simpl in H0. lia.
    + pose proof H as H1.
      rewrite <- Hcorr in H1.
      destruct H1 as [key [? ?]].
      exists key. split ; auto.
      destruct (list_eq_dec Z.eq_dec key k).
      * subst key. congruence.
      * rewrite KP.insert_map_diff ; auto.
Qed.

Lemma store_map_store_sll_update_at_idx :
  forall (lh: list addr) (b: Z -> option (addr * list addr))
         (idx new: Z) (l_idx: list addr),
    0 <= idx < NBUCK ->
    new <> NULL ->
    &(new # "blist" ->ₛ "next") <> NULL ->
    b idx = Some (Znth idx lh 0, l_idx) ->
    &(new # "blist" ->ₛ "next") # Ptr |-> Znth idx lh 0 **
    store_map store_sll b
    |-- store_map store_sll (b' b idx new).
Proof.
  intros lh b idx new l_idx Hidx Hnew Hnext Hbidx.
  set (old_head := Znth idx lh 0).
  (* 先把 store_map 在 idx 处拆出，再把头指针换成 new *)
  sep_apply (store_map_split store_sll idx (old_head, l_idx) b Hbidx).
  assert (Houtside : forall j, j <> idx -> b j = b' b idx new j).
  { intros j Hneq. unfold b'.
    destruct (Z.eq_dec j idx) as [Heq|Hneq'].
    - exfalso. apply Hneq. exact Heq.
    - reflexivity. }
  pose proof (store_map_missing_i_equiv store_sll b (b' b idx new) idx Houtside) as Heq.
  destruct Heq as [Hmiss _].
  sep_apply Hmiss.
  (* 本桶内容更新为 new :: l_idx *)
  assert (Hsll :
            &(new # "blist" ->ₛ "next") # Ptr |-> old_head **
            store_sll idx (old_head, l_idx)
            |-- store_sll idx (new, new :: l_idx)).
  { unfold store_sll.
    apply sll_head_append; assumption. }
  sep_apply Hsll.
  assert (Hb' : b' b idx new idx = Some (new, new :: l_idx)).
  { unfold b'.
    destruct (Z.eq_dec idx idx) as [_|Hneq].
    - rewrite Hbidx. reflexivity.
    - exfalso. apply Hneq. reflexivity. }
  sep_apply (store_map_merge store_sll idx (new, new :: l_idx) (b' b idx new) Hb').
  cancel.
Qed.

(** ********* Case-specific lemmas merged from hashtable ********* *)

Lemma repr_all_heads_update_bucket__findref_results :
  forall lh b i old_head old_l new_head new_l,
    0 <= i < Zlength lh ->
    b i = Some (old_head, old_l) ->
    repr_all_heads lh b ->
    repr_all_heads
      (replace_Znth i new_head lh)
      (fun j => if Z.eq_dec j i
                then Some (new_head, new_l) else b j).
Proof.
  intros lh b i old_head old_l new_head new_l Hi Hb Hrepr.
  unfold repr_all_heads in *.
  intros j p.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j.
    split.
    + intros [l Hlookup].
      destruct (Z.eq_dec i i) as [_ | Hfalse] in Hlookup;
        [| contradiction].
      inversion Hlookup.
      subst p.
      split.
      * rewrite Zlength_replace_Znth.
        exact Hi.
      * apply Znth_replace_Znth_Same.
        exact Hi.
    + intros [Hbounds Hp].
      rewrite Znth_replace_Znth_Same in Hp by exact Hi.
      subst p.
      exists new_l.
      destruct (Z.eq_dec i i); [reflexivity | contradiction].
  - split.
    + intros [l Hlookup].
      assert (Hlookup_old : b j = Some (p, l)).
      { destruct (Z.eq_dec j i) as [Hfalse | _] in Hlookup;
          [contradiction | exact Hlookup]. }
      destruct (proj1 (Hrepr j p)) as [Hbounds Hp].
      { exists l.
        exact Hlookup_old. }
      split.
      * rewrite Zlength_replace_Znth.
        exact Hbounds.
      * rewrite Znth_replace_Znth_Diff.
        -- exact Hp.
        -- exact Hi.
        -- exact Hbounds.
        -- congruence.
    + intros [Hbounds Hp].
      assert (Hbounds_old : 0 <= j < Zlength lh).
      { rewrite Zlength_replace_Znth in Hbounds.
        exact Hbounds. }
      assert (Hp_old : Znth j lh 0 = p).
      { rewrite Znth_replace_Znth_Diff in Hp.
        - exact Hp.
        - exact Hi.
        - exact Hbounds_old.
        - congruence. }
      destruct (proj2 (Hrepr j p)) as [l Hlookup_old].
      { split; assumption. }
      exists l.
      destruct (Z.eq_dec j i); [contradiction | exact Hlookup_old].
Qed.

Lemma forall2_right_lookup__clear_transition :
  forall (A B : Type) (R : A -> B -> Prop) la lb b,
    Forall2 R la lb ->
    In b lb ->
    exists a, In a la /\ R a b.
Proof.
  intros A B R la lb b Hrel.
  induction Hrel; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y.
      exists x.
      auto.
    + destruct (IHHrel Hin) as [a [Ha HR]].
      exists a.
      auto.
Qed.

Lemma forall2_left_lookup__clear_transition :
  forall (A B : Type) (R : A -> B -> Prop) la lb a,
    Forall2 R la lb ->
    In a la ->
    exists b, In b lb /\ R a b.
Proof.
  intros A B R la lb a Hrel.
  induction Hrel; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst x.
      exists y.
      auto.
    + destruct (IHHrel Hin) as [b [Hb HR]].
      exists b.
      auto.
Qed.

Lemma forall2_nodup_right__clear_transition :
  forall (A B : Type) (R : A -> B -> Prop) la lb,
    (forall a1 a2 b, R a1 b -> R a2 b -> a1 = a2) ->
    NoDup la ->
    Forall2 R la lb ->
    NoDup lb.
Proof.
  intros A B R la lb Hfunctional Hnodup Hrel.
  induction Hrel.
  - constructor.
  - inversion Hnodup as [|a la' Hnotin Hnodup']; subst.
    constructor.
    + intro Hin.
      destruct
        (forall2_right_lookup__clear_transition A B R l l' y Hrel Hin)
        as [a' [Ha' HR']].
      apply Hnotin.
      replace x with a' by (eapply Hfunctional; eauto).
      exact Ha'.
    + apply IHHrel.
      exact Hnodup'.
Qed.

Lemma forall2_remove_map__clear_transition :
  forall m key li ks,
    Forall2 (fun p k => m k = Some p) li ks ->
    ~ In key ks ->
    Forall2
      (fun p k => KP.remove_map m key k = Some p)
      li ks.
Proof.
  intros m key li ks Hrel.
  induction Hrel; intros Hnotin.
  - constructor.
  - constructor.
    + rewrite KP.remove_map_diff.
      * exact H.
      * intro Heq.
        apply Hnotin.
        left.
        symmetry.
        exact Heq.
    + apply IHHrel.
      intro Hin.
      apply Hnotin.
      right.
      exact Hin.
Qed.

Lemma key_list_for_addrs_of_forall2__clear_transition :
  forall m li ks,
    Forall2 (fun p k => m k = Some p) li ks ->
    NoDup ks ->
    key_list_for_addrs m li ks.
Proof.
  intros m li.
  revert m.
  induction li as [|p li IH]; intros m ks Hrel Hnodup.
  - inversion Hrel.
    simpl.
    exact I.
  - inversion Hrel as [|p' k li' ks' Hmap Htail]; subst.
    inversion Hnodup as [|k' ks'' Hnotin Hnodup']; subst.
    simpl.
    split.
    + exact Hmap.
    + eapply IH.
      * apply forall2_remove_map__clear_transition.
        -- exact Htail.
        -- exact Hnotin.
      * exact Hnodup'.
Qed.

Lemma choose_bucket_keys__clear_transition :
  forall (m : list Z -> option addr) (i : Z) (li : list addr),
    (forall p, In p li ->
      exists k, hash_string k mod NBUCK = i /\
                m k = Some p) ->
    exists ks, Forall2 (fun p k => m k = Some p) li ks.
Proof.
  intros m i li.
  induction li as [|p li IH]; intros Hchoose.
  - exists nil.
    constructor.
  - destruct (Hchoose p (or_introl eq_refl)) as [k [Hhash Hmap]].
    destruct IH as [ks Hrel].
    { intros p' Hin.
      apply Hchoose.
      right.
      exact Hin. }
    exists (k :: ks).
    constructor; assumption.
Qed.

Lemma remove_keys_not_in__clear_transition :
  forall m ks k,
    ~ In k ks ->
    KP.remove_keys m ks k = m k.
Proof.
  intros m ks.
  revert m.
  induction ks as [|a ks IH]; intros m k Hnotin; simpl.
  - reflexivity.
  - rewrite IH.
    + apply KP.remove_map_diff.
      intro Heq.
      apply Hnotin.
      left.
      exact Heq.
    + intro Hin.
      apply Hnotin.
      right.
      exact Hin.
Qed.

Lemma remove_keys_preserves_none__clear_transition :
  forall m ks k,
    m k = None ->
    KP.remove_keys m ks k = None.
Proof.
  intros m ks.
  revert m.
  induction ks as [|a ks IH]; intros m k Hnone; simpl.
  - exact Hnone.
  - apply IH.
    destruct (list_eq_dec Z.eq_dec a k) as [Heq | Hneq].
    + subst a.
      apply KP.remove_map_same.
    + rewrite KP.remove_map_diff.
      * exact Hnone.
      * exact Hneq.
Qed.

Lemma remove_keys_in__clear_transition :
  forall m ks k,
    In k ks ->
    KP.remove_keys m ks k = None.
Proof.
  intros m ks.
  revert m.
  induction ks as [|a ks IH]; intros m k Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst a.
      apply remove_keys_preserves_none__clear_transition.
      apply KP.remove_map_same.
    + apply IH.
      exact Hin.
Qed.

Lemma remaining_after_remove_bucket__clear_transition :
  forall m ks i,
    keys_exact_bucket m i ks ->
    forall m0,
      remaining_after_bucket_index m0 m i ->
      remaining_after_bucket_index
        m0 (KP.remove_keys m ks) (i + 1).
Proof.
  intros m ks i Hexact m0 Hremaining.
  unfold remaining_after_bucket_index in *.
  intros k p.
  split.
  - intro Hremoved.
    assert (Hnotin : ~ In k ks).
    { intro Hin.
      rewrite (remove_keys_in__clear_transition m ks k Hin) in Hremoved.
      discriminate. }
    rewrite (remove_keys_not_in__clear_transition m ks k Hnotin)
      in Hremoved.
    destruct (proj1 (Hremaining k p) Hremoved) as [Hm0 Hlower].
    split.
    + exact Hm0.
    + assert (Hneq : hash_string k mod NBUCK <> i).
      { intro Heq.
        apply Hnotin.
        apply (proj2 (Hexact k p Hremoved)).
        exact Heq. }
      lia.
  - intros [Hm0 Hlower].
    assert (Hm : m k = Some p).
    { apply (proj2 (Hremaining k p)).
      split; [exact Hm0 | lia]. }
    assert (Hnotin : ~ In k ks).
    { intro Hin.
      pose proof (proj1 (Hexact k p Hm) Hin) as Heq.
      lia. }
    rewrite remove_keys_not_in__clear_transition by exact Hnotin.
    exact Hm.
Qed.

Lemma bucket_key_list_exists__clear_transition :
  forall m b i head li,
    (forall k1 k2 p,
      m k1 = Some p -> m k2 = Some p -> k1 = k2) ->
    NoDup li ->
    contain_all_correct_addrs m b ->
    b i = Some (head, li) ->
    exists ks,
      key_list_for_addrs m li ks /\
      keys_exact_bucket m i ks /\
      (forall m0,
        remaining_after_bucket_index m0 m i ->
        remaining_after_bucket_index
          m0 (KP.remove_keys m ks) (i + 1)).
Proof.
  intros m b i head li Hinjective Hnodup Hcontain Hb.
  assert (Hchoose :
    forall p, In p li ->
      exists k,
        hash_string k mod NBUCK = i /\
        m k = Some p).
  { intros p Hin.
    apply (proj2 (Hcontain i p)).
    exists head, li.
    auto. }
  destruct (choose_bucket_keys__clear_transition m i li Hchoose)
    as [ks Hrel].
  assert (Hnodup_ks : NoDup ks).
  { eapply
      (forall2_nodup_right__clear_transition
        addr (list Z) (fun p k => m k = Some p) li ks).
    - intros p1 p2 k Hmap1 Hmap2.
      pose proof (eq_trans (eq_sym Hmap1) Hmap2) as Heq.
      inversion Heq.
      reflexivity.
    - exact Hnodup.
    - exact Hrel. }
  exists ks.
  split.
  - eapply key_list_for_addrs_of_forall2__clear_transition; eauto.
  - split.
    + unfold keys_exact_bucket.
      intros k p Hmap.
      split.
      * intro Hin.
        destruct
          (forall2_right_lookup__clear_transition
            addr (list Z) (fun p0 k0 => m k0 = Some p0)
            li ks k Hrel Hin) as [p' [Hp' Hmap']].
        destruct (Hchoose p' Hp') as [k' [Hhash Hmap_k']].
        assert (Heqk : k' = k) by (eapply Hinjective; eauto).
        subst k'.
        exact Hhash.
      * intro Hhash.
        assert (Hin_p : In p li).
        { assert (Hbucket :
            exists ph l0, b i = Some (ph, l0) /\ In p l0).
          { apply (proj1 (Hcontain i p)).
            exists k.
            auto. }
          destruct Hbucket as [ph [l0 [Hb0 Hin]]].
          rewrite Hb in Hb0.
          inversion Hb0.
          subst l0.
          exact Hin. }
        destruct
          (forall2_left_lookup__clear_transition
            addr (list Z) (fun p0 k0 => m k0 = Some p0)
            li ks p Hrel Hin_p) as [k' [Hk' Hmap']].
        assert (Heqk : k' = k) by (eapply Hinjective; eauto).
        subst k'.
        exact Hk'.
    + apply remaining_after_remove_bucket__clear_transition.
      unfold keys_exact_bucket.
      intros k p Hmap.
      split.
      * intro Hin.
        destruct
          (forall2_right_lookup__clear_transition
            addr (list Z) (fun p0 k0 => m k0 = Some p0)
            li ks k Hrel Hin) as [p' [Hp' Hmap']].
        destruct (Hchoose p' Hp') as [k' [Hhash Hmap_k']].
        assert (Heqk : k' = k) by (eapply Hinjective; eauto).
        subst k'.
        exact Hhash.
      * intro Hhash.
        assert (Hin_p : In p li).
        { assert (Hbucket :
            exists ph l0, b i = Some (ph, l0) /\ In p l0).
          { apply (proj1 (Hcontain i p)).
            exists k.
            auto. }
          destruct Hbucket as [ph [l0 [Hb0 Hin]]].
          rewrite Hb in Hb0.
          inversion Hb0.
          subst l0.
          exact Hin. }
        destruct
          (forall2_left_lookup__clear_transition
            addr (list Z) (fun p0 k0 => m k0 = Some p0)
            li ks p Hrel Hin_p) as [k' [Hk' Hmap']].
        assert (Heqk : k' = k) by (eapply Hinjective; eauto).
        subst k'.
        exact Hk'.
Qed.

Lemma sll_next_not_in__clear_transition :
  forall l p v h,
    &(p # "blist" ->ₛ "next") # Ptr |-> v ** sll h l |--
    “ ~ In p l ”.
Proof.
  induction l as [|a l IH]; intros p v h; simpl sll.
  - dump_pre_spatial.
    intros [].
  - Intros next.
    subst a.
    prop_apply_p (IH p v next).
    Intros_p Htail.
    destruct (Z.eq_dec h p) as [Heq | Hneq].
    + subst h.
      prop_apply_p
        (dup_store_ptr (&(p # "blist" ->ₛ "next")) v next).
      Intros_p Hfalse.
      contradiction.
    + dump_pre_spatial.
      intros [Heq | Hin].
      * apply Hneq.
        exact Heq.
      * apply Htail.
        exact Hin.
Qed.

Lemma sll_nodup__clear_transition :
  forall h l,
    sll h l |-- “ NoDup l ”.
Proof.
  intros h l.
  revert h.
  induction l as [|a l IH]; intros h; simpl sll.
  - dump_pre_spatial.
    constructor.
  - Intros next.
    subst a.
    prop_apply_p (sll_next_not_in__clear_transition l h next next).
    Intros_p Hnotin.
    prop_apply_p (IH next).
    Intros_p Hnodup.
    dump_pre_spatial.
    constructor; assumption.
Qed.

Lemma store_name_map_injective__clear_transition :
  forall m k1 k2 p,
    m k1 = Some p ->
    m k2 = Some p ->
    store_map store_name m |-- “ k1 = k2 ”.
Proof.
  intros m k1 k2 p Hmap1 Hmap2.
  destruct (list_eq_dec Z.eq_dec k1 k2) as [Heq | Hneq].
  - dump_pre_spatial.
    exact Heq.
  - sep_apply_l_atomic (store_map_split store_name k1 p m Hmap1).
    assert (Houtside : forall key, key <> k1 ->
              m key = KP.remove_map m k1 key).
    { intros key Hkey.
      symmetry.
      apply KP.remove_map_diff.
      congruence. }
    destruct
      (store_map_missing_i_equiv
        store_name m (KP.remove_map m k1) k1 Houtside)
      as [Hto_removed _].
    sep_apply_l_atomic Hto_removed.
    sep_apply_l_atomic
      (store_map_missing_equiv_store_map
        store_name (KP.remove_map m k1) k1
        (KP.remove_map_same m k1)).
    assert (Hmap2' : KP.remove_map m k1 k2 = Some p).
    { rewrite KP.remove_map_diff.
      - exact Hmap2.
      - exact Hneq. }
    sep_apply_l_atomic
      (store_map_split store_name k2 p (KP.remove_map m k1) Hmap2').
    unfold store_name.
    Intros key_addr1 key_addr2.
    prop_apply_p
      (dup_store_ptr (&(p # "blist" ->ₛ "key")) key_addr1 key_addr2).
    Intros_p Hfalse.
    contradiction.
Qed.

Lemma bucket_key_list_exists_remaining__clear_transition :
  forall m0 m b i head li,
    (forall k1 k2 p,
      m k1 = Some p -> m k2 = Some p -> k1 = k2) ->
    NoDup li ->
    contain_all_correct_addrs m0 b ->
    remaining_after_bucket_index m0 m i ->
    b i = Some (head, li) ->
    exists ks, current_bucket_key_list m b i li ks.
Proof.
  intros m0 m b i head li Hinjective Hnodup Hcontain Hremaining Hb.
  assert (Hchoose :
    forall p, In p li ->
      exists k,
        hash_string k mod NBUCK = i /\
        m k = Some p).
  { intros p Hin.
    destruct (proj2 (Hcontain i p)) as [k [Hhash Hm0]].
    { exists head, li.
      auto. }
    exists k.
    split.
    - exact Hhash.
    - apply (proj2 (Hremaining k p)).
      split; [exact Hm0 | lia]. }
  destruct (choose_bucket_keys__clear_transition m i li Hchoose)
    as [ks Hrel].
  assert (Hnodup_ks : NoDup ks).
  { eapply
      (forall2_nodup_right__clear_transition
        addr (list Z) (fun p k => m k = Some p) li ks).
    - intros p1 p2 k Hmap1 Hmap2.
      pose proof (eq_trans (eq_sym Hmap1) Hmap2) as Heq.
      inversion Heq.
      reflexivity.
    - exact Hnodup.
    - exact Hrel. }
  assert (Hkeys : keys_exact_bucket m i ks).
  { unfold keys_exact_bucket.
    intros k p Hmap.
    split.
    - intro Hin.
      destruct
        (forall2_right_lookup__clear_transition
          addr (list Z) (fun p0 k0 => m k0 = Some p0)
          li ks k Hrel Hin) as [p' [Hp' Hmap']].
      destruct (Hchoose p' Hp') as [k' [Hhash Hmap_k']].
      assert (Heqk : k' = k) by (eapply Hinjective; eauto).
      subst k'.
      exact Hhash.
    - intro Hhash.
      assert (Hm0 : m0 k = Some p).
      { apply (proj1 (Hremaining k p)) in Hmap.
        exact (proj1 Hmap). }
      assert (Hin_p : In p li).
      { assert (Hbucket :
          exists ph l0, b i = Some (ph, l0) /\ In p l0).
        { apply (proj1 (Hcontain i p)).
          exists k.
          auto. }
        destruct Hbucket as [ph [l0 [Hb0 Hin]]].
        rewrite Hb in Hb0.
        inversion Hb0.
        subst l0.
        exact Hin. }
      destruct
        (forall2_left_lookup__clear_transition
          addr (list Z) (fun p0 k0 => m k0 = Some p0)
          li ks p Hrel Hin_p) as [k' [Hk' Hmap']].
      assert (Heqk : k' = k) by (eapply Hinjective; eauto).
      subst k'.
      exact Hk'. }
  exists ks.
  unfold current_bucket_key_list.
  split.
  - eapply key_list_for_addrs_of_forall2__clear_transition; eauto.
  - split.
    + exists head.
      exact Hb.
    + split.
      * exact Hkeys.
      * apply remaining_after_remove_bucket__clear_transition.
        exact Hkeys.
Qed.

Lemma replace_Znth_overwrite__clear_transition :
  forall {A : Type} (l : list A) i (a b : A),
    replace_Znth i b (replace_Znth i a l) = replace_Znth i b l.
Proof.
  intros A l i a b.
  unfold replace_Znth.
  set (n := Z.to_nat i).
  clearbody n.
  clear i.
  revert n.
  induction l as [|x l IH]; intros [|n]; simpl; auto.
  f_equal.
  apply IH.
Qed.

Lemma repr_all_heads_clear__clear_transition :
  forall lh b i old li,
    0 <= i < Zlength lh ->
    b i = Some (old, li) ->
    repr_all_heads lh b ->
    repr_all_heads
      (replace_Znth i 0 lh)
      (fun j => if Z.eq_dec j i then Some (0, li) else b j).
Proof.
  intros lh b i old li Hi Hb Hrepr.
  unfold repr_all_heads in *.
  intros j p.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j.
    split.
    + intros [l Hlookup].
      destruct (Z.eq_dec i i) as [_ | Hfalse] in Hlookup;
        [| contradiction].
      inversion Hlookup.
      subst p l.
      split.
      * rewrite Zlength_replace_Znth.
        exact Hi.
      * apply Znth_replace_Znth_Same.
        exact Hi.
    + intros [Hbounds Hhead].
      rewrite Zlength_replace_Znth in Hbounds.
      rewrite Znth_replace_Znth_Same in Hhead by exact Hi.
      subst p.
      exists li.
      destruct (Z.eq_dec i i); [reflexivity | contradiction].
  - split.
    + intros [l Hlookup].
      destruct (Z.eq_dec j i) as [Hfalse | _] in Hlookup;
        [contradiction |].
      destruct (proj1 (Hrepr j p) (ex_intro _ l Hlookup))
        as [Hbounds Hhead].
      split.
      * rewrite Zlength_replace_Znth.
        exact Hbounds.
      * rewrite Znth_replace_Znth_Diff
          by (try exact Hi; try exact Hbounds; congruence).
        exact Hhead.
    + intros [Hbounds Hhead].
      rewrite Zlength_replace_Znth in Hbounds.
      assert (Hhead_old : Znth j lh 0 = p).
      { rewrite Znth_replace_Znth_Diff in Hhead
          by (try exact Hi; try exact Hbounds; congruence).
        exact Hhead. }
      destruct (proj2 (Hrepr j p) (conj Hbounds Hhead_old)) as [l Hl].
      exists l.
      destruct (Z.eq_dec j i); [contradiction | exact Hl].
Qed.

Lemma contain_all_correct_addrs_clear__clear_transition :
  forall m b i old li,
    b i = Some (old, li) ->
    contain_all_correct_addrs m b ->
    contain_all_correct_addrs
      m (fun j => if Z.eq_dec j i then Some (0, li) else b j).
Proof.
  intros m b i old li Hb Hcontain.
  unfold contain_all_correct_addrs in *.
  intros j p.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j.
    split.
    + intro Hkey.
      destruct (proj1 (Hcontain i p) Hkey)
        as [head [l [Hlookup Hin]]].
      rewrite Hb in Hlookup.
      inversion Hlookup.
      subst l.
      exists 0, li.
      split.
      * destruct (Z.eq_dec i i); [reflexivity | contradiction].
      * exact Hin.
    + intros [head [l [Hlookup Hin]]].
      destruct (Z.eq_dec i i) as [_ | Hfalse] in Hlookup;
        [| contradiction].
      inversion Hlookup.
      subst l.
      apply (proj2 (Hcontain i p)).
      exists old, li.
      auto.
  - destruct (Z.eq_dec j i) as [Hfalse | _]; [contradiction |].
    apply Hcontain.
Qed.

Lemma store_map_missing_first_equiv__clear_transition :
  forall {B : Type} (P : Z -> B -> Assertion) m m' i,
    (forall a, i < a -> m a = m' a) ->
    store_map_missing_first_i_Z P m i --||--
    store_map_missing_first_i_Z P m' i.
Proof.
  intros B P m m' i Heq.
  unfold store_map_missing_first_i_Z.
  split.
  - Intros l.
    rename H into Hdom.
    rename H0 into Hnodup.
    Exists l.
    split_pure_spatial.
    + assert (Hmap :
        map (fun a => match m a with
                       | Some b => P a b
                       | None => emp
                       end) l =
        map (fun a => match m' a with
                       | Some b => P a b
                       | None => emp
                       end) l).
      { apply map_ext_in.
        intros a Hin.
        assert (Hlt : i < a).
        { apply Hdom in Hin.
          exact (proj2 Hin). }
        rewrite (Heq a Hlt).
        reflexivity. }
      rewrite Hmap.
      cancel.
    + split_pures.
      * dump_pre_spatial.
        intros a.
        specialize (Hdom a).
        split.
        -- intro Hin.
           apply Hdom in Hin.
           destruct Hin as [[b Hb] Hlt].
           split.
           ++ exists b.
              rewrite <- Heq by exact Hlt.
              exact Hb.
           ++ exact Hlt.
        -- intros [[b Hb] Hlt].
           apply Hdom.
           split.
           ++ exists b.
              rewrite Heq by exact Hlt.
              exact Hb.
           ++ exact Hlt.
      * dump_pre_spatial.
        exact Hnodup.
  - Intros l.
    rename H into Hdom.
    rename H0 into Hnodup.
    Exists l.
    split_pure_spatial.
    + assert (Hmap :
        map (fun a => match m' a with
                       | Some b => P a b
                       | None => emp
                       end) l =
        map (fun a => match m a with
                       | Some b => P a b
                       | None => emp
                       end) l).
      { apply map_ext_in.
        intros a Hin.
        assert (Hlt : i < a).
        { apply Hdom in Hin.
          exact (proj2 Hin). }
        rewrite (Heq a Hlt).
        reflexivity. }
      rewrite Hmap.
      cancel.
    + split_pures.
      * dump_pre_spatial.
        intros a.
        specialize (Hdom a).
        split.
        -- intro Hin.
           apply Hdom in Hin.
           destruct Hin as [[b Hb] Hlt].
           split.
           ++ exists b.
              rewrite Heq by exact Hlt.
              exact Hb.
           ++ exact Hlt.
        -- intros [[b Hb] Hlt].
           apply Hdom.
           split.
           ++ exists b.
              rewrite <- Heq by exact Hlt.
              exact Hb.
           ++ exact Hlt.
      * dump_pre_spatial.
        exact Hnodup.
Qed.

Lemma store_map_missing_first_step__clear_transition :
  forall {B : Type} (P : Z -> B -> Assertion) m i v,
    m (i + 1) = Some v ->
    store_map_missing_first_i_Z P m i |--
    P (i + 1) v ** store_map_missing_first_i_Z P m (i + 1).
Proof.
  intros B P m i v Hlookup.
  unfold store_map_missing_first_i_Z.
  Intros l.
  rename H into Hdom.
  rename H0 into Hnodup.
  assert (Hin : In (i + 1) l).
  { apply Hdom.
    split.
    - exists v.
      exact Hlookup.
    - lia. }
  apply in_split in Hin.
  destruct Hin as [l1 [l2 Hl]].
  Exists ((l1 ++ l2)%list).
  split_pure_spatial.
  - subst l.
    change ((l1 ++ (i + 1) :: l2)%list)
      with ((l1 ++ ((i + 1) :: nil) ++ l2)%list).
    rewrite !map_app.
    rewrite derivable1_sepcon_iter_sepcon2.
    sep_apply (derivable1_sepcon_iter_sepcon2
      (map (fun a => match m a with
                     | Some b => P a b
                     | None => emp
                     end) ((i + 1) :: nil))
      (map (fun a => match m a with
                     | Some b => P a b
                     | None => emp
                     end) l2)).
    rewrite derivable1_iter_sepcon_l.
    simpl.
    rewrite Hlookup.
    rewrite <- derivable1_sepcon_iter_sepcon1.
    normalize.
    sepcon_assoc_change.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      intros a.
      subst l.
      specialize (Hdom a).
      pose proof Hnodup as Hnodup_removed.
      apply NoDup_remove in Hnodup_removed.
      destruct Hnodup_removed as [Hnodup_rest Hnotin].
      rewrite in_app_iff in *.
      simpl in Hdom.
      split.
      * intro Hin_rest.
        assert (Hin_old : In a l1 \/ i + 1 = a \/ In a l2) by tauto.
        apply Hdom in Hin_old.
        destruct Hin_old as [Hmap Hlt].
        split.
        -- exact Hmap.
        -- assert (a <> i + 1).
           { intro Heq.
             subst a.
             apply Hnotin.
             exact Hin_rest. }
           lia.
      * intros [Hmap Hlt].
        assert (Hin_old : In a l1 \/ i + 1 = a \/ In a l2).
        { apply Hdom.
          split; [exact Hmap | lia]. }
        destruct Hin_old as [Hin | [Heq | Hin]].
        -- left.
           exact Hin.
        -- lia.
        -- right.
           exact Hin.
    + dump_pre_spatial.
      subst l.
      apply NoDup_remove in Hnodup.
      tauto.
Qed.

Lemma store_map_missing_first_finish__clear_transition :
  forall {B : Type} (P : Z -> B -> Assertion) m i limit,
    (forall a b, m a = Some b -> a < limit) ->
    limit <= i + 1 ->
    store_map_missing_first_i_Z P m i |-- emp.
Proof.
  intros B P m i limit Hrange Hfinish.
  unfold store_map_missing_first_i_Z.
  Intros l.
  rename H into Hdom.
  destruct l as [|a l].
  - simpl.
    unfold derivable1.
    auto.
  - assert (Hin : In a (a :: l)) by (left; reflexivity).
    apply Hdom in Hin.
    destruct Hin as [[b Hb] Hlt].
    pose proof (Hrange a b Hb).
    lia.
Qed.

Lemma store_name_map_injective_all__clear_transition :
  forall m,
    store_map store_name m |--
    “ forall k1 k2 p,
        m k1 = Some p -> m k2 = Some p -> k1 = k2 ”.
Proof.
  intros m.
  destruct
    (Classical_Prop.classic
      (forall k1 k2 p,
        m k1 = Some p -> m k2 = Some p -> k1 = k2))
    as [Hinjective | Hnot].
  - apply derivable1s_coq_prop_r.
    exact Hinjective.
  - apply Classical_Pred_Type.not_all_ex_not in Hnot.
    destruct Hnot as [k1 Hnot].
    apply Classical_Pred_Type.not_all_ex_not in Hnot.
    destruct Hnot as [k2 Hnot].
    apply Classical_Pred_Type.not_all_ex_not in Hnot.
    destruct Hnot as [p Hnot].
    pose proof (Classical_Prop.not_imply_elim _ _ Hnot) as Hmap1.
    pose proof (Classical_Prop.not_imply_elim2 _ _ Hnot) as Hnot2.
    pose proof (Classical_Prop.not_imply_elim _ _ Hnot2) as Hmap2.
    pose proof (Classical_Prop.not_imply_elim2 _ _ Hnot2) as Hneq.
    prop_apply_p
      (store_name_map_injective__clear_transition
        m k1 k2 p Hmap1 Hmap2).
    Intros_p Heq.
    contradiction.
Qed.

Lemma clear_next_bucket_or_finish__clear_transition :
  forall h_bucks buck_written m0 m i lh b li_cur ks_cur,
    0 <= i < NBUCK ->
    contain_all_correct_addrs m0 b ->
    repr_all_heads lh b ->
    remaining_after_bucket_index m0 m i ->
    current_bucket_key_list m b i li_cur ks_cur ->
    PtrArray.full h_bucks NBUCK
      (replace_Znth i 0 (replace_Znth i buck_written lh)) **
    store_map store_name (KP.remove_keys m ks_cur) **
    store_map_missing_first_i_Z store_sll b i |--
    (EX buck_next : addr,
     EX li_next : list addr,
     EX ks_next : list (list Z),
      “ contain_all_correct_addrs m0
          (fun j => if Z.eq_dec j i
                    then Some (0, li_cur) else b j) /\
        repr_all_heads (replace_Znth i 0 lh)
          (fun j => if Z.eq_dec j i
                    then Some (0, li_cur) else b j) /\
        remaining_after_bucket_index m0
          (KP.remove_keys m ks_cur) (i + 1) /\
        0 <= i + 1 < NBUCK /\
        current_bucket_key_list
          (KP.remove_keys m ks_cur)
          (fun j => if Z.eq_dec j i
                    then Some (0, li_cur) else b j)
          (i + 1) li_next ks_next ” &&
      PtrArray.missing_i h_bucks (i + 1) 0 NBUCK
        (replace_Znth i 0 lh) **
      store_map_missing_first_i_Z store_sll
        (fun j => if Z.eq_dec j i
                  then Some (0, li_cur) else b j) (i + 1) **
      store_map store_name (KP.remove_keys m ks_cur) **
      (h_bucks + (i + 1) * sizeof(PTR)) # Ptr |-> buck_next **
      sll buck_next li_next)
    ||
    (“ contain_all_correct_addrs m0
          (fun j => if Z.eq_dec j i
                    then Some (0, li_cur) else b j) /\
        repr_all_heads (replace_Znth i 0 lh)
          (fun j => if Z.eq_dec j i
                    then Some (0, li_cur) else b j) /\
        remaining_after_bucket_index m0
          (KP.remove_keys m ks_cur) (i + 1) /\
        NBUCK <= i + 1 ” &&
      store_map store_name (KP.remove_keys m ks_cur) **
      PtrArray.full h_bucks NBUCK (replace_Znth i 0 lh)).
Proof.
  intros h_bucks buck_written m0 m i lh b li_cur ks_cur
    Hi Hcontain Hrepr Hremaining Hcurrent.
  unfold current_bucket_key_list in Hcurrent.
  destruct Hcurrent as [Hkeys_cur [[old Hb] [Hexact Htransition]]].
  set (m_next := KP.remove_keys m ks_cur).
  set (lh_next := replace_Znth i 0 lh).
  set (b_next :=
    fun j => if Z.eq_dec j i then Some (0, li_cur) else b j).
  rewrite replace_Znth_overwrite__clear_transition.
  fold lh_next.
  prop_apply_p (PtrArray.full_Zlength h_bucks NBUCK lh_next).
  Intros_p Hlen_next.
  assert (Hlen_lh : Zlength lh = NBUCK).
  { unfold lh_next in Hlen_next.
    rewrite Zlength_replace_Znth in Hlen_next.
    exact Hlen_next. }
  assert (Hi_lh : 0 <= i < Zlength lh) by lia.
  assert (Hcontain_next : contain_all_correct_addrs m0 b_next).
  { unfold b_next.
    eapply contain_all_correct_addrs_clear__clear_transition; eauto. }
  assert (Hrepr_next : repr_all_heads lh_next b_next).
  { unfold lh_next, b_next.
    eapply repr_all_heads_clear__clear_transition; eauto. }
  assert (Hremaining_next :
    remaining_after_bucket_index m0 m_next (i + 1)).
  { unfold m_next.
    apply Htransition.
    exact Hremaining. }
  assert (Hb_hidden : forall a, i < a -> b a = b_next a).
  { intros a Hia.
    unfold b_next.
    destruct (Z.eq_dec a i); [lia | reflexivity]. }
  destruct
    (store_map_missing_first_equiv__clear_transition
      store_sll b b_next i Hb_hidden) as [Hhide _].
  sep_apply_l_atomic Hhide.
  destruct (Z_lt_ge_dec (i + 1) NBUCK) as [Hloop | Hfinish].
  - assert (Hnext : 0 <= i + 1 < NBUCK) by lia.
    assert (Hb_next :
      exists li_next,
        b_next (i + 1) =
          Some (Znth (i + 1) lh_next 0, li_next)).
    { apply (proj2 (Hrepr_next (i + 1) (Znth (i + 1) lh_next 0))).
      split.
      - pose proof Hnext as Hnext_lh.
        rewrite <- Hlen_next in Hnext_lh.
        exact Hnext_lh.
      - reflexivity. }
    destruct Hb_next as [li_next Hb_next].
    Left.
    sep_apply
      (PtrArray.full_split_to_missing_i
        h_bucks (i + 1) NBUCK lh_next 0 Hnext).
    sep_apply
      (store_map_missing_first_step__clear_transition
        store_sll b_next i
        (Znth (i + 1) lh_next 0, li_next) Hb_next).
    simpl store_sll.
    prop_apply_p
      (sll_nodup__clear_transition
        (Znth (i + 1) lh_next 0) li_next).
    Intros_p Hnodup_next.
    prop_apply_p (store_name_map_injective_all__clear_transition m_next).
    Intros_p Hinjective_next.
    destruct
      (bucket_key_list_exists_remaining__clear_transition
        m0 m_next b_next (i + 1)
        (Znth (i + 1) lh_next 0) li_next
        Hinjective_next Hnodup_next Hcontain_next
        Hremaining_next Hb_next)
      as [ks_next Hcurrent_next].
    destruct Hnext as [Hnext_lo Hnext_hi].
    unfold lh_next, b_next, m_next.
    Exists (Znth (i + 1) (replace_Znth i 0 lh) 0) li_next ks_next.
    split_pure_spatial.
    + cancel
        (PtrArray.missing_i h_bucks (i + 1) 0 NBUCK
          (replace_Znth i 0 lh)).
      cancel (store_map store_name (KP.remove_keys m ks_cur)).
      cancel
        ((h_bucks + (i + 1) * sizeof(PTR)) # Ptr
          |-> Znth (i + 1) (replace_Znth i 0 lh) 0).
      cancel
        (sll (Znth (i + 1) (replace_Znth i 0 lh) 0) li_next).
      change (sizeof(PTR)) with ptr_size_Z.
      cancel.
      unfold derivable1.
      auto.
    + dump_pre_spatial.
      exact
        (conj Hcontain_next
          (conj Hrepr_next
            (conj Hremaining_next
              (conj (conj Hnext_lo Hnext_hi) Hcurrent_next)))).
  - assert (Hfinish_le : NBUCK <= i + 1).
    { apply Z.ge_le.
      exact Hfinish. }
    assert (Hrange :
      forall a value, b_next a = Some value -> a < NBUCK).
    { intros a [head li_a] Hlookup.
      destruct (proj1 (Hrepr_next a head)) as [Hbounds _].
      { exists li_a.
        exact Hlookup. }
      rewrite <- Hlen_next.
      exact (proj2 Hbounds). }
    sep_apply_l_atomic
      (store_map_missing_first_finish__clear_transition
        store_sll b_next i NBUCK Hrange Hfinish_le).
    Right.
    split_pure_spatial.
    + normalize; repeat cancel.
    + dump_pre_spatial.
      exact
        (conj Hcontain_next
          (conj Hrepr_next (conj Hremaining_next Hfinish_le))).
Qed.

Lemma ptr_string_name__findref_traversal :
  forall p key_addr k,
    &(p # "blist" ->ₛ "key") # Ptr |-> key_addr **
    store_string key_addr k |--
    store_name k p.
Proof.
  intros.
  unfold store_name.
  Exists key_addr.
  cancel.
Qed.

Lemma sllbseg_snoc__findref_traversal :
  forall x y p l,
    p <> 0 ->
    &(p # "blist" ->ₛ "next") <> 0 ->
    sllbseg x y l ** y # Ptr |-> p |--
    sllbseg x &(p # "blist" ->ₛ "next") (l ++ p :: nil).
Proof.
  intros x y p l Hp Hpnext.
  revert x.
  induction l as [|a l IH]; intros x; simpl sllbseg.
  - Intros_p Hx.
    Intros_p Hxy.
    subst x.
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial.
        exact Hx.
      * dump_pre_spatial.
        exact Hp.
      * dump_pre_spatial.
        exact Hpnext.
      * dump_pre_spatial.
        reflexivity.
  - Intros_p Hx.
    Intros_p Ha.
    sep_apply_l_atomic (IH (&(a # "blist" ->ₛ "next"))).
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial.
        exact Hx.
      * dump_pre_spatial.
        exact Ha.
Qed.

Lemma current_bucket_nonnull_has_key__findref_traversal :
  forall m b i head l_prev p l_tail,
    contain_all_correct_addrs m b ->
    b i = Some (head, (l_prev ++ p :: l_tail)%list) ->
    exists k, m k = Some p.
Proof.
  intros m b i head l_prev p l_tail Hcontain Hb.
  destruct (proj2 (Hcontain i p)) as [k [_ Hmap]].
  { exists head, ((l_prev ++ p :: l_tail)%list).
    split.
    - exact Hb.
    - apply in_or_app.
      right.
      simpl.
      auto. }
  exists k.
  exact Hmap.
Qed.

Lemma store_name_map_injective__findref_traversal :
  forall m k1 k2 p,
    m k1 = Some p ->
    m k2 = Some p ->
    store_map store_name m |-- “ k1 = k2 ”.
Proof.
  intros m k1 k2 p Hmap1 Hmap2.
  exact
    (store_name_map_injective__clear_transition
      m k1 k2 p Hmap1 Hmap2).
Qed.

Lemma store_name_map_injective_all__findref_traversal :
  forall m,
    store_map store_name m |--
    “ forall k1 k2 p,
        m k1 = Some p -> m k2 = Some p -> k1 = k2 ”.
Proof.
  intros m.
  exact (store_name_map_injective_all__clear_transition m).
Qed.

Lemma sll_zero_inv__findref_results :
  forall l, sll 0 l |-- “ l = nil ” && emp.
Proof.
  intros [|a l]; simpl.
  - split_pure_spatial.
    + Intros_p Hzero.
      cancel.
    + dump_pre_spatial.
      reflexivity.
  - Intros next.
    contradiction.
Qed.

Lemma sllbseg_slot_null__findref_results :
  forall x y l,
    sllbseg x y l ** y # Ptr |-> 0 |--
    EX head,
      “ x <> 0 ” && x # Ptr |-> head ** sll head l.
Proof.
  intros x y l.
  revert x.
  induction l as [|a l IH]; intros x; simpl sllbseg.
  - Intros_p Hx.
    Intros_p Hxy.
    subst x.
    Exists 0.
    split_pure_spatial.
    + simpl sll.
      split_pure_spatial.
      * cancel.
      * dump_pre_spatial.
        reflexivity.
    + dump_pre_spatial.
      exact Hx.
  - Intros_p Hx.
    Intros_p Ha.
    sep_apply_l_atomic (IH (&(a # "blist" ->ₛ "next"))).
    Intros head.
    rename H into Hnext.
    Exists a.
    split_pure_spatial.
    + simpl sll.
      Exists head.
      split_pure_spatial.
      * normalize.
        repeat cancel.
      * split_pures.
        -- dump_pre_spatial.
           exact Ha.
        -- dump_pre_spatial.
           reflexivity.
        -- dump_pre_spatial.
           exact Hnext.
    + dump_pre_spatial.
      exact Hx.
Qed.

Lemma sllbseg_slot_sll__findref_results :
  forall x y z l1 l2,
    sllbseg x y l1 ** y # Ptr |-> z ** sll z l2 |--
    EX head,
      “ x <> 0 ” && x # Ptr |-> head ** sll head (l1 ++ l2).
Proof.
  intros x y z l1.
  revert x.
  induction l1 as [|a l1 IH]; intros x l2; simpl sllbseg.
  - Intros_p Hx.
    Intros_p Hxy.
    subst x.
    Exists z.
    split_pure_spatial.
    + simpl.
      cancel.
    + dump_pre_spatial.
      exact Hx.
  - Intros_p Hx.
    Intros_p Ha.
    sep_apply_l_atomic (IH (&(a # "blist" ->ₛ "next")) l2).
    Intros head.
    rename H into Hnext.
    Exists a.
    split_pure_spatial.
    + simpl sll.
      Exists head.
      split_pure_spatial.
      * normalize.
        repeat cancel.
      * split_pures.
        -- dump_pre_spatial.
           exact Ha.
        -- dump_pre_spatial.
           reflexivity.
        -- dump_pre_spatial.
           exact Hnext.
    + dump_pre_spatial.
      exact Hx.
Qed.

Lemma sll_cons_fold__findref_results :
  forall p next tail,
    p <> 0 ->
    &(p # "blist" ->ₛ "next") <> 0 ->
    &(p # "blist" ->ₛ "next") # Ptr |-> next ** sll next tail |--
    sll p (p :: tail).
Proof.
  intros p next tail Hp Hnext.
  simpl sll.
  Exists next.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hp.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact Hnext.
Qed.

Lemma contain_all_correct_addrs_update_bucket_perm__findref_results :
  forall m b i old_head old_l new_head new_l,
    b i = Some (old_head, old_l) ->
    Permutation old_l new_l ->
    contain_all_correct_addrs m b ->
    contain_all_correct_addrs m
      (fun j => if Z.eq_dec j i
                then Some (new_head, new_l) else b j).
Proof.
  intros m b i old_head old_l new_head new_l Hb Hperm Hcontain.
  unfold contain_all_correct_addrs in *.
  intros j p.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j.
    rewrite Hcontain.
    split.
    + intros [ph [li [Hlookup Hin]]].
      rewrite Hb in Hlookup.
      inversion Hlookup.
      subst li.
      exists new_head, new_l.
      split.
      * destruct (Z.eq_dec i i); [reflexivity | contradiction].
      * eapply Permutation_in; eauto.
    + intros [ph [li [Hlookup Hin]]].
      destruct (Z.eq_dec i i) as [_ | Hfalse] in Hlookup;
        [| contradiction].
      inversion Hlookup.
      subst li.
      exists old_head, old_l.
      split.
      * exact Hb.
      * eapply Permutation_in.
        -- apply Permutation_sym.
           exact Hperm.
        -- exact Hin.
  - destruct (Z.eq_dec j i); [contradiction | exact (Hcontain j p)].
Qed.

Lemma current_bucket_exhausted_not_key__lookup_miss_results :
  forall m b i head l_prev k,
    b i = Some (head, l_prev) ->
    contain_all_correct_addrs m b ->
    not_key k l_prev m ->
    hash_string_k k mod NBUCK = i ->
    m k = None.
Proof.
  intros m b i head l_prev k Hb Hcontain Hnot_key Hhash.
  destruct (m k) as [p |] eqn:Hlookup; [| reflexivity].
  exfalso.
  destruct (proj1 (Hcontain i p)) as [bucket_head [bucket [Hb' Hin]]].
  { exists k.
    split; assumption. }
  rewrite Hb in Hb'.
  inversion Hb'.
  subst bucket.
  exact (Hnot_key p k Hin Hlookup eq_refl).
Qed.

Lemma node_value_map_lookup__findref_returns :
  forall (m_node m_value : list Z -> option addr) (k : list Z) (p : addr),
    node_value_map m_node m_value ->
    m_node k = Some p ->
    m_value k = Some &(p # "blist" ->ₛ "val").
Proof.
  intros m_node m_value k p Hmap Hlookup.
  unfold node_value_map in Hmap.
  subst m_value.
  unfold map_fun.
  rewrite Hlookup.
  reflexivity.
Qed.

Lemma dll_member_nonzero__findref_results :
  forall x up l p,
    In p l ->
    dll x up l |-- “ p <> 0 ”.
Proof.
  intros x up l.
  revert x up.
  induction l as [|a l IH]; intros x up p Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst p.
      simpl dll.
      Intros down.
      dump_pre_spatial.
      subst x.
      change (a <> 0) in H.
      exact H.
    + simpl dll.
      Intros down.
      sep_apply_l_atomic (IH down x p Hin).
      Intros_p Hp.
      dump_pre_spatial.
      exact Hp.
Qed.

Lemma dll_split_at_member__remove_entails :
  forall x x_up l p,
    In p l ->
    dll x x_up l |--
      EX dl_prev dl_up dl_tail,
        “ l = (dl_up ++ p :: dl_tail)%list ” &&
        dllseg x p x_up dl_prev dl_up **
        dll p dl_prev (p :: dl_tail).
Proof.
  intros x x_up l.
  revert x x_up.
  induction l as [|a tail IH]; intros x x_up p Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst a.
      simpl dll.
      Intros x_down.
      Exists x_up (@nil addr) tail.
      simpl app.
      simpl dllseg.
      simpl dll.
      Exists x_down.
      split_pure_spatial.
      * subst x.
        cancel (&(p # "blist" ->ₛ "down") # Ptr |-> x_down).
        cancel (&(p # "blist" ->ₛ "up") # Ptr |-> x_up).
        cancel (dll x_down p tail).
      * split_pures.
        all: dump_pre_spatial.
        all: congruence.
    + simpl dll.
      Intros x_down.
      sep_apply_l_atomic (IH x_down x p Hin).
      Intros dl_prev dl_up dl_tail.
      simpl dll.
      Intros p_down.
      Exists dl_prev (x :: dl_up) dl_tail.
      simpl app.
      simpl dllseg.
      Exists x_down.
      simpl dll.
      Exists p_down.
      split_pure_spatial.
      * cancel (&(x # "blist" ->ₛ "down") # Ptr |-> x_down).
        cancel (&(x # "blist" ->ₛ "up") # Ptr |-> x_up).
        cancel (dllseg x_down p x dl_prev dl_up).
        cancel (&(p # "blist" ->ₛ "down") # Ptr |-> p_down).
        cancel (&(p # "blist" ->ₛ "up") # Ptr |-> dl_prev).
        cancel (dll p_down p dl_tail).
      * split_pures.
        all: dump_pre_spatial.
        all: congruence.
Qed.

Lemma dll_to_null_segment__remove_entails :
  forall x x_up l,
    dll x x_up l |--
      EX y_up, dllseg x NULL x_up y_up l.
Proof.
  intros x x_up l.
  revert x x_up.
  induction l as [|a tail IH]; intros x x_up.
  - simpl dll.
    Intros_p Hx.
    Exists x_up.
    simpl dllseg.
    split_pure_spatial.
    + unfold derivable1.
      auto.
    + split_pures.
      * dump_pre_spatial.
        exact Hx.
      * dump_pre_spatial.
        reflexivity.
  - simpl dll.
    Intros x_down.
    sep_apply_l_atomic (IH x_down x).
    Intros y_up.
    Exists y_up.
    simpl dllseg.
    Exists x_down.
    split_pure_spatial.
    + cancel (&(x # "blist" ->ₛ "down") # Ptr |-> x_down).
      cancel (&(x # "blist" ->ₛ "up") # Ptr |-> x_up).
      cancel (dllseg x_down 0 x y_up tail).
    + split_pures.
      all: dump_pre_spatial.
      all: congruence.
Qed.

Lemma dll_cons_from_fields__remove_entails :
  forall x x_up x_down tail,
    x <> NULL ->
    &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
    &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
    dll x_down x tail |--
      dll x x_up (x :: tail).
Proof.
  intros x x_up x_down tail Hx.
  simpl dll.
  Exists x_down.
  split_pure_spatial.
  - cancel (&(x # "blist" ->ₛ "down") # Ptr |-> x_down).
    cancel (&(x # "blist" ->ₛ "up") # Ptr |-> x_up).
    cancel (dll x_down x tail).
  - split_pures.
    all: dump_pre_spatial.
    all: congruence.
Qed.

Lemma dllseg_dll_merge__remove_entails :
  forall x y x_up y_up l1 l2,
    dllseg x y x_up y_up l1 **
    dll y y_up l2 |--
      dll x x_up (l1 ++ l2)%list.
Proof.
  intros x y x_up y_up l1 l2.
  revert x x_up.
  induction l1 as [|a tail IH]; intros x x_up.
  - simpl dllseg.
    Intros_p Hxy.
    Intros_p Hup.
    subst x y_up.
    simpl app.
    cancel (dll y x_up l2).
  - simpl dllseg.
    Intros x_down.
    sep_apply_l_atomic (IH x_down x).
    simpl app.
    simpl dll.
    Exists x_down.
    split_pure_spatial.
    + cancel (&(x # "blist" ->ₛ "down") # Ptr |-> x_down).
      cancel (&(x # "blist" ->ₛ "up") # Ptr |-> x_up).
      cancel (dll x_down x (tail ++ l2)%list).
    + split_pures.
      all: dump_pre_spatial.
      all: congruence.
Qed.

Lemma dllseg_dll_loop_invariants__remove_entails :
  forall top itv dl_prev dl_up dl_down,
    dllseg top itv 0 dl_prev dl_up **
    dll itv dl_prev dl_down |--
      “ (top = itv -> dl_prev = 0 /\ dl_up = nil) /\
        (dl_up <> nil -> top <> 0) ”.
Proof.
  intros top itv dl_prev dl_up dl_down.
  destruct dl_up as [|a tail].
  - simpl dllseg.
    Intros_p Htop.
    Intros_p Hprev.
    dump_pre_spatial.
    split.
    + intros _.
      split; congruence.
    + intros Hnil.
      contradiction.
  - simpl dllseg.
    Intros top_down.
    rename H into Htop_nonnull.
    rename H0 into Hhead.
    destruct (Z.eq_dec top itv) as [Heq | Hneq].
    + subst itv.
      destruct dl_down as [|b rest].
      * simpl dll.
        Intros_p Hzero.
        contradiction.
      * simpl dll.
        Intros itv_down.
        rename H into Hitv_nonnull.
        rename H0 into Hitv_head.
        subst a b.
        prop_apply_p
          (dup_store_ptr
            (&(top # "blist" ->ₛ "down")) top_down itv_down).
        Intros_p Hfalse.
        contradiction.
    + dump_pre_spatial.
      split.
      * intro Hsame.
        contradiction.
      * intros _.
        exact Htop_nonnull.
Qed.

Lemma dllseg_null_loop_invariants__remove_entails :
  forall top dl_prev dl_up,
    dllseg top NULL 0 dl_prev dl_up |--
      “ (top = 0 -> dl_prev = 0 /\ dl_up = nil) /\
        (dl_up <> nil -> top <> 0) ”.
Proof.
  intros top dl_prev dl_up.
  destruct dl_up as [|a tail].
  - simpl dllseg.
    Intros_p Htop.
    Intros_p Hprev.
    dump_pre_spatial.
    split.
    + intros _.
      split; congruence.
    + intros Hnil.
      contradiction.
  - simpl dllseg.
    Intros top_down.
    rename H into Htop_nonnull.
    dump_pre_spatial.
    split.
    + intros Hzero.
      contradiction.
    + intros _.
      exact Htop_nonnull.
Qed.

Lemma proof_of_hashtbl_remove_partial_solve_wit_3_pure_split_goal_1_adapter__remove_search :
  forall (removed_pre key_pre h_pre : Z)
         (k : list Z)
         (m2 : Z -> option Z)
         (dl_prev top itv it h_pre_bucks : Z)
         (lh dl_up dl_down : list addr)
         (buck : Z)
         (l0 : list addr)
         (bucket_map : Z -> option (addr * list addr))
         (ind : Z)
         (l_res l_prev : list addr)
         (m1_node : list Z -> option addr),
    contain_all_correct_addrs m1_node bucket_map ->
    bucket_map ind = Some (buck, l0) ->
    l0 = (l_prev ++ l_res)%list ->
    (&( "b" ) # Ptr |-> itv) **
    ((&( "ind" ) # UInt |-> ind) **
    ((&(h_pre # "hashtbl" ->ₛ "bucks") # Ptr |-> h_pre_bucks) **
    ((&( "h" ) # Ptr |-> h_pre) **
    ((&( "key" ) # Ptr |-> key_pre) **
    ((&( "removed" ) # Ptr |-> removed_pre) **
    ((&( "it" ) # Ptr |-> it) **
    ((it # Ptr |-> itv) **
    ((store_map_missing_i store_sll bucket_map ind) **
    ((sllbseg (h_pre_bucks + ind * sizeof(PTR)) it l_prev) **
    ((sll itv l_res) **
    ((store_string key_pre k) **
    ((PtrArray.missing_i h_pre_bucks ind 0 NBUCK lh) **
    ((store_map store_name m1_node) **
    ((&(h_pre # "hashtbl" ->ₛ "top") # Ptr |-> top) **
    ((dllseg top itv 0 dl_prev dl_up) **
    ((dll itv dl_prev dl_down) **
    ((removed_pre # Int |->_) **
      store_map store_uint m2)))))))))))))))))
    |-- “ current_bucket_suffix m1_node bucket_map ind l_prev l_res ”.
Proof.
  intros removed_pre key_pre h_pre k m2 dl_prev top itv it h_pre_bucks
    lh dl_up dl_down buck l0 bucket_map ind l_res l_prev m1_node
    Hcontain Hbucket Hsuffix.
  apply derivable1s_coq_prop_r.
  unfold current_bucket_suffix.
  split.
  - exact Hcontain.
  - exists buck.
    rewrite Hsuffix in Hbucket.
    exact Hbucket.
Qed.

Lemma remove_map_absent_eq__lookup_miss_results :
  forall (m : list Z -> option addr) k,
    m k = None ->
    KP.remove_map m k = m.
Proof.
  intros m k Hnone.
  apply functional_extensionality.
  intro k'.
  destruct (list_eq_dec Z.eq_dec k' k) as [Heq | Hneq].
  - subst k'.
    rewrite KP.remove_map_same, Hnone.
    reflexivity.
  - rewrite KP.remove_map_diff by congruence.
    reflexivity.
Qed.

Lemma dllseg_dll__remove_absent :
  forall x y x_up y_up l1 l2,
    dllseg x y x_up y_up l1 ** dll y y_up l2 |--
    dll x x_up (l1 ++ l2).
Proof.
  intros x y x_up y_up l1.
  revert x y x_up y_up.
  induction l1 as [|a l1 IH]; intros x y x_up y_up l2.
  - simpl dllseg.
    simpl.
    Intros_p Hxy.
    Intros_p Hup.
    subst x y_up.
    cancel.
  - simpl dllseg.
    simpl.
    Intros x_down.
    Exists x_down.
    split_pure_spatial.
    + sep_apply_l_atomic (IH x_down y x y_up l2).
      repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        exact H0.
Qed.

Lemma sllbseg_start_nonnull__remove_absent :
  forall x y l,
    sllbseg x y l |-- “ x <> NULL ”.
Proof.
  intros x y [|a l]; simpl sllbseg.
  - Intros_p Hx.
    dump_pre_spatial.
    exact Hx.
  - Intros_p Hx.
    dump_pre_spatial.
    exact Hx.
Qed.

Lemma sllbseg_sll__remove_absent :
  forall p i l_prev i_v l_res,
    sllbseg p i l_prev **
    i # Ptr |-> i_v **
    sll i_v l_res |--
    EX p0,
      p # Ptr |-> p0 **
      sll p0 (l_prev ++ l_res).
Proof.
  intros p i l_prev.
  revert p i.
  induction l_prev as [|a l_prev IH]; intros p i i_v l_res.
  - simpl sllbseg.
    simpl.
    Intros_p Hp.
    Intros_p Hpi.
    subst p.
    Exists i_v.
    cancel.
  - simpl sllbseg.
    simpl.
    Intros_p Hp.
    Intros_p Ha.
    prop_apply_p
      (sllbseg_start_nonnull__remove_absent
        (&(a # "blist" ->ₛ "next")) i l_prev).
    Intros_p Hnext.
    sep_apply_l_atomic
      (IH (&(a # "blist" ->ₛ "next")) i i_v l_res).
    Intros p_tail.
    Exists a.
    Exists p_tail.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact Ha.
      * dump_pre_spatial.
        reflexivity.
      * dump_pre_spatial.
        exact Hnext.
Qed.

Lemma contain_all_correct_addrs_update_head__remove_absent :
  forall m b i old_head l new_head,
    b i = Some (old_head, l) ->
    contain_all_correct_addrs m b ->
    contain_all_correct_addrs
      m (fun j => if Z.eq_dec j i then Some (new_head, l) else b j).
Proof.
  intros m b i old_head l new_head Hb Hcontain.
  unfold contain_all_correct_addrs in *.
  intros j p.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j.
    split.
    + intro Hkey.
      destruct (proj1 (Hcontain i p) Hkey)
        as [head [l0 [Hlookup Hin]]].
      rewrite Hb in Hlookup.
      inversion Hlookup.
      subst l0.
      exists new_head, l.
      split.
      * destruct (Z.eq_dec i i); [reflexivity | contradiction].
      * exact Hin.
    + intros [head [l0 [Hlookup Hin]]].
      destruct (Z.eq_dec i i) as [_ | Hfalse] in Hlookup;
        [| contradiction].
      inversion Hlookup.
      subst l0.
      apply (proj2 (Hcontain i p)).
      exists old_head, l.
      auto.
  - destruct (Z.eq_dec j i) as [Hfalse | _]; [contradiction |].
    apply Hcontain.
Qed.

Lemma sllbseg_sll_ordered__remove_absent :
  forall p i l_prev i_v l_res,
    i # Ptr |-> i_v **
    sllbseg p i l_prev **
    sll i_v l_res |--
    EX p0,
      p # Ptr |-> p0 **
      sll p0 (l_prev ++ l_res).
Proof.
  intros p i l_prev.
  revert p i.
  induction l_prev as [|a l_prev IH]; intros p i i_v l_res.
  - simpl sllbseg.
    simpl.
    Intros_p Hp.
    Intros_p Hpi.
    subst p.
    Exists i_v.
    cancel.
  - simpl sllbseg.
    simpl.
    Intros_p Hp.
    Intros_p Ha.
    prop_apply_p
      (sllbseg_start_nonnull__remove_absent
        (&(a # "blist" ->ₛ "next")) i l_prev).
    Intros_p Hnext.
    sep_apply (IH (&(a # "blist" ->ₛ "next")) i i_v l_res).
    Intros p_tail.
    Exists a.
    Exists p_tail.
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact Ha.
      * dump_pre_spatial.
        reflexivity.
      * dump_pre_spatial.
        exact Hnext.
Qed.

Lemma sllbseg_sll_bundle__remove_absent :
  forall p i l_prev i_v l_res (R : Assertion),
    (sllbseg p i l_prev **
     (i # Ptr |-> i_v ** sll i_v l_res)) ** R |--
    EX p0,
      p # Ptr |-> p0 **
      (sll p0 (l_prev ++ l_res) ** R).
Proof.
  intros p i l_prev i_v l_res R.
  sep_apply_l_atomic
    (sllbseg_sll__remove_absent p i l_prev i_v l_res).
  Intros p0.
  Exists p0.
  repeat cancel.
Qed.

Lemma sllbseg_sll_framed__remove_absent :
  forall p i l_prev i_v l_res
         (Rbefore Rmid Rtail : Assertion),
    Rbefore **
    (i # Ptr |-> i_v **
     (Rmid **
      (sllbseg p i l_prev **
       (sll i_v l_res ** Rtail)))) |--
    EX p0,
      p # Ptr |-> p0 **
      (sll p0 (l_prev ++ l_res) **
       (Rbefore ** (Rmid ** Rtail))).
Proof.
  intros p i l_prev i_v l_res Rbefore Rmid Rtail.
  sep_apply_r_atomic
    (sllbseg_sll_bundle__remove_absent
      p i l_prev i_v l_res (Rbefore ** (Rmid ** Rtail))).
  repeat cancel.
Qed.

Lemma node_value_map_remove__remove_success_returns :
  forall (m_node m_value : list Z -> option addr) k,
    node_value_map m_node m_value ->
    node_value_map
      (KP.remove_map m_node k)
      (KP.remove_map m_value k).
Proof.
  intros m_node m_value k Hmap.
  unfold node_value_map, map_fun in *.
  subst m_value.
  apply functional_extensionality.
  intro k'.
  destruct (list_eq_dec Z.eq_dec k' k) as [Heq | Hneq].
  - subst k'.
    rewrite !KP.remove_map_same.
    reflexivity.
  - rewrite !KP.remove_map_diff by congruence.
    reflexivity.
Qed.

Lemma contain_all_addrs_remove__remove_success_returns :
  forall (m : list Z -> option addr) k p l1 l2,
    (forall k1 k2 q,
      m k1 = Some q -> m k2 = Some q -> k1 = k2) ->
    m k = Some p ->
    contain_all_addrs m ((l1 ++ p :: l2)%list) ->
    ~ In p ((l1 ++ l2)%list) ->
    contain_all_addrs (KP.remove_map m k) ((l1 ++ l2)%list).
Proof.
  intros m k p l1 l2 Hinjective Hlookup Hcontain Hnotin.
  unfold contain_all_addrs in *.
  intro q.
  split.
  - intros [key Hremoved].
    assert (Hneq : key <> k).
    { intro Heq.
      subst key.
      rewrite KP.remove_map_same in Hremoved.
      discriminate. }
    rewrite KP.remove_map_diff in Hremoved by congruence.
    assert (Hin_old : In q ((l1 ++ p :: l2)%list)).
    { apply (proj1 (Hcontain q)).
      exists key.
      exact Hremoved. }
    rewrite in_app_iff in Hin_old.
    rewrite in_app_iff.
    destruct Hin_old as [Hin_l1 | [Heq | Hin_l2]].
    + left; exact Hin_l1.
    + subst q.
      exfalso.
      apply Hneq.
      eapply Hinjective; eauto.
    + right; exact Hin_l2.
  - intro Hin_new.
    assert (Hin_old : In q ((l1 ++ p :: l2)%list)).
    { rewrite !in_app_iff in *.
      simpl.
      tauto. }
    destruct (proj2 (Hcontain q) Hin_old) as [key Hmap].
    exists key.
    rewrite KP.remove_map_diff.
    + exact Hmap.
    + intro Heq.
      subst key.
      rewrite Hlookup in Hmap.
      inversion Hmap.
      subst q.
      contradiction.
Qed.

Lemma removed_not_in_bucket__remove_success_returns :
  forall (m : list Z -> option addr) k p l_prev l_res,
    not_key k l_prev m ->
    m k = Some p ->
    NoDup (p :: l_res) ->
    ~ In p ((l_prev ++ l_res)%list).
Proof.
  intros m k p l_prev l_res Hnot_key Hlookup Hnodup.
  rewrite in_app_iff.
  intros [Hin | Hin].
  - exact (Hnot_key p k Hin Hlookup eq_refl).
  - inversion Hnodup.
    contradiction.
Qed.

Lemma contain_all_correct_addrs_remove__remove_success_returns :
  forall (m : list Z -> option addr) b k p ind old_head
         l_prev l_res new_head,
    (forall k1 k2 q,
      m k1 = Some q -> m k2 = Some q -> k1 = k2) ->
    m k = Some p ->
    hash_string k mod NBUCK = ind ->
    b ind = Some (old_head, (l_prev ++ p :: l_res)%list) ->
    contain_all_correct_addrs m b ->
    ~ In p ((l_prev ++ l_res)%list) ->
    contain_all_correct_addrs
      (KP.remove_map m k)
      (fun j => if Z.eq_dec j ind
                then Some (new_head, (l_prev ++ l_res)%list) else b j).
Proof.
  intros m b k p ind old_head l_prev l_res new_head
    Hinjective Hlookup Hhash Hb Hcorrect Hnotin.
  unfold contain_all_correct_addrs in *.
  intros i q.
  split.
  - intros [key [Hkeyhash Hremoved]].
    assert (Hneq : key <> k).
    { intro Heq.
      subst key.
      rewrite KP.remove_map_same in Hremoved.
      discriminate. }
    rewrite KP.remove_map_diff in Hremoved by congruence.
    destruct (proj1 (Hcorrect i q)) as [ph [li [Hbi Hin]]].
    { exists key; auto. }
    destruct (Z.eq_dec i ind) as [Heq | Hneq_i].
    + subst i.
      assert ((ph, li) = (old_head, (l_prev ++ p :: l_res)%list))
        by congruence.
      inversion H; subst ph li; clear H.
      exists new_head, ((l_prev ++ l_res)%list).
      split.
      * destruct (Z.eq_dec ind ind); [reflexivity | contradiction].
      * rewrite !in_app_iff in *.
        destruct Hin as [Hin | [Heq_q | Hin]].
        -- left; exact Hin.
        -- subst q.
           exfalso.
           apply Hneq.
           eapply Hinjective; eauto.
        -- right; exact Hin.
    + exists ph, li.
      split.
      * destruct (Z.eq_dec i ind); [contradiction | exact Hbi].
      * exact Hin.
  - intros [ph [li [Hnew Hin]]].
    destruct (Z.eq_dec i ind) as [Heq | Hneq_i].
    + subst i.
      destruct (Z.eq_dec ind ind) as [_ | Hfalse] in Hnew;
        [| contradiction].
      inversion Hnew; subst ph li.
      assert (Hin_old : In q ((l_prev ++ p :: l_res)%list)).
      { rewrite !in_app_iff in *.
        simpl.
        tauto. }
      destruct (proj2 (Hcorrect ind q)) as [key [Hkeyhash Hmap]].
      { exists old_head, ((l_prev ++ p :: l_res)%list).
        auto. }
      exists key.
      split; [exact Hkeyhash |].
      rewrite KP.remove_map_diff.
      * exact Hmap.
      * intro Heq.
        subst key.
        rewrite Hlookup in Hmap.
        inversion Hmap.
        subst q.
        contradiction.
    + assert (Hold : b i = Some (ph, li)).
      { destruct (Z.eq_dec i ind) as [Hfalse | _] in Hnew;
          [contradiction | exact Hnew]. }
      destruct (proj2 (Hcorrect i q)) as [key [Hkeyhash Hmap]].
      { exists ph, li; auto. }
      exists key.
      split; [exact Hkeyhash |].
      rewrite KP.remove_map_diff.
      * exact Hmap.
      * intro Heq.
        subst key.
        rewrite Hhash in Hkeyhash.
        apply Hneq_i.
        symmetry.
        exact Hkeyhash.
Qed.

Lemma sllbseg_sll__remove_success_returns :
  forall p i l_prev i_v l_res,
    sllbseg p i l_prev **
    i # Ptr |-> i_v **
    sll i_v l_res |--
    “ p <> 0 ” &&
    EX p0,
      p # Ptr |-> p0 **
      sll p0 ((l_prev ++ l_res)%list).
Proof.
  intros p i l_prev i_v l_res.
  prop_apply_p (sllbseg_start_nonnull p i l_prev).
  Intros_p Hp.
  sep_apply_l_atomic (sllbseg_sll p i l_prev i_v l_res).
  Intros p0.
  Exists p0.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hp.
Qed.

Lemma rebuild_removed_bucket_spatial__remove_success_returns :
  forall h_bucks ind lh b it l_prev b_next l_res,
    0 <= ind < NBUCK ->
    PtrArray.missing_i h_bucks ind 0 NBUCK lh **
    store_map_missing_i store_sll b ind **
    sllbseg (h_bucks + ind * sizeof(PTR)) it l_prev **
    it # Ptr |-> b_next **
    sll b_next l_res |--
    EX new_head,
      PtrArray.full h_bucks NBUCK
        (replace_Znth ind new_head lh) **
      store_map store_sll
        (fun j => if Z.eq_dec j ind
                  then Some (new_head, (l_prev ++ l_res)%list) else b j).
Proof.
  intros h_bucks ind lh b it l_prev b_next l_res Hind.
  sep_apply_l_atomic
    (sllbseg_sll__remove_success_returns
      (h_bucks + ind * sizeof(PTR)) it l_prev b_next l_res).
  Intros new_head.
  normalize.
  rewrite sizeof_ptr.
  fold ptr_size_Z.
  Exists new_head.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full
      h_bucks ind NBUCK new_head lh Hind).
  set (b_new :=
    fun j => if Z.eq_dec j ind
             then Some (new_head, (l_prev ++ l_res)%list) else b j).
  assert (Houtside : forall j, j <> ind -> b j = b_new j).
  { intros j Hneq.
    unfold b_new.
    destruct (Z.eq_dec j ind); [contradiction | reflexivity]. }
  destruct
    (store_map_missing_i_equiv store_sll b b_new ind Houtside)
    as [Hmissing _].
  sep_apply_l_atomic Hmissing.
  assert (Hb_new : b_new ind = Some (new_head, (l_prev ++ l_res)%list)).
  { unfold b_new.
    destruct (Z.eq_dec ind ind); [reflexivity | contradiction]. }
  fold b_new.
  pose proof
    (store_map_merge
      store_sll ind (new_head, (l_prev ++ l_res)%list) b_new Hb_new)
    as Hmerge.
  cbn [store_sll] in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold b_new.
  cancel.
  unfold derivable1.
  auto.
Qed.

Lemma rebuild_removed_node_spatial__remove_success_returns :
  forall h_bucks ind lh b it l_prev b_next l_res,
    0 <= ind < 211 ->
    PtrArray.missing_i h_bucks ind 0 211 lh **
    store_map_missing_i store_sll b ind **
    sllbseg (h_bucks + ind * sizeof(PTR)) it l_prev **
    it # Ptr |-> b_next **
    sll b_next l_res |--
    EX new_head,
      PtrArray.full h_bucks 211
        (replace_Znth ind new_head lh) **
      store_map store_sll
        (fun j => if Z.eq_dec j ind
                  then Some (new_head, (l_prev ++ l_res)%list) else b j).
Proof.
  intros.
  apply rebuild_removed_bucket_spatial__remove_success_returns.
  exact H.
Qed.

Lemma dllseg_dll__remove_success_returns :
  forall x y x_up y_up l1 l2,
    dllseg x y x_up y_up l1 ** dll y y_up l2 |--
    dll x x_up ((l1 ++ l2)%list).
Proof.
  intros x y x_up y_up l1.
  revert x x_up.
  induction l1 as [|a l1 IH]; intros x x_up l2; simpl.
  - Intros.
    subst x y_up.
    cancel.
  - Intros x_down.
    Exists x_down.
    sep_apply_l_atomic (IH x_down x l2).
    split_pure_spatial.
    + repeat cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: assumption.
Qed.

Lemma dll_exposed_down_not_in__remove_success_returns :
  forall l p v h h_up,
    &(p # "blist" ->ₛ "down") # Ptr |-> v **
    dll h h_up l |--
    “ ~ In p l ”.
Proof.
  induction l as [|a l IH]; intros p v h h_up; simpl dll.
  - dump_pre_spatial.
    intros [].
  - Intros h_down.
    subst a.
    destruct (Z.eq_dec h p) as [Heq | Hneq].
    + subst h.
      prop_apply_p
        (dup_store_ptr (&(p # "blist" ->ₛ "down")) v h_down).
      Intros_p Hfalse.
      contradiction.
    + prop_apply_p (IH p v h_down h).
      Intros_p Htail.
      dump_pre_spatial.
      intros [Heq | Hin].
      * apply Hneq.
        exact Heq.
      * apply Htail.
        exact Hin.
Qed.

Lemma dll_exposed_down_not_in_frame__remove_success_returns :
  forall l p v h h_up P,
    &(p # "blist" ->ₛ "down") # Ptr |-> v **
    (dll h h_up l ** P) |--
    “ ~ In p l ”.
Proof.
  intros l p v h h_up P.
  sep_apply_l_atomic
    (dll_exposed_down_not_in__remove_success_returns l p v h h_up).
  Intros_p Hnotin.
  dump_pre_spatial.
  exact Hnotin.
Qed.

Lemma expose_removed_down_with_dll__remove_success_returns :
  forall A B C D E F G H P : Assertion,
  forall l p v h h_up,
    A ** (B ** (C ** (D **
      (dll h h_up l **
       (E ** (F ** (G ** (H **
        (&(p # "blist" ->ₛ "down") # Ptr |-> v ** P))))))))) |--
    “ ~ In p l ” &&
    (&(p # "blist" ->ₛ "down") # Ptr |-> v **
     (dll h h_up l **
      (A ** (B ** (C ** (D ** (E ** (F ** (G ** (H ** P)))))))))).
Proof.
  intros A B C D E F G H P l p v h h_up.
  set (R := A ** (B ** (C ** (D **
    (E ** (F ** (G ** (H ** P))))))) : Assertion).
  split_pure_spatial.
  - cancel (&(p # "blist" ->ₛ "down") # Ptr |-> v).
    cancel (dll h h_up l).
    unfold R.
    cancel A.
    cancel B.
    cancel C.
    cancel D.
    cancel E.
    cancel F.
    cancel G.
    cancel H.
    cancel P.
  - prop_apply_p
      (dll_exposed_down_not_in__remove_success_returns
        l p v h h_up).
    Intros_p Hnotin.
    dump_pre_spatial.
    exact Hnotin.
Qed.

Lemma dllseg_nonempty_end_up_nonnull__remove_success_returns :
  forall x y x_up y_up l,
    l <> nil ->
    dllseg x y x_up y_up l |--
    “ y_up <> 0 ”.
Proof.
  intros x y x_up y_up l.
  revert x y x_up y_up.
  induction l as [|a l IH]; intros x y x_up y_up Hnonempty.
  - contradiction.
  - simpl dllseg.
    Intros x_down.
    destruct l as [|b l].
    + simpl dllseg.
      Intros_p Hdown.
      Intros_p Hup.
      dump_pre_spatial.
      unfold NULL in H.
      rewrite <- Hup.
      exact H.
    + prop_apply_p
        (IH x_down y x y_up ltac:(discriminate)).
      Intros_p Hend.
      dump_pre_spatial.
      exact Hend.
Qed.

Lemma dllseg_end_prev_zero_impossible__remove_success_returns :
  forall x y x_up l,
    x_up <> 0 ->
    dllseg x y x_up 0 l |-- “ False ”.
Proof.
  intros x y x_up l Hup.
  revert x x_up Hup.
  induction l as [|a l IH]; intros x x_up Hup; simpl dllseg.
  - Intros_p Hxy.
    Intros_p Hends.
    dump_pre_spatial.
    contradiction.
  - Intros x_down.
    rename H into Hx.
    sep_apply_l_atomic (IH x_down x Hx).
    Intros_p Hfalse.
    contradiction.
Qed.

Lemma dll_cons__remove_success_returns :
  forall x x_up x_down l,
    x <> 0 ->
    &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
    &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
    dll x_down x l |--
    dll x x_up (x :: l).
Proof.
  intros x x_up x_down l Hx.
  simpl dll.
  Exists x_down.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption || reflexivity.
Qed.

Lemma dll_zero_nil__remove_success_returns :
  forall x_up l,
    dll 0 x_up l |-- “ l = nil ” && emp.
Proof.
  intros x_up l.
  apply dll_zero.
  reflexivity.
Qed.

Lemma dll_singleton__remove_success_returns :
  forall x x_up,
    x <> 0 ->
    &(x # "blist" ->ₛ "down") # Ptr |-> 0 **
    &(x # "blist" ->ₛ "up") # Ptr |-> x_up |--
    dll x x_up (x :: nil).
Proof.
  intros x x_up Hx.
  simpl dll.
  Exists 0.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    + dump_pre_spatial. exact Hx.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma sepcon_swap__remove_success_returns :
  forall P Q : Assertion, P ** Q |-- Q ** P.
Proof.
  intros P Q.
  cancel Q.
  cancel P.
Qed.

Lemma dllseg_singleton__remove_success_returns :
  forall x y x_up y_up l,
    y <> 0 ->
    dllseg x y x_up y_up l **
    (&(y # "blist" ->ₛ "down") # Ptr |-> 0 **
     &(y # "blist" ->ₛ "up") # Ptr |-> y_up) |--
    dll x x_up ((l ++ y :: nil)%list).
Proof.
  intros x y x_up y_up l Hy.
  sep_apply_l_atomic (dll_singleton__remove_success_returns y y_up Hy).
  sep_apply_l_atomic
    (sepcon_swap__remove_success_returns
      (dll y y_up (y :: nil)) (dllseg x y x_up y_up l)).
  apply dllseg_dll__remove_success_returns.
Qed.

Lemma dllseg_singleton_frame__remove_success_returns :
  forall x y x_up y_up l {P : Assertion},
    y <> 0 ->
    dllseg x y x_up y_up l **
    (&(y # "blist" ->ₛ "down") # Ptr |-> 0 **
     (&(y # "blist" ->ₛ "up") # Ptr |-> y_up ** P)) |--
    dll x x_up ((l ++ y :: nil)%list) ** P.
Proof.
  intros x y x_up y_up l P Hy.
  cancel P.
  apply dllseg_singleton__remove_success_returns.
  exact Hy.
Qed.

Lemma dllseg_singleton_four_frames__remove_success_returns :
  forall A B C D P : Assertion,
  forall x y x_up y_up l,
    y <> 0 ->
    A ** (B ** (C ** (D **
      (dllseg x y x_up y_up l **
       (&(y # "blist" ->ₛ "down") # Ptr |-> 0 **
        (&(y # "blist" ->ₛ "up") # Ptr |-> y_up ** P)))))) |--
    A ** (B ** (C ** (D **
      (dll x x_up ((l ++ y :: nil)%list) ** P)))).
Proof.
  intros A B C D P x y x_up y_up l Hy.
  cancel A.
  cancel B.
  cancel C.
  cancel D.
  cancel P.
  apply dllseg_singleton__remove_success_returns.
  exact Hy.
Qed.

Lemma store_map_missing_to_none__remove_success_returns :
  forall {A B : Type} (P : A -> B -> Assertion)
         (m m' : A -> option B) i,
    m' i = None ->
    (forall a, a <> i -> m a = m' a) ->
    store_map_missing_i P m i |-- store_map P m'.
Proof.
  intros A B P m m' i Hnone Houtside.
  destruct (store_map_missing_i_equiv P m m' i Houtside)
    as [Hmissing _].
  sep_apply_l_atomic Hmissing.
  sep_apply_l_atomic
    (store_map_missing_equiv_store_map P m' i Hnone).
  cancel.
Qed.

Lemma merge_store_name_at__remove_success_returns :
  forall (m : list Z -> option addr) k p key_addr,
    m k = Some p ->
    store_map_missing_i store_name m k **
    &(p # "blist" ->ₛ "key") # Ptr |-> key_addr **
    store_string key_addr k |--
    store_map store_name m.
Proof.
  intros m k p key_addr Hlookup.
  sep_apply_r_atomic (store_map_merge store_name k p m Hlookup).
  assert (Hname:
    &(p # "blist" ->ₛ "key") # Ptr |-> key_addr **
    store_string key_addr k |-- store_name k p).
  { unfold store_name.
    Exists key_addr.
    cancel. }
  sep_apply_l_atomic Hname.
  cancel.
Qed.

Lemma store_name_missing_injective__remove_success_returns :
  forall (m : list Z -> option addr) k p,
    m k = Some p ->
    store_map_missing_i store_name m k **
    store_name k p |--
    “ forall k1 k2 q,
        m k1 = Some q -> m k2 = Some q -> k1 = k2 ”.
Proof.
  intros m k p Hlookup.
  sep_apply_l_atomic (store_map_merge store_name k p m Hlookup).
  apply store_name_map_injective_all__clear_transition.
Qed.

Lemma remove_node_model_invariants__remove_success_returns :
  forall (m_node m_value : list Z -> option addr)
         (b : Z -> option (addr * list addr))
         k p global_before global_after lh ind old_head
         l_prev l_res new_head,
    (forall k1 k2 q,
      m_node k1 = Some q -> m_node k2 = Some q -> k1 = k2) ->
    node_value_map m_node m_value ->
    contain_all_addrs m_node ((global_before ++ p :: global_after)%list) ->
    repr_all_heads lh b ->
    contain_all_correct_addrs m_node b ->
    m_node k = Some p ->
    ind = hash_string k mod NBUCK ->
    b ind = Some (old_head, (l_prev ++ p :: l_res)%list) ->
    not_key k l_prev m_node ->
    NoDup (p :: l_res) ->
    ~ In p ((global_before ++ global_after)%list) ->
    node_value_map
      (KP.remove_map m_node k) (KP.remove_map m_value k) /\
    contain_all_addrs
      (KP.remove_map m_node k) ((global_before ++ global_after)%list) /\
    repr_all_heads
      (replace_Znth ind new_head lh)
      (fun j => if Z.eq_dec j ind
                then Some (new_head, (l_prev ++ l_res)%list) else b j) /\
    contain_all_correct_addrs
      (KP.remove_map m_node k)
      (fun j => if Z.eq_dec j ind
                then Some (new_head, (l_prev ++ l_res)%list) else b j).
Proof.
  intros m_node m_value b k p global_before global_after lh ind
    old_head l_prev l_res new_head Hinjective Hnode_value Hcontain
    Hrepr Hcorrect Hlookup Hhash Hb Hnot_key Hnodup Hnotin_global.
  assert (Hnotin_bucket : ~ In p ((l_prev ++ l_res)%list)).
  { eapply removed_not_in_bucket__remove_success_returns; eauto. }
  assert (Hind_lh : 0 <= ind < Zlength lh).
  { apply (proj1 (Hrepr ind old_head)).
    exists ((l_prev ++ p :: l_res)%list).
    exact Hb. }
  split.
  - apply node_value_map_remove__remove_success_returns.
    exact Hnode_value.
  - split.
    + eapply contain_all_addrs_remove__remove_success_returns; eauto.
    + split.
      * eapply repr_all_heads_update_bucket__findref_results; eauto.
      * eapply contain_all_correct_addrs_remove__remove_success_returns; eauto.
Qed.

Lemma down_fields_distinct__remove_success_returns :
  forall (p q p_down q_down : addr),
    &(p # "blist" ->ₛ "down") # Ptr |-> p_down **
    &(q # "blist" ->ₛ "down") # Ptr |-> q_down |--
    “ p <> q ”.
Proof.
  intros p q p_down q_down.
  destruct (Z.eq_dec p q) as [Heq | Hneq].
  - subst q.
    prop_apply_p
      (dup_store_ptr (&(p # "blist" ->ₛ "down")) p_down q_down).
    Intros_p Hfalse.
    contradiction.
  - dump_pre_spatial.
    exact Hneq.
Qed.

Lemma dllseg_not_in_from_down_field__remove_success_returns :
  forall (p p_down x y x_up y_up : addr) (l : list addr),
    &(p # "blist" ->ₛ "down") # Ptr |-> p_down **
    dllseg x y x_up y_up l |-- “ ~ In p l ”.
Proof.
  intros p p_down x y x_up y_up l.
  apply dllseg_not_in.
Qed.

Lemma dllseg_down_not_in_right__remove_success_returns :
  forall (p p_down x y x_up y_up : addr) (l : list addr),
    dllseg x y x_up y_up l **
    &(p # "blist" ->ₛ "down") # Ptr |-> p_down |--
    “ ~ In p l ”.
Proof.
  intros p p_down x y x_up y_up l.
  revert x x_up.
  induction l as [|a l IH]; intros x x_up; simpl dllseg.
  - dump_pre_spatial.
    simpl.
    tauto.
  - Intros x_down.
    subst a.
    prop_apply
      (down_fields_distinct__remove_success_returns
        p x p_down x_down).
    Intros_p Hneq.
    sep_apply (IH x_down x).
    Intros_p Htail.
    dump_pre_spatial.
    simpl.
    intros [Heq | Hin].
    + apply Hneq.
      symmetry.
      exact Heq.
    + apply Htail.
      exact Hin.
Qed.

Lemma dllseg_endpoint_not_in_from_down_field__remove_success_returns :
  forall (p p_down x y x_up y_up y_down : addr) (l : list addr),
    (&(p # "blist" ->ₛ "down") # Ptr |-> p_down **
     &(y # "blist" ->ₛ "down") # Ptr |-> y_down) **
    (dllseg x y x_up y_up l **
     &(y # "blist" ->ₛ "up") # Ptr |-> y_up) |--
    “ ~ In p ((l ++ y :: nil)%list) ”.
Proof.
  intros p p_down x y x_up y_up y_down l.
  prop_apply
    (down_fields_distinct__remove_success_returns
      p y p_down y_down).
  Intros_p Hneq.
  prop_apply_p
    (dllseg_down_not_in_right__remove_success_returns
      p p_down x y x_up y_up l).
  Intros_p Hprefix.
  dump_pre_spatial.
  intros Hin.
  apply in_app_iff in Hin.
  destruct Hin as [Hin | Hin].
  - apply Hprefix.
    exact Hin.
  - simpl in Hin.
    destruct Hin as [Heq | Hfalse].
    + apply Hneq.
      symmetry.
      exact Heq.
    + contradiction.
Qed.

Lemma contain_all_correct_addrs_remove_bucket__remove_success_returns :
  forall (m : list Z -> option addr)
         (b : Z -> option (addr * list addr))
         (k : list Z) (p ind old_head new_head : addr)
         (l_prev l_tail : list addr),
    contain_all_correct_addrs m b ->
    b ind = Some (old_head, (l_prev ++ p :: l_tail)%list) ->
    hash_string k mod NBUCK = ind ->
    m k = Some p ->
    not_key k l_prev m ->
    NoDup (p :: l_tail) ->
    (forall k1 k2 q,
      m k1 = Some q -> m k2 = Some q -> k1 = k2) ->
    contain_all_correct_addrs
      (KP.remove_map m k)
      (fun j => if Z.eq_dec j ind
                then Some (new_head, (l_prev ++ l_tail)%list)
                else b j).
Proof.
  intros m b k p ind old_head new_head l_prev l_tail
    Hcorrect Hbucket Hhash Hlookup Hnotkey Hnodup Hinjective.
  eapply contain_all_correct_addrs_remove__remove_success_returns;
    eauto.
  eapply removed_not_in_bucket__remove_success_returns; eauto.
Qed.

Lemma store_map_missing_update__remove_success_returns :
  forall {A B : Type} (P : A -> B -> Assertion)
         (m m' : A -> option B) (i : A) (v : B),
    m' i = Some v ->
    (forall a, a <> i -> m a = m' a) ->
    P i v ** store_map_missing_i P m i |-- store_map P m'.
Proof.
  intros A B P m m' i v Hlookup Houtside.
  destruct (store_map_missing_i_equiv P m m' i Houtside) as [Hto _].
  sep_apply_l_atomic Hto.
  sep_apply_l_atomic (store_map_merge P i v m' Hlookup).
  cancel.
Qed.

Lemma sllbseg_unlink__remove_success_returns :
  forall (cell slot : addr) (l_prev : list addr)
         (next : addr) (l_tail : list addr),
    sllbseg cell slot l_prev **
    slot # Ptr |-> next **
    sll next l_tail |--
      EX head : addr,
        “ cell <> NULL ” &&
        cell # Ptr |-> head **
        sll head ((l_prev ++ l_tail)%list).
Proof.
  intros cell slot l_prev.
  revert cell.
  induction l_prev as [|p l_prev IH]; intros cell next l_tail.
  - simpl sllbseg.
    Intros_p Hcell.
    Intros_p Heq.
    subst slot.
    Exists next.
    simpl app.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      exact Hcell.
  - simpl sllbseg.
    Intros_p Hcell.
    Intros_p Hp.
    sep_apply_l_atomic
      (IH (&(p # "blist" ->ₛ "next")) next l_tail).
    Intros head.
    rename H into Hnext_cell.
    Exists p.
    simpl app.
    simpl sll.
    Exists head.
    split_pure_spatial.
    + cancel (cell # Ptr |-> p).
      cancel (&(p # "blist" ->ₛ "next") # Ptr |-> head).
      cancel (sll head ((l_prev ++ l_tail)%list)).
    + split_pures.
      * dump_pre_spatial. exact Hcell.
      * dump_pre_spatial. exact Hp.
      * dump_pre_spatial. reflexivity.
      * dump_pre_spatial. exact Hnext_cell.
Qed.

Lemma dll_zero__remove_success_returns :
  forall (x_up : addr) (l : list addr),
    dll NULL x_up l |-- “ l = nil ” && emp.
Proof.
  apply dll_zero_nil__remove_success_returns.
Qed.

Lemma dllseg_nil_elim__remove_success_returns :
  forall (x y x_up y_up : addr),
    x = y ->
    x_up = y_up ->
    dllseg x y x_up y_up nil |-- emp.
Proof.
  intros x y x_up y_up Hxy Hup.
  subst y.
  subst y_up.
  rewrite dllseg_nil_equiv.
  cancel.
Qed.

Lemma frame_dll_nil__remove_success_returns :
  forall (P : Assertion) (x_up : addr),
    P |-- P ** dll NULL x_up nil.
Proof.
  intros P x_up.
  simpl dll.
  split_pure_spatial.
  - cancel P.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma dll_not_in_from_down_field__remove_success_returns :
  forall (p p_down x x_up : addr) (l : list addr),
    &(p # "blist" ->ₛ "down") # Ptr |-> p_down **
    dll x x_up l |-- “ ~ In p l ”.
Proof.
  intros p p_down x x_up l.
  apply (dll_exposed_down_not_in__remove_success_returns
    l p p_down x x_up).
Qed.

Lemma remove_return_spatial_reorder__remove_success_returns :
  forall (removed key_pre itv key_addr val dl_prev b_down h_bucks : addr)
         (k : list Z) (m_uint : addr -> option Z)
         (m_node : list Z -> option addr)
         (b : Z -> option (addr * list addr)) (lh : list addr),
    &(itv # "blist" ->ₛ "key") # Ptr |-> key_addr **
    (store_string key_addr k **
     (store_string key_pre k **
      (&(itv # "blist" ->ₛ "val") # UInt |-> val **
       (&(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev **
        (removed # Int |-> 1 **
         (store_map store_uint m_uint **
          (store_map store_name m_node **
           (store_map store_sll b **
            (PtrArray.full h_bucks 211 lh **
             &(itv # "blist" ->ₛ "down") # Ptr |-> b_down))))))))) |--
    PtrArray.full h_bucks 211 lh **
    (store_map store_sll b **
     (store_map store_name m_node **
      (store_string key_pre k **
       (removed # Int |-> 1 **
        (store_map store_uint m_uint **
         (&(itv # "blist" ->ₛ "key") # Ptr |-> key_addr **
          (store_string key_addr k **
            (&(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev **
             (&(itv # "blist" ->ₛ "down") # Ptr |-> b_down **
              &(itv # "blist" ->ₛ "val") # UInt |-> val))))))))).
Proof.
  intros.
  cancel (PtrArray.full h_bucks 211 lh).
  cancel (store_map store_sll b).
  cancel (store_map store_name m_node).
  cancel (store_string key_pre k).
  cancel (removed # Int |-> 1).
  cancel (store_map store_uint m_uint).
  cancel (&(itv # "blist" ->ₛ "key") # Ptr |-> key_addr).
  cancel (store_string key_addr k).
  cancel (&(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev).
  cancel (&(itv # "blist" ->ₛ "down") # Ptr |-> b_down).
  cancel (&(itv # "blist" ->ₛ "val") # UInt |-> val).
Qed.

Lemma remove_return_terminal_spatial_reorder__remove_success_returns :
  forall (removed key_pre itv key_addr val dl_prev b_down h_bucks : addr)
         (k : list Z) (m_uint : addr -> option Z)
         (m_node : list Z -> option addr)
         (b : Z -> option (addr * list addr)) (lh : list addr),
    &(itv # "blist" ->ₛ "key") # Ptr |-> key_addr **
    (store_string key_addr k **
     (store_string key_pre k **
      (&(itv # "blist" ->ₛ "val") # UInt |-> val **
       (&(itv # "blist" ->ₛ "down") # Ptr |-> b_down **
        (&(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev **
         (removed # Int |-> 1 **
          (store_map store_uint m_uint **
           (store_map store_name m_node **
            (store_map store_sll b **
             PtrArray.full h_bucks 211 lh))))))))) |--
    PtrArray.full h_bucks 211 lh **
    (store_map store_sll b **
     (store_map store_name m_node **
      (store_string key_pre k **
       (removed # Int |-> 1 **
        (store_map store_uint m_uint **
         (&(itv # "blist" ->ₛ "key") # Ptr |-> key_addr **
          (store_string key_addr k **
           (&(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev **
            (&(itv # "blist" ->ₛ "down") # Ptr |-> b_down **
             &(itv # "blist" ->ₛ "val") # UInt |-> val))))))))).
Proof.
  intros.
  cancel (PtrArray.full h_bucks 211 lh).
  cancel (store_map store_sll b).
  cancel (store_map store_name m_node).
  cancel (store_string key_pre k).
  cancel (removed # Int |-> 1).
  cancel (store_map store_uint m_uint).
  cancel (&(itv # "blist" ->ₛ "key") # Ptr |-> key_addr).
  cancel (store_string key_addr k).
  cancel (&(itv # "blist" ->ₛ "up") # Ptr |-> dl_prev).
  cancel (&(itv # "blist" ->ₛ "down") # Ptr |-> b_down).
  cancel (&(itv # "blist" ->ₛ "val") # UInt |-> val).
Qed.

Lemma dllseg_cons_unfold__remove_traversal :
  forall x y x_up y_up a l,
    dllseg x y x_up y_up (a :: l) |--
      “ x <> NULL ” && “ x = a ” &&
      EX x_down,
        &(x # "blist" ->ₛ "down") # Ptr |-> x_down **
        &(x # "blist" ->ₛ "up") # Ptr |-> x_up **
        dllseg x_down y x y_up l.
Proof.
  intros.
  simpl dllseg.
  unfold derivable1.
  auto.
Qed.

Lemma dllseg_split_last__remove_setup_extraction :
  forall top top_next b top_up dl_prev dl_up_tail,
    top <> 0 ->
    &(top # "blist" ->ₛ "down") # Ptr |-> top_next **
    &(top # "blist" ->ₛ "up") # Ptr |-> top_up **
    dllseg top_next b top dl_prev dl_up_tail |--
      EX dl_prev_prev dl_up_prefix,
        “ (top :: dl_up_tail)%list =
          (dl_up_prefix ++ dl_prev :: nil)%list ” &&
        dllseg top dl_prev top_up dl_prev_prev dl_up_prefix **
        &(dl_prev # "blist" ->ₛ "down") # Ptr |-> b **
        &(dl_prev # "blist" ->ₛ "up") # Ptr |-> dl_prev_prev.
Proof.
  intros top top_next b top_up dl_prev dl_up_tail.
  revert top top_next top_up.
  induction dl_up_tail as [|a tail IH];
    intros top top_next top_up Htop.
  - simpl dllseg.
    Intros_p Hnext.
    Intros_p Hprev.
    Exists top_up (@nil addr).
    simpl app.
    simpl dllseg.
    split_pure_spatial.
    + subst top_next dl_prev.
      cancel.
    + split_pures.
      * dump_pre_spatial.
        rewrite Hprev.
        reflexivity.
      * dump_pre_spatial.
        exact Hprev.
      * dump_pre_spatial.
        reflexivity.
  - sep_apply_l_atomic
      (dllseg_cons_unfold__remove_traversal
        top_next b top dl_prev a tail).
    Intros next.
    subst a.
    sep_apply_l_atomic
      (IH top_next next top ltac:(exact H)).
    Intros dl_prev_prev dl_up_prefix.
    Exists dl_prev_prev (top :: dl_up_prefix).
    simpl app.
    simpl dllseg.
    Exists top_next.
    split_pure_spatial.
    + normalize; repeat cancel.
    + split_pures.
      * dump_pre_spatial.
        exact (f_equal (fun xs : list addr => top :: xs) H0).
      * dump_pre_spatial.
        exact Htop.
      * dump_pre_spatial.
        reflexivity.
Qed.

Lemma store_map_missing_zero_to_missing_first__clear_setup :
  forall (B : Type) (P : Z -> B -> Assertion) m,
    (forall a b, m a = Some b -> 0 <= a) ->
    store_map_missing_i P m 0 |--
    store_map_missing_first_i_Z P m 0.
Proof.
  intros B P m Hnonnegative.
  unfold store_map_missing_i, store_map_missing_first_i_Z.
  Intros l.
  rename H into Hdomain.
  rename H0 into Hnodup.
  Exists l.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      intros a.
      specialize (Hdomain a).
      split.
      * intro Hin.
        apply Hdomain in Hin.
        destruct Hin as [[b Hb] Hneq].
        split.
        -- exists b.
           exact Hb.
        -- pose proof (Hnonnegative a b Hb).
           lia.
      * intros [[b Hb] Hpositive].
        apply Hdomain.
        split.
        -- exists b.
           exact Hb.
        -- lia.
    + dump_pre_spatial.
      exact Hnodup.
Qed.

Lemma remaining_after_ge_nbuck__clear_final :
  forall m m_rem i,
    NBUCK <= i ->
    remaining_after_bucket_index m m_rem i ->
    remaining_after_bucket_index m m_rem NBUCK.
Proof.
  intros m m_rem i Hi Hrem.
  unfold remaining_after_bucket_index in *.
  intros k p.
  specialize (Hrem k p).
  pose proof (Z.mod_pos_bound (hash_string k) NBUCK) as Hmod.
  unfold NBUCK in *.
  split.
  - intro Hlookup.
    apply Hrem in Hlookup.
    lia.
  - intros [_ Hge].
    lia.
Qed.


(** ********* Removal and cleanup lemmas ********* *)

Lemma sublist_replace_Znth_zero_succ__create_bucks :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    sublist 0 i l = zeros i ->
    sublist 0 (i + 1) (replace_Znth i 0 l) = zeros (i + 1).
Proof.
  intros l i Hi Hprefix.
  rewrite (sublist_split 0 (i + 1) i (replace_Znth i 0 l)) by
    (try rewrite Zlength_replace_Znth; lia).
  rewrite sublist_replace_prefix by lia.
  rewrite (sublist_single 0 i (replace_Znth i 0 l)) by
    (rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_eq by lia.
  rewrite Hprefix.
  rewrite zeros_succ by lia.
  reflexivity.
Qed.

Lemma sublist_full_zeros_eq__create_bucks :
  forall (l : list Z) (n : Z),
    Zlength l = n ->
    sublist 0 n l = zeros n ->
    l = zeros n.
Proof.
  intros l n Hlen Hprefix.
  rewrite <- (sublist_self l n (eq_sym Hlen)).
  exact Hprefix.
Qed.

Lemma node_value_map_insert__add_final :
  forall (m_node m_value : list Z -> option addr) (k : list Z) (p : addr),
    node_value_map m_node m_value ->
    node_value_map
      (KP.insert_map m_node k p)
      (KP.insert_map m_value k (&(p # "blist" ->ₛ "val"))).
Proof.
  intros m_node m_value k p Hmap.
  unfold node_value_map in *.
  subst m_value.
  apply functional_extensionality; intro key.
  unfold KP.insert_map, map_fun.
  destruct (list_eq_dec Z.eq_dec key k) as [Heq | Hneq].
  - reflexivity.
  - destruct (m_node key); reflexivity.
Qed.

Lemma node_value_map_none__add_final :
  forall (m_node m_value : list Z -> option addr) (k : list Z),
    node_value_map m_node m_value ->
    m_value k = None ->
    m_node k = None.
Proof.
  intros m_node m_value k Hmap Hnone.
  unfold node_value_map in Hmap.
  subst m_value.
  unfold map_fun in Hnone.
  destruct (m_node k); congruence.
Qed.

Lemma store_map_name_insert__add_final :
  forall (m : list Z -> option addr) (k : list Z) (p : addr),
    m k = None ->
    store_name k p ** store_map store_name m
    |-- store_map store_name (KP.insert_map m k p).
Proof.
  intros m k p Hnone.
  sep_apply (store_map_equiv_store_map_missing store_name m k Hnone).
  assert (Houtside : forall key, key <> k ->
             m key = KP.insert_map m k p key).
  { intros key Hneq.
    symmetry.
    apply KP.insert_map_diff.
    intro Heq. apply Hneq. symmetry. exact Heq. }
  destruct (store_map_missing_i_equiv store_name m
              (KP.insert_map m k p) k Houtside) as [Hforward _].
  sep_apply Hforward.
  sep_apply (store_map_merge store_name k p (KP.insert_map m k p)
               (KP.insert_map_same m k p)).
  cancel.
Qed.

Lemma store_map_uint_insert__add_final :
  forall (m : addr -> option Z) (p v : Z),
    p # UInt |-> v ** store_map store_uint m
    |-- store_map store_uint (PV.insert_map m p v).
Proof.
  intros m p v.
  destruct (m p) as [old |] eqn:Hmp.
  - sep_apply (store_map_split store_uint p old m Hmp).
    unfold store_uint.
    Intros.
    sep_apply_l_atomic (dup_store_4bytes p v old).
    Intros_p Hfalse.
    contradiction.
  - sep_apply (store_map_equiv_store_map_missing store_uint m p Hmp).
    assert (Houtside : forall q, q <> p ->
               m q = PV.insert_map m p v q).
    { intros q Hneq.
      symmetry.
      apply PV.insert_map_diff.
      congruence. }
    destruct (store_map_missing_i_equiv store_uint m
                (PV.insert_map m p v) p Houtside) as [Hforward _].
    sep_apply Hforward.
    sep_apply (store_map_merge store_uint p v (PV.insert_map m p v)
                 (PV.insert_map_same m p v)).
    cancel.
Qed.

Lemma dll_prepend_nonempty__add_final :
  forall (new old old_down : addr) (tail : list addr),
    new <> NULL ->
    old <> NULL ->
    &(old # "blist" ->ₛ "down") # Ptr |-> old_down **
    &(old # "blist" ->ₛ "up") # Ptr |-> new **
    dll old_down old tail **
    &(new # "blist" ->ₛ "down") # Ptr |-> old **
    &(new # "blist" ->ₛ "up") # Ptr |-> NULL
    |-- dll new NULL (new :: old :: tail).
Proof.
  intros new old old_down tail Hnew Hold.
  simpl dll.
  Exists old old_down.
  normalize.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: assumption || reflexivity.
Qed.

Lemma sll_Znth0__find_setup :
  forall p l,
    sll p l |-- “ Znth 0 l 0 = p ” && sll p l.
Proof.
  intros p l.
  split_pure_spatial.
  - cancel.
  - destruct l as [|a l].
    + simpl sll.
      Intros_p Hnull.
      dump_pre_spatial.
      subst p.
      reflexivity.
    + simpl sll.
      Intros next.
      dump_pre_spatial.
      subst a.
      reflexivity.
Qed.

Lemma map_composable_node_value_lookup__find_traversal :
  forall (m_node m_value : list Z -> option addr)
         (m2 : addr -> option Z) (k : list Z) (p : addr),
    node_value_map m_node m_value ->
    map_composable m_value m2 ->
    m_node k = Some p ->
    exists v, m2 (&(p # "blist" ->ₛ "val")) = Some v.
Proof.
  intros m_node m_value m2 k p Hnode Hcompose Hlookup.
  unfold node_value_map in Hnode.
  subst m_value.
  destruct Hcompose as [Hcompose _].
  specialize (Hcompose k).
  unfold map_fun in Hcompose.
  rewrite Hlookup in Hcompose.
  destruct Hcompose as [Hnone | [q [v [Hq Hv]]]].
  - discriminate Hnone.
  - inversion Hq; subst q.
    exists v; exact Hv.
Qed.

Lemma dll_member_nonnull__find_return :
  forall x x_up l p,
    In p l ->
    dll x x_up l |-- “ p <> NULL ”.
Proof.
  intros x x_up l.
  revert x x_up.
  induction l as [|a l IH]; intros x x_up p Hin.
  - contradiction.
  - simpl dll.
    Intros x_down.
    destruct Hin as [Hp | Hin].
    + subst p.
      dump_pre_spatial. lia.
    + sep_apply (IH x_down x p Hin).
      Intros_p Hp.
      dump_pre_spatial. exact Hp.
Qed.

Lemma store_map_name_lookup_exclusive__find_traversal :
  forall (m : list Z -> option addr) (k1 k2 : list Z) (p : addr),
    k1 <> k2 ->
    m k1 = Some p ->
    store_map store_name m |-- “ m k2 <> Some p ”.
Proof.
  intros m k1 k2 p Hneq Hlookup.
  destruct (Classical_Prop.classic (m k2 = Some p)) as [Hsame | Hdiff].
  - sep_apply_l_atomic (store_map_split store_name k1 p m Hlookup).
    assert (Houtside : forall key, key <> k1 ->
              m key = KP.remove_map m k1 key).
    { intros key Hkey.
      symmetry; apply KP.remove_map_diff; congruence. }
    destruct (store_map_missing_i_equiv
                store_name m (KP.remove_map m k1) k1 Houtside)
      as [Hto_removed _].
    sep_apply_l_atomic Hto_removed.
    sep_apply_l_atomic
      (store_map_missing_equiv_store_map store_name
         (KP.remove_map m k1) k1 (KP.remove_map_same m k1)).
    assert (Hsecond : KP.remove_map m k1 k2 = Some p).
    { rewrite KP.remove_map_diff; [exact Hsame | exact Hneq]. }
    sep_apply_l_atomic
      (store_map_split store_name k2 p (KP.remove_map m k1) Hsecond).
    unfold store_name.
    Intros key_addr1 key_addr2.
    sep_apply_l_atomic
      (dup_store_ptr (&(p # "blist" ->ₛ "key")) key_addr1 key_addr2).
    Intros_p Hfalse; contradiction.
  - dump_pre_spatial; exact Hdiff.
Qed.

Lemma not_key_snoc__find_traversal :
  forall (k : list Z) (l_prev : list addr)
         (m : list Z -> option addr) (k_cur : list Z) (p : addr),
    not_key k l_prev m ->
    k <> k_cur ->
    m k_cur = Some p ->
    store_map store_name m |--
      “ not_key k (l_prev ++ (p :: nil)%list) m ”.
Proof.
  intros k l_prev m k_cur p Hnot Hneq Hlookup.
  assert (Hneq' : k_cur <> k) by congruence.
  prop_apply_p
    (store_map_name_lookup_exclusive__find_traversal
       m k_cur k p Hneq' Hlookup).
  Intros_p Habsent.
  dump_pre_spatial.
  unfold not_key in *.
  intros p0 k1 Hin Hmap.
  apply in_app_iff in Hin.
  destruct Hin as [Hin | Hin].
  - eapply Hnot; eauto.
  - simpl in Hin.
    destruct Hin as [Hp | []].
    subst p0.
    intro Heq; subst k1.
    apply Habsent; exact Hmap.
Qed.

Lemma lookup_none_after_bucket_exhaustion__find_return_empty :
  forall (m_node m_value : list Z -> option addr)
         (b : Z -> option (addr * list addr)) (k : list Z)
         (ind ph : Z) (bucket : list addr),
    node_value_map m_node m_value ->
    ind = (hash_string_k k) % (NBUCK) ->
    contain_all_correct_addrs m_node b ->
    b ind = Some (ph, bucket) ->
    not_key k bucket m_node ->
    m_value k = None.
Proof.
  intros m_node m_value b k ind ph bucket Hvalue Hind Hcorrect Hb Hnot.
  unfold node_value_map in Hvalue.
  subst m_value.
  unfold map_fun.
  destruct (m_node k) as [p |] eqn:Hkey; [| reflexivity].
  exfalso.
  unfold contain_all_correct_addrs in Hcorrect.
  specialize (Hcorrect ind p).
  assert (Hbucket : exists ph0 l0,
             b ind = Some (ph0, l0) /\ In p l0).
  { apply (proj1 Hcorrect).
    exists k. split; [| exact Hkey].
    assert (Hnonneg : 0 <= hash_string_k k).
    { unfold hash_string_k, hash_string.
      apply Z.mod_pos_bound. lia. }
    rewrite <- Z.rem_mod_nonneg by
      (try exact Hnonneg; unfold NBUCK; lia).
    unfold hash_string_k in Hind.
    symmetry. exact Hind. }
  destruct Hbucket as [ph0 [l0 [Hb0 Hin]]].
  rewrite Hb in Hb0.
  inversion Hb0; subst ph0 l0.
  unfold not_key in Hnot.
  exact (Hnot p k Hin Hkey eq_refl).
Qed.

Lemma sll_head_matches_Znth__find_return_empty :
  forall (p : addr) (l : list addr),
    sll p l |-- “ p = Znth 0 l 0 ” && sll p l.
Proof.
  intros p l.
  split_pure_spatial.
  - cancel.
  - destruct l as [|a tail].
    + simpl sll.
      Intros_p Hnull.
      dump_pre_spatial.
      subst p.
      reflexivity.
    + simpl sll.
      Intros next.
      dump_pre_spatial.
      subst a.
      reflexivity.
Qed.

Lemma replace_Znth_id__find_return_found :
  forall {A : Type} (l : list A) (i : Z) (d v : A),
    0 <= i < Zlength l ->
    Znth i l d = v ->
    replace_Znth i v l = l.
Proof.
  intros A l i d v Hi Hvalue.
  subst v.
  clear Hi.
  unfold replace_Znth, Znth.
  assert (Hreplace : forall (n : nat) (xs : list A),
             replace_nth n xs (nth n xs d) = xs).
  { intro n. induction n; intros [|x xs]; simpl; auto.
    f_equal. apply IHn. }
  apply Hreplace.
Qed.

Lemma replace_Znth_twice__find_return_found :
  forall {A : Type} (l : list A) (i : Z) (a b : A),
    replace_Znth i a (replace_Znth i b l) = replace_Znth i a l.
Proof.
  intros A l i a b.
  unfold replace_Znth.
  assert (Hreplace : forall (n : nat) (xs : list A),
             replace_nth n (replace_nth n xs b) a =
             replace_nth n xs a).
  { intro n. induction n; intros [|x xs]; simpl; auto.
    f_equal. apply IHn. }
  apply Hreplace.
Qed.

Lemma bucket_move_to_front_invariants__find_return :
  forall (m : list Z -> option Z)
         (b : Z -> option (Z * list Z)) lh ind old_head old_l new_head new_l,
    0 <= ind < Zlength lh ->
    b ind = Some (old_head, old_l) ->
    repr_all_heads lh b ->
    contain_all_correct_addrs m b ->
    (forall p, In p new_l <-> In p old_l) ->
    repr_all_heads (replace_Znth ind new_head lh)
      (update_b0_at b ind new_head new_l) /\
    contain_all_correct_addrs m
      (update_b0_at b ind new_head new_l).
Proof.
  intros m b lh ind old_head old_l new_head new_l
    Hind Hb Hrepr Hcorrect Hmembers.
  split.
  - unfold repr_all_heads in *.
    intros j p.
    destruct (Z.eq_dec j ind) as [Heq | Hneq].
    + subst j.
      split.
      * intros [l0 Hnew].
        unfold update_b0_at in Hnew.
        destruct (Z.eq_dec ind ind) as [_ | Hcontra]; [|contradiction].
        inversion Hnew; subst p l0.
        split.
        -- rewrite Zlength_replace_Znth. exact Hind.
        -- apply Znth_replace_eq. exact Hind.
      * intros [Hrange Hnth].
        rewrite Zlength_replace_Znth in Hrange.
        rewrite (Znth_replace_eq lh ind new_head 0 Hind) in Hnth.
        subst p.
        exists new_l.
        unfold update_b0_at.
        destruct (Z.eq_dec ind ind); [reflexivity | contradiction].
    + specialize (Hrepr j p).
      split.
      * intros [l0 Hnew].
        unfold update_b0_at in Hnew.
        destruct (Z.eq_dec j ind); [contradiction |].
        destruct (proj1 Hrepr (ex_intro _ l0 Hnew)) as [Hj Hnth].
        split.
        -- rewrite Zlength_replace_Znth. exact Hj.
        -- rewrite (Znth_replace_neq lh ind j new_head 0 Hind Hj ltac:(congruence)).
           exact Hnth.
      * intros [Hj Hnth].
        rewrite Zlength_replace_Znth in Hj.
        rewrite (Znth_replace_neq lh ind j new_head 0 Hind Hj ltac:(congruence)) in Hnth.
        destruct (proj2 Hrepr (conj Hj Hnth)) as [l0 Hb0].
        exists l0.
        unfold update_b0_at.
        destruct (Z.eq_dec j ind); [contradiction | exact Hb0].
  - unfold contain_all_correct_addrs in *.
    intros j p.
    specialize (Hcorrect j p).
    destruct (Z.eq_dec j ind) as [Heq | Hneq].
    + subst j.
      split.
      * intros Hkey.
        destruct (proj1 Hcorrect Hkey) as [ph0 [l0 [Hb0 Hin]]].
        rewrite Hb in Hb0.
        inversion Hb0; subst ph0 l0.
        exists new_head, new_l.
        split.
        -- unfold update_b0_at.
           destruct (Z.eq_dec ind ind); [reflexivity | contradiction].
        -- apply (proj2 (Hmembers p)). exact Hin.
      * intros [ph0 [l0 [Hb0 Hin]]].
        unfold update_b0_at in Hb0.
        destruct (Z.eq_dec ind ind) as [_ | Hcontra]; [|contradiction].
        inversion Hb0; subst ph0 l0.
        apply (proj2 Hcorrect).
        exists old_head, old_l.
        split; [exact Hb |].
        apply (proj1 (Hmembers p)). exact Hin.
    + split.
      * intros Hkey.
        destruct (proj1 Hcorrect Hkey) as [ph0 [l0 [Hb0 Hin]]].
        exists ph0, l0. split; [|exact Hin].
        unfold update_b0_at.
        destruct (Z.eq_dec j ind); [contradiction | exact Hb0].
      * intros [ph0 [l0 [Hb0 Hin]]].
        apply (proj2 Hcorrect).
        exists ph0, l0. split; [|exact Hin].
        unfold update_b0_at in Hb0.
        destruct (Z.eq_dec j ind); [contradiction | exact Hb0].
Qed.

