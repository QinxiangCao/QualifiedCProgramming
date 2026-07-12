Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.

Require Import AUXLib.Axioms.
Require Import AUXLib.Feq.

Local Open Scope Z.

(**********************************************************************************)
(*                                                                                *)
(*                   this memory model is based on Imp_RO.Mem                     *)
(*                        but mem: addr -> mem_var                                *)
(*                                                                                *)
(**********************************************************************************)

Definition addr : Type := Z.

Definition addr_eqb : addr -> addr -> bool := Z.eqb.
Definition addr_dec : forall (x y : addr), {x = y} + {x <> y} := Z.eq_dec.

Definition addr_eqb_eq : forall p1 p2, addr_eqb p1 p2 = true <-> p1 = p2 := Z.eqb_eq.

Definition addr_eqb_neq : forall p1 p2,
  addr_eqb p1 p2 = false <-> p1 <> p2 := Z.eqb_neq.

Definition addr_eqb_refl : forall p,
 addr_eqb p p = true := Z.eqb_refl.

Ltac addr_destruct x y :=
  let H := fresh "E" in
  destruct (addr_eqb x y) eqn:H;
  [apply addr_eqb_eq in H | apply addr_eqb_neq in H].


Definition byte : Type := Z.

Definition byte_eqb : byte -> byte -> bool := Z.eqb.

Inductive mem_var :=
  | Noperm (* No permission *)
  | Noninit (* Non-initialized *)
  | value (b: byte) (* assign to a byte *)
.    

Definition mem_var_eqb (a b : mem_var) : bool := 
  match a, b with 
    | Noperm , Noperm => true
    | Noninit , Noninit => true 
    | value v1 , value v2 => byte_eqb v1 v2
    | _ , _ => false  
  end.

Definition mem : Type := addr -> mem_var.

Definition empty_mem : mem := fun p => Noperm.

Definition single_byte_mem (p : addr) (n : byte) : mem :=
  fun p' => if addr_eqb p' p then value n else Noperm.

Definition single_Noninit_mem (p : addr) : mem :=
  fun p' => if addr_eqb p' p then Noninit else Noperm.

Definition mem_byte_update (m : addr -> mem_var) (p : addr) (n : byte) : mem :=
  fun p' => if addr_eqb p' p then value n else m p'.

Definition mem_noninit_update (m : addr -> mem_var) (p : addr) : mem :=
  fun p' => if addr_eqb p' p then Noninit else Noperm.

Definition mem_remove (m : addr -> mem_var) (p : addr) : mem :=
  fun p' => if addr_eqb p' p then Noperm else m p'.

Fixpoint mem_update_list (m : mem) (ps : list addr) (ns : list (option byte)) : mem :=
  match ps, ns with
  | p :: ps', n :: ns' =>
    match n with 
      | Some n => mem_byte_update (mem_update_list m ps' ns') p n
      | None => mem_noninit_update (mem_update_list m ps' ns') p
    end
  | _, _ => m
  end.

Fixpoint Z_seq_nat (p : Z) (n : nat) : list Z :=
  match n with 
    | O => nil 
    | S n' => p :: Z_seq_nat (p + 1) n' 
  end.

Definition Z_seq (p : Z) (n : Z) : list Z :=
  Z_seq_nat p (Z.to_nat n). 

Definition mem_update_N (m : mem) (p : addr) (v : byte) (n : Z) : mem :=
  mem_update_list m (Z_seq p n) (repeat (Some v) (Z.to_nat n)).

Definition mem_empty (m : mem) : Prop :=
  forall p, m p = Noperm.

Definition mem_single (m : mem) (p : addr) (n : byte) : Prop :=
  m p = value n /\ (forall p', p' <> p -> m p' = Noperm).

Definition mem_join (m1 m2 m: mem) : Prop :=
  forall p,
  (m1 p = Noperm /\ m2 p = Noperm /\ m p = Noperm) \/
  (m1 p = Noperm /\ m2 p = Noninit /\ m p = Noninit) \/
  (m1 p = Noninit /\ m2 p = Noperm /\ m p = Noninit) \/ 
  (exists n, m1 p = Noperm /\ m2 p = value n /\ m p = value n) \/
  (exists n, m1 p = value n /\ m2 p = Noperm /\ m p = value n).

#[export] Instance mem_join_congr :
  Proper (f_eq ==> f_eq ==> f_eq ==> iff) mem_join.
Proof.
  unfold Proper, respectful, mem_join, f_eq.
  intros. split ; intros ; specialize (H p); specialize (H0 p); specialize (H1 p);
  ( repeat split; intros; 
    destruct (H2 p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]] ; 
    [left | right ; left | right ; right ; left | right ; right ; right; left; exists n | right; right; right; right; exists n];
    repeat split; congruence).
Qed.

Definition mem_incl (m1 m2 : mem) : Prop :=
  forall p, m1 p <> Noperm -> m2 p = m1 p.

Lemma empty_mem_empty : mem_empty empty_mem.
Proof.
  unfold mem_empty, empty_mem. auto.
Qed.

Lemma mem_empty_IS_empty_mem : forall m, mem_empty m -> f_eq m empty_mem.
Proof.
  unfold mem_empty, empty_mem, f_eq. intros.  auto.
Qed.

Lemma single_mem_single : forall p n, mem_single (single_byte_mem p n) p n.
Proof.
  unfold mem_single, single_byte_mem.
  intros. split; intros.
  - addr_destruct p p; congruence.
  - addr_destruct p' p; congruence.
Qed.

Lemma mem_join_comm : forall m1 m2 m,
  mem_join m1 m2 m ->
  mem_join m2 m1 m.
Proof.
  unfold mem_join. intros.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]] ; [ |  |  | right ; right ; right; right ; exists n | right; right; right; left; exists n] ; tauto.
Qed.

Arguments mem_join_comm [m1] [m2] [m].

Lemma mem_join_assoc1: forall m1 m2 m3 m23 m123,
  mem_join m2 m3 m23 ->
  mem_join m1 m23 m123 ->
  exists m12,
  mem_join m1 m2 m12 /\ mem_join m12 m3 m123.
Proof.
  unfold mem_join. intros.
  exists (fun p => match m1 p with
                   | Noperm => m2 p
                   | _ => m1 p end).
  split; intros.
  - destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
    destruct (H0 p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]] ; try congruence; 
     [ | | do 4 right; exists n' | | | | do 3 right; left ; exists n ] ; try (rewrite H4 ; tauto).
  - destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
  destruct (H0 p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]] ; try congruence; 
   [ | | do 4 right; exists n' | | | do 3 right; left; exists n'; rewrite H3 in H5; rewrite H5 in H2 | do 4 right; exists n; rewrite H3 in H5; rewrite <- H5 in H6 ] ; try (rewrite H4 ; tauto).
Qed.

Arguments mem_join_assoc1 [m1] [m2] [m3] [m23] [m123].

Lemma mem_join_assoc2: forall m1 m2 m3 m12 m123,
  mem_join m1 m2 m12 ->
  mem_join m12 m3 m123 ->
  exists m23,
  mem_join m2 m3 m23 /\ mem_join m1 m23 m123.
Proof.
  intros. apply mem_join_comm in H. apply mem_join_comm in H0.
  pose proof (mem_join_assoc1 H H0).
  destruct H1 as [m23 [? ?] ].
  apply mem_join_comm in H1. apply mem_join_comm in H2.
  exists m23. auto.
Qed.

Arguments mem_join_assoc2 [m1] [m2] [m3] [m12] [m123].

Lemma mem_join_emp1 : forall m,
  mem_join empty_mem m m.
Proof.
  intros. unfold mem_join.
  intros. destruct (m p) eqn:? ; try tauto.
  do 3 right. left. exists b. tauto.
Qed.

Lemma mem_join_emp2 : forall m,
  mem_join m empty_mem m.
Proof.
  intros. unfold mem_join.
  intros. destruct (m p) eqn:? ; try tauto.
  do 4 right. exists b. tauto.
Qed.

Lemma mem_join_eq_inv1 : forall m1 m1' m2 m2' m m',
  f_eq m2 m2' ->
  f_eq m m' ->
  mem_join m1 m2 m ->
  mem_join m1' m2' m' ->
  f_eq m1 m1'.
Proof.
  unfold mem_join, f_eq.
  intros. rename x into p.
  specialize (H p). specialize (H0 p).
  destruct (H1 p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
  destruct (H2 p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]] ; 
  congruence.
Qed.

Lemma mem_join_eq_inv2 : forall m1 m1' m2 m2' m m',
  f_eq m1 m1' ->
  f_eq m m' ->
  mem_join m1 m2 m ->
  mem_join m1' m2' m' ->
  f_eq m2 m2'.
Proof.
  unfold mem_join, f_eq.
  intros. rename x into p.
  specialize (H p). specialize (H0 p).
  destruct (H1 p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
  destruct (H2 p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]] ; 
  congruence.
Qed.

Lemma mem_join_None1 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m1 p = Noperm ->
  m p = m2 p.
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
  congruence.
Qed.

Arguments mem_join_None1 [m1] [m2] [m].

Lemma mem_join_None2 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m2 p = Noperm ->
  m p = m1 p.
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
  congruence.
Qed.

Arguments mem_join_None2 [m1] [m2] [m].

Lemma mem_join_None3 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m p = Noperm ->
  m1 p = Noperm /\ m2 p = Noperm.
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
  split; congruence.
Qed.

Arguments mem_join_None3 [m1] [m2] [m].

Lemma mem_join_Some1 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m1 p = Noninit ->
  m2 p = Noperm /\ m p = Noninit.
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
  split; congruence.
Qed.

Lemma mem_join_Some2 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m2 p = Noninit ->
  m1 p = Noperm /\ m p = Noninit.
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; 
  split; congruence.
Qed.

Lemma mem_join_Some3 : forall m1 m2 m p n,
  mem_join m1 m2 m ->
  m1 p = value n ->
  m2 p = Noperm /\ m p = value n.
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]]; 
  split; congruence.
Qed.

Lemma mem_join_Some4 : forall m1 m2 m p n,
  mem_join m1 m2 m ->
  m2 p = value n ->
  m1 p = Noperm /\ m p = value n.
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]]; 
  split; congruence.
Qed.

Lemma mem_join_Some6 : forall m1 m2 m p n,
  mem_join m1 m2 m ->
  m p = value n ->
  (m1 p = value n /\ m2 p = Noperm) \/ (m1 p = Noperm /\ m2 p = value n).
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]]; try congruence.
  - right. split; congruence.
  - left. split; congruence.
Qed.

Lemma mem_join_Some5 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m p = Noninit ->
  (m1 p = Noninit /\ m2 p = Noperm) \/ (m1 p = Noperm /\ m2 p = Noninit).
Proof.
  intros. unfold mem_join in H.
  destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]]; try congruence.
  - right. split; congruence.
  - left. split; congruence.
Qed.

Lemma mem_join_update1 : forall m1 m1' m2 m m' p n0,
  mem_join m1 m2 m ->
  m1 p = value n0 ->
  (forall p', p' <> p -> m1 p' = m1' p') ->
  m' p = m1' p ->
  (forall p', p' <> p -> m p' = m' p') ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join. intros.
  addr_destruct p0 p.
  - subst. pose proof (mem_join_Some3 _ _ _ _ _ H H0). destruct H4.
    destruct (m1' p).
    + left. tauto.
    + right. right. left. tauto.
    + do 4 right. exists b. tauto.
  - specialize (H1 _ E). specialize (H3 _ E).
    destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]] ;
    destruct (H p0) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]] ; try congruence;
    try (rewrite H1 in H7; rewrite H3 in H9 ; tauto).
    + do 3 right. left. exists n'. repeat split; congruence.
    + do 4 right. exists n'. repeat split; congruence.
Qed.

Lemma mem_join_update2 : forall m1 m1' m2 m m' p,
  mem_join m1 m2 m ->
  m1 p = Noninit ->
  (forall p', p' <> p -> m1 p' = m1' p') ->
  m' p = m1' p ->
  (forall p', p' <> p -> m p' = m' p') ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join. intros.
  addr_destruct p0 p.
  - subst. pose proof (mem_join_Some1 _ _ _ _  H H0). destruct H4.
    destruct (m1' p).
    + left. tauto.
    + right. right. left. tauto.
    + do 4 right. exists b. tauto.
  - specialize (H1 _ E). specialize (H3 _ E).
    destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]] ;
    destruct (H p0) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]] ; try congruence;
    try (rewrite H1 in H7; rewrite H3 in H9 ; tauto).
    + do 3 right. left. exists n'. repeat split; congruence.
    + do 4 right. exists n'. repeat split; congruence.
Qed.

Lemma mem_join_update_None1 : forall m1 m1' m2 m m' p,
  mem_join m1 m2 m ->
  m p = Noperm ->
  (forall p', p' <> p -> m1 p' = m1' p') ->
  m' p = m1' p ->
  (forall p', p' <> p -> m p' = m' p') ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join. intros.
  addr_destruct p0 p.
  - subst. pose proof (mem_join_None3 _ H H0). destruct H4.
    destruct (m1' p) ; try tauto.
    do 4 right. exists b ; tauto.
  - specialize (H1 _ E). specialize (H3 _ E).
    destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]] ;
    destruct (H p0) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n' [? [? ?]]] | [n' [? [? ?]]] ]]]] ; try congruence;
    try (rewrite H1 in H7; rewrite H3 in H9 ; tauto).
    + do 3 right. left. exists n'. repeat split; congruence.
    + do 4 right. exists n'. repeat split; congruence.
Qed.

Lemma mem_join_update_list : forall m1 m1' m2 m m' ps,
  mem_join m1 m2 m ->
  (forall p, In p ps -> m p = Noperm) ->
  (forall p, In p ps -> m1' p = m' p) ->
  (forall p, ~ In p ps -> m1 p = m1' p) ->
  (forall p, ~ In p ps -> m p = m' p) ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join in *. intros p.
  destruct (in_dec addr_dec p ps) as [HIN | HIN].
  - specialize (H0 p HIN). specialize (H1 p HIN).
    destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]];
    try congruence.
    rewrite H5. rewrite H1.
    destruct (m' p) ; try tauto.
    do 4 right. exists b. tauto.
  - specialize (H2 p HIN). specialize (H3 p HIN).
    destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; rewrite H2 in H4; rewrite H3 in H6;
    try tauto.
    + do 3 right. left. exists n. tauto.
    + do 4 right. exists n. tauto.
Qed.

Lemma mem_join_update_range : forall m1 m1' m2 m m' p1 p2,
  mem_join m1 m2 m ->
  (forall p, p >= p1 -> p < p2 -> m p = Noperm) ->
  (forall p, p >= p1 -> p < p2 -> m1' p = m' p) ->
  (forall p, (p < p1 \/ p >= p2) -> m1 p = m1' p) ->
  (forall p, (p < p1 \/ p >= p2) -> m p = m' p) ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join in *. intros p.
  assert ((p >= p1 /\ p < p2) \/ (p < p1 \/ p >= p2)) as HR by lia.
  destruct HR as [ [HR1 HR2] | HR].
  - specialize (H0 p HR1 HR2). specialize (H1 p HR1 HR2).
    destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]];
    try congruence.
    rewrite H5. rewrite H1.
    destruct (m' p) ; try tauto.
    do 4 right. exists b. tauto.
  - specialize (H2 p HR). specialize (H3 p HR).
    destruct (H p) as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]]; rewrite H2 in H4; rewrite H3 in H6;
    try tauto.
    + do 3 right. left. exists n. tauto.
    + do 4 right. exists n. tauto.
Qed.

Lemma mem_join_incl_l : forall m1 m2 m,
  mem_join m1 m2 m ->
  mem_incl m1 m.
Proof.
  unfold mem_join, mem_incl. intros.
  specialize (H p).
  destruct H as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]].
  all: try tauto; congruence.
Qed.

Lemma mem_join_incl_r : forall m1 m2 m,
  mem_join m1 m2 m ->
  mem_incl m2 m.
Proof.
  unfold mem_join, mem_incl. intros.
  specialize (H p).
  destruct H as [ [ ? [? ?]] | [ [ ? [ ? ? ]] | [ [ ? [ ? ? ]] | [ [n [? [? ?]]] | [n [? [? ?]]] ]]]];
  try tauto; congruence.
Qed.

Lemma mem_update_N_in : forall m p v n p',
  p' >= p ->
  p' < p + n ->
  mem_update_N m p v n p' = value v.
Proof.
  unfold mem_update_N, Z_seq.
  intros. 
  destruct (Z_lt_ge_dec n 0) ; simpl in * ; try lia.
  rewrite <- (Z2Nat.id n) in H0 ; try lia.  clear g.
  set (n0 := Z.to_nat n) in *.
  clearbody n0. clear n. rename n0 into n.
  generalize dependent p.
  induction n; intros; simpl in * ; try lia.
  unfold mem_byte_update. addr_destruct p' p; auto.
  apply IHn; lia.
Qed.

Lemma mem_update_N_notin : forall m p v n p',
  p' < p \/ p' >= p + n ->
  mem_update_N m p v n p' = m p'.
Proof.
  unfold mem_update_N, Z_seq.
  intros. 
  destruct (Z_lt_ge_dec n 0).
  - replace (Z.to_nat n) with O by lia.
    simpl. reflexivity. 
  - rewrite <- (Z2Nat.id n) in H ; try lia.  clear g.
    set (n0 := Z.to_nat n) in *.
    clearbody n0. clear n. rename n0 into n.
    generalize dependent p.
    induction n; intros; simpl in * ; try auto.
    unfold mem_byte_update. addr_destruct p' p; auto.
    + lia.
    + apply IHn; lia.
Qed.

Ltac my_destruct H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | mem => let m := fresh "m" in destruct H as [m H];my_destruct H
              | addr -> mem_var => let m := fresh "m" in destruct H as [m H];my_destruct H
              | Z => let z := fresh "z" in destruct H as [z H];my_destruct H
              | _ => destruct H as [? H];my_destruct H
              end
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              my_destruct H;
              my_destruct H0
  | _ \/ _ => destruct H as [H | H];
              my_destruct H
  | _ => (discriminate || contradiction  || idtac)
  end.

Lemma single_mem_get_eq : forall x v, (single_byte_mem x v) x = value v.
Proof. unfold single_byte_mem;intros. rewrite addr_eqb_refl. reflexivity. Qed.

Lemma single_mem_get_neq : forall x v y,  x <> y -> (single_byte_mem x v) y <> value v.
Proof. unfold single_byte_mem;intros.
    destruct (addr_eqb y x) eqn:?;auto.
    rewrite addr_eqb_eq in Heqb.
    congruence. congruence. Qed.

Lemma mem_join_emp : mem_join empty_mem empty_mem empty_mem.
Proof.  cbv. auto. Qed.

Lemma mem_empty_IS_empty_mem' : forall m, mem_empty m -> m = empty_mem.
Proof. intros. apply fun_ext1;eapply mem_empty_IS_empty_mem;eauto. Qed.

Lemma mem_join_emp_l: forall m m1, mem_join empty_mem m m1 -> m1 = m.
Proof.
  unfold mem_join, empty_mem;intros.
  apply fun_ext1. intros.
  specialize (H a).
  destruct (m1 a) eqn:? ; destruct (m a) eqn:?;auto; my_destruct H.
  congruence.
Qed.

Lemma mem_join_emp_r: forall m m1, mem_join m empty_mem m1 -> m1 = m.
Proof.
  unfold mem_join, empty_mem;intros.
  apply fun_ext1. intros.
  specialize (H a).
  destruct (m1 a) eqn:? ; destruct (m a) eqn:?;auto; my_destruct H.
  congruence.
Qed.

Lemma mem_join_eq:
  forall m1  m2 m m' : addr -> mem_var,
  mem_join m1 m2 m -> mem_join m1 m2 m' -> m = m'.
Proof.
  unfold mem_join;intros.
  apply fun_ext1. intros.
  specialize (H a).
  specialize (H0 a).
  destruct (m1 a) eqn:? ; destruct (m2 a) eqn:?;auto; my_destruct H;my_destruct H0.
  all: congruence.
Qed.

Arguments mem_join_eq [m1] [m2] [m] [m'].


Lemma mem_join_eq_l:
  forall m1 m1' m2 m : addr -> mem_var,
  mem_join m1 m2 m -> mem_join m1' m2 m -> m1 = m1'.
Proof.
  intros.
  apply fun_ext1.
  eapply (mem_join_eq_inv1 m1 m1' m2 m2 m m);eauto.
  apply f_eq_refl.
  apply f_eq_refl.
Qed.

Arguments mem_join_eq_l [m1] [m1'] [m2] [m].

Lemma mem_join_eq_r:
  forall m1 m2 m2' m : addr -> mem_var,
  mem_join m1 m2 m -> mem_join m1 m2' m -> m2 = m2'.
Proof.
  intros.
  apply fun_ext1.
  eapply (mem_join_eq_inv1 m2 m2' m1 m1 m m);eauto.
  apply f_eq_refl.
  apply f_eq_refl.
  apply mem_join_comm;auto.
  apply mem_join_comm;auto.
Qed.

Arguments mem_join_eq_r [m1] [m2] [m2'] [m].

Lemma mem_join_Some_eq_l : forall m1 m2 m3 x v1 v2,
  mem_join m1 m2 m3 ->
  m1 x = value v1 ->
  m3 x = value v2 ->
  v2 = v1.
Proof.
  unfold mem_join; intros.
  specialize (H x).
  my_destruct H;congruence.
Qed.

Arguments mem_join_Some_eq_l [m1] [m2] [m3] [x] [v1] [v2].

Lemma mem_join_Some_eq_r : forall m1 m2 m3 x v1 v2,
  mem_join m1 m2 m3 ->
  m2 x = value v1 ->
  m3 x = value v2 ->
  v2 = v1.
Proof.
  unfold mem_join; intros.
  specialize (H x).
  my_destruct H;congruence.
Qed.

Arguments mem_join_Some_eq_r [m1] [m2] [m3] [x] [v1] [v2].

Lemma mem_join_None: forall m1 m2 m3 x,
  mem_join m1 m2 m3 ->
  m3 x = Noperm ->
  m1 x = Noperm /\ m2 x = Noperm.
Proof.
  unfold mem_join;intros.
  specialize (H x).
  my_destruct H;try congruence.
  tauto.
Qed.

Arguments mem_join_None [m1] [m2] [m3] [x].

Lemma mem_update_eq : forall m x v, (mem_byte_update m x v) x = value v. 
Proof.
  unfold mem_byte_update;intros.
  rewrite addr_eqb_refl. auto. 
Qed.

Lemma mem_update_neq : forall m x v x', x' <> x -> (mem_byte_update m x v) x' = m x'. 
Proof.
  unfold mem_byte_update;intros.
  apply addr_eqb_neq in H.
  rewrite H.
  auto.
Qed.

Lemma mem_update_single_eq : forall x v v0, (mem_byte_update (single_byte_mem x v) x v0) = single_byte_mem x v0. 
Proof.
  unfold mem_byte_update, single_byte_mem;intros.
  apply fun_ext1. intro.
  destruct (addr_eqb a x);auto.
Qed.
  
Lemma mem_update_unfold : forall m m' x v, m' x = value v -> (forall p', p' <> x -> m p' = m' p') -> m' = mem_byte_update m x v.
Proof.
  unfold mem_byte_update;intros.
  apply fun_ext1.
  intro.
  destruct (addr_eqb a x) eqn:?.
  - apply addr_eqb_eq in Heqb. subst. auto.
  - apply addr_eqb_neq in Heqb. erewrite H0;eauto.
Qed.

Lemma mem_join_mem_update_l : forall m1 m2 m3 x v, mem_join m1 m2 m3 -> m1 x <> Noperm -> mem_join (mem_byte_update m1 x v) m2 (mem_byte_update m3 x v).
Proof.
  unfold mem_join,mem_byte_update;intros.
  specialize (H p).
  my_destruct H ; addr_destruct p x ; subst ; try tauto.
  - do 4 right. exists v. tauto. 
  - do 3 right. left. exists x0. tauto.
  - do 4 right. exists v. tauto.
  - do 4 right. exists x0. tauto.
Qed. 

Lemma mem_join_mem_update_l' : forall m1 m2 m3 x v, mem_join m1 m2 m3 -> m3 x= Noperm -> mem_join (mem_byte_update m1 x v) m2 (mem_byte_update m3 x v).
Proof.
  unfold mem_join,mem_byte_update;intros.
  specialize (H p).
  my_destruct H ; addr_destruct p x ; subst ; try tauto ; try congruence.
  - do 4 right. exists v. tauto. 
  - do 3 right. left. exists x0. tauto.
  - do 4 right. exists x0. tauto.
Qed. 

Lemma mem_join_single_mem_update_l : forall m p v, m p = Noperm -> mem_join m (single_byte_mem p v) (mem_byte_update m p v).
Proof.
  unfold mem_join, single_byte_mem, mem_byte_update;intros.
  addr_destruct p0 p.
  - subst p. do 3 right. left. exists v. tauto.
  - destruct (m p0) eqn: ? ; try tauto.
    do 4 right. exists b. tauto.
Qed. 

Lemma mem_join_single_mem_remove_l : forall m p v m1,  mem_join m (single_byte_mem p v) m1 -> m = (mem_remove m1 p ).
Proof.
  unfold mem_join, single_byte_mem, mem_remove;intros.
  apply fun_ext1;intros.
  specialize ( H a).
  destruct (addr_eqb a p) eqn:?.
  -  apply addr_eqb_eq in Heqb.
  subst p.
  my_destruct H;auto.
  - apply addr_eqb_neq in Heqb.
    my_destruct H;try congruence.
Qed. 

Arguments  mem_join_single_mem_remove_l [m] [p] [v] [m1].

Lemma mem_remove_eq : forall m x, mem_remove m x x = Noperm.
Proof.
  unfold mem_remove;intros. rewrite addr_eqb_refl. auto. Qed.

Lemma mem_remove_neq : forall m x x', x' <> x -> mem_remove m x x' = m x'.
Proof.
  unfold mem_remove;intros.
  apply addr_eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.

Lemma mem_remove_unfold : forall m m' x , m' x = Noperm -> (forall p', p' <> x -> m p' = m' p') -> m' = mem_remove m x.
Proof.
  unfold mem_remove;intros.
  apply fun_ext1.
  intro.
  destruct (addr_eqb a x) eqn:?.
  - apply addr_eqb_eq in Heqb. subst. auto.
  - apply addr_eqb_neq in Heqb. erewrite H0;eauto.
Qed.

Lemma mem_join_mem_remove_l : forall m1 m2 m3 x, mem_join m1 m2 m3 -> m1 x <> Noperm -> mem_join (mem_remove m1 x) m2 (mem_remove m3 x).
Proof.
  unfold mem_join,mem_remove;intros.
  specialize (H p).
  my_destruct H ; addr_destruct p x ; subst; simpl in * ; try tauto.
  - do 3 right. left. exists x0. tauto.
  - do 4 right. exists x0. tauto.
Qed. 

Definition disjoint (m1 m2:mem) :=
  forall (x : addr),
  match m1 x, m2 x with
    |  _ , Noperm => True
    |  Noperm , _ => True
    |  _, _ => False
  end.

Definition merge (m1 m2:mem)  : mem :=
  fun (a : addr) =>
  match (m1 a, m2 a) with
  | (value b1, _) => value b1
  | (Noninit, value b2) => value b2
  | (Noninit, _) => Noninit
  | (Noperm, _) => m2 a
  end.

Definition minus (m1 m2: mem) : mem := 
  fun (a : addr) =>
  match (m1 a, m2 a) with
  | (value b1, Noperm) => value b1
  | (value b1, _) => Noperm
  | (Noninit, Noperm) => Noninit
  | (Noninit, _) => Noperm
  | (Noperm, _) => Noperm
  end.

Definition sub (m1 m2: mem) : Prop := 
  forall x, m1 x <> Noperm -> m2 x = m1 x.

Lemma mem_get_single_mem_sub : forall m x v, m x = value v -> sub (single_byte_mem x v) m.
Proof.
  unfold sub,single_byte_mem;intros.
  addr_destruct x0 x ; subst ; try tauto.
Qed.

Arguments mem_get_single_mem_sub [m] [x] [v].

Lemma disjoint_comm : forall m1 m2, disjoint m1 m2 -> disjoint m2 m1.
Proof.    
  unfold disjoint ; intros.
  specialize (H x).
  destruct (m1 x) , (m2 x) ; try tauto. 
Qed.

Arguments disjoint_comm [m1] [m2].

Lemma disjoint_merge_mem_join : forall m1 m2, disjoint m1 m2 -> mem_join m1 m2 (merge m1 m2).
Proof.
  unfold disjoint, mem_join, merge;intros.
  specialize (H p).
  destruct (m1 p), (m2 p);try tauto.
  do 3 right;left. eexists;eauto.
  do 4 right. eexists;eauto.
Qed. 

Arguments disjoint_merge_mem_join [m1] [m2].

Lemma sub_minus_mem_join : forall m1 m2, sub m1 m2 -> mem_join m1 (minus m2 m1) m2.
Proof.
  unfold sub, mem_join, minus;intros.
  specialize (H p).
  destruct (m1 p), (m2 p) ; try tauto.
  + do 3 right. left. eexists; eauto.
  + assert (Noninit <> Noperm) by congruence.
    specialize (H H0). congruence.
  + assert (Noninit <> Noperm) by congruence.
    specialize (H H0). congruence.
  + assert (value b <> Noperm) by congruence.
    specialize (H H0). congruence.
  + assert (value b <> Noperm) by congruence.
    specialize (H H0). congruence.
  + assert (value b <> Noperm) by congruence.
    specialize (H H0). do 4 right. exists b. tauto.
Qed.

Arguments sub_minus_mem_join [m1] [m2].

Lemma mem_join_sub_l : forall m1 m2 m,  mem_join m1 m2 m -> sub m1 m.
Proof.
  unfold sub, mem_join;intros.
  specialize (H x).
  my_destruct H;congruence.
Qed.

Arguments mem_join_sub_l [m1] [m2] [m].

Lemma sub_merge_sub : forall m1 m2 m,  sub m1 m -> sub m2 m -> sub (merge m1 m2) m.
Proof.
  unfold sub, merge;intros.
  specialize (H x).
  specialize (H0  x).
  destruct (m1 x), (m2 x); try tauto.
Qed.

Arguments mem_join_sub_l [m1] [m2] [m].

Lemma mem_join_disjoint_l_ex : forall m1 m2 m3 m4 m,
  disjoint m1 m3 -> mem_join m1 m2 m -> mem_join m3 m4 m -> exists m5 m6, mem_join m1 m3 m5 /\ mem_join m5 m6 m.
Proof.
  intros.
  exists (merge m1 m3).
  exists (minus m (merge m1 m3)).
  pose proof (disjoint_merge_mem_join H).
  split;auto.
  apply sub_minus_mem_join.
  apply sub_merge_sub.
  eapply mem_join_sub_l;eauto.
  eapply mem_join_sub_l;eauto.
Qed.

Lemma mem_join_disjoint : forall m1 m2 m3, mem_join m1 m2 m3 -> disjoint m1 m2.
Proof.
  unfold mem_join, disjoint;intros.
  specialize (H x).
  my_destruct H;try rewrite H;try rewrite H0; try rewrite H1; auto. 
Qed.

Arguments mem_join_disjoint [m1] [m2] [m3].

Lemma disjoint_mem_join_l : forall m1 m2 m3 m4, disjoint m1 m4 -> mem_join m2 m3 m4 -> disjoint m1 m2.
Proof.
  unfold mem_join, disjoint;intros.
  specialize (H0 x).
  specialize (H x).
  my_destruct H0 ; try rewrite H0 in * ; try rewrite H2 in * ; auto;
  destruct (m1 x) ; tauto. 
Qed.

Arguments disjoint_mem_join_l [m1] [m2] [m3] [m4].

Lemma disjoint_mem_join_r : forall m1 m2 m3 m4, disjoint m1 m4 -> mem_join m2 m3 m4 -> disjoint m1 m3.
Proof.
  unfold mem_join, disjoint;intros.
  specialize (H0 x).
  specialize (H x).
  my_destruct H0 ; try rewrite H1 in * ; try rewrite H2 in * ; auto;
  destruct (m1 x) ; tauto. 
Qed.

Arguments disjoint_mem_join_r [m1] [m2] [m3] [m4].

Lemma mem_join_eqmerge : forall m1 m2 m3, mem_join m1 m2 m3 -> m3 = merge m1 m2.
Proof.
  intros.
  eapply mem_join_eq;eauto.
  eapply disjoint_merge_mem_join.
  eapply mem_join_disjoint;eauto.
Qed.

Arguments mem_join_eqmerge [m1] [m2] [m3].

Lemma mem_join_merge_assoc_l : forall m1 m2 m3 m4, disjoint m1 m2 -> mem_join (merge m1 m2) m3 m4 -> mem_join m1 (merge m2 m3) m4.
Proof.
  intros.
  unfold mem_join , merge, disjoint in * ; intros.
  specialize (H0 p).
  specialize (H p).
  my_destruct H0 ; destruct (m1 p) , (m2 p) ; try rewrite H1 ; try rewrite H2 ; try congruence ; try tauto.
  - do 3 right. left. eexists ; eauto.
  - do 3 right. left. eexists ; eauto.
  - do 4 right. eexists ; eauto.
Qed.

Arguments mem_join_merge_assoc_l [m1] [m2] [m3] [m4].

Lemma mem_join_merge_assoc_r : forall m1 m2 m3 m4, disjoint m2 m3 -> mem_join m1 (merge m2 m3) m4 -> mem_join (merge m1 m2) m3 m4.
Proof.
  intros.
  unfold mem_join , merge, disjoint in * ; intros.
  specialize (H0 p).
  specialize (H p).
  my_destruct H0 ; destruct (m2 p) , (m3 p) ; try rewrite H0 in * ; try rewrite H1 ; try rewrite H2 ; try congruence ; try tauto.
  - do 3 right. left. eexists ; eauto.
  - do 4 right. eexists ; eauto.
  - do 4 right. eexists ; eauto.
Qed.

Arguments mem_join_merge_assoc_r [m1] [m2] [m3] [m4].

Ltac solve_empmem :=
  repeat match goal with
  | H: mem_empty ?m |- _ => apply mem_empty_IS_empty_mem' in H; subst m
  | H: mem_join _ empty_mem _ |- _ => apply mem_join_emp_r in H;subst 
  | H: mem_join empty_mem _ _ |- _ => apply mem_join_emp_l in H;subst
  | |- mem_join _ _ empty_mem => apply mem_join_emp
  | |- mem_join ?x _ ?x => apply mem_join_emp2
  | |- mem_join _ ?x ?x => apply mem_join_emp1
  | |- mem_join _ empty_mem ?x => apply mem_join_emp2
  | |- mem_join empty_mem _ ?x => apply mem_join_emp1
  | |- mem_empty _ => apply empty_mem_empty 
  end.