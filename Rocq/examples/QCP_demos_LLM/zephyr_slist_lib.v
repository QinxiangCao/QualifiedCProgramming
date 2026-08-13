(* ==========================================================================
   Separation logic library for Zephyr's intrusive singly linked list
   (sys_slist_t / sys_snode_t).

   Design influence: Hermes & Krebbers, ITP 2024 (deque section). See
   documents/zephyr_slist_predicate_plan.md and ..._research.md.

   Two layers:

   - Layer A — spine (sections 1–4): owns only the `next` field of each
     sys_snode_t, plus the two fields of the sys_slist_t wrapper.
     Parameterised by `ns : list addr`, the list of NODE addresses.
     Head and tail of the wrapper struct are predicate-internal, not
     parameters of `slist_spine`.

   - Layer B — payload (after Layer A's definitions): the per-container
     `body : addr -> A -> Assertion` predicate is supplied by the
     client; Layer B glues the spine with an `iter_sepcon` over a
     `zip_body`-built list of payload assertions. `body` describes
     everything in the container except the `next` field.

   The remaining sections (5–8) are lemmas about Layer A.
   ========================================================================== *)

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

(* --------------------------------------------------------------------------
   1. Field cells
   
  &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt.

  &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> h.

  &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> t.
   -------------------------------------------------------------------------- *)

(* --------------------------------------------------------------------------
   2. Closed node chain: snode_listrep h ns
      Owns the `next` field of every node address in `ns`. The chain
      starts at `h`, visits exactly the addresses in `ns` in order, and
      ends at NULL.
   -------------------------------------------------------------------------- *)

Fixpoint snode_listrep (h : addr) (ns : list addr) : Assertion :=
  match ns with
  | nil      => “ h = NULL ” && emp
  | n :: ns' => “ h = n /\ n <> NULL ” &&
                EX nxt : addr,
                  &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt **
                  snode_listrep nxt ns'
  end.

(* --------------------------------------------------------------------------
   3. Open node-chain segment: snode_chain from to ns
      Owns `next` fields of every node in `ns`. The chain runs `from`
      to `to`; `to` itself is NOT owned. Used for in-place iteration
      and segment-style reasoning.
   -------------------------------------------------------------------------- *)

Fixpoint snode_chain (from to : addr) (ns : list addr) : Assertion :=
  match ns with
  | nil      => “ from = to ” && emp
  | n :: ns' => “ from = n /\ n <> NULL ” &&
                EX nxt : addr,
                  &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt **
                  snode_chain nxt to ns'
  end.

(* --------------------------------------------------------------------------
   4. The wrapper-level spine predicate.
   -------------------------------------------------------------------------- *)

Definition slist_last_default (ns : list addr) : addr :=
  match ns with
  | nil => NULL
  | _   => last ns NULL
  end.

Definition slist_head_default (ns : list addr) : addr :=
  match ns with
  | nil      => NULL
  | n :: _   => n
  end.

Definition slist_spine (l : addr) (ns : list addr) : Assertion :=
  EX h t : addr,
    “ h = slist_head_default ns /\ t = slist_last_default ns ” &&
    &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> h **
    &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> t **
    snode_listrep h ns.

(* --------------------------------------------------------------------------
   Layer B: payload / container ownership.

   Design: spine and payload table together describe the full memory
   layout of the slist. `ns` is the ordered list of node addresses;
   `m : addr -> option A` is the partial map sending each node address
   to its logical payload. The two are kept in 1-1 correspondence via
   the iff:

       forall n, In n ns <-> exists v, m n = Some v.

   `body : addr -> A -> Assertion` is the per-type predicate describing
   the "rest of the container" at node address `n` carrying logical
   value `v` — i.e. everything *except* the `sys_snode_t.next` field
   (which Layer A owns).
   -------------------------------------------------------------------------- *)

(* --------------------------------------------------------------------------
   Layer B: full memory layout of a Zephyr slist of zephyr_slist_items.

       struct zephyr_slist_item {
           sys_snode_t node;     /* at offset 0 — node address aliases
                                    container address */
           int         value;
       };

   The `value` field of each container is owned per node via
   `store_map`. With `node` at offset 0 the container address equals
   the node address, so the field access goes through `n` directly.

   `zephyr_slist_of l ns m`: spine list of node addresses `ns` plus
   payload table `m`, in 1-1 correspondence
   (forall n, In n ns <-> exists v, m n = Some v).

   `zephyr_slist l m`: client-facing form, hides `ns`.
   -------------------------------------------------------------------------- *)

Definition zephyr_slist_of (l : addr) (ns : list addr)
                           (m : addr -> option Z) : Assertion :=
  “ forall n, In n ns <-> exists v, m n = Some v ” &&
  slist_spine l ns **
  store_map (fun n v => &(n # "zephyr_slist_item" ->ₛ "value") # Int |-> v) m.

Definition zephyr_slist (l : addr) (m : addr -> option Z) : Assertion :=
  EX ns : list addr, zephyr_slist_of l ns m.

(* --------------------------------------------------------------------------
   5. Basic lemmas about snode_listrep
   -------------------------------------------------------------------------- *)

Lemma snode_listrep_zero : forall h ns,
  h = NULL ->
  snode_listrep h ns |-- “ ns = nil ” && emp.
Proof.
  intros h ns Hh.
  destruct ns as [| n ns'].
  - simpl.
    split_pure_spatial.
    + Intros_p Hnil.
      cancel.
    + dump_pre_spatial.
      reflexivity.
  - simpl.
    subst h.
    Intros nxt.
    destruct H as [Hheq Hne].
    subst n.
    contradiction.
Qed.

Lemma snode_listrep_nonzero : forall h ns,
  h <> NULL ->
  snode_listrep h ns |--
    EX n ns' nxt,
      “ ns = n :: ns' /\ h = n ” &&
      &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt **
      snode_listrep nxt ns'.
Proof.
  intros h ns Hh.
  destruct ns as [| n ns'].
  - simpl.
    Intros_p Hnil.
    contradiction.
  - simpl.
    Intros nxt.
    destruct H as [Hhn Hne].
    Exists n ns' nxt.
    split_pure_spatial.
    + cancel (&(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt).
      cancel (snode_listrep nxt ns').
    + dump_pre_spatial.
      split; [reflexivity | exact Hhn].
Qed.

(* Push a fresh node at the head of a closed chain. *)
Lemma snode_listrep_cons : forall n nxt ns,
  n <> NULL ->
  &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt ** snode_listrep nxt ns |--
  snode_listrep n (n :: ns).
Proof.
  intros n nxt ns Hn.
  simpl.
  Exists nxt.
  split_pure_spatial.
  - cancel (&(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt).
    cancel (snode_listrep nxt ns).
  - dump_pre_spatial.
    split; [reflexivity | exact Hn].
Qed.

(* --------------------------------------------------------------------------
   6. Basic lemmas about snode_chain (open segment)
   -------------------------------------------------------------------------- *)

Lemma snode_chain_nil : forall p,
  snode_chain p p [] |-- emp.
Proof.
  intros p. simpl.
  Intros_p Hpp. cancel.
Qed.

Lemma snode_chain_emp_to_nil : forall p,
  emp |-- snode_chain p p [].
Proof.
  intros p. simpl.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma snode_chain_singleton : forall n nxt,
  n <> NULL ->
  &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt |-- snode_chain n nxt [n].
Proof.
  intros n nxt Hn.
  change (snode_chain n nxt [n]) with
    (“ n = n /\ n <> NULL ” &&
     (EX x : addr, &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> x **
       snode_chain x nxt [])).
  Exists nxt.
  split_pure_spatial.
  - cancel (&(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt).
    apply snode_chain_emp_to_nil.
  - dump_pre_spatial.
    split; [reflexivity | exact Hn].
Qed.

(* Concatenation: glue two segments. *)
Lemma snode_chain_app : forall ns1 ns2 p q r,
  snode_chain p q ns1 ** snode_chain q r ns2 |--
  snode_chain p r (ns1 ++ ns2).
Proof.
  intros ns1; revert ns1.
  induction ns1 as [| n ns1' IH]; intros ns2 p q r.
  - simpl.
    Intros_p Hpq. subst q.
    cancel.
  - simpl.
    Intros nxt.
    destruct H as [Hpn Hne].
    Exists nxt.
    split_pure_spatial.
    + cancel (&(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt).
      apply (IH ns2 nxt q r).
    + dump_pre_spatial.
      split; [exact Hpn | exact Hne].
Qed.

(* Snoc lemma: append a single node at the tail of a chain. *)
Lemma snode_chain_snoc : forall ns p q r,
  q <> NULL ->
  snode_chain p q ns ** &(q # "sys_snode_t" ->ₛ "next") # Ptr |-> r |--
  snode_chain p r (ns ++ [q]).
Proof.
  intros ns p q r Hq.
  sep_apply (snode_chain_singleton q r Hq).
  sep_apply (snode_chain_app ns [q] p q r).
  cancel.
Qed.

(* Bridge: a chain ending at NULL is a closed listrep. *)
Lemma snode_chain_null_listrep : forall ns h,
  snode_chain h NULL ns |-- snode_listrep h ns.
Proof.
  induction ns as [| n ns' IH]; intros h.
  - simpl.
    Intros_p Hh. subst h.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - simpl.
    Intros nxt.
    destruct H as [Hhn Hne].
    Exists nxt.
    split_pure_spatial.
    + cancel (&(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt).
      apply IH.
    + dump_pre_spatial.
      split; [exact Hhn | exact Hne].
Qed.

(* Bridge other direction: a closed listrep is a chain ending at NULL. *)
Lemma snode_listrep_to_chain_null : forall ns h,
  snode_listrep h ns |-- snode_chain h NULL ns.
Proof.
  induction ns as [| n ns' IH]; intros h.
  - simpl.
    Intros_p Hh. subst h.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - simpl.
    Intros nxt.
    destruct H as [Hhn Hne].
    Exists nxt.
    split_pure_spatial.
    + cancel (&(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt).
      apply IH.
    + dump_pre_spatial.
      split; [exact Hhn | exact Hne].
Qed.

(* Split a closed chain at an arbitrary position: the prefix becomes an
   open chain, the suffix remains a closed listrep. *)
Lemma snode_listrep_app : forall ns1 ns2 h,
  snode_listrep h (ns1 ++ ns2) |--
  EX m : addr, snode_chain h m ns1 ** snode_listrep m ns2.
Proof.
  induction ns1 as [| n ns1' IH]; intros ns2 h.
  - simpl.
    Exists h.
    cancel (snode_listrep h ns2).
    apply snode_chain_emp_to_nil.
  - simpl.
    Intros nxt.
    destruct H as [Hhn Hne].
    sep_apply (IH ns2 nxt).
    Intros m.
    Exists m nxt.
    split_pure_spatial.
    + cancel (&(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt).
      cancel.
    + dump_pre_spatial.
      split; [exact Hhn | exact Hne].
Qed.

(* --------------------------------------------------------------------------
   7. Lemmas about slist_spine

      These are the "API-facing" lemmas: they describe what the wrapper
      predicate looks like in each canonical situation, and what
      mutations preserve it.
   -------------------------------------------------------------------------- *)

Lemma slist_spine_nil : forall l,
  slist_spine l [] |--
    &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> NULL ** &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> NULL.
Proof.
  intros l.
  unfold slist_spine.
  Intros h t.
  destruct H as [Hh Ht].
  unfold slist_head_default in Hh. subst h.
  unfold slist_last_default in Ht. subst t.
  simpl.
  Intros_p Hh'.
  cancel.
Qed.

Lemma slist_spine_nil_intro : forall l,
  &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> NULL ** &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> NULL |--
  slist_spine l [].
Proof.
  intros l.
  unfold slist_spine.
  Exists NULL NULL.
  split_pure_spatial.
  - cancel (&(l # "sys_slist_t" ->ₛ "head") # Ptr |-> NULL).
    cancel (&(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> NULL).
    simpl.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. reflexivity.
  - repeat split_pures; dump_pre_spatial; auto.
Qed.

Lemma slist_spine_singleton_intro : forall l n,
  n <> NULL ->
  &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> n ** &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> n ** &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> NULL |--
  slist_spine l [n].
Proof.
  intros l n Hn.
  unfold slist_spine.
  Exists n n.
  simpl.
  Exists NULL.
  split_pure_spatial.
  - cancel (&(l # "sys_slist_t" ->ₛ "head") # Ptr |-> n).
    cancel (&(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> n).
    cancel.
  - repeat split_pures; dump_pre_spatial; auto.
Qed.

(* Prepend at head: state matches `sys_slist_prepend`'s effect. *)
Lemma slist_spine_prepend : forall l n ns,
  n <> NULL ->
  &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> n **
  &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> (slist_last_default (n :: ns)) **
  &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> (slist_head_default ns) **
  snode_listrep (slist_head_default ns) ns |--
  slist_spine l (n :: ns).
Proof.
  intros l n ns Hn.
  unfold slist_spine.
  Exists n (slist_last_default (n :: ns)).
  simpl snode_listrep.
  Exists (slist_head_default ns).
  split_pure_spatial.
  - cancel (&(l # "sys_slist_t" ->ₛ "head") # Ptr |-> n).
    cancel (&(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> slist_last_default (n :: ns)).
    cancel.
  - repeat split_pures; dump_pre_spatial; auto.
Qed.

(* Pop head: dual of prepend. Strips the first node out of the spine
   and returns its `next` pointer plus the residual listrep. The
   pure connection `nxt = slist_head_default ns` falls out of
   `snode_listrep`'s case split and can be recovered downstream via
   `snode_listrep_zero` / `snode_listrep_nonzero` if a caller needs
   it explicitly. *)
Lemma slist_spine_pop_head : forall l n ns,
  slist_spine l (n :: ns) |--
    “ n <> NULL ” &&
    EX nxt : addr,
      &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> n **
      &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> (slist_last_default (n :: ns)) **
      &(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt **
      snode_listrep nxt ns.
Proof.
  intros l n ns.
  unfold slist_spine.
  Intros h t.
  destruct H as [Hh Ht]; simpl in Hh, Ht; subst h t.
  simpl snode_listrep.
  Intros nxt.
  Exists nxt.
  change (match ns with | [] => n | _ :: _ => last ns NULL end) with
    (slist_last_default (n :: ns)).
  split_pure_spatial.
  - cancel (&(l # "sys_slist_t" ->ₛ "head") # Ptr |-> n).
    cancel (&(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> slist_last_default (n :: ns)).
    cancel (&(n # "sys_snode_t" ->ₛ "next") # Ptr |-> nxt).
    cancel (snode_listrep nxt ns).
  - dump_pre_spatial.
    exact (proj2 H).
Qed.

(* Segment split via `snode_listrep_app`: exposes an intermediate
   address `m` so the prefix becomes an open chain and the suffix
   stays a closed listrep. The workhorse for in-place iteration
   specs. *)
Lemma slist_spine_listrep_split : forall l ns1 ns2,
  slist_spine l (ns1 ++ ns2) |--
    EX h m t : addr,
      “ h = slist_head_default (ns1 ++ ns2) /\
        t = slist_last_default (ns1 ++ ns2) ” &&
      &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> h **
      &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> t **
      snode_chain h m ns1 **
      snode_listrep m ns2.
Proof.
  intros l ns1 ns2.
  unfold slist_spine.
  Intros h t.
  sep_apply (snode_listrep_app ns1 ns2 h).
  Intros m.
  Exists h m t.
  split_pure_spatial.
  - cancel (&(l # "sys_slist_t" ->ₛ "head") # Ptr |-> h).
    cancel (&(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> t).
    cancel (snode_chain h m ns1).
    cancel (snode_listrep m ns2).
  - dump_pre_spatial.
    exact H.
Qed.

(* --------------------------------------------------------------------------
   8. Pure-shape consequence: distinctness.

      A chain owns each `next` field exclusively, so node addresses in
      `ns` are pairwise distinct.
   -------------------------------------------------------------------------- *)

Lemma snode_next_neq : forall p q v1 v2,
  &(p # "sys_snode_t" ->ₛ "next") # Ptr |-> v1 ** &(q # "sys_snode_t" ->ₛ "next") # Ptr |-> v2 |-- “ p <> q ”.
Proof.
  intros p q v1 v2.
  destruct (Z.eq_dec p q) as [Heq | Hne].
  - subst q.
    prop_apply (dup_store_ptr (&( p # "sys_snode_t" ->ₛ "next")) v1 v2).
    Intros_p Hfalse. contradiction.
  - dump_pre_spatial. exact Hne.
Qed.

Lemma snode_next_not_in_listrep : forall ns p v h,
  &(p # "sys_snode_t" ->ₛ "next") # Ptr |-> v ** snode_listrep h ns |-- “ ~ In p ns ”.
Proof.
  induction ns as [| n ns' IH]; intros p v h; simpl.
  - dump_pre_spatial.
    intros [].
  - Intros nxt.
    prop_apply (snode_next_neq p n v nxt). Intros.
    prop_apply (IH p v nxt). Intros.
    dump_pre_spatial.
    intros [Heq | Hin]; [apply H0; symmetry; exact Heq | apply H1; exact Hin].
Qed.

Lemma snode_listrep_distinct : forall ns h,
  snode_listrep h ns |-- “ NoDup ns ”.
Proof.
  induction ns as [| n ns' IH]; intros h; simpl.
  - dump_pre_spatial. constructor.
  - Intros nxt.
    prop_apply (snode_next_not_in_listrep ns' n nxt nxt). Intros.
    prop_apply (IH nxt). Intros.
    dump_pre_spatial.
    constructor; assumption.
Qed.

(* --------------------------------------------------------------------------
   9. Layer B lemmas.
   -------------------------------------------------------------------------- *)

(* --- Empty list. -------------------------------------------------------

   In the empty case the iff forces `m` to be everywhere None — i.e.
   the map is empty. *)

Lemma zephyr_slist_of_nil_intro : forall l m,
  (forall n, m n = None) ->
  &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> NULL **
  &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> NULL **
  store_map (fun n v => &(n # "zephyr_slist_item" ->ₛ "value") # Int |-> v) m |--
  zephyr_slist_of l [] m.
Proof.
  intros l m Hempty.
  unfold zephyr_slist_of.
  split_pure_spatial.
  - sep_apply (slist_spine_nil_intro l).
    cancel (slist_spine l []).
    cancel.
  - dump_pre_spatial.
    simpl. intros n; split;
      [contradiction
      | intros [v Hv]; rewrite Hempty in Hv; discriminate].
Qed.

Lemma zephyr_slist_of_nil : forall l m,
  zephyr_slist_of l [] m |--
  “ forall n, m n = None ” &&
  &(l # "sys_slist_t" ->ₛ "head") # Ptr |-> NULL **
  &(l # "sys_slist_t" ->ₛ "tail") # Ptr |-> NULL **
  store_map (fun n v => &(n # "zephyr_slist_item" ->ₛ "value") # Int |-> v) m.
Proof.
  intros l m.
  unfold zephyr_slist_of. Intros.
  split_pure_spatial.
  - sep_apply (slist_spine_nil l).
    cancel.
  - dump_pre_spatial.
    intros n. specialize (H n). simpl in H.
    destruct (m n) eqn:Heq;
      [exfalso; apply H; exists z; reflexivity | reflexivity].
Qed.

Lemma zephyr_slist_nil_intro : forall l m,
  zephyr_slist_of l [] m |-- zephyr_slist l m.
Proof.
  intros l m.
  unfold zephyr_slist. Exists (@nil addr). cancel.
Qed.
