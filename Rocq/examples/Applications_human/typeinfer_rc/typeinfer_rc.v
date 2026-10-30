From Coq Require Import ZArith List String Lia.
From AUXLib Require Import ListLib.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From MonadLib.MonadErr Require Import StateRelMonadErr.
From SimpleC.EE.Applications_human.typeinfer Require Export type_infer_lib sound_pv.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

From SimpleC.SL Require Export RCMap.
From Coq Require Import Logic.FunctionalExtensionality Sorting.Permutation.

(* A key denotes a physical slot, not a union member name.  In particular,
   VAR.name, ATOM.name, ARROW.from and APP.tfn share Payload0; the active
   tag below determines its points-to type.  The list contains no ownership. *)
Inductive TypeFieldSlot := RefCount | Tag | Payload0 | Payload1.
Definition TypeFieldKey := (addr * TypeFieldSlot)%type.
Definition field_key (p : addr) (s : TypeFieldSlot) : TypeFieldKey := (p,s).
Definition field_fresh (k : TypeFieldKey) (L : list TypeFieldKey) : Prop := ~ In k L.

(* Strategy scheduling marker only: L is the suffix being searched for the
   physical field (p,s). Parent markers remain while the search descends.
   True carries neither freshness evidence nor ownership: strategies derive
   field_fresh bottom-up from [] and proven head inequality before splitting.
   Tagcancel removes these markers, then forgets left-hand freshness facts;
   right-hand freshness obligations are never erased. *)
Definition field_lookup
    (p : addr) (s : TypeFieldSlot) (L : list TypeFieldKey) : Prop := True.

Definition field_slot_eq_dec : forall x y : TypeFieldSlot, {x=y}+{x<>y}.
Proof. decide equality. Defined.
Definition field_key_eq_dec : forall x y : TypeFieldKey, {x=y}+{x<>y}.
Proof. decide equality; [apply field_slot_eq_dec | apply Z.eq_dec]. Defined.
Definition field_mask (L : list TypeFieldKey) (k : TypeFieldKey)
    (P : Assertion) : Assertion :=
  if in_dec field_key_eq_dec k L then emp else P.

(* Address-only payload: tag, first payload word, second payload word.
   Tags 0/3 use the first word as an integer name; tags 1/2 use both as
   pointer addresses.  This is representation metadata, not a new TypeTree. *)
(* TypeTree 实例：tag=0 是 Atom，3 是 Var，1 是 Arrow，2 是 Apply。
   叶子的 a 是名字/编号；复合节点的 a/b 是地址，而非嵌套的 TypeTree。
   因此 RCMap 本身可以表达共享，数学树由下面的 decode_type 解释出来。 *)
Record TypeNode := Node { node_tag : Z; node_a : Z; node_b : Z }.
Definition payload_keys (p : addr) (n : TypeNode) : list TypeFieldKey :=
  match node_tag n with
  | 0 | 3 => [(p,Payload0)]
  | _ => [(p,Payload0);(p,Payload1)]
  end.
Definition node_children (n : TypeNode) : list addr :=
  if (Z.eqb (node_tag n) 1 || Z.eqb (node_tag n) 2)%bool
  then [node_a n; node_b n] else [].
Module TypePayload <: RC_PAYLOAD_SIG.
  Definition node := TypeNode.
  Definition children := node_children.
End TypePayload.
Module TypeRCMap := MakeRCMap TypePayload.
Module TypeRCMapFacts := RCMapFacts TypePayload TypeRCMap.
Definition RcState := TypeRCMap.state.

(* 实例透明性的计算桥梁；已有低层证明展开递归 kernel 时使用。
   这不是另一份程序或假设，双方是定义上相等的同一个实现。 *)
Lemma type_release_program_eq : forall M p,
  TypeRCMap.release_program M p = RCMap.release_program node_children M p.
Proof. reflexivity. Qed.

(* 仅供本 case 的表示层证明使用：归约默认实例的投影与隐含 payload
   类型参数，使 lia/cancel/rewrite 看到一致的 kernel 项；不展开 RC 语义。 *)
Ltac type_rcmap_reduce :=
  cbv beta iota zeta delta
    [TypePayload.node TypePayload.children RcState
     TypeRCMap.state TypeRCMap.view TypeRCMap.nodes TypeRCMap.roots
     TypeRCMap.counts TypeRCMap.reserved TypeRCMap.valid TypeRCMap.preserves
     TypeRCMap.retain TypeRCMap.publish TypeRCMap.delete TypeRCMap.decrement
     TypeRCMap.retain_program TypeRCMap.release_program] in *.

(* 实例特有的约束：合法 tag，且变量编号落在 100 项 solution 的范围内。
   子指针有效性由通用 RCMap.valid 中的 closed 处理。 *)
Definition payload_valid (n : TypeNode) : Prop :=
  0 <= node_tag n <= 3 /\
  (node_tag n = 3 -> 0 <= node_a n < 100).

Definition rc_valid (M : RcState) : Prop :=
  TypeRCMap.valid M /\
  forall p n, TypeRCMap.nodes M p = Some n -> payload_valid n.

(* “p 在 M 中表示 tr”的纯关系，按数学树 tr 递归，不去递归展开 C 内存。
   同一个地址可以在解码时被重复使用，允许左右子树共享一个节点。
   叶子的未使用 b 在解码约定中取 0；payload_valid 本身没有要求这一点。 *)
Fixpoint decode_type (M : RcState) (p : addr) (tr : TypeTree) : Prop :=
  match tr with
  | TVar v => TypeRCMap.nodes M p = Some (Node 3 v 0)
  | TAtom a => TypeRCMap.nodes M p = Some (Node 0 a 0)
  | TArrow l r => exists pl pr,
      TypeRCMap.nodes M p = Some (Node 1 pl pr) /\
      decode_type M pl l /\ decode_type M pr r
  | TApply l r => exists pl pr,
      TypeRCMap.nodes M p = Some (Node 2 pl pr) /\
      decode_type M pl l /\ decode_type M pr r
  end.

(* 名字保留 store_type，但类型是 Prop，不是 Assertion：只负责解码。
   它既不拥有 p 的字段，也不代表一个可独立 release 的 owning 引用。
   如果 p 是存放指针的槽位，应另持有槽位 |-> 地址，再用此关系解释地址；
   这里的 p 已经是节点地址。 *)
Definition store_type (M : RcState) (p : addr) (tr : TypeTree) : Prop :=
  decode_type M p tr.

(* 只拥有本节点的 tag 和当前 union 分支字段；不含 refcnt，也不递归拥有
   孩子节点。最后的通配分支在 rc_valid 下只能用于 tag=2。 *)
Definition store_node_payload (p : addr) (n : TypeNode) : Assertion :=
  (&(p # "atype" ->ₛ "t") # Int |-> node_tag n) **
  match node_tag n with
  | 0 => (&(p # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name") # Int |-> node_a n)
  | 3 => (&(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> node_a n)
  | 1 => (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> node_a n) **
         (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> node_b n)
  | _ => (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> node_a n) **
         (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> node_b n)
  end.

(* 单节点物理权限：refcnt 的实际值等于 counts M p，再加该节点 payload。
   这一步才把“逻辑账本”与“实际内存中的引用计数”连接起来。 *)
Definition store_node (M : RcState) (p : addr) (n : TypeNode) : Assertion :=
  (&(p # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M p) **
  store_node_payload p n.

(* 对 nodes 中所有活节点做分离合取，每个节点恰好拥有一次。
   store_map 隐藏有限枚举及其大分离合取，不把它变成运行时数据结构。
   rc_valid M + store_world M 才同时给出账目约束和相应字段的内存权限。 *)
Definition store_world (M : RcState) : Assertion :=
  store_map (store_node M) (TypeRCMap.nodes M).

(* Only the active union view is owned.  Payload1 of a leaf is emp: it is
   not an allocated second field and must not be offered by a field rule. *)
Definition store_type_field (M : RcState) (p : addr) (n : TypeNode)
    (s : TypeFieldSlot) : Assertion :=
  match s with
  | RefCount => &(p # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M p
  | Tag => &(p # "atype" ->ₛ "t") # Int |-> node_tag n
  | Payload0 => match node_tag n with
      | 0 => &(p # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name") # Int |-> node_a n
      | 3 => &(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> node_a n
      | 1 => &(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> node_a n
      | _ => &(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> node_a n
      end
  | Payload1 => match node_tag n with
      | 0 | 3 => emp
      | 1 => &(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> node_b n
      | _ => &(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> node_b n
      end
  end.

Definition field_active (n : TypeNode) (s : TypeFieldSlot) : Prop :=
  s <> Payload1 \/ node_tag n = 1 \/ node_tag n = 2.

Definition store_node_missing (M : RcState) (L : list TypeFieldKey)
    (p : addr) (n : TypeNode) : Assertion :=
  field_mask L (p,RefCount) (store_type_field M p n RefCount) **
  field_mask L (p,Tag) (store_type_field M p n Tag) **
  field_mask L (p,Payload0) (store_type_field M p n Payload0) **
  field_mask L (p,Payload1) (store_type_field M p n Payload1).

(* One finite map, with an arbitrary finite list of omitted physical slots.
   Reordering or repeating a key does not create permission.  Extraction
   requires k not in L; aliases therefore cannot be extracted twice. *)
Definition store_world_missing (M : RcState) (L : list TypeFieldKey) : Assertion :=
  store_map (store_node_missing M L) (TypeRCMap.nodes M).

Lemma field_mask_ext : forall L K k P,
  (In k L <-> In k K) -> field_mask L k P = field_mask K k P.
Proof.
  intros L K k P H; unfold field_mask;
    destruct (in_dec field_key_eq_dec k L), (in_dec field_key_eq_dec k K);
    try reflexivity; tauto.
Qed.

Lemma store_world_missing_ext : forall M L K,
  (forall k, In k L <-> In k K) ->
  store_world_missing M L = store_world_missing M K.
Proof.
  intros M L K H; unfold store_world_missing.
  assert (store_node_missing M L = store_node_missing M K) as E.
  { apply functional_extensionality; intro p.
    apply functional_extensionality; intro n.
    unfold store_node_missing; rewrite ! (field_mask_ext L K); auto. }
  rewrite E; reflexivity.
Qed.

Lemma store_world_missing_permutation : forall M L K,
  Permutation L K -> store_world_missing M L = store_world_missing M K.
Proof.
  intros M L K H; apply store_world_missing_ext; intro k.
  split; intro Hin.
  - eapply Permutation_in; [exact H | exact Hin].
  - eapply Permutation_in; [apply Permutation_sym; exact H | exact Hin].
Qed.

Lemma store_world_missing_duplicate : forall M k L,
  store_world_missing M (k::k::L) = store_world_missing M (k::L).
Proof. intros; apply store_world_missing_ext; intro x; simpl; tauto. Qed.

(* Predicate changes can be transported through the finite map without
   choosing a computational enumeration of its domain. *)
Lemma iter_sepcon_map_entails {A : Type} : forall (l : list A) P Q,
  (forall a, In a l -> P a |-- Q a) ->
  iter_sepcon (map P l) |-- iter_sepcon (map Q l).
Proof.
  induction l as [|a l IH]; intros P Q H.
  - simpl; entailer!.
  - change (iter_sepcon ([P a] ++ map P l) |-- iter_sepcon ([Q a] ++ map Q l)).
    rewrite derivable1_iter_sepcon_app2.
    rewrite <- derivable1_iter_sepcon_app1.
    unfold iter_sepcon at 1 3; simpl.
    sep_apply (H a (or_introl eq_refl)).
    sep_apply (IH P Q ltac:(intros; apply H; right; assumption)).
    cancel.
Qed.

Lemma store_map_pred_entails {A B : Type} : forall (m : A -> option B) P Q,
  (forall a b, m a = Some b -> P a b |-- Q a b) ->
  store_map P m |-- store_map Q m.
Proof.
  intros m P Q H; unfold store_map; Intros l; Exists l; entailer!.
  apply iter_sepcon_map_entails; intros a Ha.
  destruct (m a) as [b|] eqn:E; [apply H; exact E | entailer!].
Qed.

Lemma store_node_missing_nil : forall M p n,
  store_node_missing M [] p n --||-- store_node M p n.
Proof.
  intros; unfold store_node_missing, field_mask, store_type_field,
    store_node, store_node_payload; simpl.
  destruct (node_tag n) as [|[[z|z|]|z|]|z]; split; cbn; entailer!.
Qed.

Lemma store_world_missing_nil : forall M,
  store_world_missing M [] --||-- store_world M.
Proof.
  intros; unfold store_world_missing, store_world; split;
    apply store_map_pred_entails; intros; apply store_node_missing_nil.
Qed.

Lemma store_node_missing_other : forall M L p s q n,
  p <> q -> store_node_missing M ((p,s)::L) q n = store_node_missing M L q n.
Proof.
  intros M L p s q n H; unfold store_node_missing.
  repeat rewrite (field_mask_ext ((p,s)::L) L) by (simpl; split; intuition congruence).
  reflexivity.
Qed.

Lemma store_node_missing_split : forall M L p n s,
  ~ In (p,s) L -> store_node_missing M L p n --||--
    store_type_field M p n s ** store_node_missing M ((p,s)::L) p n.
Proof.
  intros M L p n s H.
  assert (E : forall k P, field_mask ((p,s)::L) k P =
    if field_key_eq_dec (p,s) k then emp else field_mask L k P).
  { intros k P; unfold field_mask.
    destruct (field_key_eq_dec (p,s) k);
      destruct (in_dec field_key_eq_dec k ((p,s)::L));
      destruct (in_dec field_key_eq_dec k L); try reflexivity;
      simpl in *; intuition congruence. }
  assert (F : forall P, field_mask L (p,s) P = P).
  { intro P; unfold field_mask; destruct (in_dec field_key_eq_dec (p,s) L); tauto. }
  unfold store_node_missing; rewrite !E.
  destruct s; rewrite F;
    repeat match goal with |- context [field_key_eq_dec ?k ?j] =>
      destruct (field_key_eq_dec k j) end; try congruence;
    split; entailer!.
Qed.

Lemma store_map_missing_pred_entails {A B : Type} :
  forall (m : A -> option B) p P Q,
  (forall a b, m a = Some b -> a <> p -> P a b |-- Q a b) ->
  store_map_missing_i P m p |-- store_map_missing_i Q m p.
Proof.
  intros m p P Q H; unfold store_map_missing_i; Intros l; Exists l; entailer!.
  apply iter_sepcon_map_entails; intros a Ha.
  destruct (m a) as [b|] eqn:E; [|entailer!].
  apply H; [exact E | apply H0 in Ha; tauto].
Qed.

Lemma store_world_missing_split : forall M L p n s,
  TypeRCMap.nodes M p = Some n -> ~ In (p,s) L ->
  store_world_missing M L |--
    store_type_field M p n s ** store_world_missing M ((p,s)::L).
Proof.
  intros M L p n s Hn Hfresh; unfold store_world_missing.
  sep_apply (store_map_split (store_node_missing M L) p n (TypeRCMap.nodes M) Hn).
  sep_apply (proj1 (store_node_missing_split M L p n s Hfresh)).
  sep_apply (store_map_missing_pred_entails (TypeRCMap.nodes M) p
    (store_node_missing M L) (store_node_missing M ((p,s)::L))
    ltac:(intros; rewrite store_node_missing_other by congruence; cancel)).
  sep_apply_r_atomic (store_map_merge (store_node_missing M ((p,s)::L)) p n
    (TypeRCMap.nodes M) Hn).
  cancel.
  reflexivity.
Qed.

Lemma store_world_missing_merge : forall M L p n s,
  TypeRCMap.nodes M p = Some n -> ~ In (p,s) L ->
  store_type_field M p n s ** store_world_missing M ((p,s)::L)
    |-- store_world_missing M L.
Proof.
  intros M L p n s Hn Hfresh; unfold store_world_missing.
  sep_apply (store_map_split (store_node_missing M ((p,s)::L)) p n
    (TypeRCMap.nodes M) Hn).
  sep_apply (proj2 (store_node_missing_split M L p n s Hfresh)).
  sep_apply (store_map_missing_pred_entails (TypeRCMap.nodes M) p
    (store_node_missing M ((p,s)::L)) (store_node_missing M L)
    ltac:(intros; rewrite store_node_missing_other by congruence; cancel)).
  sep_apply_r_atomic (store_map_merge (store_node_missing M L) p n (TypeRCMap.nodes M) Hn).
  cancel.
  reflexivity.
Qed.

(* Node-level map frames used only while proving the field-list laws.
   C clients use store_world_missing, never a combination-specific frame. *)
Definition store_world_except (M : RcState) (p : addr) : Assertion :=
  store_map_missing_i (store_node M) (TypeRCMap.nodes M) p.

(* active union 字段，不含 tag/refcnt；供下面细粒度拆分使用。 *)
Definition store_payload_aux (p : addr) (n : TypeNode) : Assertion :=
  match node_tag n with
  | 0 => (&(p # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name") # Int |-> node_a n)
  | 3 => (&(p # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> node_a n)
  | 1 => (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> node_a n) **
         (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> node_b n)
  | _ => (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> node_a n) **
         (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> node_b n)
  end.

(* Removing two whole nodes requires p <> q in the corresponding laws.
   Aliasing uses the one-node law; no duplicate physical ownership arises. *)
Definition store_world_except2 (M : RcState) (p q : addr) : Assertion :=
  store_map_missing_i (store_node M)
    (fun r => if Z.eq_dec p r then None else TypeRCMap.nodes M r) q.

Lemma store_node_missing_unaffected : forall M L p n,
  (forall s, ~ In (p,s) L) ->
  store_node_missing M L p n --||-- store_node M p n.
Proof.
  intros M L p n H.
  assert (E : store_node_missing M L p n = store_node_missing M [] p n).
  { unfold store_node_missing.
    repeat rewrite (field_mask_ext L []) by (simpl; split; intros; [exfalso; eapply H; eauto | contradiction]).
    reflexivity. }
  rewrite E; apply store_node_missing_nil.
Qed.

Lemma store_world_missing_at : forall M L p n,
  TypeRCMap.nodes M p = Some n ->
  (forall q s, In (q,s) L -> q = p) ->
  store_world_missing M L --||--
    store_node_missing M L p n ** store_world_except M p.
Proof.
  intros M L p n Hn Hkeys; unfold store_world_missing, store_world_except; split.
  - sep_apply (store_map_split (store_node_missing M L) p n (TypeRCMap.nodes M) Hn).
    sep_apply (store_map_missing_pred_entails (TypeRCMap.nodes M) p
      (store_node_missing M L) (store_node M)
      ltac:(intros; apply store_node_missing_unaffected; intros s Hin; apply Hkeys in Hin; congruence)).
    cancel; reflexivity.
  - sep_apply (store_map_missing_pred_entails (TypeRCMap.nodes M) p
      (store_node M) (store_node_missing M L)
      ltac:(intros; apply store_node_missing_unaffected; intros s Hin; apply Hkeys in Hin; congruence)).
    sep_apply_r_atomic (store_map_merge (store_node_missing M L) p n (TypeRCMap.nodes M) Hn).
    cancel; reflexivity.
Qed.

Lemma field_mask_cons : forall k j L P,
  field_mask (k::L) j P =
    if field_key_eq_dec k j then emp else field_mask L j P.
Proof.
  intros k j L P; unfold field_mask.
  destruct (field_key_eq_dec k j);
    destruct (in_dec field_key_eq_dec j (k::L));
    destruct (in_dec field_key_eq_dec j L); try reflexivity;
    simpl in *; intuition congruence.
Qed.

Ltac reduce_field_masks :=
  unfold store_node_missing;
  repeat rewrite field_mask_cons;
  cbn [field_mask];
  repeat match goal with |- context [field_key_eq_dec ?k ?j] =>
    destruct (field_key_eq_dec k j) end; try congruence.

Lemma store_node_missing_tag : forall M p n,
  store_node_missing M [(p,Tag)] p n --||--
    (&(p # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M p) **
    store_payload_aux p n.
Proof.
  intros M p n; reduce_field_masks.
  unfold store_type_field, store_payload_aux.
  destruct (node_tag n) as [|[[z|z|]|z|]|z]; split; cbn; entailer!.
Qed.

Lemma store_node_missing_count : forall M p n,
  store_node_missing M [(p,RefCount)] p n --||-- store_node_payload p n.
Proof.
  intros M p n; reduce_field_masks.
  unfold store_type_field, store_node_payload.
  destruct (node_tag n) as [|[[z|z|]|z|]|z]; split; cbn; entailer!.
Qed.

Lemma store_node_missing_payload : forall M p n,
  store_node_missing M (payload_keys p n) p n --||--
    (&(p # "atype" ->ₛ "refcnt") # Int |-> TypeRCMap.counts M p) **
    (&(p # "atype" ->ₛ "t") # Int |-> node_tag n).
Proof.
  intros M p n; unfold payload_keys.
  destruct (node_tag n) as [|[[z|z|]|z|]|z] eqn:E;
    reduce_field_masks; unfold store_type_field; rewrite E; split; cbn; entailer!.
Qed.

Lemma payload_keys_owner : forall p n q s, In (q,s) (payload_keys p n) -> q = p.
Proof.
  intros p n q s; unfold payload_keys.
  destruct (node_tag n) as [|[[z|z|]|z|]|z]; simpl; intuition congruence.
Qed.

(* Compatibility bridges are proof lemmas, not extra C predicates. They
   allow existing node-level VC helpers to consume the uniform list view. *)



Lemma store_map_two_view {B : Type} : forall (P : addr -> B -> Assertion) m p np q nq,
  m p = Some np -> m q = Some nq -> p <> q ->
  store_map P m --||-- P p np ** P q nq **
    store_map_missing_i P (fun r => if Z.eq_dec p r then None else m r) q.
Proof.
  intros P m p np q nq Hp Hq Hneq.
  set (deleted := fun r => if Z.eq_dec p r then None else m r).
  assert (Heq : forall r, r <> p -> m r = deleted r).
  { intros r Hr; unfold deleted; destruct (Z.eq_dec p r); congruence. }
  assert (Hdel : deleted p = None).
  { unfold deleted; destruct (Z.eq_dec p p); congruence. }
  assert (Hqdel : deleted q = Some nq).
  { unfold deleted; destruct (Z.eq_dec p q); congruence. }
  split.
  - sep_apply (store_map_split P p np m Hp).
    sep_apply (proj1 (store_map_missing_i_equiv P m deleted p Heq)).
    sep_apply (store_map_missing_equiv_store_map P deleted p Hdel).
    sep_apply (store_map_split P q nq deleted Hqdel).
    fold deleted; cancel; reflexivity.
  - fold deleted.
    transitivity (P p np ** store_map P deleted).
    + sep_apply_r_atomic (store_map_merge P q nq deleted Hqdel).
      cancel (P p np); cancel (P q nq); reflexivity.
    + sep_apply (store_map_equiv_store_map_missing P deleted p Hdel).
      sep_apply (proj2 (store_map_missing_i_equiv P m deleted p Heq)).
      sep_apply_r_atomic (store_map_merge P p np m Hp).
      cancel (P p np); reflexivity.
Qed.

Lemma store_world_missing_at_two : forall M L p np q nq,
  TypeRCMap.nodes M p = Some np -> TypeRCMap.nodes M q = Some nq -> p <> q ->
  (forall r s, In (r,s) L -> r = p \/ r = q) ->
  store_world_missing M L --||--
    store_node_missing M L p np ** store_node_missing M L q nq ** store_world_except2 M p q.
Proof.
  intros M L p np q nq Hp Hq Hneq Hkeys.
  set (deleted := fun r => if Z.eq_dec p r then None else TypeRCMap.nodes M r).
  assert (Houtside : forall r n, deleted r = Some n -> r <> q ->
    store_node_missing M L r n --||-- store_node M r n).
  { intros r n Hr Hnr; apply store_node_missing_unaffected; intros s Hin.
    apply Hkeys in Hin; destruct Hin as [Heq|Heq]; [subst r|congruence].
    unfold deleted in Hr; destruct (Z.eq_dec p p); congruence. }
  unfold store_world_missing, store_world_except2; fold deleted; split.
  - sep_apply (proj1 (store_map_two_view (store_node_missing M L)
      (TypeRCMap.nodes M) p np q nq Hp Hq Hneq)).
    cancel (store_node_missing M L p np); cancel (store_node_missing M L q nq).
    apply store_map_missing_pred_entails; intros; apply Houtside; assumption.
  - sep_apply_r_atomic (proj2 (store_map_two_view (store_node_missing M L)
      (TypeRCMap.nodes M) p np q nq Hp Hq Hneq)).
    cancel (store_node_missing M L p np); cancel (store_node_missing M L q nq).
    apply store_map_missing_pred_entails; intros; apply Houtside; assumption.
Qed.

Lemma store_node_missing_ext : forall M L K p n,
  (forall s, In (p,s) L <-> In (p,s) K) ->
  store_node_missing M L p n = store_node_missing M K p n.
Proof.
  intros M L K p n H; unfold store_node_missing.
  rewrite !(field_mask_ext L K); auto.
Qed.



(* 给 C 注解使用的简短实例接口；这些只是前面定义的包装，不是新状态。
   reservations_same 用于说明临时 retain/release 配平后，保留引用账目
   回到基准值。它不要求节点图、计数、solution 都回到原值。 *)
Definition node_at (M : RcState) (p : addr) (n : TypeNode) : Prop :=
  TypeRCMap.nodes M p = Some n.

Definition rc_count (M : RcState) (p : addr) : Z := TypeRCMap.counts M p.
Definition rc_roots (M : RcState) (p : addr) : Z := TypeRCMap.roots M p.
Definition rc_reserved (M : RcState) (p : addr) : Z := TypeRCMap.reserved M p.
Definition rc_publish (M : RcState) (p : addr) : RcState := TypeRCMap.publish M p.
Definition rc_reservations_same (B M : RcState) : Prop :=
  forall p, TypeRCMap.reserved B p = TypeRCMap.reserved M p.
Definition rc_delete (M : RcState) (p : addr) (n : TypeNode) : RcState :=
  TypeRCMap.delete M p n.
Definition rc_decrement (M : RcState) (p : addr) : RcState :=
  TypeRCMap.decrement M p.
Definition rc_preserves (B M : RcState) : Prop := TypeRCMap.preserves B M.

(* solution 的单个数组槽位：真正拥有的是槽位 |-> p；槽位内容的解释
   是纯事实。None 对应空指针，Some tr 对应 M 中可解码为 tr 的非空地址。
   注意不在这里重复拥有 p 的节点字段；节点字段统一在 world 中。 *)
Definition solution_entry (M : RcState) (s : sol) (base i p : Z) : Assertion :=
  ((base + i * sizeof(PTR)) # Ptr |-> p) **
  match s i with
  | None => “ p = 0 ” && emp
  | Some tr => “ p <> 0 /\ decode_type M p tr ” && emp
  end.

(* 按槽位出现次数核对 owning 引用预算：两个槽位存 p 就需要两个引用。
   用 <= 而非 =，允许还有其他图外 owning 引用未由本数组占用。
   reserved 不能算给数组，否则一次临时 retain 就可能虚构第二个槽位的
   所有权；下面 retained_one_slot_cannot_back_two 专门排除这种情况。

   适用边界：这是当前单个全局 solution 的集中记账。若推广到多个独立容器，
   必须核对它们的总用量或引入可分配的线性凭证；不能让每个容器分别拿同一
   roots-reserved 上界，就声称它们组合后仍不会重复消费引用预算。 *)
Definition solution_roots (M : RcState) (l : list addr) : Prop :=
  forall p, p <> 0 -> Z.of_nat (count_occ Z.eq_dec l p) <=
    TypeRCMap.roots M p - TypeRCMap.reserved M p.

(* 整张 100 项表：l 是实际地址列表，s 是原有的数学 solution。
   M 只用来解释 l 并核对引用数，M.nodes 仍只存 type 节点，不存 solution。
   与 world 做 ** 时，数组槽位和节点字段分别拥有；数学 s 的意义没有改变。
   get_map 可以借用已有地址而不 retain；新增 owning 槽位则要配套 retain
   和 publish。publish 不写物理计数，只交付已有的那一个引用。 *)
Definition store_solution (M : RcState) (base : addr) (s : sol) : Assertion :=
  EX l : list addr,
    “ solution_roots M l ” &&
    “ forall i, i < 0 \/ 100 <= i -> s i = None ” &&
    store_array (solution_entry M s) base 100 l.

Lemma solution_roots_retain : forall M p l,
  solution_roots (RCMap.retain M p) l <-> solution_roots M l.
Proof.
  unfold solution_roots; intros; setoid_rewrite RCMap.retain_available; reflexivity.
Qed.

Lemma solution_roots_decrement : forall M p l,
  solution_roots (RCMap.decrement M p) l <-> solution_roots M l.
Proof.
  unfold solution_roots; intros; setoid_rewrite RCMap.decrement_available; reflexivity.
Qed.

(* Regression for the independent checker's [A,A] table: retaining a
   representative never manufactures another table-owned reference. *)
Lemma retained_one_slot_cannot_back_two : forall M p,
  p <> 0 -> RCMap.roots M p - RCMap.reserved M p = 1 ->
  ~ solution_roots (RCMap.retain M p) [p;p].
Proof.
  intros M p Hp Hbudget. rewrite solution_roots_retain.
  intro H; specialize (H p Hp).
  change (Z.of_nat (count_occ Z.eq_dec [p;p] p) <=
    RCMap.roots M p - RCMap.reserved M p) in H.
  rewrite Hbudget in H.
  cbn -[Z.eq_dec] in H; destruct (Z.eq_dec p p); [cbn in H; lia|contradiction].
Qed.

(* 给最终数学规格的视图：物理表仍存 raw，返回的数学 s 是 raw 的压缩结果。
   这里只证明二者满足 sol_compress_to，不声称 C 已逐槽重写物理数组。 *)
Definition store_compressed_solution (M : RcState) (base : addr) (s : sol) : Assertion :=
  EX raw : sol,
    “ sol_compress_to raw s /\ sol_finite s /\ sol_no_loop raw ” &&
    store_solution M base raw.

(* 将 monad 程序的正常返回包装成规格关系。nrm 的两个 tt 是 monad 状态，
   真正变化的账本 M' 是返回值；因此没有另藏一份隐式可变 map。
   nrm 不等于“任意输入都安全”，有效性和内存前提仍由调用规格提供。 *)
Definition retain_rel (M : RcState) (p : addr) (M' : RcState) : Prop :=
  MonadErr.nrm (TypeRCMap.retain_program M p) tt M' tt.
Definition release_rel (M : RcState) (p : addr) (M' : RcState) : Prop :=
  MonadErr.nrm (TypeRCMap.release_program M p) tt M' tt.

(* 权限提取的关键桥梁：由 map 中的纯查询事实，选择 world 已经拥有的那一项，
   拆成节点和剩余 frame。结论不是凭空生成节点，也不能同时保留完整 world。 *)
Lemma store_world_open : forall M p n,
  RCMap.nodes M p = Some n ->
  store_world M |-- store_node M p n ** store_world_except M p.
Proof.
  intros M p n H; unfold store_world, store_world_except.
  sep_apply (store_map_split (store_node M) p n (TypeRCMap.nodes M) H).
  cancel.
Qed.

(* 旧节点未被破坏时，旧地址的数学解释继续成立；此引理只传递纯解码事实。 *)
Lemma decode_type_preserves : forall B M p tr,
  RCMap.preserves B M -> decode_type B p tr -> decode_type M p tr.
Proof.
  intros B M p tr [Hp Hr]; revert p; induction tr; cbn; intros p H;
    unfold TypeRCMap.nodes in *; cbn [TypeRCMap.view] in *.
  - auto.
  - auto.
  - destruct H as [pl [pr [H [Hl Hr']]]].
    exists pl,pr; repeat split; eauto.
  - destruct H as [pl [pr [H [Hl Hr']]]].
    exists pl,pr; repeat split; eauto.
Qed.

(* 同一账本中，一个地址不能解码成两个不同的数学树；可用于别名分支。 *)
Lemma decode_type_unique : forall M p tr1 tr2,
  decode_type M p tr1 -> decode_type M p tr2 -> tr1 = tr2.
Proof.
  intros M p tr1; revert p; induction tr1; intros p tr2 H1 H2;
    destruct tr2; cbn in H1,H2;
    unfold TypeRCMap.nodes in H1,H2;
    cbn [TypeRCMap.view] in H1,H2;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H as [? H]
    | H : _ /\ _ |- _ => destruct H
    end;
    try congruence;
    match goal with
    | H : RCMap.nodes _ _ = Some _, H' : RCMap.nodes _ _ = Some _ |- _ =>
      rewrite H in H'; inversion H'; subst
    end; f_equal; eauto.
Qed.

(* Only integer-capacity errors are represented by the following error
   component.  Missing-node branches return an error code; they do NOT
   assert memory safety.  The C proof must establish their impossibility
   separately from rc_valid and decode_type.  The capacity precondition
   therefore cannot assume release safety or functional correctness. *)
(* 实现模型返回 (C 返回码, 新 RC 账本, 新数学 solution)。
   返回码 0/1/2 与 monad 的 err 是两件事：正常返回失败码仍属于 nrm；
   err 在这里追踪 retain 容量检查失败，不把算法正确性作为假设塞进去。 *)
Definition InferResult := (Z * RcState * sol)%type.

(* 抽象 atype_repr 的代表元选择：any/testPure 描述满足已有代表元关系的
   地址和类型，不是可执行搜索算法；选中后 retain 一个临时 owning 引用。
   调用结束还要 release 该临时引用。 *)
Definition repr_choice (M : RcState) (s : sol) (v : Z)
    : RCProgram (addr * RcState) :=
  p <- any addr ;;
  tr <- any TypeTree ;;
  testPure (decode_type M p tr /\ repr_rel_node s (TVar v) tr) ;;
  M' <- TypeRCMap.retain_program M p ;;
  ret (p,M').

(* 三阶段对应 C 中 atype_unify / atype_unify1 / atype_unify2：
   stage 0 处理左侧代表元，stage 1 处理右侧代表元，其余分支处理结构统一。
   代表元分支的 retain -> 递归调用 -> release 描述临时引用的完整生命周期。
   未绑定变量的成功分支 retain -> publish -> sol_update，把新增引用交给表。
   Arrow/Apply 先递归第一个孩子，成功后才处理第二个。
   choice 是关系式的抽象分支（变量分支允许直接返回失败码），不是对原始
   统一算法的数学定义；实际 C 的数学正确性仍需另外证明。 *)
Definition infer_rec
    (W : Z -> addr -> addr -> RcState -> sol -> RCProgram InferResult)
    (stage : Z) (p q : addr) (M : RcState) (s : sol)
    : RCProgram InferResult :=
  match TypeRCMap.nodes M p, TypeRCMap.nodes M q with
  | Some np, Some nq =>
    if Z.eq_dec stage 0 then
      if Z.eq_dec (node_tag np) 3 then
        match s (node_a np) with
        | None => W 1 p q M s
        | Some _ =>
          '(p',M1) <- repr_choice M s (node_a np) ;;
          '(r,M2,s2) <- W 1 p' q M1 s ;;
          M3 <- TypeRCMap.release_program M2 p' ;;
          ret (r,M3,s2)
        end
      else W 1 p q M s
    else if Z.eq_dec stage 1 then
      if Z.eq_dec (node_tag nq) 3 then
        match s (node_a nq) with
        | None => W 2 p q M s
        | Some _ =>
          '(q',M1) <- repr_choice M s (node_a nq) ;;
          '(r,M2,s2) <- W 2 p q' M1 s ;;
          M3 <- TypeRCMap.release_program M2 q' ;;
          ret (r,M3,s2)
        end
      else W 2 p q M s
    else if Z.eq_dec (node_tag np) 3 then
      choice (ret (1,M,s))
        (tr <- any TypeTree ;;
         testPure (decode_type M q tr /\ not_occur_final s (node_a np) tr) ;;
         M' <- TypeRCMap.retain_program M q ;;
         ret (0,TypeRCMap.publish M' q,sol_update s (node_a np) tr))
    else if Z.eq_dec (node_tag nq) 3 then
      choice (ret (1,M,s))
        (tr <- any TypeTree ;;
         testPure (decode_type M p tr /\ not_occur_final s (node_a nq) tr) ;;
         M' <- TypeRCMap.retain_program M p ;;
         ret (0,TypeRCMap.publish M' p,sol_update s (node_a nq) tr))
    else if Z.eq_dec (node_tag np) (node_tag nq) then
      if (Z.eqb (node_tag np) 1 || Z.eqb (node_tag np) 2)%bool then
        '(r,M1,s1) <- W 0 (node_a np) (node_a nq) M s ;;
          if Z.eq_dec r 0 then W 0 (node_b np) (node_b nq) M1 s1
          else ret (r,M1,s1)
      else if Z.eq_dec (node_a np) (node_a nq)
           then ret (0,M,s) else ret (2,M,s)
    else ret (2,M,s)
  | _,_ => ret (2,M,s)
  end.

Definition infer := Rec infer_rec.

(* 只要求上述抽象执行不存在容量错误；不是“所有输入都安全/一定终止”的
   总括前提，也不含 unify_rel 或 sol_correct_iter 作为要求的结果。
   C 的内存安全、引用账目保持和原有统一正确性分别由证明建立。

   更具体地，rc_capacity stage M s p q 排除从这个入口出发，抽象程序的
   任意允许分支在某次 retain 时遇到 counts >= 2147483647；stage=0/1/2
   分别对应 unify/unify1/unify2。它不是只检查入口处 p、q 的 counts：
   后续选到的代表元、递归孩子和重复 retain 也需要容量。这里的 err 不包含
   C 返回码 1/2，所以统一失败不违反 rc_capacity；反过来，只有“无 err”
   也不能推出存在正常返回，更不能代替终止证明。

   这个条件当前仍依赖 infer 的执行模型，是实现的溢出安全前提，而不是
   typeinfer 的数学输入域。公开成功结果仍是原来的 sol_correct_iter。
   若将来要换成更简单的静态计数上界，需另证该上界足以推出此条件，不能
   直接拿“现在 counts 没有达到上限”替换整个执行过程的容量要求。 *)
Definition rc_capacity (stage : Z) (M : RcState) (s : sol) (p q : addr) : Prop :=
  ~ MonadErr.err (infer stage p q M s) tt.

(* 正常结果关系供各 C 调用之间串联账本和 solution；r 虽写在 addr 参数组中，
   此处语义是整数返回码。repr_result、solution_at 也是供注解使用的包装。 *)
Definition infer_result (stage : Z) (M : RcState) (s : sol)
    (p q r : addr) (M' : RcState) (s' : sol) : Prop :=
  MonadErr.nrm (infer stage p q M s) tt (r,M',s') tt.

Definition repr_result (M : RcState) (s : sol) (v p : Z) (M' : RcState) : Prop :=
  MonadErr.nrm (repr_choice M s v) tt (p,M') tt.

Definition solution_at (s : sol) (v : Z) (tr : TypeTree) : Prop :=
  s v = Some tr.

(* 以下单调/连续性引理允许按 Rec_unfold 展开递归模型。
   它们是 monad 不动点的技术条件，不是额外的 RC 不变量或算法正确性公理。 *)
Lemma infer_call_mono_cont : forall st p q M s,
  mono_cont (fun W : Z -> addr -> addr -> RcState -> sol -> RCProgram InferResult =>
    W st p q M s).
Proof.
  intros st p q M s.
  apply (mono_cont_at (fun W : Z -> addr -> addr -> RcState -> sol -> RCProgram InferResult => W st p q M) s).
  apply (mono_cont_at (fun W : Z -> addr -> addr -> RcState -> sol -> RCProgram InferResult => W st p q) M).
  apply (mono_cont_at (fun W : Z -> addr -> addr -> RcState -> sol -> RCProgram InferResult => W st p) q).
  apply (mono_cont_at (fun W : Z -> addr -> addr -> RcState -> sol -> RCProgram InferResult => W st) p).
  apply (mono_cont_at (fun W : Z -> addr -> addr -> RcState -> sol -> RCProgram InferResult => W) st).
  apply mono_cont_id.
Qed.

Lemma infer_rec_mono_cont : mono_cont infer_rec.
Proof.
  unfold infer_rec.
  let rec solve_mc :=
    lazymatch goal with
    | |- mono_cont (fun x => x) => apply mono_cont_id
    | |- mono_cont (fun W : Z -> addr -> addr -> RcState -> sol -> RCProgram InferResult =>
          W _ _ _ _ _) => apply infer_call_mono_cont
    | |- mono_cont (fun x i => _) => apply mono_cont_pointwise; intro; solve_mc
    | |- mono_cont (fun x => Monad.bind _ _) =>
        apply mono_cont_bind; [solve_mc | intro; solve_mc]
    | |- mono_cont (fun x => MonadErr.bind _ _) =>
        apply mono_cont_bind; [solve_mc | intro; solve_mc]
    | |- mono_cont (fun x => choice _ _) =>
        apply mono_cont_choice; [solve_mc | solve_mc]
    | |- mono_cont (fun x => match ?a with _ => _ end) => destruct a; solve_mc
    | |- mono_cont (fun x => ?f ?arg) =>
        first [apply mono_cont_const |
          apply (mono_cont_at (fun x => f) arg); solve_mc |
          match goal with |- ?G => idtac "RC monotonicity remaining:" G; fail 1 end]
    | |- mono_cont _ => apply mono_cont_const
    end in solve_mc.
Qed.

Lemma infer_err_unfold : forall stage p q M s,
  MonadErr.err (infer stage p q M s) tt <->
  MonadErr.err (infer_rec infer stage p q M s) tt.
Proof.
  intros stage p q M s.
  pose proof (Rec_unfold infer_rec infer_rec_mono_cont) as H.
  destruct (H stage p q M s) as [Hn He].
  apply He.
Qed.

(* These separated addresses are compatible with distinct C allocations.
   The atom already has two external references; unifying the variable with
   it exercises a third, genuinely shared reference. *)
(* 例一：变量 4096 和原子 8192，原子已有两个图外引用。
   下方分别证明容量条件、账本有效性和类型解码，避免把这些性质混为一谈。
   这是纯模型例子，没有在此构造实际 C 堆的 store_world 证明。 *)
Definition capacity_demo : RcState :=
  RCMap.make
    (fun p => if Z.eq_dec p 4096 then Some (Node 3 0 0)
              else if Z.eq_dec p 8192 then Some (Node 0 7 0) else None)
    (fun p => if Z.eq_dec p 4096 then 1 else if Z.eq_dec p 8192 then 2 else 0)
    (fun p => if Z.eq_dec p 4096 then 1 else if Z.eq_dec p 8192 then 2 else 0)
    (fun _ => 0).

Example capacity_demo_full_inference :
  rc_capacity 0 capacity_demo (fun _ => None) 4096 8192.
Proof.
  unfold rc_capacity.
  rewrite infer_err_unfold.
  change (~ MonadErr.err (infer 1 4096 8192 capacity_demo (fun _ => None)) tt).
  rewrite infer_err_unfold.
  change (~ MonadErr.err (infer 2 4096 8192 capacity_demo (fun _ => None)) tt).
  rewrite infer_err_unfold.
  cbn [infer_rec capacity_demo RCMap.retain_program].
  firstorder.
Qed.

Lemma capacity_demo_nodes : forall p n,
  RCMap.nodes capacity_demo p = Some n <->
  (p = 4096 /\ n = Node 3 0 0) \/ (p = 8192 /\ n = Node 0 7 0).
Proof.
  intros p n; unfold capacity_demo; type_rcmap_reduce; cbn -[Z.eq_dec].
  destruct (Z.eq_dec p 4096), (Z.eq_dec p 8192); subst;
    split; intro H; try congruence; intuition congruence.
Qed.

Example capacity_demo_valid : rc_valid capacity_demo.
Proof.
  split.
  - split.
    + exists [(4096,Node 3 0 0);(8192,Node 0 7 0)]; split.
      * split.
        -- cbn; repeat constructor; cbn; intuition congruence.
        -- intros p n; rewrite capacity_demo_nodes; cbn; split.
           ++ intros [H|[H|H]]; [inversion H; subst; auto|inversion H; subst; auto|contradiction].
           ++ intros [[-> ->]|[-> ->]]; auto.
      * intro p; unfold RCMap.incoming, capacity_demo; cbn -[Z.eq_dec]. lia.
    + split.
      * intros p n q H Hq; apply capacity_demo_nodes in H;
          destruct H as [[-> ->]|[-> ->]]; contradiction.
      * split.
        -- exists (fun _ => 0); split; [intros; lia|].
           intros p n q H Hq; apply capacity_demo_nodes in H;
             destruct H as [[-> ->]|[-> ->]]; contradiction.
        -- split.
           ++ intro p; unfold capacity_demo; cbn -[Z.eq_dec];
                destruct (Z.eq_dec p 4096), (Z.eq_dec p 8192); lia.
           ++ split.
              ** intros p n H; apply capacity_demo_nodes in H;
                   destruct H as [[-> ->]|[-> ->]]; vm_compute; intuition congruence.
              ** split.
                 --- intros p H; unfold capacity_demo in *; cbn -[Z.eq_dec] in *;
                       destruct (Z.eq_dec p 4096), (Z.eq_dec p 8192); try discriminate; auto.
                 --- intro p; unfold capacity_demo; cbn -[Z.eq_dec];
                       destruct (Z.eq_dec p 4096), (Z.eq_dec p 8192); lia.
  - intros p n H; apply capacity_demo_nodes in H;
      destruct H as [[-> ->]|[-> ->]]; unfold payload_valid; cbn; lia.
Qed.

Example capacity_demo_types :
  store_type capacity_demo 4096 (TVar 0) /\
  store_type capacity_demo 8192 (TAtom 7).
Proof. split; reflexivity. Qed.

(* This is a single, deliberately explicit capacity condition.  It does not
   contain rc_valid, decode_type, safe release, unify_rel, or sol_correct_iter
   as a required result.  Proofs below will expose arithmetic-only sufficient
   cases, and the C/VC proof must separately prove heap preservation. *)

(* Concrete shared graph: the arrow has two owning edges to the same atom,
   and the atom also has an external root.  The finite enumeration is proof
   evidence, not a stored live-key field. *)
(* 例二：地址 1 的 Arrow 有两个孩子，均为地址 2；地址 2 另有一个外部根。
   地址 2 的 (roots, incoming, counts, reserved) 起初为 (1,2,3,0)。
   删除父节点后变为 (3,0,3,2)，两次 release 后变为 (1,0,1,0)，故不会误删
   仍被外部引用的原子。下面 accounting 验算账目，execution 证明 monad 轨迹。
   地址 1/2 仅用作逻辑图中的示例，不声称是可实际分配的互不重叠 C 节点。 *)
Definition shared_demo : RcState :=
  RCMap.make
    (fun p => if Z.eq_dec p 1 then Some (Node 1 2 2)
              else if Z.eq_dec p 2 then Some (Node 0 7 0) else None)
    (fun p => if Z.eq_dec p 1 then 1 else if Z.eq_dec p 2 then 1 else 0)
    (fun p => if Z.eq_dec p 1 then 1 else if Z.eq_dec p 2 then 3 else 0)
    (fun p => if Z.eq_dec p 1 then 1 else 0).

Example shared_demo_decode :
  decode_type shared_demo 1 (TArrow (TAtom 7) (TAtom 7)).
Proof. exists 2,2; vm_compute; auto. Qed.

Example shared_demo_incoming :
  RCMap.incoming node_children [(1,Node 1 2 2);(2,Node 0 7 0)] 2 = 2.
Proof. reflexivity. Qed.

Lemma shared_demo_nodes : forall p n,
  RCMap.nodes shared_demo p = Some n <->
  (p = 1 /\ n = Node 1 2 2) \/ (p = 2 /\ n = Node 0 7 0).
Proof.
  intros p n; unfold shared_demo; type_rcmap_reduce; cbn.
  destruct (Z.eq_dec p 1), (Z.eq_dec p 2); subst;
    split; intro H; try congruence; intuition congruence.
Qed.

Example shared_demo_valid : rc_valid shared_demo.
Proof.
  split.
  - split.
    + exists [(1,Node 1 2 2);(2,Node 0 7 0)]; split.
      * split.
        -- cbn; repeat constructor; cbn; intuition congruence.
        -- intros p n; rewrite shared_demo_nodes; cbn; split.
           ++ intros [H|[H|H]]; [inversion H; subst; auto|inversion H; subst; auto|contradiction].
           ++ intros [[-> ->]|[-> ->]]; auto.
      * intro p; unfold RCMap.incoming, shared_demo; cbn -[Z.eq_dec].
        destruct (Z.eq_dec p 1), (Z.eq_dec p 2), (Z.eq_dec 2 p); subst;
          cbn -[Z.eq_dec]; try congruence; lia.
    + split.
      * intros p n q H Hq; apply shared_demo_nodes in H.
        destruct H as [[-> ->]|[-> ->]]; cbn in Hq.
        -- destruct Hq as [<-|[<-|Hq]]; try contradiction;
             exists (Node 0 7 0); reflexivity.
        -- contradiction.
      * split.
        -- exists (fun p => if Z.eq_dec p 1 then 1 else 0); split.
           ++ intros p n H; destruct (Z.eq_dec p 1); lia.
           ++ intros p n q H Hq; apply shared_demo_nodes in H.
              destruct H as [[-> ->]|[-> ->]]; cbn in Hq.
              ** destruct Hq as [<-|[<-|Hq]]; try contradiction; cbn; lia.
              ** contradiction.
        -- split.
           ++ intro p; unfold shared_demo; cbn -[Z.eq_dec];
                destruct (Z.eq_dec p 1), (Z.eq_dec p 2); lia.
           ++ split.
              ** intros p n H; apply shared_demo_nodes in H;
                   destruct H as [[-> ->]|[-> ->]]; vm_compute; intuition congruence.
              ** split.
                 --- intros p H; unfold shared_demo in *; cbn -[Z.eq_dec] in *;
                       destruct (Z.eq_dec p 1), (Z.eq_dec p 2); try discriminate; auto.
                 --- intro p; unfold shared_demo; cbn -[Z.eq_dec];
                       destruct (Z.eq_dec p 1), (Z.eq_dec p 2); lia.
  - intros p n H; apply shared_demo_nodes in H;
      destruct H as [[-> ->]|[-> ->]]; unfold payload_valid; cbn; lia.
Qed.

Example shared_demo_retain_headroom :
  ~ MonadErr.err (RCMap.retain_program shared_demo 2) tt /\
  retain_rel shared_demo 2 (RCMap.retain shared_demo 2) /\
  RCMap.counts (RCMap.retain shared_demo 2) 2 = 4.
Proof.
  unfold retain_rel, RCMap.retain_program; cbn.
  repeat split; try reflexivity.
  - intros [H|[x [u [H1 H2]]]]; [apply H; right; vm_compute; auto|contradiction].
  - exists tt,tt; repeat split; try reflexivity; right; vm_compute; auto.
Qed.

Example shared_demo_repeated_release_accounting :
  let M1 := RCMap.delete node_children shared_demo 1 (Node 1 2 2) in
  let M2 := RCMap.decrement M1 2 in
  let M3 := RCMap.decrement M2 2 in
  RCMap.roots M1 2 = 3 /\ RCMap.counts M1 2 = 3 /\
  RCMap.roots M2 2 = 2 /\ RCMap.counts M2 2 = 2 /\
  RCMap.roots M3 2 = 1 /\ RCMap.counts M3 2 = 1 /\
  RCMap.reserved M1 2 = 2 /\ RCMap.reserved M2 2 = 1 /\
  RCMap.reserved M3 2 = 0 /\
  RCMap.nodes M3 2 = Some (Node 0 7 0).
Proof. vm_compute; repeat split; reflexivity. Qed.

Example shared_demo_repeated_release_execution :
  release_rel shared_demo 1
    (RCMap.decrement
      (RCMap.decrement (RCMap.delete node_children shared_demo 1 (Node 1 2 2)) 2) 2).
Proof.
  set (Mf := RCMap.decrement
      (RCMap.decrement (RCMap.delete node_children shared_demo 1 (Node 1 2 2)) 2) 2).
  unfold release_rel; rewrite type_release_program_eq; unfold RCMap.release_program.
  apply RCMap.release_nrm_unfold.
  change (MonadErr.nrm (Rec (RCMap.release_rec node_children)
    ([2;2], RCMap.delete node_children shared_demo 1 (Node 1 2 2))) tt Mf tt).
  rewrite RCMap.release_nrm_unfold.
  change (MonadErr.nrm (Rec (RCMap.release_rec node_children)
    ([2], RCMap.decrement (RCMap.delete node_children shared_demo 1 (Node 1 2 2)) 2)) tt Mf tt).
  rewrite RCMap.release_nrm_unfold.
  change (MonadErr.nrm (Rec (RCMap.release_rec node_children)
    ([], RCMap.decrement (RCMap.decrement (RCMap.delete node_children shared_demo 1 (Node 1 2 2)) 2) 2)) tt Mf tt).
  rewrite RCMap.release_nrm_unfold; cbn; split; reflexivity.
Qed.

(* 第二个实例不是 TypeNode：payload 为“符号 + 任意长 owning 孩子表”。
   它只演示同一接口支持不同对象形状，不宣称已验证表达式匹配的 C 实现。
   地址 1 有三条均指向 2 的边，不能降成 set，也不能套用固定二叉节点。 *)
Module VariadicPayloadDemo <: RC_PAYLOAD_SIG.
  Definition node := (Z * list addr)%type.
  Definition children := @snd Z (list addr).
End VariadicPayloadDemo.
Module VariadicRCMapDemo := MakeRCMap VariadicPayloadDemo.
Module VariadicRCMapFactsDemo := RCMapFacts VariadicPayloadDemo VariadicRCMapDemo.

Definition variadic_demo : VariadicRCMapDemo.state :=
  RCMap.make
    (fun p => if Z.eq_dec p 1 then Some (10,[2;2;2])
              else if Z.eq_dec p 2 then Some (20,[]) else None)
    (fun p => if Z.eq_dec p 1 then 1 else if Z.eq_dec p 2 then 1 else 0)
    (fun p => if Z.eq_dec p 1 then 1 else if Z.eq_dec p 2 then 4 else 0)
    (fun p => if Z.eq_dec p 1 then 1 else 0).

Lemma variadic_demo_nodes : forall p n,
  VariadicRCMapDemo.nodes variadic_demo p = Some n <->
  (p = 1 /\ n = (10,[2;2;2])) \/ (p = 2 /\ n = (20,[])).
Proof.
  intros p n.
  change ((if Z.eq_dec p 1 then Some (10,[2;2;2])
    else if Z.eq_dec p 2 then Some (20,[]) else None) = Some n <->
    (p = 1 /\ n = (10,[2;2;2])) \/ (p = 2 /\ n = (20,[]))).
  destruct (Z.eq_dec p 1) as [->|H1].
  - split.
    + intro H; injection H as H; left; split; [reflexivity|symmetry; exact H].
    + intros [[_ H]|[H _]]; [rewrite H; reflexivity|discriminate H].
  - destruct (Z.eq_dec p 2) as [->|H2].
    + split.
      * intro H; injection H as H; right; split; [reflexivity|symmetry; exact H].
      * intros [[H _]|[_ H]]; [discriminate H|rewrite H; reflexivity].
    + split; [discriminate|intros [[H _]|[H _]]; contradiction].
Qed.

Example variadic_demo_valid : VariadicRCMapDemo.valid variadic_demo.
Proof.
  split.
  - exists [(1,(10,[2;2;2]));(2,(20,[]))]; split.
    + split.
      * cbn; repeat constructor; cbn; intuition congruence.
      * intros p n; change (In (p,n) [(1,(10,[2;2;2]));(2,(20,[]))] <->
          VariadicRCMapDemo.nodes variadic_demo p = Some n).
        rewrite variadic_demo_nodes; cbn; split.
        -- intros [H|[H|H]]; [inversion H; subst; auto|inversion H; subst; auto|contradiction].
        -- intros [[-> ->]|[-> ->]]; auto.
    + intro p; unfold RCMap.incoming, variadic_demo; cbn -[Z.eq_dec].
      destruct (Z.eq_dec p 1), (Z.eq_dec p 2), (Z.eq_dec 2 p); subst;
        cbn -[Z.eq_dec]; try congruence; lia.
  - split.
    + intros p n q H Hq; apply variadic_demo_nodes in H.
      destruct H as [[-> ->]|[-> ->]]; cbn in Hq.
      * destruct Hq as [<-|[<-|[<-|Hq]]]; try contradiction;
          exists (20,[]); reflexivity.
      * contradiction.
    + split.
      * exists (fun p => if Z.eq_dec p 1 then 1 else 0); split.
        -- intros p n H; destruct (Z.eq_dec p 1); lia.
        -- intros p n q H Hq; apply variadic_demo_nodes in H.
           destruct H as [[-> ->]|[-> ->]]; cbn in Hq.
           ++ destruct Hq as [<-|[<-|[<-|Hq]]]; try contradiction; cbn; lia.
           ++ contradiction.
      * split.
        -- intro p; unfold variadic_demo; cbn -[Z.eq_dec];
             destruct (Z.eq_dec p 1), (Z.eq_dec p 2); lia.
        -- split.
           ++ intros p n H; apply variadic_demo_nodes in H;
                destruct H as [[-> ->]|[-> ->]]; vm_compute; intuition congruence.
           ++ split.
              ** intros p H; unfold variadic_demo in *; cbn -[Z.eq_dec] in *;
                   destruct (Z.eq_dec p 1), (Z.eq_dec p 2); try discriminate; auto.
              ** intro p; unfold variadic_demo; cbn -[Z.eq_dec];
                   destruct (Z.eq_dec p 1), (Z.eq_dec p 2); lia.
Qed.

Example variadic_demo_retain_valid :
  VariadicRCMapDemo.valid (VariadicRCMapDemo.retain variadic_demo 2).
Proof.
  apply VariadicRCMapFactsDemo.retain_valid; [apply variadic_demo_valid|].
  right; split; [exists (20,[]); reflexivity | vm_compute; auto].
Qed.

Example variadic_demo_repeated_release_accounting :
  let M1 := VariadicRCMapDemo.delete variadic_demo 1 (10,[2;2;2]) in
  let M2 := VariadicRCMapDemo.decrement M1 2 in
  let M3 := VariadicRCMapDemo.decrement M2 2 in
  let M4 := VariadicRCMapDemo.decrement M3 2 in
  VariadicRCMapDemo.reserved M1 2 = 3 /\
  VariadicRCMapDemo.reserved M4 2 = 0 /\
  VariadicRCMapDemo.counts M1 2 = 4 /\
  VariadicRCMapDemo.counts M4 2 = 1 /\
  VariadicRCMapDemo.nodes M4 1 = None /\
  VariadicRCMapDemo.nodes M4 2 = Some (20,[]).
Proof. vm_compute; repeat split; reflexivity. Qed.

Example variadic_demo_repeated_release_execution :
  let M1 := VariadicRCMapDemo.delete variadic_demo 1 (10,[2;2;2]) in
  let M2 := VariadicRCMapDemo.decrement M1 2 in
  let M3 := VariadicRCMapDemo.decrement M2 2 in
  let M4 := VariadicRCMapDemo.decrement M3 2 in
  MonadErr.nrm (VariadicRCMapDemo.release_program variadic_demo 1)
    tt M4 tt.
Proof.
  cbn zeta.
  change (MonadErr.nrm (RCMap.release_program VariadicPayloadDemo.children
    variadic_demo 1) tt
    (RCMap.decrement (RCMap.decrement (RCMap.decrement
      (RCMap.delete VariadicPayloadDemo.children variadic_demo 1
        (10,[2;2;2])) 2) 2) 2) tt).
  unfold RCMap.release_program.
  do 5 (apply RCMap.release_nrm_unfold; cbn).
  split; reflexivity.
Qed.



