Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From AUXLib Require Import Axioms.
From SumLib Require Import Sum.
From SumLib Require Import ZRange.

Import ListNotations.

Local Open Scope Z_scope.

(** * 额外的 [Finite] 实例 *)

(** ** 1. 有限集合的子集 *)

(** 如果 [P] 有限，那么 [fun x => P x /\ Q x] 也有限，
    枚举通过对 [Q] 的可判定性过滤 [enum P] 得到。 *)
#[export] Instance Finite_subset
    {A : Type} (P Q : A -> Prop) `{Finite A P} :
  Finite (fun x => P x /\ Q x).
Proof.
  refine {| enum :=
    filter (fun x => if prop_dec (Q x) then true else false)
           (@enum A P _) |}.
  - intros x.
    rewrite filter_In.
    split.
    + intros [HP HQ].
      split.
      * apply (proj1 (enum_ok x)). exact HP.
      * destruct (prop_dec (Q x)) as [_ | Hnot]; [reflexivity | contradiction].
    + intros [Hin Htest].
      split.
      * apply (proj2 (enum_ok x)). exact Hin.
      * destruct (prop_dec (Q x)) as [HQ | Hnot]; [exact HQ | discriminate].
  - apply NoDup_filter_bool.
    apply enum_nodup.
Defined.

(** ** 2. 两个有限集合的乘积 *)

Lemma NoDup_list_prod {A B : Type} (l1 : list A) (l2 : list B) :
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
  intros Hl1 Hl2.
  induction l1 as [|a l1 IH]; simpl.
  - constructor.
  - inversion Hl1 as [|? ? Hnotin Hl1']; subst.
    apply NoDup_app.
    + (* NoDup (map (pair a) l2) *)
      clear IH Hl1' Hnotin.
      induction l2 as [|b l2 IH2]; simpl.
      * constructor.
      * inversion Hl2 as [|? ? Hnotin2 Hl2']; subst.
        constructor.
        -- intro Hin. apply in_map_iff in Hin as [b' [Heq Hin']].
           inversion Heq; subst. contradiction.
        -- apply IH2. exact Hl2'.
    + apply IH. exact Hl1'.
    + (* disjointness between (map (pair a) l2) and (list_prod l1 l2) *)
      intros [x y] Hin1 Hin2.
      apply in_map_iff in Hin1 as [b [Heq Hin']].
      inversion Heq; subst.
      apply in_prod_iff in Hin2 as [Hinx _].
      contradiction.
Qed.

#[export] Instance Finite_prod
    {A B : Type} (PA : A -> Prop) (PB : B -> Prop)
    `{Finite A PA} `{Finite B PB} :
  Finite (fun p : A * B => PA (fst p) /\ PB (snd p)).
Proof.
  refine {| enum := list_prod (@enum A PA _) (@enum B PB _) |}.
  - intros [a b]; simpl.
    rewrite in_prod_iff.
    split.
    + intros [HA HB].
      split.
      * apply (proj1 (enum_ok a)). exact HA.
      * apply (proj1 (enum_ok b)). exact HB.
    + intros [Hina Hinb].
      split.
      * apply (proj2 (enum_ok a)). exact Hina.
      * apply (proj2 (enum_ok b)). exact Hinb.
  - apply NoDup_list_prod; apply enum_nodup.
Defined.

(** ** 3. 有限字母表上定长序列 *)

(** [all_lists k l] 枚举所有长度为 [k]、元素取自 [l] 的列表。 *)
Fixpoint all_lists {A : Type} (k : nat) (l : list A) : list (list A) :=
  match k with
  | O => [ [] ]
  | S k' => flat_map (fun x => map (cons x) (all_lists k' l)) l
  end.

Lemma in_all_lists {A : Type} (l : list A) :
  forall k (a : list A),
    In a (all_lists k l) <-> length a = k /\ Forall (fun x => In x l) a.
Proof.
  induction k as [|k IH]; intros a; simpl.
  - split.
    + intros [Heq | []]. subst. split; [reflexivity | constructor].
    + intros [Hlen _]. destruct a; simpl in Hlen; [left; reflexivity | discriminate].
  - rewrite in_flat_map.
    split.
    + intros [x [Hinx Hin]].
      apply in_map_iff in Hin as [a' [Heq Hin']].
      subst a.
      apply IH in Hin' as [Hlen Hfa].
      simpl. split.
      * f_equal. exact Hlen.
      * constructor; assumption.
    + intros [Hlen Hfa].
      destruct a as [|x a]; simpl in Hlen; [discriminate |].
      inversion Hfa as [|? ? Hinx Hfa']; subst.
      exists x. split; [exact Hinx |].
      apply in_map_iff. exists a. split; [reflexivity |].
      apply IH. split; [simpl in Hlen; lia | exact Hfa'].
Qed.

(** 把头元素 cons 到一个固定列表族上，再对一个无重复的头列表做 flat_map，
    结果无重复（头元素区分各组）。 *)
Lemma NoDup_flat_map_cons {A : Type} (base : list (list A)) (l : list A) :
  NoDup base -> NoDup l ->
  NoDup (flat_map (fun x => map (cons x) base) l).
Proof.
  intros Hbase Hl.
  induction l as [|x l IHl]; simpl.
  - constructor.
  - inversion Hl as [|? ? Hnotin Hl']; subst.
    apply NoDup_app.
    + apply FinFun.Injective_map_NoDup; [| exact Hbase].
      intros u v Heq. injection Heq; auto.
    + apply IHl; exact Hl'.
    + intros a Hin1 Hin2.
      apply in_map_iff in Hin1 as [a1 [Heq1 Hin1']].
      apply in_flat_map in Hin2 as [y [Hiny Hin2']].
      apply in_map_iff in Hin2' as [a2 [Heq2 Hin2'']].
      subst a.
      injection Heq2 as Hxy _.
      subst y. contradiction.
Qed.

Lemma NoDup_all_lists {A : Type} (l : list A) :
  forall k, NoDup l -> NoDup (all_lists k l).
Proof.
  induction k as [|k IH]; intros Hl; simpl.
  - constructor; [intros [] | constructor].
  - apply NoDup_flat_map_cons.
    + apply IH. exact Hl.
    + exact Hl.
Qed.

#[export] Instance Finite_bounded_lists
    {A : Type} (n : Z) (Alpha : A -> Prop) `{Finite A Alpha} :
  Finite (fun a : list A => Zlength a = n /\ Forall Alpha a).
Proof.
  refine {| enum :=
    if Z.ltb n 0 then []
    else all_lists (Z.to_nat n) (@enum A Alpha _) |}.
  - intros a.
    destruct (Z.ltb n 0) eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      split.
      * intros [Hzl _].
        pose proof (Zlength_nonneg a). lia.
      * intros [].
    + apply Z.ltb_ge in Hlt.
      rewrite in_all_lists.
      split.
      * intros [Hzl Hfa].
        split.
        -- rewrite Zlength_correct in Hzl. lia.
        -- rewrite Forall_forall in Hfa |- *.
           intros x Hin. apply (proj1 (enum_ok x)). apply Hfa. exact Hin.
      * intros [Hlen Hfa].
        split.
        -- rewrite Zlength_correct. lia.
        -- rewrite Forall_forall in Hfa |- *.
           intros x Hin. apply (proj2 (enum_ok x)). apply Hfa. exact Hin.
  - destruct (Z.ltb n 0).
    + constructor.
    + apply NoDup_all_lists. apply enum_nodup.
Defined.

(** P088 形状的健全性检查：定长、元素落在 [0,5] 的整数列表集合是有限的。 *)
Local Instance finite_Z_0_5 : Finite (fun x : Z => 0 <= x <= 5).
Proof.
  refine {| enum := Zrange 0 6 |}.
  - intros x. rewrite <- In_Zrange. lia.
  - apply NoDup_Zrange.
Defined.

Example finite_P088_shape (n : Z) :
  Finite (fun a : list Z => Zlength a = n /\ Forall (fun x => 0 <= x <= 5) a).
Proof.
  apply (Finite_bounded_lists n (fun x => 0 <= x <= 5)).
Defined.

(** ** 4. 幂集 —— 有限集合的子集族 *)

(** [sublists l] 枚举 [l] 的全部子列表（幂集）。 *)
Fixpoint sublists {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [ [] ]
  | x :: l' =>
      let s := sublists l' in
      s ++ map (cons x) s
  end.

(** [s] 是 [l] 的子列表，意味着 [s] 的元素都来自 [l]。 *)
Lemma sublists_incl {A : Type} (l : list A) :
  forall s, In s (sublists l) -> forall x, In x s -> In x l.
Proof.
  induction l as [|y l IH]; intros s Hs x Hx; simpl in *.
  - destruct Hs as [Heq | []]. subst s. inversion Hx.
  - apply in_app_or in Hs as [Hs | Hs].
    + right. apply (IH s Hs x Hx).
    + apply in_map_iff in Hs as [s' [Heq Hs']]. subst s.
      destruct Hx as [Hx | Hx].
      * left. exact Hx.
      * right. apply (IH s' Hs' x Hx).
Qed.

(** 过滤得到的子列表确实在 [sublists l] 中。 *)
Lemma filter_in_sublists {A : Type} (l : list A) :
  forall (sel : A -> bool), In (filter sel l) (sublists l).
Proof.
  induction l as [|y l IH]; intros sel; simpl.
  - left. reflexivity.
  - destruct (sel y) eqn:Hsel.
    + apply in_or_app. right.
      apply in_map_iff. exists (filter sel l). split; [reflexivity | apply IH].
    + apply in_or_app. left. apply IH.
Qed.

(** 在 NoDup 列表上，子列表是无重复的。 *)
Lemma sublists_NoDup_elts {A : Type} (l : list A) :
  NoDup l -> forall s, In s (sublists l) -> NoDup s.
Proof.
  induction l as [|y l IH]; intros Hl s Hs; simpl in Hs.
  - destruct Hs as [Heq | []]. subst. constructor.
  - inversion Hl as [|? ? Hnotin Hl']; subst.
    apply in_app_or in Hs as [Hs | Hs].
    + apply (IH Hl' s Hs).
    + apply in_map_iff in Hs as [s' [Heq Hs']]. subst s.
      constructor.
      * intro Hin. apply sublists_incl with (l := l) (x := y) in Hs'; [contradiction | exact Hin].
      * apply (IH Hl' s' Hs').
Qed.

(** [sublists l] 自身无重复（当 [l] 无重复时）。 *)
Lemma NoDup_sublists {A : Type} (l : list A) :
  NoDup l -> NoDup (sublists l).
Proof.
  induction l as [|y l IH]; intros Hl; simpl.
  - constructor; [intros [] | constructor].
  - inversion Hl as [|? ? Hnotin Hl']; subst.
    apply NoDup_app.
    + apply IH. exact Hl'.
    + apply FinFun.Injective_map_NoDup; [| apply IH; exact Hl'].
      intros u v Heq. injection Heq; auto.
    + (* disjoint: a sublist of l never contains y, but every (cons y _) does *)
      intros s Hin1 Hin2.
      apply in_map_iff in Hin2 as [s' [Heq Hs']]. subst s.
      (* y is a member of (y :: s'), and (y :: s') in sublists l forces In y l *)
      apply Hnotin.
      apply (sublists_incl l (y :: s') Hin1 y).
      simpl. left. reflexivity.
Qed.

(** 关键引理：[l] 无重复时，它的子列表完全由 "包含哪些元素" 决定，
    即同成员的子列表必然相等（子列表是保序子序列）。 *)
Lemma sublists_eq_of_same_members {A : Type} (l : list A) :
  NoDup l ->
  forall s1 s2,
    In s1 (sublists l) -> In s2 (sublists l) ->
    (forall x, In x s1 <-> In x s2) ->
    s1 = s2.
Proof.
  induction l as [|y l IH]; intros Hl s1 s2 Hs1 Hs2 Hmem; simpl in Hs1, Hs2.
  - destruct Hs1 as [E1 | []]; destruct Hs2 as [E2 | []]; subst; reflexivity.
  - inversion Hl as [|? ? Hnotin Hl']; subst.
    (* For each si in sublists (y::l), either si in sublists l (no y),
       or si = y :: s' with s' in sublists l (has y). *)
    assert (Hcase : forall s, In s (sublists (y :: l)) ->
              (In s (sublists l) /\ ~ In y s) \/
              (exists s', s = y :: s' /\ In s' (sublists l) /\ ~ In y s')).
    { intros s Hs. simpl in Hs. apply in_app_or in Hs as [Hs | Hs].
      - left. split; [exact Hs |].
        intro Hy. apply Hnotin. apply (sublists_incl l s Hs y Hy).
      - right. apply in_map_iff in Hs as [s' [E Hs']]. subst s.
        exists s'. split; [reflexivity |]. split; [exact Hs' |].
        intro Hy. apply Hnotin. apply (sublists_incl l s' Hs' y Hy). }
    destruct (Hcase s1 Hs1) as [[Hin1 Hny1] | [s1' [E1 [Hin1 Hny1]]]];
    destruct (Hcase s2 Hs2) as [[Hin2 Hny2] | [s2' [E2 [Hin2 Hny2]]]].
    + (* both without y *)
      apply (IH Hl' s1 s2 Hin1 Hin2 Hmem).
    + (* s1 without y, s2 = y::s2' with y *)
      exfalso. subst s2. assert (In y s1) as Hy1.
      { apply Hmem. left. reflexivity. }
      contradiction.
    + exfalso. subst s1. assert (In y s2) as Hy2.
      { apply Hmem. left. reflexivity. }
      contradiction.
    + (* both = y :: _ *)
      subst s1 s2. f_equal.
      apply (IH Hl' s1' s2' Hin1 Hin2).
      intros x. split; intros Hx.
      * assert (In x (y :: s2')) as Hin.
        { apply Hmem. right. exact Hx. }
        destruct Hin as [E | Hin]; [subst x; contradiction | exact Hin].
      * assert (In x (y :: s1')) as Hin.
        { apply Hmem. right. exact Hx. }
        destruct Hin as [E | Hin]; [subst x; contradiction | exact Hin].
Qed.

(** 在某个谓词上局部单射的 [map] 保持 [NoDup]。 *)
Lemma Injective_map_NoDup_in {A B : Type} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros Hinj Hnd. induction l as [|a l IH]; simpl.
  - constructor.
  - inversion Hnd as [|? ? Hnotin Hnd']; subst.
    constructor.
    + intro Hin. apply in_map_iff in Hin as [b [Heq Hb]].
      assert (a = b).
      { apply Hinj; [left; reflexivity | right; exact Hb | symmetry; exact Heq]. }
      subst b. contradiction.
    + apply IH.
      * intros x y Hx Hy. apply Hinj; right; assumption.
      * exact Hnd'.
Qed.

#[export] Instance Finite_powerset
    {A : Type} (U : A -> Prop) `{Finite A U} :
  Finite (fun S : A -> Prop => forall x, S x -> U x).
Proof.
  refine {| enum :=
    map (fun l => fun x => In x l) (sublists (@enum A U _)) |}.
  - intros S.
    split.
    + intros Hsub.
      apply in_map_iff.
      exists (filter (fun x => if prop_dec (S x) then true else false) (@enum A U _)).
      split.
      * (* S = fun x => In x (filter ...) *)
        apply functional_extensionality. intros x.
        cbn beta.
        apply propositional_extensionality.
        rewrite filter_In.
        split.
        -- intros [_ Htest].
           destruct (prop_dec (S x)) as [HSx | Hn]; [exact HSx | discriminate].
        -- intros HSx.
           split.
           ++ apply (proj1 (enum_ok x)). apply Hsub. exact HSx.
           ++ destruct (prop_dec (S x)) as [_ | Hn]; [reflexivity | contradiction].
      * apply filter_in_sublists.
    + intros Hin.
      apply in_map_iff in Hin as [l [Heq Hl]].
      subst S.
      intros x Hx.
      apply (proj2 (enum_ok x)).
      apply sublists_incl with (l := @enum A U _) (s := l) (x := x); assumption.
  - (* NoDup of the mapped powerset *)
    apply Injective_map_NoDup_in.
    + (* injectivity on elements of (sublists enum) *)
      intros l1 l2 Hl1 Hl2 Heq.
      (* (fun x => In x l1) = (fun x => In x l2) -> same membership -> l1 = l2 *)
      assert (Hext : forall x, In x l1 <-> In x l2).
      { intros x.
        change ((fun y => In y l1) x <-> (fun y => In y l2) x).
        rewrite Heq. tauto. }
      apply (sublists_eq_of_same_members (@enum A U _) enum_nodup l1 l2 Hl1 Hl2 Hext).
    + apply NoDup_sublists. apply enum_nodup.
Defined.
