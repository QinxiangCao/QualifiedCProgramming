
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.

Import SetsNotation.

Local Open Scope sets.
Local Open Scope Z.

Section floyd.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {step_aux_unique: StepUniqueDirected G V E}
        {g: G}
        {g_valid: gvalid g}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).

(* floyd算法允许存在负权，但是不允许存在负权回路 *)

Context {non_neg_loop: forall u p, valid_epath g u p u -> Z_op_le (Some 0) (epath_weight g p)}.

Theorem floyd_warshall_update_start: 
  forall S k v d_kv, 
    min_value_weight_epath_in_vset g k v S d_kv <->
    min_value_weight_epath_in_vset g k v (S ∪ [k]) d_kv.
Proof.
  intros. split; intros.
  - unfold min_value_weight_epath_in_vset in *.
    destruct H as [[[p [[Hpvalid Hpmin]]]]|[]].
    (* 一般情况：最短路径存在 *)
    * left; split; auto.
      exists p; split; auto; split.
      eapply (is_epath_through_vset_subset) with (S1:=S); [eauto|left; auto].
      intros q Hq. 
      pose proof Hq as Hq'.
      eapply is_epath_through_vset_split in Hq as [Hq|[p_pre [p_mid [p_suf [H_pre [H_suf [H_mid Heq]]]]]]]; auto.
      (* 路径 q 分解: k --p_pre--> k --p_mid--> k --p_suf--> v
                      \___≥0环____/\____≥0环___/\___通过S___/
         消除两个非负环后: k ----------------------p_suf--> v 更优 *)
      destruct H_mid as [H_mid _]; apply non_neg_loop in H_mid.
      destruct H_pre as [H_pre _]; apply non_neg_loop in H_pre. 
      apply Hpmin in H_suf.
      
      rewrite Heq; rewrite !epath_weight_app_assoc. 
      eapply Z_op_le_trans; [apply H_suf|].
      rewrite <- Z_op_plus_O_l at 1.
      apply Z_op_plus_mono; auto.
      rewrite <- Z_op_plus_O_l at 1.
      apply Z_op_plus_mono; [auto|apply Z_op_le_refl].

    (* 特殊情况：路径不存在 *)
    * right; split; auto.
      intros q Hq.
      rewrite Z_op_none_le_iff.
      eapply is_epath_through_vset_split in Hq as [Hq|[p_pre [p_mid [p_suf [H_pre [H_suf [H_mid Heq]]]]]]]; auto.
      + apply H in Hq.
        rewrite Z_op_none_le_iff in Hq. auto.
      + apply H in H_suf.
        rewrite Z_op_none_le_iff in H_suf.
        rewrite Heq; rewrite !epath_weight_app_assoc;
        rewrite H_suf; rewrite !Z_op_plus_none_r; reflexivity.


  - unfold min_value_weight_epath_in_vset in *.
    destruct H as [[[p [[Hpvalid Hpmin]]]]|[]].
    (* 一般情况：最短路径存在 *)
    * pose proof Hpvalid as Hp'. 
      eapply is_epath_through_vset_split in Hpvalid as [|[p_pre [p_mid [p_suf [H_pre [H_suf [H_mid Heq]]]]]]]; auto. 
      + left; split; auto. 
        exists p; split; auto; split; auto. 
        intros q Hq. 
        eapply is_epath_through_vset_subset with (S2:=S ∪ [k]) in Hq; [|left; auto].
        apply Hpmin; auto.
      + (* 最优路径 p 分解: k --p_pre--> k --p_mid--> k --p_suf--> v
                           \___≥0环____/\____≥0环____/\___通过S___/
           若环非零则与 p 最短矛盾；若都是零环则取 p_suf 作为 S 中最优路径 *)


        destruct (classic (Z_op_le (epath_weight g (p_pre ++ p_mid)) (Some 0))).
        (* 当 p_pre ++ p_mid 是正环时 *)
        2: { 
          destruct d_kv. 2: { 
            right; split; auto.
            intros q Hq.
            rewrite Z_op_none_le_iff.
            eapply is_epath_through_vset_subset with (S2:=S ∪ [k]) in Hq;
            [|left; auto].
            apply Hpmin in Hq; rewrite H in Hq; 
            rewrite Z_op_none_le_iff in Hq; auto.
          } exfalso. 
          apply is_epath_through_vset_subset with (S2:=S ∪ [k]) in H_suf; [|left; auto]. 
          apply Hpmin in H_suf; auto. 
          rewrite Heq in H_suf. 
          rewrite app_assoc in H_suf. 
          rewrite epath_weight_app_assoc in H_suf. 
          destruct (epath_weight g (p_pre ++ p_mid)) eqn: Heq1; 
          destruct (epath_weight g p_suf) eqn: Heq2; simpl in *; try lia. 
          all: 
          (rewrite Heq in H;
          rewrite app_assoc in H; 
          rewrite epath_weight_app_assoc in H;
          rewrite Heq1, Heq2 in H;
          inversion H). } 

        (* 当 p_pre ++ p_mid 是零环时 *)
        assert (epath_weight g (p_pre ++ p_mid) = Some 0). {
          destruct H_pre as [H_pre _].
          destruct H_mid as [H_mid _]. 
          apply non_neg_loop in H_pre, H_mid. 
          rewrite epath_weight_app_assoc. 
          rewrite epath_weight_app_assoc in H1. 
          destruct (epath_weight g p_pre); destruct (epath_weight g p_mid); simpl in *; try lia.
          f_equal; lia. } 
        assert (H_suf_weight: epath_weight g p_suf = d_kv). {
          rewrite Heq in H. 
          rewrite app_assoc in H. 
          rewrite epath_weight_app_assoc in H. 
          rewrite H2 in H. 
          rewrite <- H. 
          rewrite Z_op_plus_O_l. 
          reflexivity. } 
        left; split; auto. 
        exists p_suf; split; auto. 
        split; auto. 
        intros q Hq.
        eapply is_epath_through_vset_subset with (S2:=S ∪ [k]) in Hq; [|left; auto]. 
        apply Hpmin in Hq. 
        rewrite H_suf_weight, <- H; auto.

    (* 特殊情况：路径不存在 *)
    * right; split; auto.
      intros q Hq.
      rewrite Z_op_none_le_iff.
      eapply is_epath_through_vset_subset with (S2:=S ∪ [k]) in Hq;
      [|left; auto].
      apply H in Hq; rewrite Z_op_none_le_iff in Hq; auto. 
  Unshelve. auto. auto. auto.
Qed.

Theorem floyd_warshall_update_end: 
  forall S u k d_uk, 
    min_value_weight_epath_in_vset g u k S d_uk <->
    min_value_weight_epath_in_vset g u k (S ∪ [k]) d_uk. 
Proof. 
  intros. split; intros. 
  - unfold min_value_weight_epath_in_vset in *. 
    destruct H as [[[p [[Hpvalid Hpmin]]]]|[]].
    (* 一般情况：最短路径存在 *)
    * left; split; auto. 
      exists p; split; auto; split. 
      eapply (is_epath_through_vset_subset) with (S1:=S); [eauto|left; auto]. 
      intros q Hq. 
      pose proof Hq as Hq'.
      eapply is_epath_through_vset_split in Hq as [Hq|[p_pre [p_mid [p_suf [H_pre [H_suf [H_mid Heq]]]]]]]; auto.
      (* 路径 q 分解: u --p_pre--> k --p_mid--> k --p_suf--> k
                      \___通过S___/\___≥0环____/\___≥0环____/
         消除两个非负环后: u --p_pre----------------------> k 更优 *)
      destruct H_mid as [H_mid _]; apply non_neg_loop in H_mid.
      destruct H_suf as [H_suf _]; apply non_neg_loop in H_suf.
      apply Hpmin in H_pre.
      
      rewrite Heq; rewrite !epath_weight_app_assoc.
      eapply Z_op_le_trans; [apply H_pre|].
      rewrite <- Z_op_plus_O_r at 1.
      apply Z_op_plus_mono; [apply Z_op_le_refl|].
      rewrite <- Z_op_plus_O_r at 1.
      apply Z_op_plus_mono; auto.


    (* 特殊情况：路径不存在 *)
    * right; split; auto.
      intros q Hq. 
      rewrite Z_op_none_le_iff. 
      eapply is_epath_through_vset_split in Hq as [Hq|[p_pre [p_mid [p_suf [H_pre [H_suf [H_mid Heq]]]]]]]; auto.
      + apply H in Hq. 
        rewrite Z_op_none_le_iff in Hq. auto. 
      + apply H in H_pre. 
        rewrite Z_op_none_le_iff in H_pre. 
        rewrite Heq; rewrite epath_weight_app_assoc; 
        rewrite H_pre; reflexivity. 


  - unfold min_value_weight_epath_in_vset in *. 
    destruct H as [[[p [[Hpvalid Hpmin]]]]|[]].  
    * pose proof Hpvalid as Hp'.
      eapply is_epath_through_vset_split in Hpvalid as [|[p_pre [p_mid [p_suf [H_pre [H_suf [H_mid Heq]]]]]]]; auto.
      + left; split; auto.
        exists p; split; auto; split; auto.
        intros q Hq.
        eapply is_epath_through_vset_subset with (S2:=S ∪ [k]) in Hq; [|left; auto].
        apply Hpmin; auto.
      + (* 最优路径 p 分解: u --p_pre--> k --p_mid--> k --p_suf--> k
                           \___通过S___/\___≥0环____/\___≥0环____/
           若环非零则与 p 最短矛盾；若都是零环则取 p_pre 作为 S 中最优路径 *)


        destruct (classic (Z_op_le (epath_weight g (p_mid ++ p_suf)) (Some 0))).
        (* 当 p_mid ++ p_suf 是正环时 *)
        2: {
          destruct d_uk. 2: {
            right; split; auto.
            intros q Hq.
            rewrite Z_op_none_le_iff.
            eapply is_epath_through_vset_subset with (S2:=S ∪ [k]) in Hq;
            [|left; auto].
            apply Hpmin in Hq; rewrite H in Hq;
            rewrite Z_op_none_le_iff in Hq; auto.
          } exfalso.
          apply is_epath_through_vset_subset with (S2:=S ∪ [k]) in H_pre; [|left; auto].
          apply Hpmin in H_pre; auto.
          rewrite Heq in H_pre.
          rewrite epath_weight_app_assoc in H_pre.
          destruct (epath_weight g p_pre) eqn: Heq1;
          destruct (epath_weight g (p_mid ++ p_suf)) eqn: Heq2; simpl in *; try lia.
          all:
          (rewrite Heq in H;
          rewrite epath_weight_app_assoc in H;
          rewrite Heq1, Heq2 in H;
          inversion H). } 

        (* 当 p_mid ++ p_suf 是零环时 *)
        assert (epath_weight g (p_mid ++ p_suf) = Some 0). {
          destruct H_mid as [H_mid _].
          destruct H_suf as [H_suf _].
          apply non_neg_loop in H_mid, H_suf.
          rewrite epath_weight_app_assoc.
          rewrite epath_weight_app_assoc in H1.
          destruct (epath_weight g p_mid); destruct (epath_weight g p_suf); simpl in *; try lia.
          f_equal; lia. }
        assert (H_pre_weight: epath_weight g p_pre = d_uk). {
          rewrite Heq in H.
          rewrite epath_weight_app_assoc in H.
          rewrite H2 in H.
          rewrite <- H.
          rewrite Z_op_plus_O_r.
          reflexivity. }
        left; split; auto.
        exists p_pre; split; auto.
        split; auto.
        intros q Hq.
        eapply is_epath_through_vset_subset with (S2:=S ∪ [k]) in Hq; [|left; auto].
        apply Hpmin in Hq.
        rewrite H_pre_weight, <- H; auto.

    * right; split; auto.
      intros q Hq. 
      rewrite Z_op_none_le_iff. 
      eapply is_epath_through_vset_subset with (S2:=S ∪ [k]) in Hq; 
      [|left; auto]. 
      apply H in Hq; rewrite Z_op_none_le_iff in Hq; auto.
  Unshelve. auto. auto. auto.
Qed.


Theorem floyd_warshall_step_spec :
  forall S u v k d_uvS d_ukS d_kvS, 
    min_value_weight_epath_in_vset g u v S d_uvS ->
    min_value_weight_epath_in_vset g u k S d_ukS ->
    min_value_weight_epath_in_vset g k v S d_kvS ->
    min_value_weight_epath_in_vset g u v (S ∪ [k]) (Z_op_min d_uvS (Z_op_plus d_ukS d_kvS)).
Proof.
  intros S u v k d_uvS d_ukS d_kvS H_uvS H_ukS H_kvS. 
  destruct H_uvS as [ [H_uvS Huv_none] | [ H_uv_separate Huv_none] ]; 
  destruct H_ukS as [ [H_ukS Huk_none] | [ H_uk_separate Huk_none] ]; 
  destruct H_kvS as [ [H_kvS Hkv_none] | [ H_kv_separate Hkv_none] ].

  { (* case: d_uvS = Some, d_ukS = Some, d_kvS = Some *)
    destruct H_uvS as [p_uv [[Hp_uv Hp_uv_min] Hp_uv_weight]]. 
    destruct H_ukS as [p_uk [[Hp_uk Hp_uk_min] Hp_uk_weight]]. 
    destruct H_kvS as [p_kv [[Hp_kv Hp_kv_min] Hp_kv_weight]]. 
    left; split. 
    2: { destruct ((Z_op_min d_uvS (Z_op_plus d_ukS d_kvS))); simpl; auto. } 
    destruct (Z_op_le_ge_cases d_uvS (Z_op_plus d_ukS d_kvS)) as [H_le | H_ge].
    - exists p_uv; split. 
      2: { 
        rewrite Hp_uv_weight.  
        destruct (d_uvS); destruct (Z_op_plus d_ukS d_kvS); simpl in *; auto. 
        f_equal. lia. exfalso; auto.
      } 
      split. 
      1: { 
        eapply is_epath_through_vset_subset with (S1:=S); eauto. 
        left; auto. } 
      intros p Hp. 
      eapply is_epath_through_vset_split in Hp as [|[p_uk' [p_loop [p_kv' [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto. 
      subst. 
      rewrite !epath_weight_app_assoc. 
      apply Hp_uk_min in H_uk_valid. 
      apply Hp_kv_min in H_vk_valid. 
      apply (Z_op_le_trans _ _ _ H_le). 
      apply Z_op_plus_mono; auto. 
      rewrite <- Z_op_plus_O_l at 1. 
      apply Z_op_plus_mono; auto. 
      destruct H_loop_valid as [H_loop_valid _].
      apply non_neg_loop in H_loop_valid. auto.
    - exists (p_uk ++ p_kv); split. 
      2: { 
        rewrite epath_weight_app_assoc. 
        rewrite Hp_uk_weight, Hp_kv_weight.
        destruct (d_uvS); destruct (Z_op_plus d_ukS d_kvS); simpl in *; auto. 
        f_equal. lia. exfalso; auto.
      } 
      split. 
      1: {
        eapply is_epath_through_vset_union; auto.
      } 
      intros p Hp. 
      eapply is_epath_through_vset_split in Hp as [|[p_uk' [p_loop [p_kv' [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto. 
      * rewrite epath_weight_app_assoc. 
        rewrite Hp_uk_weight, Hp_kv_weight. 
        apply (Z_op_le_trans _ _ _ H_ge). 
        eapply Hp_uv_min in H; subst; auto. 
      * rewrite Heq. 
        rewrite !epath_weight_app_assoc. 
        apply Z_op_plus_mono; auto. 
        rewrite <- Z_op_plus_O_l at 1. 
        apply Z_op_plus_mono; auto. 
        destruct H_loop_valid as [H_loop_valid _].
        apply non_neg_loop in H_loop_valid. auto. 
  }

  { (* case: d_uvS = Some, d_ukS = Some, d_kvS = None *)
    destruct H_uvS as [p_uv [[Hp_uv Hp_uv_min] Hp_uv_weight]]. 
    destruct H_ukS as [p_uk [[Hp_uk Hp_uk_min] Hp_uk_weight]]. 
    rewrite Hkv_none. 
    rewrite Z_op_plus_none_r. 
    rewrite Z_op_min_none_r. 
    left; split; auto. 
    exists p_uv; split; auto. 
    split;[eapply is_epath_through_vset_subset with (S1:=S); eauto; left; auto|]. 
    intros p Hp. 
    eapply is_epath_through_vset_split in Hp as [|[p_uk' [p_loop [p_kv' [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto. 
    eapply H_kv_separate in H_vk_valid. 
    rewrite Z_op_none_le_iff in H_vk_valid. 
    subst; rewrite !epath_weight_app_assoc. 
    rewrite H_vk_valid. 
    rewrite !Z_op_plus_none_r. 
    apply Z_op_le_none_r. 
  } 
  
  { (* case: d_uvS = Some, d_ukS = None, d_kvS = Some *)
    destruct H_uvS as [p_uv [[Hp_uv Hp_uv_min] Hp_uv_weight]]. 
    destruct H_kvS as [p_kv [[Hp_kv Hp_kv_min] Hp_kv_weight]]. 
    rewrite Huk_none. 
    rewrite Z_op_min_none_r. 
    left; split; auto. 
    exists p_uv; split; auto. 
    split;[eapply is_epath_through_vset_subset with (S1:=S); eauto; left; auto|]. 
    intros p HpSk. 
    eapply is_epath_through_vset_split in HpSk as [|[p_uk' [p_loop [p_kv' [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto. 
    apply H_uk_separate in H_uk_valid; rewrite Z_op_none_le_iff in H_uk_valid.
    subst; rewrite !epath_weight_app_assoc. 
    rewrite H_uk_valid. 
    simpl. 
    apply Z_op_le_none_r. 
  } 
  
  { (* case: d_uvS = None, d_ukS = Some, d_kvS = Some *)
    destruct H_uvS as [p_uv [[Hp_uv Hp_uv_min] Hp_uv_weight]]. 
    rewrite Huk_none, Hkv_none. 
    rewrite Z_op_min_none_r. 
    left; split; auto. 
    exists p_uv; split; auto. 
    split;[eapply is_epath_through_vset_subset with (S1:=S); eauto; left; auto|]. 
    intros p HpSk. 
    eapply is_epath_through_vset_split in HpSk as [|[p_uk' [p_loop [p_kv' [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto. 
    apply H_uk_separate in H_uk_valid; rewrite Z_op_none_le_iff in H_uk_valid.
    subst; rewrite !epath_weight_app_assoc. 
    rewrite H_uk_valid. 
    simpl. 
    apply Z_op_le_none_r. 
  } 
  
  { (* case: d_uvS = None, d_ukS = Some, d_kvS = Some *)
    destruct H_ukS as [p_uk [[Hp_uk Hp_uk_min] Hp_uk_weight]]. 
    destruct H_kvS as [p_kv [[Hp_kv Hp_kv_min] Hp_kv_weight]]. 
    left; split; [|apply Z_op_le_none_r]. 
    exists (p_uk ++ p_kv); split. 
    2: { rewrite epath_weight_app_assoc. 
      rewrite Hp_uk_weight, Hp_kv_weight. 
      rewrite Huv_none. destruct (Z_op_plus d_ukS d_kvS); auto. } 
    split;[eapply is_epath_through_vset_union; auto|]. 
    intros p Hp. 
    eapply is_epath_through_vset_split in Hp as [|[p_uk' [p_loop [p_kv' [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto. 
    * apply H_uv_separate in H.  
      rewrite Z_op_none_le_iff in H. 
      rewrite H. 
      apply Z_op_le_none_r.
    * rewrite Heq. 
      rewrite !epath_weight_app_assoc. 
      apply Z_op_plus_mono; auto. 
      rewrite <- Z_op_plus_O_l at 1. 
      apply Z_op_plus_mono; auto. 
      destruct H_loop_valid as [H_loop_valid _].
      apply non_neg_loop in H_loop_valid. auto. 
  } 
  
  { (* case: d_uvS = None, d_ukS = Some, d_kvS = None *)
    destruct H_ukS as [p_uk [[Hp_uk Hp_uk_min] Hp_uk_weight]]. 
    rewrite Hkv_none, Huv_none. 
    rewrite Z_op_plus_none_r. 
    rewrite Z_op_min_none_r. 
    right; split; auto. 
    intros p Hp. 
    eapply is_epath_through_vset_split in Hp as [|[p_uk' [p_loop [p_kv' [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto.
    subst; rewrite !epath_weight_app_assoc. 
    apply H_kv_separate in H_vk_valid. 
    rewrite Z_op_none_le_iff in H_vk_valid. 
    rewrite H_vk_valid. 
    rewrite !Z_op_plus_none_r. 
    reflexivity.
  }

  { (* case: d_uvS = None, d_ukS = None, d_kvS = Some *)
    destruct H_kvS as [p_kv [[Hp_kv Hp_kv_min] Hp_kv_weight]]. 
    rewrite Huk_none, Huv_none. 
    simpl.
    right; split; auto. 
    intros p Hp. 
    eapply is_epath_through_vset_split in Hp as [|[p_uk' [p_loop [p_kv' [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto.
    subst; rewrite !epath_weight_app_assoc. 
    apply H_uk_separate in H_uk_valid. 
    rewrite Z_op_none_le_iff in H_uk_valid. 
    rewrite H_uk_valid. 
    simpl. exact I. 
  }
  
  { (* case: d_uvS = None, d_ukS = None, d_kvS = None *)
    right; split; [| subst; simpl; auto]. 
    intros p HpSk. 
    eapply is_epath_through_vset_split in HpSk as [|[p_uk [p_loop [p_kv [H_uk_valid [H_vk_valid [H_loop_valid Heq]]]]]]]; auto. 
    apply H_uk_separate in H_uk_valid; rewrite Z_op_none_le_iff in H_uk_valid. 
    apply H_kv_separate in H_vk_valid; rewrite Z_op_none_le_iff in H_vk_valid.
    subst. 
    rewrite !epath_weight_app_assoc. 
    rewrite H_uk_valid, H_vk_valid; simpl. exact I.
  } 
  Unshelve. auto. auto. auto. auto.
  auto. auto. auto. auto.
  auto. auto. auto. 
Qed.

End floyd.
