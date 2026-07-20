Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import glibc_slist_iter_back_2_rel_goal.
Require Import glibc_slist_iter_back_2_rel_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import glibc_slist_lib.
Require Import glibc_slist_iter_back_2_rel_lib.
Local Open Scope sac.

Lemma proof_of_glibc_slist_clean_iter_back_2_entail_wit_1 : glibc_slist_clean_iter_back_2_entail_wit_1.
Proof.
  pre_process.
  subst_eqs.
  Exists l1_low_level_spec.
  Exists (@nil Z).
  split_pure_spatial.
  - simpl sll.
    entailer!.
  - split_pure_and_solve.
    unfold glibc_slist_clean_iter_back_2_M in PreH2 at 1.
    prog_nf in PreH2.
    unfold glibc_slist_clean_iter_back_2_M_loop1_before in PreH2 at 1.
    prog_nf in PreH2.
    dump_pre_spatial.
    unfold glibc_slist_clean_iter_back_2_M_loop1.
    prog_nf.
    replace (app l1_low_level_spec nil) with l1_low_level_spec by (symmetry; apply app_nil_r).
    exact PreH2.
  Unshelve.
  all: entailer!.
Qed.
Lemma proof_of_glibc_slist_clean_iter_back_2_entail_wit_2 : glibc_slist_clean_iter_back_2_entail_wit_2.
Proof.
  pre_process.
  subst_eqs.
  destruct l1_1 as [| d l0].
  - simpl sllseg.
    Intros.
    subst; contradiction.
  - simpl sllseg.
    Intros y.
    Exists y.
    Exists ldone_2.
    Exists d.
    Exists l0.
    Exists (d :: l0).
    split_pure_spatial.
    + entailer!.
    + split_pure_and_solve.
      unfold glibc_slist_clean_iter_back_2_M_loop1 in PreH2 at 1.
      prog_nf in PreH2.
      unfold glibc_slist_clean_iter_back_2_M_loop1_aux in PreH2 at 1.
      prog_nf in PreH2.
      unfold_loop in PreH2.
      prog_nf in PreH2.
      unfold glibc_slist_clean_iter_back_2_M_loop1_body in PreH2 at 1.
      prog_nf in PreH2.
      safe_choice_r PreH2.
      * unfold glibc_slist_clean_iter_back_2_M_loop1_M2 in PreH2 at 1.
        prog_nf in PreH2.
        unfold continue in PreH2 at 1.
        eapply (safeExec_proequiv _
          (r <- glibc_slist_clean_iter_back_2_M_loop2_aux (d :: l0, s);;
           a' <- glibc_slist_clean_iter_back_2_M_loop1_after_inner_2 (d :: l0, s) r;;
           r1 <- repeat_break glibc_slist_clean_iter_back_2_M_loop1_body a';;
           glibc_slist_clean_iter_back_2_M_loop1_end (d :: app l0 ldone_2) r1)) in PreH2.
        2:{
          apply common_step_equiv; intros r.
          apply common_step_equiv; intros a'.
          rewrite bind_ret_l.
          reflexivity.
        }
        dump_pre_spatial.
        unfold glibc_slist_clean_iter_back_2_M_loop2.
        unfold glibc_slist_clean_iter_back_2_M_loop2_cont.
        prog_nf.
        simpl app.
        simpl app in PreH2.
        exact PreH2.
      * unfold glibc_slist_clean_iter_back_2_loop1_guardP.
        simpl.
        discriminate.
      * unfold glibc_slist_clean_iter_back_2_prev_case.
        simpl.
        dump_pre_spatial.
        auto.
  Unshelve.
  all: try (dump_pre_spatial;
            unfold glibc_slist_clean_iter_back_2_prev_case;
            simpl; auto).
  all: try (unfold range; split; [rewrite Zlength_nil; lia | constructor]).
  * dump_pre_spatial.
    unfold glibc_slist_clean_iter_back_2_prev_case.
    simpl.
    auto.
Qed.
Lemma proof_of_glibc_slist_clean_iter_back_2_entail_wit_3 : glibc_slist_clean_iter_back_2_entail_wit_3.
Proof.
  pre_process.
  subst_eqs.
  Exists y_2.
  Exists ldone_2.
  Exists (@nil Z).
  Exists v.
  Exists lrest.
  Exists (v :: lrest).
  split_pure_spatial.
  - simpl sllseg.
    entailer!.
  - split_pure_and_solve.
Qed.
Lemma proof_of_glibc_slist_clean_iter_back_2_entail_wit_4 : glibc_slist_clean_iter_back_2_entail_wit_4.
Proof.
  pre_process.
  subst_eqs.
  destruct lrest_3 as [| vnext lrest_next].
  - simpl sllseg.
    Intros.
    subst; contradiction.
  - simpl sllseg.
    Intros y.
    Exists y.
    Exists ldone_2.
    Exists (app lpre_2 (v_3 :: nil)).
    Exists vnext.
    Exists lrest_next.
    Exists (vnext :: lrest_next).
    split_pure_spatial.
    + entailer!.
      sep_apply_left (sllseg_len1 node v_3 y_2 PreH4).
      sep_apply_left (sllseg_sllseg x_pre node y_2 lpre_2 (v_3 :: nil)).
      entailer!.
    + split_pure_and_solve.
      unfold glibc_slist_clean_iter_back_2_M_loop2 in PreH3 at 1.
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop2_aux in PreH3 at 1.
      prog_nf in PreH3.
      unfold_loop in PreH3.
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop2_body in PreH3 at 1.
      prog_nf in PreH3.
      safe_choice_r PreH3.
      * unfold glibc_slist_clean_iter_back_2_M_loop2_M2 in PreH3 at 1.
        prog_nf in PreH3.
        unfold continue in PreH3 at 1.
        eapply (safeExec_proequiv _
          (r <- glibc_slist_clean_iter_back_2_M_loop2_aux (vnext :: lrest_next, s_2);;
           glibc_slist_clean_iter_back_2_M_loop2_cont
             (app (app lpre_2 (v_3 :: vnext :: lrest_next)) ldone_2)
             (app lpre_2 (v_3 :: vnext :: lrest_next)) s_2 r)) in PreH3.
        2:{
          unfold glibc_slist_clean_iter_back_2_M_loop2_aux.
          rewrite bind_ret_l.
          reflexivity.
        }
        dump_pre_spatial.
        unfold glibc_slist_clean_iter_back_2_M_loop2.
        pose proof (app_assoc lpre_2 (v_3 :: nil) (vnext :: lrest_next)) as Happ.
        simpl in Happ.
        eapply (safeExec_proequiv _
          (r <- glibc_slist_clean_iter_back_2_M_loop2_aux (vnext :: lrest_next, s_2);;
           glibc_slist_clean_iter_back_2_M_loop2_cont
             (app (app (app lpre_2 (v_3 :: nil)) (vnext :: lrest_next)) ldone_2)
             (app (app lpre_2 (v_3 :: nil)) (vnext :: lrest_next)) s_2 r)) in PreH3.
        2:{
          change (app (app lpre_2 (v_3 :: nil)) (vnext :: lrest_next))
            with (lpre_2 +:: v_3 ++ vnext :: lrest_next).
          change (app (app (app lpre_2 (v_3 :: nil)) (vnext :: lrest_next)) ldone_2)
            with (app (lpre_2 +:: v_3 ++ vnext :: lrest_next) ldone_2).
          rewrite <- Happ.
          reflexivity.
        }
        exact PreH3.
      * unfold glibc_slist_clean_iter_back_2_loop2_guardP.
        simpl.
        auto.
      * dump_pre_spatial.
        unfold range in *.
        destruct PreH6 as [_ Hpre].
        destruct PreH7 as [_ Htail].
        destruct PreH8 as [Hlen _].
        split.
        -- unfold app in Hlen.
           unfold app.
           rewrite Zlength_app in Hlen.
           rewrite !Zlength_cons in Hlen.
           rewrite Zlength_app.
           rewrite Zlength_cons.
           rewrite Zlength_nil.
           pose proof (Zlength_nonneg lrest_next).
           lia.
        -- apply Forall_app.
           split.
           ++ exact Hpre.
           ++ inversion Htail; subst.
              constructor; auto.
      * entailer!.
        unfold glibc_slist_clean_iter_back_2_prev_case.
        unfold range in PreH7.
        destruct PreH7 as [Hlen_tail Hforall_tail].
        split.
        -- rewrite !Zlength_cons in Hlen_tail.
           rewrite Zlength_cons.
           pose proof (Zlength_nonneg lrest_next).
           lia.
        -- inversion Hforall_tail; subst; assumption.
  Unshelve.
  * assert (Hrange_reassoc:
      range (app (app lpre_2 (v_3 :: nil)) (vnext :: lrest_next))) by
      (unfold range in *; destruct PreH8 as [Hlen Hforall]; split;
       [ assert (Hlen_eq:
           Zlength (app (app lpre_2 (v_3 :: nil)) (vnext :: lrest_next)) =
           Zlength (app lpre_2 (v_3 :: vnext :: lrest_next)))
           by (clear - lpre_2 v_3 vnext lrest_next;
               induction lpre_2 as [|a lpre IH]; simpl; auto;
               rewrite !Zlength_cons; rewrite IH; reflexivity);
         rewrite Hlen_eq; exact Hlen
       | revert Hforall;
         clear - lpre_2 v_3 vnext lrest_next;
         induction lpre_2 as [|a lpre IH]; intros Hforall; simpl in *; auto;
         inversion Hforall; subst; constructor; auto ]).
    entailer!.
  * assert (Hprev:
      glibc_slist_clean_iter_back_2_prev_case node
        (app lpre_2 (v_3 :: nil)) y_2 x_pre) by
      (unfold glibc_slist_clean_iter_back_2_prev_case; intros Hnode; contradiction).
    entailer!.
Qed.
Lemma proof_of_glibc_slist_clean_iter_back_2_entail_wit_5 : glibc_slist_clean_iter_back_2_entail_wit_5.
Proof.
  pre_process.
  subst_eqs.
  destruct lrest_2 as [| w rest].
  - simpl in PreH3.
    Exists ldone_2.
    Exists lpre_2.
    Exists v_3.
    Exists st.
    split_pure_spatial.
    + entailer!.
      simpl sllseg.
      entailer!.
    + pose proof PreH3 as Hsum_safe.
      unfold glibc_slist_clean_iter_back_2_M_loop2 in Hsum_safe at 1.
      prog_nf in Hsum_safe.
      unfold glibc_slist_clean_iter_back_2_M_loop2_aux in Hsum_safe at 1.
      prog_nf in Hsum_safe.
      unfold_loop in Hsum_safe.
      prog_nf in Hsum_safe.
      unfold glibc_slist_clean_iter_back_2_M_loop2_body in Hsum_safe at 1.
      prog_nf in Hsum_safe.
      apply safeExec_choice_l in Hsum_safe.
      safe_step Hsum_safe.
      * unfold glibc_slist_clean_iter_back_2_M_loop2_M1 in Hsum_safe at 1.
        prog_nf in Hsum_safe.
        safe_step Hsum_safe.
        destruct H as [Hsum_lo Hsum_hi].
        split_pure_and_solve.
  - simpl sllseg.
    destruct ldone_2 as [| done ldone].
    + simpl sll.
      Intros z.
      subst; contradiction.
    + simpl sll.
      Intros z.
      Intros y.
      sep_apply (dup_store_int (&( st # "list" ->ₛ "data")) w done).
      entailer!.
Qed. 

Lemma proof_of_glibc_slist_clean_iter_back_2_derive_high_level_spec_by_low_level_spec :
  glibc_slist_clean_iter_back_2_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists (MonadErr.nrm
    (glibc_slist_clean_iter_back_2_M l1_high_level_spec) tt).
  Exists l1_high_level_spec.
  entailer!.
  - apply derivable1_wand_sepcon_adjoint.
    Intros l2.
    Intros r.
    Intros retval_2.
    Exists retval_2.
    destruct (@Hoare_safeexec_compose unit (list Z * Z)
                (fun _ : unit => range l1_high_level_spec)
                (glibc_slist_clean_iter_back_2_M l1_high_level_spec)
                (fun r _ => r = (l1_high_level_spec, list_sum l1_high_level_spec))
                (glibc_slist_clean_iter_back_2_M_Hoare l1_high_level_spec)
                ATrue (maketuple l2 r) tt H0 H) as [sigma' [Hret _]].
    unfold maketuple in Hret.
    inversion Hret; subst.
    entailer!.
  - apply safeExec_monad_Atrue_finnal.
    destruct (glibc_slist_clean_iter_back_2_M_Hoare l1_high_level_spec) as [_ Herr].
    intro Herr0.
    eapply Herr; [exact H | exact Herr0].
Qed.
Lemma proof_of_glibc_slist_clean_iter_back_2_entail_wit_6 : glibc_slist_clean_iter_back_2_entail_wit_6.
Proof.
  pre_process.
  subst_eqs.
  specialize (PreH13 eq_refl) as [Hlpre Hnode].
  subst_eqs.
  Exists v.
  Exists ldone_2.
  split_pure_spatial.
  - simpl sllseg. simpl sll.
    Exists st.
    entailer!.
  - split_pure_and_solve.
    unfold glibc_slist_clean_iter_back_2_M_loop2 in PreH3 at 1.
    prog_nf in PreH3.
    unfold glibc_slist_clean_iter_back_2_M_loop2_aux in PreH3 at 1.
    prog_nf in PreH3.
    unfold_loop in PreH3.
    prog_nf in PreH3.
    unfold glibc_slist_clean_iter_back_2_M_loop2_body in PreH3 at 1.
    prog_nf in PreH3.
    apply safeExec_choice_l in PreH3.
    safe_step PreH3.
    + unfold glibc_slist_clean_iter_back_2_M_loop2_M1 in PreH3 at 1.
      prog_nf in PreH3.
      safe_step PreH3.
      unfold break in PreH3 at 1.
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop2_cont in PreH3 at 1.
      simpl app in PreH3.
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop1_after_inner_2 in PreH3 at 1.
      simpl in PreH3.
      prog_nf in PreH3.
      safe_step PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop1_aux in PreH3.
      eapply safeExec_proequiv in PreH3.
      2: {
        eapply programbind_Proper.
        - apply repeat_break_unfold.
        - reflexivity.
      }
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop1_body in PreH3 at 1.
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_loop1_guardP in PreH3.
      simpl in PreH3.
      eapply safeExec_proequiv in PreH3.
      2: { apply bind_choice_equiv. }
      safe_choice_l PreH3.
      unfold break in PreH3.
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop1_end in PreH3.
      prog_nf in PreH3.
      unfold maketuple.
      dump_pre_spatial.
      exact PreH3.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_back_2_entail_wit_7 : glibc_slist_clean_iter_back_2_entail_wit_7.
Proof.
  pre_process.
  subst_eqs.
  Exists lpre.
  Exists (v :: ldone_2).
  split_pure_spatial.
  - simpl sll.
    Exists st.
    entailer!.
    sep_apply store_ptr_undef_store_ptr.
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - split_pure_and_solve.
    + unfold glibc_slist_clean_iter_back_2_M_loop2 in PreH3 at 1.
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop2_aux in PreH3 at 1.
      prog_nf in PreH3.
      unfold_loop in PreH3.
      prog_nf in PreH3.
      unfold glibc_slist_clean_iter_back_2_M_loop2_body in PreH3 at 1.
      prog_nf in PreH3.
      apply safeExec_choice_l in PreH3.
      safe_step PreH3.
      * unfold glibc_slist_clean_iter_back_2_M_loop2_M1 in PreH3 at 1.
        prog_nf in PreH3.
        safe_step PreH3.
        unfold break in PreH3 at 1.
        prog_nf in PreH3.
        unfold glibc_slist_clean_iter_back_2_M_loop2_cont in PreH3 at 1.
        simpl app in PreH3.
        prog_nf in PreH3.
        unfold glibc_slist_clean_iter_back_2_M_loop1_after_inner_2 in PreH3 at 1.
        prog_nf in PreH3.
        assert (Hfront_all : forall (l : list Z) (last_value : Z),
          (fix front_and_last (l0 : list Z) : list Z * Z :=
             match l0 with
             | nil => (nil, 0)
             | v0 :: nil => (nil, v0)
             | v0 :: (_ :: _) as l' =>
                 let (front, last) := front_and_last l' in (v0 :: front, last)
             end) (app l (last_value :: nil)) = (l, last_value))
          by (induction l as [| a tl IH]; intros last_value; simpl; auto;
              destruct tl as [| b tl]; simpl; auto;
              specialize (IH last_value); simpl in IH; rewrite IH; auto).
        specialize (Hfront_all lpre v) as Hfront.
        rewrite Hfront in PreH3.
        prog_nf in PreH3.
        safe_step PreH3.
        unfold glibc_slist_clean_iter_back_2_M_loop1 at 1.
        prog_nf.
        assert (Happ_all : forall (l : list Z) (last_value : Z) (done : list Z),
          app l (last_value :: done) = app (app l (last_value :: nil)) done).
        { induction l as [| a tl IH]; intros last_value done; simpl; try reflexivity.
          f_equal; apply IH.
        }
        specialize (Happ_all lpre v ldone_2) as Happ.
        rewrite <- Happ in PreH3.
        dump_pre_spatial.
        exact PreH3.
Qed. 
Lemma proof_of_glibc_slist_clean_iter_back_2_return_wit_1 : glibc_slist_clean_iter_back_2_return_wit_1.
Proof.
  pre_process.
  subst_eqs.
  Exists (l1_1 ++ ldone).
  Exists s.
  split_pure_spatial.
  - sep_apply sllseg_sll.
    entailer!.
  - split_pure_and_solve.
    destruct l1_1 as [| a l1_1].
    + simpl.
      simpl in PreH2.
      unfold glibc_slist_clean_iter_back_2_M_loop1 in PreH2.
      unfold glibc_slist_clean_iter_back_2_M_loop1_aux in PreH2.
      eapply safeExec_proequiv in PreH2.
      2: {
        eapply programbind_Proper.
        - apply repeat_break_unfold.
        - reflexivity.
      }
      prog_nf in PreH2.
      unfold glibc_slist_clean_iter_back_2_M_loop1_body in PreH2 at 1.
      prog_nf in PreH2.
      unfold glibc_slist_clean_iter_back_2_loop1_guardP in PreH2.
      simpl in PreH2.
      eapply safeExec_proequiv in PreH2.
      2: { apply bind_choice_equiv. }
      safe_choice_l PreH2.
      unfold break in PreH2.
      prog_nf in PreH2.
      unfold glibc_slist_clean_iter_back_2_M_loop1_end in PreH2.
      prog_nf in PreH2.
      unfold maketuple.
      dump_pre_spatial.
      exact PreH2.
    + simpl.
      destruct ldone as [| b ldone].
      * simpl.
        Intros z.
        entailer!.
      * simpl.
        Intros z y.
        sep_apply (dup_store_int (&( st # "list" ->ₛ "data")) a b).
        entailer!.
Qed. 
