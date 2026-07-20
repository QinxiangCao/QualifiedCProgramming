
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare.
Require Import TraceLib.MapLib.
Require Import Coq.Lists.List.

Ltac my_destruct H :=
  match type of H with
  | exists (_ : ?A), _ => destruct H as [? H];my_destruct H
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              my_destruct H;
              my_destruct H0
  | _ \/ _ => destruct H as [H | H];
              my_destruct H
  | _ => (discriminate || contradiction  || idtac)
  end.
(* only change the behavior in Hoare choice *)

Import MonadNotation.
Local Open Scope monad.
Ltac hoare_auto_s_disj :=
  unfold continue, break, If, if_else;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto_s_disj
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto_s_disj
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_left; try hoare_auto_s_disj
    | |- Hoare _ (bind (any _) _) _ => apply Hoare_any_bind; intros; try hoare_auto_s_disj
    | |- Hoare _ (bind (get _) _) _ => hoare_bind Hoare_get_s; intros; apply Hoare_stateless'; intros; subst; try hoare_auto_s_disj
    | |- Hoare _ (bind (get' _) _) _ => hoare_bind Hoare_get'; intros; apply Hoare_stateless'; intros; subst; try hoare_auto_s_disj
    | |- Hoare _ (bind (update _) _) _ => hoare_bind' Hoare_update_s; apply Hoare_state_intro; intros; try hoare_auto_s_disj
    | |- Hoare _ (bind (update' _) _) _ => hoare_bind' Hoare_update'; try hoare_auto_s_disj
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind'; intros; try hoare_auto_s_disj
    | |- Hoare _ (assume _ ;; _) _ => hoare_bind' Hoare_assume_s; intros; apply Hoare_stateless'; intros; try hoare_auto_s_disj
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice_disj; try hoare_auto_s_disj
    | |- Hoare _ _ _ => hoare_single_s
end; auto.


Ltac equiv_dec_refl v :=
  unfold t_set;
  let H := fresh "c" in
  destruct (equiv_dec v v) as [|H]; [ try reflexivity | exfalso; apply H; reflexivity].

Ltac equiv_dec_simpl u v := 
  unfold t_set;
  let H := fresh "Heq_uv" in 
  let H0 := fresh "Hneq_uv" in 
  destruct (equiv_dec u v) as [Heq_uv | Hneq_uv]; 
  [assert (u = v) by apply H; clear H; subst v |
   assert (u <> v) by apply H0; clear H0];
   auto; try (eexists; auto); try (congruence).

   
Ltac hoare_fix_nolv_fs_auto A :=
  lazymatch goal with
    | |- @Hoare ?Sigma ?R ?P (Rec ?F ?a) ?Q =>
      unfold Rec; hoare_fix_nolv_fs_auto A
    | |- @Hoare ?Σ ?R ?P (Lfix ?F ?a) ?Q => 
      let fs_pre := fresh "fs_pre" in evar (fs_pre: A -> Σ -> Prop);
      let fs_post := fresh "fs_post" in evar (fs_post: A -> R -> Σ -> Prop);
      let h := fresh "h" in assert (fs_pre = fs_pre) as h; [
        let fs_pre' := eval pattern (a) in P in 
        match fs_pre' with 
        | ?fs_pre'' _ => exact (Logic.eq_refl fs_pre'') end
        |
      ];
      clear h; let h := fresh "h" in assert (fs_post = fs_post) as h; [
        let fs_post' := eval pattern (a) in Q in 
        match fs_post' with 
        | ?fs_post'' _ => exact (Logic.eq_refl fs_post'') end
        |
      ]; clear h;
      let fs_instance :=
      constr:({|
          mFS_lv := R;
          mFS_pre := fun t _ s => fs_pre t s;
          mFS_Post := fun t _ r s => fs_post t r s
      |}) in 
      pose (fs := fs_instance);
      subst fs_pre; subst fs_post; simpl in fs;
      let HFS := fresh "HFS" in 
      pose proof @Hoare_fix_logicv_fspecs Σ A R F fs as HFS;
      subst fs; simpl in HFS; eapply HFS; clear HFS; 
      [| |exact tt] end.

Tactic Notation "hoare_bind''" uconstr(H) :=
  eapply Hoare_bind; [ | intros; eapply H]; intros.

Tactic Notation "hoare_fix_nolv_ls_auto" uconstr(H) constr(a) constr(f):= 
  let HH := fresh "HH" in 
  pose proof @H as HH; 
  unfold f in HH;
  instantiate (1 := 
  {| mFS_lv := a;
  mFS_pre := _;
  mFS_Post := _|});
  unfold monad_sat_funcspec; simpl;
  match a with
  | unit => intros; apply HH; eauto
  | _ => apply HH; eauto
end.

Ltac unfold_Forall H :=
  match type of H with
  | Forall _ nil => idtac
  | Forall _ (_ :: _) =>
    let Ha := fresh "IHa" in
    let Hb := fresh "IHb" in
    inversion H as [| ? ? Ha Hb]; subst;
    unfold monad_sat_funcspec in Ha; simpl in Ha;
    unfold_Forall Hb
  end; clear H.
Import ListNotations.
Theorem cons_eq_singleton_app {X: Type}: forall (x: X)(l: list X), 
  x :: l = [x] ++ l.
Proof. induction l; firstorder. Qed.  

Ltac split_r n := 
  match n with 
  | O => idtac
  | S ?n' => split; [|split_r n']
  end.

Ltac hoare_conj_n n :=
  match n with
  | 0 => idtac
  | S ?n' => apply Hoare_conj; [|hoare_conj_n n']
  end.

Ltac forall_n n :=
  match n with
  | 0 => apply Forall_nil
  | S ?n' => apply Forall_cons; [ | forall_n n' ]
  end.

Lemma Hoare_false {Σ A: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    Hoare (fun _ => False) c Q.
Proof. unfold Hoare; intros; tauto. Qed.
