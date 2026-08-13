Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From TraceLib Require Import CommonTactics MapLib.
From GraphLib Require Import GraphLib tarjan.
From Algorithms Require Import Tarjan.

Import MonadNotation.
Local Open Scope monad.

Ltac unfold_op :=
    unfold visit, set_low, set_dfn, set_tree, 
        add_bridge, update_low, incr_timer.

Ltac unfold_preloop :=
    intro_state; unfold preloop; unfold_op; hoare_auto_s; try intro_state.

Lemma Hoare_exclude_middle {A Σ}:
  forall (P Q R: Σ -> Prop) (c: program Σ A),
    Hoare (fun s => P s /\ ~ R s) c (fun _ s => Q s) ->
    Hoare (fun s => P s /\ R s) c (fun _ s => Q s) -> 
    Hoare (fun s => P s) c (fun _ s => Q s).
Proof. unfold Hoare. intros. destruct (classic (R s1)); firstorder. Qed.

Lemma Hoare_implies {A Σ}:
  forall (P Q R: Σ -> Prop) (c: program Σ A),
    Hoare P c (fun _ => Q) ->
    Hoare P c (fun _ s => Q s -> R s) ->
    Hoare P c (fun _ => R).
Proof. unfold Hoare. intros. eapply H0; eauto. Qed.

Lemma Hoare_conj2 {A Σ}:
  forall (P1 P2 Q1 Q2: Σ -> Prop) (c: program Σ A),
    Hoare P1 c (fun _ s => Q1 s) ->
    Hoare P2 c (fun _ s => Q2 s) ->
    Hoare (fun s => P1 s /\ P2 s) c (fun _ s => Q1 s /\ Q2 s).
Proof. firstorder. Qed.

Ltac hoare_conj2_n n :=
  match n with
  | 0 => idtac
  | S ?n' => apply Hoare_conj2; [|hoare_conj2_n n']
  end.

(* Ltac hoare_single_s :=
  match goal with
  | |- Hoare _ (skip) _ => (apply Hoare_ret' || hoare_cons_post Hoare_ret');
                           let H := fresh "H" in intros ? H; my_destruct H
  | |- Hoare _ (ret _) _ => (apply Hoare_ret' || hoare_cons_post Hoare_ret')
  | |- Hoare _ (any _) _ => (apply Hoare_any || hoare_cons_post Hoare_any)
  | |- Hoare _ (get _) _ => (apply Hoare_get_s || hoare_cons_post Hoare_get_s)
  | |- Hoare _ (get' _) _ => (apply Hoare_get' || hoare_cons_post Hoare_get')
  | |- Hoare _ (update _) _ => (apply Hoare_update_s || hoare_cons_post Hoare_update_s)
  | |- Hoare _ (update' _) _ => (apply Hoare_update' || hoare_cons_post Hoare_update')
  | |- Hoare _ (assume!! _) _ => (apply Hoare_assume' || hoare_cons_post Hoare_assume')
  | |- Hoare _ (assume _) _ => (apply Hoare_assume_s || hoare_cons_post Hoare_assume_s)
  | |- Hoare _ (continue_case (by_continue _)) _ => (apply Hoare_cnt_cnt || hoare_cons_post Hoare_cnt_cnt)
  | |- Hoare _ (break_case (by_break _)) _ => (apply Hoare_brk_brk || hoare_cons_post Hoare_brk_brk)
  | |- Hoare _ (break_case (by_continue _)) _ => (apply Hoare_brk_cnt || hoare_cons_post Hoare_brk_cnt)
  | |- Hoare _ (continue_case (by_break _)) _ => (apply Hoare_cnt_brk || hoare_cons_post Hoare_cnt_brk)
  end; intros.
  
  
Ltac hoare_auto_s :=
  unfold continue, break, If, if_else;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto_s
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto_s
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_left; try hoare_auto_s
    | |- Hoare _ (bind (any _) _) _ => apply Hoare_any_bind; intros; try hoare_auto_s
    | |- Hoare _ (bind (get _) _) _ => hoare_bind Hoare_get_s; intros; apply Hoare_stateless'; intros; subst; try hoare_auto_s
    | |- Hoare _ (bind (get' _) _) _ => hoare_bind Hoare_get'; intros; apply Hoare_stateless'; intros; subst; try hoare_auto_s
    | |- Hoare _ (bind (update _) _) _ => hoare_bind' Hoare_update_s; apply Hoare_state_intro; intros; try hoare_auto_s
    | |- Hoare _ (bind (update' _) _) _ => hoare_bind' Hoare_update'; try hoare_auto_s
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind'; intros; try hoare_auto_s
    | |- Hoare _ (assume _ ;; _) _ => hoare_bind' Hoare_assume_s; intros; apply Hoare_stateless'; intros; try hoare_auto_s
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice; try hoare_auto_s
    | |- Hoare _ _ _ => hoare_single_s
end; auto.

Goal forall x: nat,  Hoare (fun s: nat => True) 
                           (assume (fun _ => x = 2);; assume (fun _ => x = 3);; skip) 
                           (fun _ s => s = 0). 
Proof.
  intros. 
  intro_state.
  hoare_auto_s.
    match goal with
  | |- Hoare _ (skip) _ => (apply Hoare_ret' || hoare_cons_post Hoare_ret')
    end.
  hoare_single_s.
  apply Hoare_ret'. *)
