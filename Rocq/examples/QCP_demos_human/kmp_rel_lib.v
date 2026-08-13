Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
From SetsClass Require Import SetsClass.
From AUXLib Require Import ListLib VMap relations.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import AUXLib.ListLib.


Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

From MonadLib Require Export MonadLib.
Export StateRelMonadErr.
From MonadLib.Examples Require Export kmp.

Export MonadNotation.
Local Open Scope monad.

Definition applyf {A B: Type} (f: A -> B) (a: A) := f a.

Definition option_int_repr (x: option Z): Z :=
  match x with
  | Some n => n
  | None => -1
  end.

Definition constr_loop_from {A: Type} (default: A) str i vnext j :=
  '(vnext', j') <- range_iter i (Zlength str) (constr_body default str) (vnext, j);;
  return vnext'.

Definition constr_loop_from_after {A: Type} (default: A) str i vnext :=
  fun j => constr_loop_from default str (i+1) (vnext ++ [j]) j.
  
Definition match_loop_from {A: Type} (default: A) patn text vnext i j :=
  res <- range_iter_break i (Zlength text) (match_body default patn text vnext) j;;
  match res with
  | by_continue _ => return None
  | by_break r => return (Some r) 
  end.

Definition match_loop_from_after {A: Type} (default: A) patn text vnext i :=
  fun j =>
    res <-
      choice
        (assume!! (j = Zlength patn);;
         break (i - Zlength patn + 1))
        (assume!! (j < Zlength patn);;
         continue j);;
    res' <-
      match res with
      | by_continue j =>
          range_iter_break (i+1) (Zlength text) (match_body default patn text vnext) j
      | by_break r => break r
      end;;
    match res' with
    | by_continue _ => return None
    | by_break r => return (Some r)
    end.

Lemma first_occur_nonneg {A:Type}: forall (patn text: list A) z,
  patn <> nil ->
  first_occur patn text z -> z >= 0.
Proof.
  intros.
  destruct H0 as [H0 _].
  destruct (Z_lt_ge_dec z 0); auto.
  pose proof (f_equal (@Zlength _) H0).
  rewrite Zlength_sublist' in H1.
  apply Zlength_nonnil in H; lia.
Qed.

Lemma string_Zlength: forall (str: list Z) a n,
  Zlength (str ++ a :: nil) = n + 1 -> Zlength str = n.
Proof.
  intros.
  rewrite Zlength_app in H.
  replace (Zlength [a]) with 1 in H by easy.
  lia.
Qed. 

Lemma replace_Znth_length {A: Type}:
  forall (l:list A) n a, 
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros l n; unfold replace_Znth. 
  remember (Z.to_nat n) as k; clear Heqk.
  revert k; induction l; intros.
  - destruct k; simpl; easy.
  - destruct k; simpl; repeat rewrite Zlength_cons; auto.
    rewrite IHl; auto.
Qed.
      
