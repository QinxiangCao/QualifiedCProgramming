Require Import SetsClass.SetsClass.
Require Import AUXLib.SetsFastTac.
Import SetsNotation.
Import SetProd.

Local Open Scope sets.

Ltac old_simpl_term T :=
  let T1 := SIMPLIFY_TAC T in
  let T2 := SETS_ELE_In_simplify_rec T1 in
  constr:(T2).

Section Bench.
  Variables A B C D : Type.
  Variables X Y Z W : A -> B -> C -> D -> Prop.
  Variables P Q : Prop.

  Ltac lifted_set_sample :=
    constr:(
      ((X ∩ Y) ∪ (Z ∩ W) ∪ (⌜P⌝ ∩ X)) ⊆
      ((X ∪ Z) ∩ (Y ∪ W ∪ ⌜Q⌝))).

  Ltac prod_sample :=
    constr:(
      ((fun a : A => P) × (fun b : B => Q)) ⊆
      ((fun a : A => P) × (fun b : B => Q)) ∪ Sets.empty).

  Goal True.
  Proof.
    idtac "bench_term_old_x200".
    Time do 200
      (let T := lifted_set_sample in
       let _ := old_simpl_term T in idtac).
    exact I.
  Qed.

  Goal True.
  Proof.
    idtac "bench_term_fast_x200".
    Time do 200
      (let T := lifted_set_sample in
       let _ := sets_unfold_fast_term T in idtac).
    exact I.
  Qed.

  Goal True.
  Proof.
    idtac "bench_term_fast_with_singleton_x200".
    Time do 200
      (let T := lifted_set_sample in
       let _ := sets_unfold_fast_term_with_singleton T in idtac).
    exact I.
  Qed.

  Goal
    ((X ∩ Y) ∪ (Z ∩ W) ∪ (⌜P⌝ ∩ X)) ⊆
    ((X ∪ Z) ∩ (Y ∪ W ∪ ⌜Q⌝)).
  Proof.
    idtac "bench_goal_fast".
    Time sets_unfold_fast.
  Abort.

  Goal
    (((X ∩ Y) ∪ (Z ∩ W) ∪ (⌜P⌝ ∩ X)) ⊆
     ((X ∪ Z) ∩ (Y ∪ W ∪ ⌜Q⌝))) -> True.
  Proof.
    intros H.
    idtac "bench_hyp_fast".
    Time sets_unfold_fast_in H.
    exact I.
  Qed.

  Goal True.
  Proof.
    idtac "bench_prod_old_x200".
    Time do 200
      (let T := prod_sample in
       let _ := old_simpl_term T in idtac).
    exact I.
  Qed.

  Goal True.
  Proof.
    idtac "bench_prod_fast_x200".
    Time do 200
      (let T := prod_sample in
       let _ := sets_unfold_fast_term T in idtac).
    exact I.
  Qed.
End Bench.
