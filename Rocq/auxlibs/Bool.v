Require Export Coq.Bool.Bool.

Lemma andb_true_left_true {b1 b2} :
    andb b1 b2 = true -> b1 = true.
Proof.
  destruct b1; simpl; auto.
Defined.

Lemma andb_true_right_true {b1 b2} :
    andb b1 b2 = true -> b2 = true.
Proof.
  intros H.
  rewrite (andb_true_left_true H) in H.
  exact H.
Defined.
