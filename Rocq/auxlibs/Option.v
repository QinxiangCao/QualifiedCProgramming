(* Similar to stdpp *)
Definition is_Some {A} (o: option A) : Prop :=
  exists v, o = Some v.


Lemma is_Some_alt {A} (o: option A) :
  is_Some o <-> match o with
  | Some v => True
  | None => False
  end.
Proof.
  unfold is_Some.
  split.
  - intros [v ->]. tauto.
  - destruct o; [intros _; eexists; reflexivity | contradiction].
Qed.


Lemma mk_is_Some {A} (mx : option A) x : mx = Some x -> is_Some mx.
Proof. intros ->. eexists; reflexivity. Qed.

Lemma is_Some_None {A} : ~ is_Some (@None A).
Proof. destruct 1 as [v H]. discriminate. Qed.
