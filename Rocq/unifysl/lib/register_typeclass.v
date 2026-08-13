Class RegisterClass (Kind: Type) {A: Type} (a: A) (n: nat):= {}.

Ltac rec_from_n n tac :=
  try (tac n; rec_from_n (S n) tac).

Ltac get_nth' K n :=
  let A := fresh "A" in
  evar (A: Type);
  let a := fresh "a" in
  evar (a: A);
  let H := fresh "H" in
  assert (RegisterClass K a n) as H by (unfold a, A; once (typeclasses eauto));
  match type of H with
  | RegisterClass _ ?a _ => exact a
  end.

Ltac get_nth K n :=
  let a := eval cbv beta zeta in ltac:(get_nth' K n) in a.

Goal RegisterClass unit 0 0 -> RegisterClass unit true 1 -> False.
  intros.
  let a := get_nth unit 1 in pose a.
Abort.

Ltac pose_proof_instance_as F name:=
  idtac;
  first [ let G := eval cbv beta in (F ltac:(typeclasses eauto)) in
          pose_proof_instance_as G name
        | match type of F with
          | forall _: _, _ => fail 2
          end
        | pose proof F as name].
