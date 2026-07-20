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
