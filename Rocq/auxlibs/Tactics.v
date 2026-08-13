Ltac prep_from H :=
  let T := type of H in
  match T with
  | ?P -> ?Q =>
      let Htmp := fresh "Htmp" in
      assert P as Htmp;
      [ idtac | specialize (H Htmp); clear Htmp ]
  end.