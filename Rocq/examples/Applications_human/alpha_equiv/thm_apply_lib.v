From Coq Require Import ZArith List.
From SimpleC.EE.Applications_human.alpha_equiv Require Export ast_lib.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib safeexec_lib.
Import ListNotations.
Local Open Scope Z_scope.
Import MonadNotation.
Local Open Scope monad.

(* Antecedents of an implication chain ending in an alpha-equivalent goal.
   None distinguishes a failed match from a match with no antecedents. *)
Fixpoint thm_apply_requirements (theorem goal : term) : option (list term) :=
  if term_alpha_eq theorem goal then Some nil
  else match theorem with
       | TermApply (TermApply (TermConst CImpl _) assumption) conclusion =>
           match thm_apply_requirements conclusion goal with
           | Some assumptions => Some (assumption :: assumptions)
           | None => None
           end
       | _ => None
       end.

Definition thm_app_result (theorem : term) (substitutions : list var_sub)
    (goal : term) : solve_res :=
  match thm_subst_allres theorem substitutions with
  | None => SRBool 0
  | Some (_, instantiated) =>
      if term_alpha_eq instantiated goal then SRBool 1
      else SRTList (match thm_apply_requirements instantiated goal with
                    | Some assumptions => assumptions
                    | None => nil
                    end)
  end.

Lemma check_from_mid_result : forall theorem goal prefix,
  Hoare (fun _ : unit => True)
    (check_from_mid_rel theorem goal prefix)
    (fun result _ => snd result =
      match thm_apply_requirements theorem goal with
      | Some assumptions => prefix ++ assumptions
      | None => nil
      end).
Proof.
  induction theorem as [v | c z | left IHleft right IHright | q v body IHbody];
    intros goal prefix;
    unfold check_from_mid_rel;
    rewrite (repeat_break_unfold check_list_gen_body _);
    unfold check_list_gen_body;
    cbn [thm_apply_requirements];
    destruct term_alpha_eq eqn:Heq;
    try (rewrite bind_ret_left; apply Hoare_ret'; intros; cbn; now rewrite app_nil_r).
  - cbn [sep_impl]. rewrite bind_ret_left.
    apply Hoare_ret'; intros; reflexivity.
  - cbn [sep_impl]. rewrite bind_ret_left.
    apply Hoare_ret'; intros; reflexivity.
  - destruct left as [v | c z | ll lr | q v body];
      try (cbn [sep_impl]; rewrite bind_ret_left;
           apply Hoare_ret'; intros; reflexivity).
    destruct ll as [v | c z | ll lr0 | q v body];
      try (cbn [sep_impl]; rewrite bind_ret_left;
           apply Hoare_ret'; intros; reflexivity).
    destruct c;
      try (cbn [sep_impl]; rewrite bind_ret_left;
           apply Hoare_ret'; intros; reflexivity).
    cbn [sep_impl]. rewrite bind_ret_left.
    specialize (IHright goal (prefix ++ [lr])).
    unfold check_from_mid_rel in IHright.
    destruct (thm_apply_requirements right goal) as [assumptions|] eqn:Hreq.
    + rewrite <- app_assoc in IHright. exact IHright.
    + exact IHright.
  - cbn [sep_impl]. rewrite bind_ret_left.
    apply Hoare_ret'; intros; reflexivity.
Qed.

Lemma thm_app_result_correct : forall theorem substitutions goal,
  Hoare (fun _ : unit => True)
    (thm_app_rel theorem substitutions goal)
    (fun result _ => result = thm_app_result theorem substitutions goal).
Proof.
  intros theorem substitutions goal.
  unfold thm_app_rel, thm_app, thm_app_result.
  destruct (thm_subst_allres theorem substitutions) as [[pq instantiated]|].
  - destruct (term_alpha_eq instantiated goal) eqn:Heq.
    + apply Hoare_ret'; intros; reflexivity.
    + eapply Hoare_bind.
      * apply (check_from_mid_result instantiated goal nil).
      * intros [last assumptions].
        unfold get_list.
        apply Hoare_ret'. intros state Hresult.
        cbn in Hresult. now rewrite Hresult.
  - apply Hoare_ret'; intros; reflexivity.
Qed.


Require Import Coq.Strings.String.
Lemma store_term_const_fold_order__implication_returns: forall x ctype content, x <> 0 -> SimpleC.SL.SeparationLogic.naive_C_Rules.derivable1 (SimpleC.SL.SeparationLogic.naive_C_Rules.sepcon (SimpleC.SL.SeparationLogic.naive_C_Rules.sepcon (SimpleC.SL.SeparationLogic.naive_C_Rules.store_int (SimpleC.SL.CNotation.eval_addr_expr (SimpleC.SL.CNotation.RE_addr_of (SimpleC.SL.CNotation.LE_dot_field (SimpleC.SL.CNotation.LE_dot_field (SimpleC.SL.CNotation.LE_arrow_field (SimpleC.SL.CNotation.RE_const x (SimpleC.SL.CNotation.FET_alias "term"%string)) "content"%string) "Const"%string) "type"%string))) (ctID ctype)) (SimpleC.SL.SeparationLogic.naive_C_Rules.store_int (SimpleC.SL.CNotation.eval_addr_expr (SimpleC.SL.CNotation.RE_addr_of (SimpleC.SL.CNotation.LE_dot_field (SimpleC.SL.CNotation.LE_dot_field (SimpleC.SL.CNotation.LE_arrow_field (SimpleC.SL.CNotation.RE_const x (SimpleC.SL.CNotation.FET_alias "term"%string)) "content"%string) "Const"%string) "content"%string))) content)) (SimpleC.SL.SeparationLogic.naive_C_Rules.store_int (SimpleC.SL.CNotation.eval_addr_expr (SimpleC.SL.CNotation.RE_addr_of (SimpleC.SL.CNotation.LE_arrow_field (SimpleC.SL.CNotation.RE_const x (SimpleC.SL.CNotation.FET_alias "term"%string)) "type"%string))) (termtypeID (TermConst ctype content)))) (store_term x (TermConst ctype content)).
Proof.
  Import SimpleC.SL.CNotation SimpleC.SL.SeparationLogic SimpleC.SL.CommonAssertion Logic.LogicGenerator.demo932.Interface SimpleC.SL.SeparationLogic.naive_C_Rules.
  Local Open Scope string_scope.
  Local Open Scope sac.
  intros.
  unfold store_term, store_term', NULL.
  simpl.
  split_pure_spatial.
  - cancel (&( x # "term" ->ₛ "type") # Int |-> 1).
    cancel (&( x # "term" ->ₛ "content" .ₛ "Const" .ₛ "type") # Int |-> ctID ctype).
    cancel (&( x # "term" ->ₛ "content" .ₛ "Const" .ₛ "content") # Int |-> content).
  - split_pures; dump_pre_spatial; try assumption.
Qed.
Lemma store_term_apply_fold_order__implication_returns: forall x y z lt rt, x <> 0 -> SimpleC.SL.SeparationLogic.naive_C_Rules.derivable1 (SimpleC.SL.SeparationLogic.naive_C_Rules.sepcon (SimpleC.SL.SeparationLogic.naive_C_Rules.sepcon (SimpleC.SL.SeparationLogic.naive_C_Rules.sepcon (SimpleC.SL.SeparationLogic.naive_C_Rules.sepcon (SimpleC.SL.SeparationLogic.naive_C_Rules.store_ptr (SimpleC.SL.CNotation.eval_addr_expr (SimpleC.SL.CNotation.RE_addr_of (SimpleC.SL.CNotation.LE_dot_field (SimpleC.SL.CNotation.LE_dot_field (SimpleC.SL.CNotation.LE_arrow_field (SimpleC.SL.CNotation.RE_const x (SimpleC.SL.CNotation.FET_alias "term"%string)) "content"%string) "Apply"%string) "left"%string))) y) (store_term y lt)) (SimpleC.SL.SeparationLogic.naive_C_Rules.store_ptr (SimpleC.SL.CNotation.eval_addr_expr (SimpleC.SL.CNotation.RE_addr_of (SimpleC.SL.CNotation.LE_dot_field (SimpleC.SL.CNotation.LE_dot_field (SimpleC.SL.CNotation.LE_arrow_field (SimpleC.SL.CNotation.RE_const x (SimpleC.SL.CNotation.FET_alias "term"%string)) "content"%string) "Apply"%string) "right"%string))) z)) (store_term z rt)) (SimpleC.SL.SeparationLogic.naive_C_Rules.store_int (SimpleC.SL.CNotation.eval_addr_expr (SimpleC.SL.CNotation.RE_addr_of (SimpleC.SL.CNotation.LE_arrow_field (SimpleC.SL.CNotation.RE_const x (SimpleC.SL.CNotation.FET_alias "term"%string)) "type"%string))) (termtypeID (TermApply lt rt)))) (store_term x (TermApply lt rt)).
Proof.
  Import SimpleC.SL.CNotation SimpleC.SL.SeparationLogic SimpleC.SL.CommonAssertion Logic.LogicGenerator.demo932.Interface SimpleC.SL.SeparationLogic.naive_C_Rules.
  Local Open Scope string_scope.
  Local Open Scope sac.
  intros.
  unfold store_term, store_term', NULL.
  simpl.
  Exists y z.
  split_pure_spatial.
  - cancel (&( x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "left") # Ptr |-> y).
    cancel (&( x # "term" ->ₛ "content" .ₛ "Apply" .ₛ "right") # Ptr |-> z).
    cancel (store_term y lt).
    cancel (store_term z rt).
    cancel (&( x # "term" ->ₛ "type") # Int |-> 2).
  - split_pures; dump_pre_spatial; try assumption.
Qed.
