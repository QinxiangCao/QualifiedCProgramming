Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Field.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.

From Coq Require Reals SpecFloat.
From Flocq.Core Require Core.
From Flocq.IEEE754 Require Import Binary.
From CDCLLib Require Export cdcl_shared_lib.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import SeparationLogic.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

Ltac int_auto := AUXLib.int_auto.int_auto.

Ltac msat_cancel_len ls k :=
  lazymatch ls with
  | nil => k O
  | _ :: ?tl => msat_cancel_len tl ltac:(fun n => k (S n))
  end.

Ltac msat_cancel_length ls := msat_cancel_len ls ltac:(fun n => n).

Ltac msat_cancel_pred n :=
  lazymatch n with O => O | S ?m => m end.

Ltac msat_cancel_index_walk n i l l0 :=
  lazymatch l with
  | nil => let len := msat_cancel_length l0 in constr:((S len, n :: l0))
  | n :: ?tl => constr:((i, l0))
  | _ :: ?tl =>
      let pi := msat_cancel_pred i in msat_cancel_index_walk n pi tl l0
  end.

Ltac msat_cancel_atom_index n l :=
  let len := msat_cancel_length l in msat_cancel_index_walk n len l l.

Ltac msat_cancel_deep_walk se l0 :=
  lazymatch se with
  | @Syntax.sepcon ?L0 ?sepconL0 ?sp ?sq =>
      lazymatch msat_cancel_deep_walk sp l0 with
      | (?dp, ?l1) =>
          lazymatch msat_cancel_deep_walk sq l1 with
          | (?dq, ?l2) => constr:((TheoryOfCancel.sepcon_deep dp dq, l2))
          end
      end
  | ?sp ** ?sq =>
      lazymatch msat_cancel_deep_walk sp l0 with
      | (?dp, ?l1) =>
          lazymatch msat_cancel_deep_walk sq l1 with
          | (?dq, ?l2) => constr:((TheoryOfCancel.sepcon_deep dp dq, l2))
          end
      end
  | @Syntax.impp ?L0 ?minL0 ?sp ?sq =>
      lazymatch msat_cancel_deep_walk sp l0 with
      | (?dp, ?l1) =>
          lazymatch msat_cancel_deep_walk sq l1 with
          | (?dq, ?l2) => constr:((TheoryOfCancel.impp_deep dp dq, l2))
          end
      end
  | ?sp --> ?sq =>
      lazymatch msat_cancel_deep_walk sp l0 with
      | (?dp, ?l1) =>
          lazymatch msat_cancel_deep_walk sq l1 with
          | (?dq, ?l2) => constr:((TheoryOfCancel.impp_deep dp dq, l2))
          end
      end
  | emp => constr:((TheoryOfCancel.emp_deep, l0))
  | ?sp =>
      lazymatch msat_cancel_atom_index sp l0 with
      | (?i, ?l1) => constr:((TheoryOfCancel.varp_deep i, l1))
      end
  end.

Ltac msat_cancel_deep se :=
  lazymatch msat_cancel_deep_walk se (@nil Assertion) with
  | (TheoryOfCancel.impp_deep ?dp ?dq, ?tbl) => constr:((dp, dq, tbl))
  end.

(* Preserve shallow atoms in the position tree for residual reconstruction. *)
Ltac msat_cancel_pos_walk se :=
  lazymatch se with
  | @Syntax.sepcon ?L0 ?sepconL0 ?sp ?sq =>
      let tp := msat_cancel_pos_walk sp in
      let tq := msat_cancel_pos_walk sq in
      constr:(TheoryOfCancel.sepcon_pos tp tq)
  | ?sp ** ?sq =>
      let tp := msat_cancel_pos_walk sp in
      let tq := msat_cancel_pos_walk sq in
      constr:(TheoryOfCancel.sepcon_pos tp tq)
  | ?sp => constr:(TheoryOfCancel.var_pos sp None)
  end.

Ltac msat_cancel_pos_tree se :=
  lazymatch se with
  | @Syntax.impp ?L0 ?minL0 ?sp ?sq =>
      let tp := msat_cancel_pos_walk sp in
      let tq := msat_cancel_pos_walk sq in constr:((tp, tq))
  | ?sp --> ?sq =>
      let tp := msat_cancel_pos_walk sp in
      let tq := msat_cancel_pos_walk sq in constr:((tp, tq))
  end.

(* Reflect both sides, mark matching atoms, and apply [cancel_sound]. *)
Ltac msat_theory_cancel :=
    lazymatch goal with
    | |- ?provable_head ?se =>
        lazymatch msat_cancel_deep se with
        | (?dp, ?dq, ?tbl) =>
            lazymatch msat_cancel_pos_tree se with
            | (?tp, ?tq) =>
                let marked := eval cbv beta iota zeta delta
                  [TheoryOfCancel.cancel_mark TheoryOfCancel.cancel_mark'
                   TheoryOfCancel.cancel_mark_context TheoryOfCancel.beq
                   Nat.eqb] in
                  (TheoryOfCancel.cancel_mark dp dq tp tq) in
                lazymatch marked with
                | (?tp', ?tq') =>
                    apply (@TheoryOfCancel.cancel_sound
                      L minL sepconL empL GammaP minAX sepconAX
                      (@Deduction.Deduction2Axiomatization_empAX
                         L minL sepconL empL GammaD1 GammaP GammaD1P empD)
                      tp' tq');
                    [ cbv beta delta [TheoryOfCancel.cancel_same]; reflexivity
                    | cbv beta delta [TheoryOfCancel.cancel_different
                         TheoryOfCancel.unmark_sort];
                      repeat unfold TheoryOfCancel.unmark_sort'; idtac ]
                end
            end
        end
    end.

(* This adapter also supports partial cancellation; it is not a closer. *)
Ltac msat_cancel_sound :=
  lazymatch goal with
  | |- ?P |-- ?Q =>
    apply (proj2 (naive_C_Rules.__derivable1_provable P Q));
    msat_theory_cancel;
    change (@Logic.MinimumLogic.Syntax.impp
      naive_C_Rules.L naive_C_Rules.minL) with naive_C_Rules.impp;
    lazymatch goal with
    | |- ?provable_head (naive_C_Rules.impp ?RP ?RQ) =>
      change (naive_C_Rules.provable (naive_C_Rules.impp RP RQ));
      apply (proj1 (naive_C_Rules.__derivable1_provable RP RQ))
    end;
    change (@Logic.SeparationLogic.Syntax.sepcon
      naive_C_Rules.L naive_C_Rules.sepconL) with naive_C_Rules.sepcon;
    change (@Logic.SeparationLogic.Syntax.emp
      naive_C_Rules.L naive_C_Rules.empL) with naive_C_Rules.emp
  end.

(* Keep the fast path only when both the spatial and pure branches close. *)
Ltac msat_entailer_with tac :=
  first
    [ solve
        [ split_pure_spatial;
          [ Intros;
            msat_cancel_sound;
            change (emp |-- emp);
            cancel
          | Intros; split_pures; dump_pre_spatial;
            first [ solve [ simpl_entail_with tac ] | solve [ auto | tac ] ] ] ]
    | solve [ Intros; msat_cancel_sound; change (emp |-- emp); cancel ]
    | solve
        [ Intros; split_pures; dump_pre_spatial;
          first [ solve [ simpl_entail_with tac ] | solve [ auto | tac ] ] ]
    | solve [ simpl_entail_with tac ]
    | solve [ repeat split; solve [ auto | tac ] ] ].

Ltac msat_propagation_drained :=
  intros n F A_arr A_x M [_ Hprop] Hdrain;
  destruct Hprop as [Hweak Hlevel Hfrontier Hheap Hreasonless];
  constructor; try assumption;
  destruct Hheap as [Hcovers|[_ [Hpending _]]]; [exact Hcovers | lia].


Ltac msat_nodup :=
  repeat (constructor;
          [ let H := fresh "Hin" in
            intro H; simpl in H;
            repeat (destruct H as [H|H]); try lia; try contradiction
          | ]);
  constructor.

(* Exposing / refolding the first two cells of an [IntArray.seg]: the same
   two-element case analysis proves both directions. *)
Tactic Notation "msat_intarray_first_two" ident(a) ident(b) ident(rest) :=
  intros p l Hlen;
  destruct l as [|a l];
  [ rewrite Zlength_nil in Hlen; lia | ];
  destruct l as [|b rest];
  [ rewrite Zlength_cons, Zlength_nil in Hlen; lia | ];
  assert (Htail :
    sublist 2 (Zlength (a :: b :: rest)) (a :: b :: rest) = rest)
    by (rewrite (sublist_cons2 2 (Zlength (a :: b :: rest)) a (b :: rest))
          by (rewrite !Zlength_cons in Hlen |- *; lia);
        change (sublist 1 (Zlength (a :: b :: rest) - 1) (b :: rest) = rest);
        rewrite (sublist_cons2 1 (Zlength (a :: b :: rest) - 1) b rest)
          by (rewrite !Zlength_cons in Hlen |- *; lia);
        replace (Zlength (a :: b :: rest) - 1 - 1) with (Zlength rest)
          by (rewrite !Zlength_cons; lia);
        apply sublist_self; reflexivity);
  rewrite Htail;
  unfold IntArray.seg; simpl;
  replace (p + 0) with p by lia;
  replace
    (match sizeof(INT) with
     | 0 => 0
     | Z.pos y => Z.pos y
     | Z.neg y => Z.neg y
     end) with (sizeof(INT)) by (destruct (sizeof(INT)); reflexivity);
  change (Znth 0 (a :: b :: rest) 0) with a;
  change (Znth 1 (a :: b :: rest) 0) with b;
  cancel (p # Int |-> a);
  cancel ((p + 4) # Int |-> b);
  cancel.

(* Reconcile nested solver statistics fields with [stats_t] fields. *)

Tactic Notation "stats_dot_bridge" constr(s) ident(p) :=
  assert (E0 : &( s # "solver_t" ->ₛ "stats" .ₛ "starts")
               = &( p # "stats_t" ->ₛ "starts"))
    by (unfold p; csimpl; reflexivity);
  assert (E1 : &( s # "solver_t" ->ₛ "stats" .ₛ "decisions")
               = &( p # "stats_t" ->ₛ "decisions"))
    by (unfold p; csimpl; reflexivity);
  assert (E2 : &( s # "solver_t" ->ₛ "stats" .ₛ "propagations")
               = &( p # "stats_t" ->ₛ "propagations"))
    by (unfold p; csimpl; reflexivity);
  assert (E3 : &( s # "solver_t" ->ₛ "stats" .ₛ "inspects")
               = &( p # "stats_t" ->ₛ "inspects"))
    by (unfold p; csimpl; reflexivity);
  assert (E4 : &( s # "solver_t" ->ₛ "stats" .ₛ "conflicts")
               = &( p # "stats_t" ->ₛ "conflicts"))
    by (unfold p; csimpl; reflexivity);
  assert (E5 : &( s # "solver_t" ->ₛ "stats" .ₛ "clauses")
               = &( p # "stats_t" ->ₛ "clauses"))
    by (unfold p; csimpl; reflexivity);
  assert (E6 : &( s # "solver_t" ->ₛ "stats" .ₛ "clauses_literals")
               = &( p # "stats_t" ->ₛ "clauses_literals"))
    by (unfold p; csimpl; reflexivity);
  assert (E7 : &( s # "solver_t" ->ₛ "stats" .ₛ "learnts")
               = &( p # "stats_t" ->ₛ "learnts"))
    by (unfold p; csimpl; reflexivity);
  assert (E8 : &( s # "solver_t" ->ₛ "stats" .ₛ "learnts_literals")
               = &( p # "stats_t" ->ₛ "learnts_literals"))
    by (unfold p; csimpl; reflexivity);
  assert (E9 : &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals")
               = &( p # "stats_t" ->ₛ "max_literals"))
    by (unfold p; csimpl; reflexivity);
  assert (E10 : &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals")
               = &( p # "stats_t" ->ₛ "tot_literals"))
    by (unfold p; csimpl; reflexivity);
  rewrite E0, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
