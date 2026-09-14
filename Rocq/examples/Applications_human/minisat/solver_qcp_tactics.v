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
(* Load the reals and Flocq modules; [Binary] is imported below.
   The additional local imports used by [MSatFloatFacts] are in
   [solver_qcp_model.v], inside that module. *)
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


(* Proof tactics using the shared framework vocabulary. *)

(* G7 compliance: this file calls `entailer_with` directly instead of the `entailer!`
   notation, whose own definition is `entailer_with ltac:(lia || nia || int_auto)`
   (CommonAssertion.v).  A Tactic Notation body resolves its names where the notation is
   DEFINED, so `entailer!` itself needs no `int_auto` in scope here; the textual
   expansion resolves at the USE site instead, and does need the name in scope.
   Aliasing the one tactic avoids importing the module's other names.
   `solver_qcp_strategy_proof.v` inherits this by importing us. *)
Ltac int_auto := AUXLib.int_auto.int_auto.

(* Certified spatial cancellation shared by library and manual proofs.
   The existing proof-common engine is moved here without tactic-body edits.
   It uses the framework's [TheoryOfCancel.cancel_sound] certificate and
   leaves the unmatched spatial entailment to the caller. *)

(* Length of the Ltac-level atom table [ls], in continuation-passing style:
   [k] receives the [nat].  The table is an Ltac list of [Assertion]s built
   while the entailment is reflected, so its length is a tactic-level
   computation, not [List.length]. *)
Ltac msat_cancel_len ls k :=
  lazymatch ls with
  | nil => k O
  | _ :: ?tl => msat_cancel_len tl ltac:(fun n => k (S n))
  end.

(* [msat_cancel_len] under the identity continuation: returns the length. *)
Ltac msat_cancel_length ls := msat_cancel_len ls ltac:(fun n => n).

(* Predecessor of a [nat] literal, saturating at [O]. *)
Ltac msat_cancel_pred n :=
  lazymatch n with O => O | S ?m => m end.

(* Look the atom [n] up in the table.  [l] is the not-yet-examined suffix and
   [i] the index of its head, counting DOWN from the length of the whole table
   [l0], because the table is built by consing on the front.  Returns
   [(index, table)]: the existing index if [n] is already there, otherwise the
   fresh index and the extended table. *)
Ltac msat_cancel_index_walk n i l l0 :=
  lazymatch l with
  | nil => let len := msat_cancel_length l0 in constr:((S len, n :: l0))
  | n :: ?tl => constr:((i, l0))
  | _ :: ?tl =>
      let pi := msat_cancel_pred i in msat_cancel_index_walk n pi tl l0
  end.

(* Index of the atom [n] in the table [l], extending [l] when [n] is new. *)
Ltac msat_cancel_atom_index n l :=
  let len := msat_cancel_length l in msat_cancel_index_walk n len l l.

(* Reflect the assertion [se] into [TheoryOfCancel]'s deep syntax, threading
   the atom table [l0] through so that syntactically equal atoms get the same
   index.  Returns [(deep_term, table)].  Both the raw [Syntax.sepcon] /
   [Syntax.impp] applications and their [**] / [-->] notations are matched:
   which of the two a goal shows depends on how it was built. *)
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

(* Reflect the whole entailment: split the deep implication into its two
   sides and return [(lhs, rhs, atom_table)]. *)
Ltac msat_cancel_deep se :=
  lazymatch msat_cancel_deep_walk se (@nil Assertion) with
  | (TheoryOfCancel.impp_deep ?dp ?dq, ?tbl) => constr:((dp, dq, tbl))
  end.

(* The position tree of one side of the entailment: the same [sepcon] spine
   as the deep term, but keeping the SHALLOW atoms, which is what
   [cancel_sound] needs to rebuild the residual goal. *)
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

(* The position trees of both sides of the entailment [se], as a pair. *)
Ltac msat_cancel_pos_tree se :=
  lazymatch se with
  | @Syntax.impp ?L0 ?minL0 ?sp ?sq =>
      let tp := msat_cancel_pos_walk sp in
      let tq := msat_cancel_pos_walk sq in constr:((tp, tq))
  | ?sp --> ?sq =>
      let tp := msat_cancel_pos_walk sp in
      let tq := msat_cancel_pos_walk sq in constr:((tp, tq))
  end.

(* Cancels the syntactically equal atoms of a separation-logic entailment.
   Reflects both sides into [TheoryOfCancel]'s deep syntax over one shared
   atom table, marks the matching pairs with [cancel_mark], applies
   [cancel_sound], and discharges the "same" side by [reflexivity].  It ends
   in [idtac], leaving the residual entailment open, so every call site keeps
   its own closer.  Called from solver_qcp_proof_manual_part4.v (two direct calls). *)
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

(* Convert native entailment to the existing engine's provable implication,
   then return its residual to native entailment and connective spellings.
   This adapter also supports partial cancellation; it is not a closer. *)
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

(* Keep the fast path only when both the spatial and pure branches close.
   [solve] makes any remaining goal fail the first alternative; [first] then
   restores the original proof state before running the original closer. *)
Ltac msat_entailer_with tac :=
  first
    [ solve
        [ split_pure_spatial;
          [ Intros;
            msat_cancel_sound;
            change (emp |-- emp);
            reflexivity
          | entailer_with tac ] ]
    | entailer_with tac ].

(* Shared script for the two drained-propagation exits: the stable and the
   assuming carrier are discharged by the very same steps, only the name of
   the assumption list binder differs. *)
Ltac msat_propagation_drained :=
  intros n F A_arr A_x M [_ Hprop] Hdrain;
  destruct Hprop as [Hweak Hlevel Hfrontier Hheap Hreasonless];
  constructor; try assumption;
  destruct Hheap as [Hcovers|[_ [Hpending _]]]; [exact Hcovers | lia].

(** Closing note on the contract vocabulary above.  The exact seed shadow is
    kept in C-facing contracts, while semantic
    endgames depend only on seed finiteness.  The weak/strong split likewise
    keeps transient propagation-frontier and heap facts out of UNSAT returns.
    Assumption-loop failure routes use [msolver_inv_assuming], whose processed
    prefix is indexed by the current decision level rather than the stale
    stored root.  Derived facts such as [db_entailed], [trail_covers], and
    totality at an empty covered heap remain lemmas instead of record fields. *)

(** * Computation tactics for the consistency witnesses.

    The [w0_inv], [w2_inv], [w3_weak] and [w4_assuming_gen] witnesses are
    declared in [solver_qcp_lib.v], under [msat_s10_witness].  The tactics
    below support their finite calculations and record projections. *)

(** ** Tiny computation helpers. *)

Ltac msat_nodup :=
  repeat (constructor;
          [ let H := fresh "Hin" in
            intro H; simpl in H;
            repeat (destruct H as [H|H]); try lia; try contradiction
          | ]);
  constructor.

(* A [replace_Znth] outside a sublist window is invisible to that window.
   [D] is the element type's default (0 for Z, nil for a list of lists). *)
Ltac msat_sublist_replace_outside D :=
  intros l i v lo hi Hrange Hhi Hi Hout;
  apply (proj2 (list_eq_ext
    (sublist lo hi (replace_Znth i v l)) (sublist lo hi l) D));
  split;
  [ rewrite !Zlength_sublist by (rewrite ?Zlength_replace_Znth; lia); lia
  | intros k Hk;
    assert (Hk' : 0 <= k < hi - lo)
      by (rewrite Zlength_sublist in Hk by
            (rewrite ?Zlength_replace_Znth; lia);
          exact Hk);
    rewrite !Znth_sublist by lia;
    apply Znth_replace_Znth_Diff; lia ].

(* Exposing / refolding the first two cells of an [IntArray.seg]: the same
   two-element case analysis proves both directions.  [a] [b] [rest] name the
   list head cells the destructs introduce. *)
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
  entailer_with lia.

(* ====================================================================== *)
(* The stats field SPELLING bridge.                                       *)
(*                                                                        *)
(*   [stats_rep p st] spells its fields as [&( p # "stats_t" ->s f )]     *)
(*   with p the stats sub-object; every addclause VC spells the same      *)
(*   address dotted, [&( s # "solver_t" ->s "stats" .s f )].  QCP has no  *)
(*   congruence closure over spellings, so the two are unrelated atoms    *)
(*   and no entailer will bridge them.                                    *)
(*                                                                        *)
(*   [csimpl] is the framework's normaliser for exactly this (its own     *)
(*   test suite proves the identity, CNotation.v).  But it must be aimed  *)
(*   at a SMALL goal: run on the full eleven-field entailment under the   *)
(*   solver frame it does not terminate.  The corpus recipe (used by      *)
(*   proof_of_solver_analyze_which_implies_wit_2 in part5) is to [set]    *)
(*   the stats pointer -- which both fixes the typing, since the bare     *)
(*   nested form is an rvalue_expr rather than an addr, and shrinks each  *)
(*   goal to a two-term address equation -- then rewrite.                 *)
(*                                                                        *)
(*   Done once here, these two lemmas serve all ten stats-touching        *)
(*   addclause VCs (8 return wits + which_implies 10 and 11).             *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* The stats address bridge, once.  The lemmas below each pasted the same
   eleven address equalities [Ei : &(s->stats .f) = &(p->stats_t f)], each
   closed by the same [unfold p / csimpl / reflexivity] script, plus the
   eleven-way rewrite (about 35 lines apiece).  [csimpl] is cheap ONLY on such
   a bare address equality, as in the [solver_dot_addr] block; the
   tactic sequence here is the one the eleven proofs would otherwise each
   spell out.
   [p] is taken as an ident so [unfold p] still names the [set] alias.    *)
(* ---------------------------------------------------------------------- *)
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
