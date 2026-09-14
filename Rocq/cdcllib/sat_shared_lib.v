Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
From ListLib.Base Require Import Positional Inductive.
From ListLib.General Require Import Length Forall NoDup Presuffix IndexedElements.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list.

(** * sat_shared_lib: representation-independent SAT semantics.

    Propositional literals, clauses and CNFs; total and partial valuations;
    satisfaction, entailment and the unit/counting vocabulary the dense solver
    arrays summarise ([clause_true_count], [clause_unassigned_count],
    [literal_var_count]); plus the list algebra those proofs need.  Nothing
    here mentions separation logic or any C data structure, so both verified
    solvers can share one meaning of "satisfiable".

    Importers:
      - [CDCLLib.cdcl_shared_lib] re-exports this file, and through it
      - the CDCL case library, and
      - the MiniSat model/library chain.
    Editing this file therefore rebuilds BOTH proof chains. *)

(* ==================== Syntax and valuations ==================== *)
(* The vocabulary every later group is phrased in: a literal is a signed
   variable index, a clause a list of literals, a CNF a list of clauses; a
   total valuation answers every variable, a partial one may answer None. *)

(* A literal is a variable index carrying a sign: Pos x asks for x true,
   Neg x asks for x false. *)
Inductive literal : Type :=
| Pos (x : Z)
| Neg (x : Z).

(* A clause is the disjunction of its literals. *)
Definition clause := list literal.

(* A CNF formula is the conjunction of its clauses. *)
Definition cnf := list clause.

(* A total valuation gives every variable a boolean value. *)
Definition valuation := Z -> bool.

(* The spelling the CDCL annotations use for a total valuation; it is the
   name declared Extern Coq in CDCL_qcp_def.h. *)
Definition Assignment := valuation.

(* A partial valuation leaves a variable unassigned by answering None. *)
Definition partial_valuation := Z -> option bool.

(* ==================== Function update ==================== *)
(* Point update of a function on Z, with its two computation rules.  Every
   one-variable state change in both solvers is stated as such an update, so a
   changed cell reduces through the same two lemmas on either side. *)

(* Override f at x with v and leave f alone everywhere else. *)
Definition sat_function_update {A : Type}
    (f : Z -> A) (x : Z) (v : A) : Z -> A :=
  fun y => if Z.eq_dec y x then v else f y.

(* Reading the updated point back gives the new value. *)
Lemma sat_function_update_eq : forall A (f : Z -> A) x v,
  sat_function_update f x v x = v.
Proof.
  intros A f x v. unfold sat_function_update.
  destruct (Z.eq_dec x x); [reflexivity | contradiction].
Qed.

(* Every other point keeps the value it had. *)
Lemma sat_function_update_neq : forall A (f : Z -> A) x y v,
  x <> y -> sat_function_update f x v y = f y.
Proof.
  intros A f x y v Hneq. unfold sat_function_update.
  destruct (Z.eq_dec y x); [congruence | reflexivity].
Qed.

(* ==================== Well-formedness and evaluation ==================== *)
(* What it means for a literal, a formula and a valuation to stay inside the n
   variables the solver allocated, and how a literal is evaluated under a total
   valuation and under a partial one. *)

(* Variable x is one of the n variables the solver allocated. *)
Definition var_in_range (n x : Z) : Prop := 0 <= x < n.

(* The variable a literal is about, forgetting its sign. *)
Definition literal_var (l : literal) : Z :=
  match l with Pos x | Neg x => x end.

(* A literal is well formed when its variable is in range. *)
Definition literal_wf (n : Z) (l : literal) : Prop :=
  var_in_range n (literal_var l).

(* A CNF is well formed when n is nonnegative and every literal of every
   clause is in range. *)
Definition cnf_wf (n : Z) (f : cnf) : Prop :=
  0 <= n /\ Forall (fun c => Forall (literal_wf n) c) f.

(* A valuation is bounded when it answers false outside the n allocated
   variables, so two bounded valuations differ only where it matters. *)
Definition bounded_valuation (n : Z) (rho : valuation) : Prop :=
  forall x, ~ var_in_range n x -> rho x = false.

(* Value of a literal under a total valuation. *)
Definition eval_literal (rho : valuation) (l : literal) : bool :=
  match l with
  | Pos x => rho x
  | Neg x => negb (rho x)
  end.

(* Value of a literal under a partial valuation, or None when the literal
   variable is still unassigned. *)
Definition eval_partial_literal
    (sigma : partial_valuation) (l : literal) : option bool :=
  match sigma (literal_var l) with
  | None => None
  | Some b =>
      Some (match l with Pos _ => b | Neg _ => negb b end)
  end.

(* ==================== Satisfaction, models, entailment ==================== *)
(* The meaning of the two verdicts a solver may return: cnf_sat n F is SAT,
   cnf_unsat n F is UNSAT.  entails_clause is the soundness obligation every
   clause the search learns has to meet. *)

(* A clause holds under rho when at least one of its literals is true. *)
Definition clause_satisfied (rho : valuation) (c : clause) : Prop :=
  exists l, In l c /\ eval_literal rho l = true.

(* rho models f when it satisfies every clause of f. *)
Definition models (rho : valuation) (f : cnf) : Prop :=
  Forall (clause_satisfied rho) f.

(* The SAT verdict: F is well formed and some bounded valuation models it. *)
Definition cnf_sat (n : Z) (F : cnf) : Prop :=
  cnf_wf n F /\
  exists J : Assignment, bounded_valuation n J /\ models J F.

(* c follows from f when every model of f satisfies c.  This is the
   obligation a learned clause has to meet for the search to stay sound. *)
Definition entails_clause (f : cnf) (c : clause) : Prop :=
  forall rho, models rho f -> clause_satisfied rho c.

(* The UNSAT verdict: F is well formed and no bounded valuation models it. *)
Definition cnf_unsat (n : Z) (f : cnf) : Prop :=
  cnf_wf n f /\
  forall rho, bounded_valuation n rho -> ~ models rho f.

(* ==================== Exact clause summaries ==================== *)
(* Per-clause counters: how many literals are already true, and how many are
   still unassigned.  The CDCL solver keeps exactly this pair in its C state
   (the true_counts and unassigned arrays of CDCL_qcp_def.h), and both solvers
   read a conflict and a unit clause off the two counters alone. *)

(** Exact summaries used as semantic state by the implementation. *)
Fixpoint clause_true_count
    (sigma : partial_valuation) (c : clause) : Z :=
  match c with
  | [] => 0
  | l :: c' =>
      match eval_partial_literal sigma l with
      | Some true => 1 + clause_true_count sigma c'
      | _ => clause_true_count sigma c'
      end
  end.

(* How many literals of c have a variable that is still unassigned. *)
Fixpoint clause_unassigned_count
    (sigma : partial_valuation) (c : clause) : Z :=
  match c with
  | [] => 0
  | l :: c' =>
      match eval_partial_literal sigma l with
      | None => 1 + clause_unassigned_count sigma c'
      | _ => clause_unassigned_count sigma c'
      end
  end.

(* Every literal of c is false under sigma: the conflict shape. *)
Definition clause_false
    (sigma : partial_valuation) (c : clause) : Prop :=
  forall l, In l c -> eval_partial_literal sigma l = Some false.

(* No true literal and exactly one unassigned literal: the shape that forces
   the remaining literal to be satisfied. *)
Definition clause_unit
    (sigma : partial_valuation) (c : clause) : Prop :=
  clause_true_count sigma c = 0 /\
  clause_unassigned_count sigma c = 1.

(* How many literals of c are about variable x, counting both signs. *)
Fixpoint literal_var_count (x : Z) (c : clause) : Z :=
  match c with
  | [] => 0
  | l :: c' =>
      if literal_var l =? x
      then 1 + literal_var_count x c'
      else literal_var_count x c'
  end.

(* How many literals of c about the variable x are made true by giving x
   the value b. *)
Fixpoint literal_true_at_count (x : Z) (b : bool) (c : clause) : Z :=
  match c with
  | [] => 0
  | l :: c' =>
      if literal_var l =? x
      then if eval_literal (fun _ => b) l
           then 1 + literal_true_at_count x b c'
           else literal_true_at_count x b c'
      else literal_true_at_count x b c'
  end.

(* Unassign x in sigma: the pure counterpart of the solver undoing an
   assignment on backtracking. *)
Definition clear_partial
    (sigma : partial_valuation) (x : Z) : partial_valuation :=
  sat_function_update sigma x None.

(* The literal about x that is true when x has the value b. *)
Definition satisfying_literal (x : Z) (b : bool) : literal :=
  if b then Pos x else Neg x.

(* The literal about x that is false when x has the value b. *)
Definition falsified_literal (x : Z) (b : bool) : literal :=
  if b then Neg x else Pos x.

(* ==================== Decidability ==================== *)
(* Case splits over a finite list of literals are discharged constructively
   rather than classically: Coq.Logic.Classical_Prop is deliberately not among
   the Require lines at the top of this file, and every case split over a
   literal or a clause membership is decided by one of the three procedures
   below. *)

(* Decidable equality of literals; the case-split engine for clause_mem_dec,
   for the counting lemmas below and for the watch frontier. *)
Definition literal_eq_dec (l1 l2 : literal) : {l1 = l2} + {l1 <> l2}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* Decide clause membership by induction using [literal_eq_dec].
   The proof is self-contained and does not rely on an unqualified [In_dec]. *)
Lemma clause_mem_dec :
  forall (l : literal) (c : clause), {In l c} + {~ In l c}.
Proof.
  intros l c. induction c as [|a c IH].
  - right. intros Hin. contradiction.
  - destruct (literal_eq_dec a l) as [Heq|Hne].
    + left. left. exact Heq.
    + destruct IH as [Hin|Hnin].
      * left. right. exact Hin.
      * right. intros [Ha|Hin]; [exact (Hne Ha)|exact (Hnin Hin)].
Qed.

(* Decides whether some literal of c is about the variable x, by the same
   induction as clause_mem_dec. *)
Lemma clause_var_occurs_dec :
  forall (c : clause) (x : Z),
    {exists l, In l c /\ literal_var l = x} +
    {~ exists l, In l c /\ literal_var l = x}.
Proof.
  induction c as [|l c IH]; intros x.
  - right. intros [l' [Hin _]]. contradiction.
  - destruct (Z.eq_dec (literal_var l) x) as [Heq|Hne].
    + left. exists l. split; [left; reflexivity|exact Heq].
    + destruct (IH x) as [Hyes|Hno].
      * left. destruct Hyes as [l' [Hin Hvar]].
        exists l'. split; [right; exact Hin|exact Hvar].
      * right. intros [l' [Hin Hvar]].
        destruct Hin as [Heql|Hin'].
        -- rewrite <- Heql in Hvar. exact (Hne Hvar).
        -- exact (Hno (ex_intro _ l' (conj Hin' Hvar))).
Qed.

(** ===== SEED CANDIDATES: generic list lemmas, future ListLib promotion targets ===== *)
(* promotion target: ListLib/Forall.v *)
Lemma Forall_Znth_elim :
  forall (A : Type) (P : A -> Prop) (l : list A) (d : A) i,
    Forall P l -> 0 <= i < Zlength l -> P (Znth i l d).
Proof.
  intros A P l; induction l as [|a l IH]; intros d i Hall Hi.
  - rewrite Zlength_nil in Hi; lia.
  - inversion Hall as [|? ? Ha Htail]; subst.
    rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons; exact Ha.
    + rewrite Znth_cons by lia.
      apply IH; [exact Htail|lia].
Qed.

(* promotion target: ListLib/Length.v *)
Lemma Znth_In :
  forall (A : Type) (l : list A) (d : A) i,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l; induction l as [|a l IH]; intros d i Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons; left; reflexivity.
    + rewrite Znth_cons by lia; right; apply IH; lia.
Qed.

(* promotion target: ListLib/Base/Positional.v *)
Lemma Znth_map :
  forall (A B : Type) (f : A -> B) (l : list A) (i : Z) (da : A) (db : B),
    0 <= i < Zlength l ->
    Znth i (List.map f l) db = f (Znth i l da).
Proof.
  intros A B f l; induction l as [|x xs IH]; intros i da db Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    cbn [List.map].
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + repeat rewrite Znth0_cons. reflexivity.
    + repeat rewrite Znth_cons by lia.
      apply IH. lia.
Qed.

(* promotion target: ListLib/Base/Positional.v *)
Lemma replace_Znth_replace_Znth_Same :
  forall (A : Type) (l : list A) i a b,
  0 <= i ->
  replace_Znth i b (replace_Znth i a l) = replace_Znth i b l.
Proof.
  intros A l. induction l as [|z l IH]; intros i a b Hi.
  - reflexivity.
  - destruct (Z.eq_dec i 0) as [->|Hi0].
    + reflexivity.
    + rewrite !replace_Znth_cons by lia.
      f_equal. apply IH. lia.
Qed.

(* promotion target: ListLib/NoDup.v *)
Lemma NoDup_Z_bounded_length : forall xs n,
  0 <= n ->
  NoDup xs ->
  (forall x, In x xs -> 0 <= x < n) ->
  Z.of_nat (List.length xs) <= n.
Proof.
  intros xs n Hn Hnodup Hbounded.
  assert (Hmap_nodup : NoDup (map Z.to_nat xs)).
  {
    induction xs as [|x xs IH]; simpl.
    - constructor.
    - inversion Hnodup as [|? ? Hnotin Htail]; subst.
      constructor.
      + intro Hin.
        apply in_map_iff in Hin.
        destruct Hin as [y [Heq Hyin]].
        apply Hnotin.
        assert (Hx0 : 0 <= x) by
          (pose proof (Hbounded x (or_introl eq_refl)); lia).
        assert (Hy0 : 0 <= y) by
          (pose proof (Hbounded y (or_intror Hyin)); lia).
        apply Z2Nat.inj in Heq; try assumption.
        subst y. exact Hyin.
      + apply IH.
        * exact Htail.
        * intros y Hy. apply Hbounded. right. exact Hy.
  }
  assert (Hincl : incl (map Z.to_nat xs) (seq 0 (Z.to_nat n))).
  {
    intros k Hkin.
    apply in_map_iff in Hkin.
    destruct Hkin as [x [<- Hxin]].
    apply in_seq.
    pose proof (Hbounded x Hxin) as [Hx0 Hxn].
    split; [lia|].
    apply Z2Nat.inj_lt; lia.
  }
  pose proof (NoDup_incl_length Hmap_nodup Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  exact Hlen.
Qed.

(* ==================== Verdict core and summary lemmas ==================== *)
(* The bulk of the file: how the two clause counters move when a variable is
   assigned and when the move is undone, which counter shapes force a unit or a
   conflict, and the few positional list facts the dense array proofs need. *)

(* Reading past the end of a list gives the default element. *)
Lemma znth_out_of_bounds :
  forall (A : Type) (l : list A) (d : A) i,
    0 <= i -> Zlength l <= i -> Znth i l d = d.
Proof.
  intros A l; induction l as [|a l IH]; intros d i Hi Hout.
  - unfold Znth; simpl; destruct (Z.to_nat i); reflexivity.
  - rewrite Zlength_cons in Hout.
    pose proof (Zlength_nonneg l).
    assert (i <> 0) by lia.
    rewrite Znth_cons by lia.
    apply IH; lia.
Qed.

(* A false clause has true count 0 and unassigned count 0. *)
Lemma clause_false_counts :
  forall sigma c,
    clause_false sigma c ->
    clause_true_count sigma c = 0 /\
    clause_unassigned_count sigma c = 0.
Proof.
  intros sigma c; induction c as [|l c IH]; intro Hfalse.
  - split; reflexivity.
  - assert (Hhead : eval_partial_literal sigma l = Some false).
    { apply Hfalse. left. reflexivity. }
    assert (Htail : clause_false sigma c).
    { intros l' Hin. apply Hfalse. right. exact Hin. }
    specialize (IH Htail).
    simpl. rewrite Hhead. simpl. exact IH.
Qed.

(* The UNSAT route: once F entails the empty clause, no bounded valuation
   models F -- this is the step that turns a derived empty clause into the
   UNSAT verdict. *)
Lemma entails_empty_cnf_unsat :
  forall n F,
    cnf_wf n F ->
    entails_clause F nil ->
    cnf_unsat n F.
Proof.
  intros n F Hwf Hentails.
  unfold cnf_unsat.
  split; [exact Hwf|].
  intros rho Hbounded Hmodels.
  specialize (Hentails rho Hmodels).
  unfold clause_satisfied in Hentails.
  destruct Hentails as [l [Hin _]].
  contradiction.
Qed.

(** The constructive core of the SAT verdict.  Under "every literal of [c] is
    assigned", the clause is either false outright or contains a true literal.
    This dichotomy is what [classic] used to supply; it needs no axiom, because
    [c] is a finite list and each literal's value under [sigma] is a
    computation.  Establishing it constructively is what makes the CDCL
    endgame -- and hence the whole mathematical core of both developments --
    axiom-free. *)
(* A fully assigned clause is either false or holds by a true literal. *)
Lemma partial_clause_false_or_true :
  forall sigma c,
    (forall l, In l c ->
      exists b, sigma (literal_var l) = Some b) ->
    clause_false sigma c \/
    (exists l, In l c /\ eval_partial_literal sigma l = Some true).
Proof.
  intros sigma c.
  induction c as [|l c IH]; intros Hassigned.
  - left. intros l Hin. contradiction.
  - destruct (Hassigned l (or_introl eq_refl)) as [b Hb].
    assert (Heval : exists v, eval_partial_literal sigma l = Some v).
    {
      unfold eval_partial_literal.
      rewrite Hb.
      eexists. reflexivity.
    }
    destruct Heval as [v Heval].
    destruct v.
    + right. exists l. split; [left; reflexivity|exact Heval].
    + assert (Htail_assigned : forall l', In l' c ->
        exists b', sigma (literal_var l') = Some b').
      { intros l' Hin. apply Hassigned. right. exact Hin. }
      destruct (IH Htail_assigned) as [Htailfalse|[l' [Hin Htrue]]].
      * left. intros l' [<- | Hin]; [exact Heval|exact (Htailfalse l' Hin)].
      * right. exists l'. split; [right; exact Hin|exact Htrue].
Qed.

(* A fully assigned clause that is not false exhibits a true literal. *)
Lemma partial_clause_has_true :
  forall sigma c,
    (forall l, In l c ->
      exists b, sigma (literal_var l) = Some b) ->
    ~ clause_false sigma c ->
    exists l, In l c /\ eval_partial_literal sigma l = Some true.
Proof.
  intros sigma c Hassigned Hnotfalse.
  destruct (partial_clause_false_or_true
              sigma c Hassigned) as [Hfalse|Htrue].
  - contradiction.
  - exact Htrue.
Qed.

(* A total valuation agreeing with sigma on the variable of l gives l the
   value sigma gives it: the bridge from the partial state to a model. *)
Lemma eval_partial_literal_total_agree :
  forall sigma rho l v b,
    sigma (literal_var l) = Some b ->
    rho (literal_var l) = b ->
    eval_partial_literal sigma l = Some v ->
    eval_literal rho l = v.
Proof.
  intros sigma rho [x|x] v b Hassigned Hagree Heval;
    unfold eval_partial_literal in Heval; simpl in *;
    rewrite Hassigned in Heval;
    inversion Heval; subst v;
    rewrite Hagree; reflexivity.
Qed.

(* A literal only evaluates under sigma if its variable is assigned. *)
Lemma eval_partial_literal_assigned :
  forall sigma l v,
    eval_partial_literal sigma l = Some v ->
    exists b, sigma (literal_var l) = Some b.
Proof.
  intros sigma [y|y] v; unfold literal_var, eval_partial_literal; simpl;
    destruct (sigma y) as [b|] eqn:Hcell; intro H; try discriminate;
    eauto.
Qed.

(* The occurrence counter is nonnegative. *)
Lemma literal_var_count_nonneg : forall x c, 0 <= literal_var_count x c.
Proof.
  intros x c; induction c as [|l c IH].
  - reflexivity.
  - cbn [literal_var_count].
    destruct (literal_var l =? x).
    + change (0 <= 1 + literal_var_count x c).
      lia.
    + exact IH.
Qed.

(* The true-at counter is nonnegative. *)
Lemma literal_true_at_count_nonneg : forall x b c,
  0 <= literal_true_at_count x b c.
Proof.
  intros x b c; induction c as [|l c IH].
  - reflexivity.
  - cbn [literal_true_at_count].
    destruct (literal_var l =? x).
    + destruct (eval_literal (fun _ => b) l).
      * change (0 <= 1 + literal_true_at_count x b c).
        lia.
      * exact IH.
    + exact IH.
Qed.

(* The counter update law for an assignment: giving an unassigned x the value
   b lowers the unassigned count of c by the occurrences of x in c and raises
   its true count by the occurrences that b makes true. *)
Lemma clause_counts_assign : forall sigma x b c,
  sigma x = None ->
  clause_unassigned_count (sat_function_update sigma x (Some b)) c =
    clause_unassigned_count sigma c - literal_var_count x c /\
  clause_true_count (sat_function_update sigma x (Some b)) c =
    clause_true_count sigma c + literal_true_at_count x b c.
Proof.
  intros sigma x b c; induction c as [|l c IH]; intro Hx.
  - split; reflexivity.
  - cbn -[eval_partial_literal sat_function_update Z.add Z.sub] in *.
  specialize (IH Hx).
  destruct l as [y|y];
    destruct (Z.eq_dec x y) as [->|Hxy].
  + replace (eval_partial_literal (sat_function_update sigma y (Some b)) (Pos y))
      with (Some b) by
        (unfold eval_partial_literal; rewrite sat_function_update_eq; reflexivity).
    replace (eval_partial_literal sigma (Pos y)) with (None : option bool) by
      (unfold eval_partial_literal, literal_var; destruct (sigma y) eqn:Hy;
       [rewrite Hx in Hy; discriminate|reflexivity]).
    rewrite Z.eqb_refl. destruct IH as [IHu IHt].
    destruct b; cbn -[Z.add Z.sub]; split; lia.
  + replace (eval_partial_literal (sat_function_update sigma x (Some b)) (Pos y))
      with (eval_partial_literal sigma (Pos y)) by
        (unfold eval_partial_literal;
         rewrite sat_function_update_neq by exact Hxy; reflexivity).
    assert (Hyx : (y =? x) = false) by (apply Z.eqb_neq; lia).
    replace (y =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct IH as [IHu IHt].
    destruct (eval_partial_literal sigma (Pos y)) as [[|]|];
      cbn -[Z.add Z.sub]; rewrite Hyx; rewrite IHu, IHt.
    all: split; lia.
  + replace (eval_partial_literal (sat_function_update sigma y (Some b)) (Neg y))
      with (Some (negb b)) by
        (unfold eval_partial_literal; rewrite sat_function_update_eq; reflexivity).
    replace (eval_partial_literal sigma (Neg y)) with (None : option bool) by
      (unfold eval_partial_literal, literal_var; destruct (sigma y) eqn:Hy;
       [rewrite Hx in Hy; discriminate|reflexivity]).
    rewrite Z.eqb_refl. destruct IH as [IHu IHt].
    destruct b; cbn -[Z.add Z.sub]; split; lia.
  + replace (eval_partial_literal (sat_function_update sigma x (Some b)) (Neg y))
      with (eval_partial_literal sigma (Neg y)) by
        (unfold eval_partial_literal;
         rewrite sat_function_update_neq by exact Hxy; reflexivity).
    assert (Hyx : (y =? x) = false) by (apply Z.eqb_neq; lia).
    replace (y =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct IH as [IHu IHt].
    destruct (eval_partial_literal sigma (Neg y)) as [[|]|];
      cbn -[Z.add Z.sub]; rewrite Hyx;
      rewrite IHu, IHt; split; lia.
Qed.

(* The same law read backwards: unassigning x moves both counters the other
   way by the same two amounts. *)
Lemma clause_counts_clear : forall sigma x b c,
  sigma x = Some b ->
  clause_unassigned_count (clear_partial sigma x) c =
    clause_unassigned_count sigma c + literal_var_count x c /\
  clause_true_count (clear_partial sigma x) c =
    clause_true_count sigma c - literal_true_at_count x b c.
Proof.
  intros sigma x b c; induction c as [|l c IH]; intro Hx.
  - split; reflexivity.
  - cbn -[eval_partial_literal clear_partial sat_function_update Z.add Z.sub] in *.
  specialize (IH Hx).
  destruct l as [y|y];
    destruct (Z.eq_dec x y) as [->|Hxy].
  + replace (eval_partial_literal (clear_partial sigma y) (Pos y))
      with (None : option bool) by
      (unfold eval_partial_literal, clear_partial;
       rewrite sat_function_update_eq; reflexivity).
    replace (eval_partial_literal sigma (Pos y)) with (Some b) by
      (unfold eval_partial_literal, literal_var; destruct (sigma y) eqn:Hy;
       [inversion Hx; subst; reflexivity|discriminate]).
    rewrite Z.eqb_refl. destruct IH as [IHu IHt].
    destruct b; cbn -[Z.add Z.sub]; split; lia.
  + replace (eval_partial_literal (clear_partial sigma x) (Pos y))
      with (eval_partial_literal sigma (Pos y)) by
        (unfold eval_partial_literal, clear_partial;
         rewrite sat_function_update_neq by exact Hxy; reflexivity).
    assert (Hyx : (y =? x) = false) by (apply Z.eqb_neq; lia).
    replace (y =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct IH as [IHu IHt].
    destruct (eval_partial_literal sigma (Pos y)) as [[|]|];
      cbn -[Z.add Z.sub]; rewrite Hyx;
      rewrite IHu, IHt; split; lia.
  + replace (eval_partial_literal (clear_partial sigma y) (Neg y))
      with (None : option bool) by
      (unfold eval_partial_literal, clear_partial;
       rewrite sat_function_update_eq; reflexivity).
    replace (eval_partial_literal sigma (Neg y)) with (Some (negb b)) by
      (unfold eval_partial_literal, literal_var; destruct (sigma y) eqn:Hy;
       [inversion Hx; subst; reflexivity|discriminate]).
    rewrite Z.eqb_refl. destruct IH as [IHu IHt].
    destruct b; cbn -[Z.add Z.sub]; split; lia.
  + replace (eval_partial_literal (clear_partial sigma x) (Neg y))
      with (eval_partial_literal sigma (Neg y)) by
        (unfold eval_partial_literal, clear_partial;
         rewrite sat_function_update_neq by exact Hxy; reflexivity).
    assert (Hyx : (y =? x) = false) by (apply Z.eqb_neq; lia).
    replace (y =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct IH as [IHu IHt].
    destruct (eval_partial_literal sigma (Neg y)) as [[|]|];
      cbn -[Z.add Z.sub]; rewrite Hyx;
      rewrite IHu, IHt; split; lia.
Qed.

(* The true count lies between 0 and the length of the clause. *)
Lemma clause_true_count_bounds :
  forall (sigma : partial_valuation) (c : clause),
    0 <= clause_true_count sigma c <= Zlength c.
Proof.
  intros sigma c.
  induction c as [| l c IH].
  - cbn [clause_true_count].
    rewrite Zlength_nil. lia.
  - cbn [clause_true_count].
    rewrite Zlength_cons.
    destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
    + destruct b; lia.
    + exact (conj (proj1 IH)
        (Z.le_trans _ _ _ (proj2 IH) (Z.le_succ_diag_r _))).
Qed.

(* The unassigned count lies between 0 and the length of the clause. *)
Lemma clause_unassigned_count_bounds :
  forall (sigma : partial_valuation) (c : clause),
    0 <= clause_unassigned_count sigma c <= Zlength c.
Proof.
  intros sigma c.
  induction c as [| l c IH].
  - cbn [clause_unassigned_count].
    rewrite Zlength_nil. lia.
  - cbn [clause_unassigned_count].
    rewrite Zlength_cons.
    destruct (eval_partial_literal sigma l) eqn:Heval.
    + exact (conj (proj1 IH)
        (Z.le_trans _ _ _ (proj2 IH) (Z.le_succ_diag_r _))).
    + lia.
Qed.

(* Nonnegativity of the true count on its own, the form the arithmetic
   side conditions of the CDCL bound proofs chain on. *)
Lemma clause_true_count_nonnegative_base :
  forall sigma c, 0 <= clause_true_count sigma c.
Proof.
  intros sigma c; induction c as [|l c IH];
    cbn -[eval_partial_literal Z.add]; [lia|].
  destruct (eval_partial_literal sigma l) as [[|]|];
    cbn -[eval_partial_literal Z.add]; lia.
Qed.

(* Nonnegativity of the unassigned count on its own, the same use. *)
Lemma clause_unassigned_count_nonnegative_base :
  forall sigma c, 0 <= clause_unassigned_count sigma c.
Proof.
  intros sigma c; induction c as [|l c IH];
    cbn -[eval_partial_literal Z.add]; [lia|].
  destruct (eval_partial_literal sigma l) as [[|]|];
    cbn -[eval_partial_literal Z.add]; lia.
Qed.

(* Both counters zero is the same thing as a false clause: the converse of
   clause_false_counts, and how a conflict is recognised from the arrays. *)
Lemma clause_counts_zero_false :
  forall sigma c,
    clause_true_count sigma c = 0 ->
    clause_unassigned_count sigma c = 0 ->
    clause_false sigma c.
Proof.
  intros sigma c; induction c as [|l c IH]; intros Htrue Hun l' Hin.
  - contradiction.
  - simpl in Hin; cbn -[eval_partial_literal Z.add] in Htrue, Hun.
    destruct (eval_partial_literal sigma l) as [[|]|] eqn:Heval.
    + pose proof (clause_true_count_nonnegative_base sigma c); lia.
    + destruct Hin as [<-|Hin]; [exact Heval|].
      eapply IH; eauto.
    + pose proof (clause_unassigned_count_nonnegative_base sigma c); lia.
Qed.

(* One true literal already puts the true count at one or more. *)
Lemma clause_true_count_member_true :
  forall sigma c l,
    In l c -> eval_partial_literal sigma l = Some true ->
    1 <= clause_true_count sigma c.
Proof.
  intros sigma c; induction c as [|a c IH]; intros l Hin Heval.
  - contradiction.
  - simpl in Hin; cbn -[eval_partial_literal Z.add].
    destruct Hin as [->|Hin].
    + rewrite Heval.
      pose proof
        (clause_true_count_nonnegative_base sigma c);
      lia.
    + specialize (IH l Hin Heval).
      destruct (eval_partial_literal sigma a) as [[|]|];
        cbn -[eval_partial_literal Z.add]; lia.
Qed.

(* One unassigned literal already puts the unassigned count at one or more. *)
Lemma clause_unassigned_count_member_none :
  forall sigma c l,
    In l c -> eval_partial_literal sigma l = None ->
    1 <= clause_unassigned_count sigma c.
Proof.
  intros sigma c; induction c as [|a c IH]; intros l Hin Heval.
  - contradiction.
  - simpl in Hin; cbn -[eval_partial_literal Z.add].
    destruct Hin as [->|Hin].
    + rewrite Heval.
      pose proof
        (clause_unassigned_count_nonnegative_base
          sigma c);
      lia.
    + specialize (IH l Hin Heval).
      destruct (eval_partial_literal sigma a) as [[|]|];
        cbn -[eval_partial_literal Z.add]; lia.
Qed.

(* Two distinct unassigned literals put the unassigned count at two or more,
   which is how the unit shape is ruled out. *)
Lemma clause_unassigned_count_two_none :
  forall sigma c l1 l2,
    l1 <> l2 -> In l1 c -> In l2 c ->
    eval_partial_literal sigma l1 = None ->
    eval_partial_literal sigma l2 = None ->
    2 <= clause_unassigned_count sigma c.
Proof.
  intros sigma c; induction c as [|a c IH];
    intros l1 l2 Hneq H1 H2 He1 He2.
  - contradiction.
  - simpl in H1, H2; cbn -[eval_partial_literal Z.add].
    destruct H1 as [H1|H1], H2 as [H2|H2].
    + subst; contradiction.
    + subst a; rewrite He1.
      pose proof
        (clause_unassigned_count_member_none
          sigma c l2 H2 He2); lia.
    + subst a; rewrite He2.
      pose proof
        (clause_unassigned_count_member_none
          sigma c l1 H1 He1); lia.
    + specialize (IH l1 l2 Hneq H1 H2 He1 He2).
      destruct (eval_partial_literal sigma a) as [[|]|];
        cbn -[eval_partial_literal Z.add]; lia.
Qed.

(* While x is unassigned its satisfying literal has no value. *)
Lemma eval_satisfying_literal_none :
  forall sigma x b,
    sigma x = None ->
    eval_partial_literal sigma (satisfying_literal x b) = None.
Proof.
  intros sigma x []; unfold satisfying_literal, eval_partial_literal,
    literal_var; simpl; intros H; rewrite H; reflexivity.
Qed.

(* Once x holds b its satisfying literal is true. *)
Lemma eval_satisfying_literal_true :
  forall sigma x b,
    sigma x = Some b ->
    eval_partial_literal sigma (satisfying_literal x b) = Some true.
Proof.
  intros sigma x []; unfold satisfying_literal, eval_partial_literal,
    literal_var; simpl; intros H; rewrite H; reflexivity.
Qed.

(* Conversely, a true satisfying literal pins the value of x under rho. *)
Lemma eval_satisfying_literal_true_inv : forall rho x b,
  eval_literal rho (satisfying_literal x b) = true -> rho x = b.
Proof.
  intros rho x [|] H; simpl in H; [exact H|].
  destruct (rho x); simpl in H; [discriminate|reflexivity].
Qed.

(* Once x holds b its falsified literal is false. *)
Lemma eval_falsified_literal_false :
  forall sigma x b,
    sigma x = Some b ->
    eval_partial_literal sigma (falsified_literal x b) = Some false.
Proof.
  intros sigma x []; unfold falsified_literal, eval_partial_literal,
    literal_var; simpl; intros H; rewrite H; reflexivity.
Qed.

(* In a unit clause whose unassigned literal is about x, every literal about
   another variable is false: the premise the antecedent record needs. *)
Lemma clause_unit_other_false :
  forall sigma c x b,
    clause_unit sigma c -> sigma x = None ->
    In (satisfying_literal x b) c ->
    forall l, In l c -> literal_var l <> x ->
      eval_partial_literal sigma l = Some false.
Proof.
  intros sigma c x b [Htrue Hunassigned] Hnone HinSat l Hin Hvar.
  pose proof
    (eval_satisfying_literal_none
      sigma x b Hnone) as Hsatnone.
  assert (Hneq : l <> satisfying_literal x b).
  { intro Heq; subst l; unfold satisfying_literal in Hvar;
      destruct b; cbn in Hvar; contradiction. }
  destruct (eval_partial_literal sigma l) as [[|]|] eqn:Heval.
  - exfalso.
    pose proof
      (clause_true_count_member_true
        sigma c l Hin Heval); lia.
  - reflexivity.
  - exfalso.
    pose proof
      (clause_unassigned_count_two_none
        sigma c l (satisfying_literal x b) Hneq Hin HinSat
        Heval Hsatnone); lia.
Qed.

(* A clause that never mentions x has both x counters at zero. *)
Lemma literal_counts_no_var :
  forall x b c,
    (forall l, In l c -> literal_var l <> x) ->
    literal_var_count x c = 0 /\ literal_true_at_count x b c = 0.
Proof.
  intros x b c; induction c as [|l c IH]; intro Hnone.
  - split; reflexivity.
  - cbn [literal_var_count literal_true_at_count].
    assert (Hlx : literal_var l <> x) by (apply Hnone; left; reflexivity).
    assert (Heq : Z.eqb (literal_var l) x = false)
      by (apply Z.eqb_neq; exact Hlx).
    rewrite Heq.
    apply IH; intros l' Hin; apply Hnone; right; exact Hin.
Qed.

(* An unassigned variable leaves both of its literals without a value. *)
Lemma eval_partial_literal_unassigned :
  forall sigma l,
    sigma (literal_var l) = None -> eval_partial_literal sigma l = None.
Proof.
  intros sigma [y|y]; unfold literal_var, eval_partial_literal; simpl;
    intro H; rewrite H; reflexivity.
Qed.

(* A literal about x that occurs in c puts the occurrence count at one or more. *)
Lemma literal_var_count_member :
  forall x c l,
    In l c -> literal_var l = x -> 1 <= literal_var_count x c.
Proof.
  intros x c; induction c as [|a c IH]; intros l Hin Hvar.
  - contradiction.
  - cbn [literal_var_count]; simpl in Hin.
    destruct Hin as [->|Hin].
    + rewrite Hvar, Z.eqb_refl.
      pose proof (literal_var_count_nonneg x c); lia.
    + destruct (Z.eqb (literal_var a) x);
        specialize (IH l Hin Hvar); lia.
Qed.

(* The satisfying literal of x occurring in c puts the true-at count at one
   or more. *)
Lemma literal_true_count_member_satisfying :
  forall x b c,
    In (satisfying_literal x b) c ->
    1 <= literal_true_at_count x b c.
Proof.
  intros x b c; induction c as [|a c IH]; intro Hin.
  - contradiction.
  - cbn [literal_true_at_count]; simpl in Hin.
    destruct Hin as [->|Hin].
    + assert (Hvar :
        Z.eqb (literal_var (satisfying_literal x b)) x = true).
      { destruct b; cbn [satisfying_literal literal_var];
          apply Z.eqb_refl. }
      rewrite Hvar.
      assert (Heval : eval_literal (fun _ : Z => b)
        (satisfying_literal x b) = true).
      { destruct b; reflexivity. }
      rewrite Heval.
      pose proof (literal_true_at_count_nonneg x b c); lia.
    + destruct (Z.eqb (literal_var a) x);
        [destruct (eval_literal (fun _ : Z => b) a)|];
        specialize (IH Hin); lia.
Qed.

(* At most as many occurrences of x are made true as there are occurrences. *)
Lemma literal_true_count_le_var_count :
  forall x b c,
    literal_true_at_count x b c <= literal_var_count x c.
Proof.
  intros x b c; induction c as [|a c IH].
  - reflexivity.
  - cbn [literal_true_at_count literal_var_count].
    destruct (Z.eqb (literal_var a) x); [destruct (eval_literal (fun _ => b) a)|];
      lia.
Qed.

(* Satisfying the unassigned literal of a unit clause leaves that clause with
   true count 1 and unassigned count 0: propagation makes a clause satisfied. *)
Lemma unit_assignment_counts :
  forall sigma x b c,
    sigma x = None -> clause_unit sigma c ->
    In (satisfying_literal x b) c ->
    clause_true_count (sat_function_update sigma x (Some b)) c = 1 /\
    clause_unassigned_count (sat_function_update sigma x (Some b)) c = 0.
Proof.
  intros sigma x b c Hnone [Htrue Hunassigned] Hin.
  destruct (clause_counts_assign sigma x b c Hnone) as
    [Hunassigned_eq Htrue_eq].
  assert (Hvar_ge : 1 <= literal_var_count x c).
  { eapply literal_var_count_member;
      [exact Hin|destruct b; reflexivity]. }
  pose proof
    (clause_unassigned_count_nonnegative_base
      (sat_function_update sigma x (Some b)) c) as Hnew_unassigned_nonneg.
  assert (Hvar : literal_var_count x c = 1) by lia.
  assert (Htrue_ge : 1 <= literal_true_at_count x b c).
  { apply literal_true_count_member_satisfying;
      exact Hin. }
  pose proof (literal_true_count_le_var_count
    x b c) as Htrue_le.
  assert (Htrue_at : literal_true_at_count x b c = 1) by lia.
  split; lia.
Qed.

(* A true literal makes the true count strictly positive. *)
Lemma clause_true_count_positive :
  forall sigma c l,
  In l c -> eval_partial_literal sigma l = Some true ->
  0 < clause_true_count sigma c.
Proof.
  intros sigma c; induction c as [|h c IH]; intros l Hin Heval.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + cbn [clause_true_count]. rewrite Heval.
      change (0 < 1 + clause_true_count sigma c).
      pose proof (clause_true_count_bounds
        sigma c); lia.
    + specialize (IH l Hin Heval).
      cbn [clause_true_count].
      destruct (eval_partial_literal sigma h) as [[|]|].
      * change (0 < 1 + clause_true_count sigma c).
        pose proof (clause_true_count_bounds
          sigma c); lia.
      * exact IH.
      * exact IH.
Qed.

(* A clause whose variables are all above x does not mention x. *)
Lemma literal_var_count_zero_below : forall x c,
  (forall l, In l c -> x < literal_var l) ->
  literal_var_count x c = 0.
Proof.
  intros x c; induction c as [|l c IH]; intros Hbelow.
  - reflexivity.
  - cbn [literal_var_count].
    assert (Hlx : literal_var l <> x).
    { specialize (Hbelow l ltac:(left; reflexivity)); lia. }
    rewrite (proj2 (Z.eqb_neq _ _) Hlx).
    apply IH. intros l' Hin. apply Hbelow. right; exact Hin.
Qed.

(* If either sign of x occurs in c, the occurrence count is positive. *)
Lemma literal_var_count_positive_of_in :
  forall x c,
  In (Pos x) c \/ In (Neg x) c -> 0 < literal_var_count x c.
Proof.
  intros x c; induction c as [|l c IH]; intros Hin.
  - destruct Hin as [Hin|Hin]; contradiction.
  - cbn [literal_var_count].
    destruct (Z.eqb (literal_var l) x) eqn:Hlx.
    + pose proof (literal_var_count_nonneg x c); lia.
    + apply IH.
      destruct Hin as [[Heq|Hin]|[Heq|Hin]].
      * subst l; cbn in Hlx; rewrite Z.eqb_refl in Hlx; discriminate.
      * left; exact Hin.
      * subst l; cbn in Hlx; rewrite Z.eqb_refl in Hlx; discriminate.
      * right; exact Hin.
Qed.

(* If neither sign of x occurs in c, the occurrence count is zero. *)
Lemma literal_var_count_zero_if_absent :
  forall x c,
  ~ In (Pos x) c -> ~ In (Neg x) c -> literal_var_count x c = 0.
Proof.
  intros x c; induction c as [|l c IH]; intros Hpos Hneg.
  - reflexivity.
  - cbn [literal_var_count].
    destruct l as [y|y]; cbn [literal_var].
    + assert (Hy : y <> x).
      { intro; subst y; apply Hpos; left; reflexivity. }
      rewrite (proj2 (Z.eqb_neq _ _) Hy).
      apply IH; intro Hin; [apply Hpos|apply Hneg]; right; exact Hin.
    + assert (Hy : y <> x).
      { intro; subst y; apply Hneg; left; reflexivity. }
      rewrite (proj2 (Z.eqb_neq _ _) Hy).
      apply IH; intro Hin; [apply Hpos|apply Hneg]; right; exact Hin.
Qed.

(* Once x holds b, the literals of c that b makes true are among the literals
   the whole state makes true. *)
Lemma literal_true_at_count_le_true_count :
  forall sigma x b c,
  sigma x = Some b ->
  literal_true_at_count x b c <= clause_true_count sigma c.
Proof.
  intros sigma x b c; induction c as [|l c IH]; intros Hsigma.
  - reflexivity.
  - cbn -[eval_partial_literal Z.add Z.sub] in *.
    specialize (IH Hsigma).
    destruct l as [y|y]; destruct (Z.eq_dec x y) as [->|Hxy].
    + replace (eval_partial_literal sigma (Pos y)) with (Some b) by
        (unfold eval_partial_literal, literal_var; rewrite Hsigma; reflexivity).
      rewrite Z.eqb_refl. destruct b; cbn -[Z.add Z.sub]; lia.
    + assert (Hyx : Z.eqb y x = false) by (apply Z.eqb_neq; lia).
      destruct (eval_partial_literal sigma (Pos y)) as [[|]|];
        cbn -[Z.add Z.sub]; rewrite Hyx; lia.
    + replace (eval_partial_literal sigma (Neg y)) with (Some (negb b)) by
        (unfold eval_partial_literal, literal_var; rewrite Hsigma; reflexivity).
      rewrite Z.eqb_refl. destruct b; cbn -[Z.add Z.sub]; lia.
    + assert (Hyx : Z.eqb y x = false) by (apply Z.eqb_neq; lia).
      destruct (eval_partial_literal sigma (Neg y)) as [[|]|];
        cbn -[Z.add Z.sub]; rewrite Hyx; lia.
Qed.

(* Compatibility name for the same fact as
   [clause_unassigned_count_nonnegative_base].  Existing callers use this name;
   the binder spelling does not change the proposition. *)
Lemma clause_unassigned_count_nonneg :
  forall sigma L, 0 <= clause_unassigned_count sigma L.
Proof.
  intros sigma L.
  induction L as [|l L IH]; [reflexivity|].
  simpl.
  destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
  - exact IH.
  - change (0 <= 1 + clause_unassigned_count sigma L).
    lia.
Qed.

(* An unassigned member puts the unassigned count of L at one or more. *)
Lemma clause_unassigned_count_ge_one :
  forall sigma L u,
    In u L ->
    eval_partial_literal sigma u = None ->
    1 <= clause_unassigned_count sigma L.
Proof.
  intros sigma L.
  induction L as [|l L IH]; intros u Hin Hnone.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [<-|Hin].
    + simpl. rewrite Hnone.
      pose proof
        (clause_unassigned_count_nonneg
          sigma L) as Hcount_nonneg.
      change (1 + 0 <= 1 + clause_unassigned_count sigma L).
      apply Z.add_le_mono_l.
      exact Hcount_nonneg.
    + simpl.
      specialize (IH u Hin Hnone).
      destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
      * exact IH.
      * change (1 <= 1 + clause_unassigned_count sigma L).
        lia.
Qed.

(* A duplicate-free clause with one unassigned literal and every other
   literal false is exactly a unit clause, in counter form. *)
Lemma clause_counts_unique_none :
  forall sigma L u,
    NoDup L ->
    In u L ->
    eval_partial_literal sigma u = None ->
    (forall l, In l L -> l <> u ->
      eval_partial_literal sigma l = Some false) ->
    clause_true_count sigma L = 0 /\
    clause_unassigned_count sigma L = 1.
Proof.
  intros sigma L.
  induction L as [|l L IH]; intros u Hnodup Hin Hnone Hother.
  - contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    destruct
      (literal_eq_dec l u) as [Heq|Hneq].
    + subst l.
      assert (Htailfalse : clause_false sigma L).
      {
        intros l' Hin'.
        apply Hother.
        - right. exact Hin'.
        - intro Heq'.
          subst l'.
          contradiction.
      }
      pose proof
        (clause_false_counts
          sigma L Htailfalse) as [Ht Hu].
      simpl. rewrite Hnone, Ht, Hu.
      split; lia.
    + assert (Hin_tail : In u L).
      { destruct Hin as [Heq|Hin]; [contradiction|exact Hin]. }
      assert (Hother_tail :
        forall l', In l' L -> l' <> u ->
          eval_partial_literal sigma l' = Some false).
      {
        intros l' Hin' Hneq'.
        apply Hother; [right; exact Hin'|exact Hneq'].
      }
      specialize (IH u Hnodup_tail Hin_tail Hnone Hother_tail)
        as [Ht Hu].
      assert (Hlfalse : eval_partial_literal sigma l = Some false).
      { apply Hother; [left; reflexivity|exact Hneq]. }
      simpl. rewrite Hlfalse, Ht, Hu.
      split; reflexivity.
Qed.

(* Two distinct unassigned members of a duplicate-free clause put its
   unassigned count at two or more: the clause does not assert yet. *)
Lemma clause_unassigned_count_ge_two :
  forall sigma L u v,
    NoDup L ->
    In u L ->
    In v L ->
    u <> v ->
    eval_partial_literal sigma u = None ->
    eval_partial_literal sigma v = None ->
    2 <= clause_unassigned_count sigma L.
Proof.
  intros sigma L.
  induction L as [|l L IH];
    intros u v Hnodup Hinu Hinv Huv Hnoneu Hnonev.
  - contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    destruct
      (literal_eq_dec l u) as [Hlu|Hlu].
    + subst l.
      assert (Hinv_tail : In v L).
      {
        destruct Hinv as [Hvu|Hinv].
        - exfalso. apply Huv. exact Hvu.
        - exact Hinv.
      }
      simpl. rewrite Hnoneu.
      pose proof
        (clause_unassigned_count_ge_one
          sigma L v Hinv_tail Hnonev) as Hcount.
      change (1 + 1 <= 1 + clause_unassigned_count sigma L).
      apply Z.add_le_mono_l.
      exact Hcount.
    + destruct
        (literal_eq_dec l v) as [Hlv|Hlv].
      * subst l.
        assert (Hinu_tail : In u L).
        {
          destruct Hinu as [Hvu|Hinu].
          - exfalso. apply Huv. symmetry. exact Hvu.
          - exact Hinu.
        }
        simpl. rewrite Hnonev.
        pose proof
          (clause_unassigned_count_ge_one
            sigma L u Hinu_tail Hnoneu) as Hcount.
        change (1 + 1 <= 1 + clause_unassigned_count sigma L).
        apply Z.add_le_mono_l.
        exact Hcount.
      * assert (Hinu_tail : In u L).
        { destruct Hinu as [H|H]; [contradiction|exact H]. }
        assert (Hinv_tail : In v L).
        { destruct Hinv as [H|H]; [contradiction|exact H]. }
        specialize
          (IH u v Hnodup_tail Hinu_tail Hinv_tail
            Huv Hnoneu Hnonev).
        simpl.
        destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
        -- exact IH.
        -- change (2 <= 1 + clause_unassigned_count sigma L).
           lia.
Qed.

(* In a duplicate-free clause whose variables are pairwise distinct, a
   variable that occurs at all occurs exactly once. *)
Lemma literal_var_count_unique_one :
  forall c x,
    NoDup c ->
    (forall l1 l2,
      In l1 c -> In l2 c ->
      literal_var l1 = literal_var l2 -> l1 = l2) ->
    (exists l, In l c /\ literal_var l = x) ->
    literal_var_count x c = 1.
Proof.
  intros c.
  induction c as [|h c IH]; intros x Hnodup Hinjective Hexists.
  - destruct Hexists as [l [Hin _]]. contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    destruct (Z.eq_dec (literal_var h) x) as [Hhead|Hhead].
    + assert (Habsent : forall l, In l c -> literal_var l <> x).
      {
        intros l Hin Hlx.
        assert (Hl_eq : l = h).
        {
          apply Hinjective; [right; exact Hin|left; reflexivity|].
          lia.
        }
        subst l. contradiction.
      }
      pose proof
        (literal_counts_no_var x true c Habsent)
        as [Htail _].
      unfold literal_var_count; fold literal_var_count.
      destruct (literal_var h =? x)%Z eqn:Heq.
      * lia.
      * apply Z.eqb_neq in Heq. contradiction.
    + assert (Hexists_tail : exists l, In l c /\ literal_var l = x).
      {
        destruct Hexists as [l [[Hl|Hl] Hvar]].
        - subst l. contradiction.
        - exists l. split; assumption.
      }
      assert (Hinjective_tail : forall l1 l2,
        In l1 c -> In l2 c ->
        literal_var l1 = literal_var l2 -> l1 = l2).
      {
        intros l1 l2 Hin1 Hin2 Hvar.
        apply Hinjective; [right|right|]; assumption.
      }
      specialize (IH x Hnodup_tail Hinjective_tail Hexists_tail).
      unfold literal_var_count; fold literal_var_count.
      destruct (literal_var h =? x)%Z eqn:Heq.
      * apply Z.eqb_eq in Heq. contradiction.
      * exact IH.
Qed.

(* No variable occurs twice in c, so a variable determines its literal. *)
Definition clause_var_injective (c : clause) : Prop :=
  forall l1 l2,
    In l1 c -> In l2 c -> literal_var l1 = literal_var l2 -> l1 = l2.

(* Distinct variables in the projected list give that injectivity. *)
Lemma NoDup_map_var_injective : forall c : clause,
  NoDup (map literal_var c) -> clause_var_injective c.
Proof.
  intros c Hnd.
  induction c as [|a c IH]; intros l1 l2 Hin1 Hin2 Hv.
  - destruct Hin1.
  - cbn [map] in Hnd. inversion Hnd as [|? ? Hna Hnd']; subst.
    destruct Hin1 as [E1|Hin1]; destruct Hin2 as [E2|Hin2].
    + congruence.
    + subst l1. exfalso. apply Hna. rewrite Hv. apply in_map. exact Hin2.
    + subst l2. exfalso. apply Hna. rewrite <- Hv. apply in_map.
      exact Hin1.
    + exact (IH Hnd' l1 l2 Hin1 Hin2 Hv).
Qed.

(* In such a clause, a literal about x that occurs beside the satisfying
   literal of x is that literal. *)
Lemma clause_var_injective_var_lit :
  forall c x b l,
    clause_var_injective c ->
    In (satisfying_literal x b) c ->
    In l c -> literal_var l = x ->
    l = satisfying_literal x b.
Proof.
  intros c x b l Hinj Hsat Hin Hvar.
  apply Hinj; [exact Hin|exact Hsat|].
  rewrite Hvar; destruct b; reflexivity.
Qed.

(* Two states that differ only at x agree on every literal about another
   variable: the frame rule of the counting lemmas. *)
Lemma eval_partial_literal_other :
  forall sigma1 sigma2 x l,
    (forall y, y <> x -> sigma2 y = sigma1 y) ->
    literal_var l <> x ->
    eval_partial_literal sigma2 l = eval_partial_literal sigma1 l.
Proof.
  intros sigma1 sigma2 x [y|y] Hsame Hneq;
    unfold eval_partial_literal; simpl in *;
    rewrite Hsame by exact Hneq; reflexivity.
Qed.

(* Agreement on the variable of l is enough to give l the same value. *)
Lemma eval_partial_literal_assignment_at :
  forall sigma1 sigma2 l,
    sigma1 (literal_var l) = sigma2 (literal_var l) ->
    eval_partial_literal sigma1 l = eval_partial_literal sigma2 l.
Proof.
  intros sigma1 sigma2 [x|x] Heq;
    unfold eval_partial_literal, literal_var in *;
    rewrite Heq;
    reflexivity.
Qed.

(* A literal that is false cannot be about a variable that is unassigned. *)
Lemma eval_false_var_not_none :
  forall sigma x l,
    sigma x = None ->
    eval_partial_literal sigma l = Some false ->
    literal_var l <> x.
Proof.
  intros sigma x l Hnone Hfalse Heq.
  assert (Hnone_l : sigma (literal_var l) = None).
  { rewrite Heq. exact Hnone. }
  unfold eval_partial_literal in Hfalse.
  rewrite Hnone_l in Hfalse.
  discriminate.
Qed.

(* ==================== Negation ==================== *)
(* Flipping the sign of a literal, and how the two evaluators react.  The watch
   frontier of cdcl_shared_lib.v is stated over negated literals, so this group
   is the bridge between a false literal and frontier membership. *)

(* Flip the sign of a literal, keeping its variable. *)
Definition literal_neg (l : literal) : literal :=
  match l with
  | Pos x => Neg x
  | Neg x => Pos x
  end.

(* Flipping twice is the identity. *)
Lemma literal_neg_involutive : forall l, literal_neg (literal_neg l) = l.
Proof. intros [x|x]; reflexivity. Qed.

(* Flipping a sign keeps the variable. *)
Lemma literal_var_neg : forall l, literal_var (literal_neg l) = literal_var l.
Proof. intros [x|x]; reflexivity. Qed.

(* Under a total valuation the flipped literal takes the negated value. *)
Lemma eval_literal_neg : forall rho l,
  eval_literal rho (literal_neg l) = negb (eval_literal rho l).
Proof.
  intros rho [x|x]; simpl; [reflexivity|].
  rewrite negb_involutive; reflexivity.
Qed.

(* Under a partial valuation the flipped literal negates the option, with
   None staying None. *)
Lemma eval_partial_literal_neg : forall s l,
  eval_partial_literal s (literal_neg l)
  = option_map negb (eval_partial_literal s l).
Proof.
  intros s [x|x]; unfold eval_partial_literal, literal_neg, literal_var;
    simpl; destruct (s x) as [b|]; simpl; try reflexivity.
  rewrite negb_involutive; reflexivity.
Qed.

(* The negation of the literal x satisfies is the literal x falsifies. *)
Lemma literal_neg_satisfying : forall x b,
  literal_neg (satisfying_literal x b) = falsified_literal x b.
Proof. intros x [|]; reflexivity. Qed.


(* A false literal is the falsified literal of its own variable value: how a
   conflict clause is read back as a set of assignments. *)
Lemma eval_partial_false_shape :
  forall (s : partial_valuation) (l : literal),
  eval_partial_literal s l = Some false ->
  exists b, s (literal_var l) = Some b /\
            l = falsified_literal (literal_var l) b.
Proof.
  intros s [x|x] H; unfold eval_partial_literal, literal_var in H;
    cbn in H.
  - destruct (s x) as [b|] eqn:E; [|discriminate].
    injection H as ->. exists false. split; [exact E|reflexivity].
  - destruct (s x) as [b|] eqn:E; [|discriminate].
    destruct b; cbn in H; [|discriminate].
    exists true. split; [exact E|reflexivity].
Qed.


(* ==================== Units and entailment ==================== *)
(* Extending a formula by derived unit clauses.  cnf_with_units F A is what the
   search has really refuted when it reports UNSAT under a set A of assumed
   literals, so the monotonicity lemmas of this group carry that verdict. *)

(* The one-literal clause, the clause form of an assumed literal. *)
Definition unit_clause (l : literal) : clause := [l].

(* F extended by one unit clause per assumed literal of A. *)
Definition cnf_with_units (F : cnf) (A : list literal) : cnf :=
  F ++ map unit_clause A.

(* Satisfaction only depends on the multiset of literals. *)
Lemma clause_satisfied_perm : forall rho c c',
  Permutation c c' -> clause_satisfied rho c -> clause_satisfied rho c'.
Proof.
  intros rho c c' Hperm [l [Hin Heval]].
  exists l. split; [|exact Heval].
  eapply Permutation_in; eauto.
Qed.

(* Falsity only depends on the multiset of literals. *)
Lemma clause_false_perm : forall sigma c c',
  Permutation c c' -> clause_false sigma c -> clause_false sigma c'.
Proof.
  intros sigma c c' Hperm Hfalse l Hin.
  apply Hfalse.
  eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hin].
Qed.

(* Entailment only depends on the multiset of literals of the conclusion,
   which is what lets a learned clause be reordered. *)
Lemma entails_clause_perm : forall F c c',
  Permutation c c' -> entails_clause F c -> entails_clause F c'.
Proof.
  intros F c c' Hperm Hent rho Hmodels.
  eapply clause_satisfied_perm; [exact Hperm|apply Hent; exact Hmodels].
Qed.

(* A clause of the formula is entailed by it. *)
Lemma entails_clause_in : forall F c, In c F -> entails_clause F c.
Proof.
  intros F c Hin rho Hmodels.
  unfold models in Hmodels.
  rewrite Forall_forall in Hmodels.
  apply Hmodels; exact Hin.
Qed.

(* A model of a formula models each of its subsets. *)
Lemma models_incl : forall rho F G,
  incl F G -> models rho G -> models rho F.
Proof.
  intros rho F G Hincl Hmodels.
  unfold models in *.
  rewrite Forall_forall in *.
  intros c Hc. apply Hmodels. apply Hincl. exact Hc.
Qed.

(* Entailment survives adding clauses to the formula. *)
Lemma entails_clause_mono : forall F G c,
  incl F G -> entails_clause F c -> entails_clause G c.
Proof.
  intros F G c Hincl Hent rho Hmodels.
  apply Hent. eapply models_incl; eauto.
Qed.

(* Assuming more literals gives a larger formula. *)
Lemma cnf_with_units_incl : forall F A B,
  incl A B -> incl (cnf_with_units F A) (cnf_with_units F B).
Proof.
  intros F A B H c Hc. unfold cnf_with_units in *.
  apply in_app_or in Hc. apply in_or_app.
  destruct Hc as [Hc|Hc]; [left; exact Hc|right].
  apply in_map_iff in Hc. destruct Hc as [a [<- Ha]].
  apply in_map. apply H. exact Ha.
Qed.

(* Entailment under a set of assumptions survives assuming more. *)
Lemma entails_units_mono : forall F A B c,
  incl A B ->
  entails_clause (cnf_with_units F A) c -> entails_clause (cnf_with_units F B) c.
Proof.
  intros F A B c H Hent.
  eapply entails_clause_mono; [apply cnf_with_units_incl; exact H|exact Hent].
Qed.

(* Resolution in the form the search uses: if c is entailed, l is in c and
   the negation of every other member is entailed, then l alone is entailed. *)
Lemma entails_unit_step : forall F c l,
  entails_clause F c ->
  In l c ->
  (forall l', In l' c -> l' <> l -> entails_clause F [literal_neg l']) ->
  entails_clause F [l].
Proof.
  intros F c l Hent Hinl Hothers rho Hmodels.
  destruct (Hent rho Hmodels) as [k [Hink Hk]].
  destruct (literal_eq_dec k l) as [->|Hne].
  - exists l. split; [left; reflexivity|exact Hk].
  - exfalso.
    destruct (Hothers k Hink Hne rho Hmodels) as [k' [Hink' Hk']].
    destruct Hink' as [<-|[]].
    rewrite eval_literal_neg, Hk in Hk'. discriminate.
Qed.

(* Modelling the unit part is the same as making every assumed literal true. *)
Lemma models_units_iff : forall rho A,
  models rho (map unit_clause A) <->
  Forall (fun a => eval_literal rho a = true) A.
Proof.
  intros rho A. unfold models. split.
  - intro H. induction A as [|a A IH]; [constructor|].
    cbn [map] in H.
    inversion H as [|? ? Hhead Htail]; subst.
    destruct Hhead as [k [Hink Hk]].
    destruct Hink as [<-|[]].
    constructor; [exact Hk|apply IH; exact Htail].
  - intro H. induction H as [|a A Ha HA IH]; [constructor|].
    cbn [map]. constructor; [|exact IH].
    exists a. split; [left; reflexivity|exact Ha].
Qed.

(* Building a model of the extended formula from the two halves. *)
Lemma models_clause_units_intro : forall rho F A,
  models rho F ->
  Forall (fun a => eval_literal rho a = true) A ->
  models rho (cnf_with_units F A).
Proof.
  intros rho F A HF HA.
  unfold cnf_with_units, models.
  apply Forall_app. split; [exact HF|].
  apply (proj2 (models_units_iff rho A)); exact HA.
Qed.

(* Reading the two halves back off a model of the extended formula. *)
Lemma models_clause_units_elim : forall rho F A,
  models rho (cnf_with_units F A) ->
  models rho F /\ Forall (fun a => eval_literal rho a = true) A.
Proof.
  intros rho F A H.
  unfold cnf_with_units, models in H.
  apply Forall_app in H. destruct H as [HF HA].
  split; [exact HF|].
  apply (proj1 (models_units_iff rho A)); exact HA.
Qed.

(* The two directions above as one equivalence. *)
Lemma models_cnf_with_units : forall rho F A,
  models rho (cnf_with_units F A) <->
  models rho F /\ Forall (fun a => eval_literal rho a = true) A.
Proof.
  intros rho F A. split.
  - apply models_clause_units_elim.
  - intros [HF HA]. apply models_clause_units_intro; assumption.
Qed.

(* What F entails, F with assumptions entails. *)
Lemma entails_clause_units_weaken : forall F A c,
  entails_clause F c -> entails_clause (cnf_with_units F A) c.
Proof.
  intros F A c Hent.
  apply (entails_clause_mono F (cnf_with_units F A) c).
  - unfold cnf_with_units. intros x Hx. apply in_or_app. left. exact Hx.
  - exact Hent.
Qed.

(* An assumed literal is entailed by the extended formula. *)
Lemma entails_clause_units_unit : forall F A a,
  In a A -> entails_clause (cnf_with_units F A) [a].
Proof.
  intros F A a Hin.
  apply entails_clause_in.
  unfold cnf_with_units. apply in_or_app. right.
  apply in_map with (f := unit_clause) in Hin. exact Hin.
Qed.

(* The extended formula is well formed when the assumed literals are. *)
Lemma cnf_with_units_wf : forall n F A,
  cnf_wf n F -> Forall (literal_wf n) A -> cnf_wf n (cnf_with_units F A).
Proof.
  intros n F A [Hn HF] HA.
  split; [exact Hn|].
  unfold cnf_with_units. apply Forall_app. split; [exact HF|].
  apply Forall_map. revert HA. apply Forall_impl.
  intros a Ha. unfold unit_clause. constructor; [exact Ha|constructor].
Qed.

(* ==================== Restriction and congruence ==================== *)
(* Two valuations that agree on the n allocated variables model the same well
   formed CNF, so any model can be replaced by its bounded restriction: the
   step that turns a found assignment into the SAT verdict. *)

(* Agreement on the variable of a literal is enough to give it the same value. *)
Lemma eval_literal_congr : forall rho rho' l,
  rho (literal_var l) = rho' (literal_var l) ->
  eval_literal rho l = eval_literal rho' l.
Proof. intros rho rho' [x|x] H; simpl in *; rewrite H; reflexivity. Qed.

(* Two valuations agreeing on the n allocated variables model the same well
   formed CNF. *)
Lemma models_congr_on_range : forall n G rho rho',
  cnf_wf n G ->
  (forall x, 0 <= x < n -> rho x = rho' x) ->
  models rho G -> models rho' G.
Proof.
  intros n G rho rho' [_ Hwf] Hagree Hm.
  unfold models in *. rewrite Forall_forall in *.
  intros c Hc.
  destruct (Hm c Hc) as [l [Hin Heval]].
  specialize (Hwf c Hc). rewrite Forall_forall in Hwf.
  specialize (Hwf l Hin). unfold literal_wf, var_in_range in Hwf.
  exists l. split; [exact Hin|].
  rewrite <- (eval_literal_congr rho rho' l (Hagree _ Hwf)). exact Heval.
Qed.

(* rho cut down to the n allocated variables, answering false outside. *)
Definition rho_restrict (n : Z) (rho : valuation) : valuation :=
  fun x => if 0 <=? x then (if x <? n then rho x else false) else false.

(* Inside the range the restriction answers what rho answers. *)
Lemma rho_restrict_in : forall n rho x,
  0 <= x < n -> rho_restrict n rho x = rho x.
Proof.
  intros n rho x [H1 H2]. unfold rho_restrict.
  assert (E1 : (0 <=? x) = true) by (apply Z.leb_le; lia).
  assert (E2 : (x <? n) = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2. reflexivity.
Qed.

(* The restriction is bounded, so it is a witness the SAT verdict accepts. *)
Lemma rho_restrict_bounded : forall n rho, bounded_valuation n (rho_restrict n rho).
Proof.
  intros n rho x Hx. unfold var_in_range in Hx. unfold rho_restrict.
  destruct (0 <=? x) eqn:E1; [|reflexivity].
  destruct (x <? n) eqn:E2; [|reflexivity].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply Hx. lia.
Qed.

(* Any model of a well formed CNF restricts to a bounded model of it. *)
Lemma models_rho_restrict : forall n G rho,
  cnf_wf n G -> models rho G -> models (rho_restrict n rho) G.
Proof.
  intros n G rho Hwf Hm.
  eapply models_congr_on_range; [exact Hwf | | exact Hm].
  intros x Hx. symmetry. apply rho_restrict_in. exact Hx.
Qed.

(* Unsatisfiability under a set of assumptions survives assuming more,
   provided the added literals are in range: the verdict is stable under the
   assumptions the search has not undone yet. *)
Lemma cnf_unsat_units_mono : forall n F A A',
  incl A A' ->
  Forall (literal_wf n) A' ->
  cnf_unsat n (cnf_with_units F A) ->
  cnf_unsat n (cnf_with_units F A').
Proof.
  intros n F A A' Hincl HA'wf [Hwf Hun].
  assert (HFwf : cnf_wf n F).
  { destruct Hwf as [Hn Hall].
    unfold cnf_with_units in Hall. apply Forall_app in Hall.
    split; [exact Hn | apply Hall]. }
  split; [apply cnf_with_units_wf; assumption|].
  intros rho Hb Hm. apply (Hun rho Hb).
  apply models_cnf_with_units.
  pose proof (proj1 (models_cnf_with_units rho F A') Hm) as [HmF HA'true].
  split; [exact HmF|].
  apply Forall_forall. intros a Ha.
  rewrite Forall_forall in HA'true.
  apply HA'true. apply Hincl. exact Ha.
Qed.
