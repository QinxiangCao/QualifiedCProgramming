Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(photo:list(list Z))->bool; true denotes #Color. *)
Definition Pixel (c : Z) : Prop :=
  c = 67 \/ c = 77 \/ c = 89 \/ c = 87 \/ c = 71 \/ c = 66.

Definition Pre (photo : list (list Z)) : Prop :=
  (* The solver Require states these constraints explicitly:
       1 <= Zlength photo <= 100 /\
       exists m, 1 <= m <= 100 /\
         Forall (fun row => Zlength row = m /\ Forall Pixel row) photo. *)
  True.

Definition HasColor (photo : list (list Z)) : Prop :=
  exists row c, In row photo /\ In c row /\ (c = 67 \/ c = 77 \/ c = 89).

Definition Spec (photo : list (list Z)) (out : bool) : Prop :=
  (out = true /\ HasColor photo) \/ (out = false /\ ~ HasColor photo).

Definition SolverReturnBridge (out : bool) (ret : Z) : Prop :=
  (out = true /\ ret = 1) \/ (out = false /\ ret = 0).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma Zlength_concat_uniform__initialization :
  forall (rows : list (list Z)) (width : Z),
    Forall (fun row => Zlength row = width) rows ->
    Zlength (concat rows) = Zlength rows * width.
Proof.
  intros rows width Hrows.
  induction Hrows as [| row rows Hrow Hrows IH]; simpl.
  - reflexivity.
  - rewrite Zlength_app, Zlength_cons, Hrow, IH. lia.
Qed.

Lemma pre_rectangular_facts__initialization :
  forall (photo : list (list Z)) (n m : Z) (d : list Z),
    n = Zlength photo ->
    (forall i, 0 <= i < n -> Zlength (Znth i photo d) = m) ->
    Zlength (concat photo) = n * m.
Proof.
  intros photo n m d Hn Hrows.
  assert (Hall : Forall (fun row => Zlength row = m) photo).
  {
    apply Forall_forall.
    intros row Hin.
    pose proof (@In_nth (list Z) photo row d Hin) as [i [Hi Hnth]].
    specialize (Hrows (Z.of_nat i)).
    specialize (Hrows ltac:(rewrite Hn, Zlength_correct; lia)).
    unfold Znth in Hrows.
    rewrite Nat2Z.id in Hrows.
    rewrite Hnth in Hrows.
    exact Hrows.
  }
  pose proof (Zlength_concat_uniform__initialization photo m Hall) as Hconcat.
  rewrite Hconcat, <- Hn.
  reflexivity.
Qed.
Lemma has_color_concat_characterization__results :
  forall photo,
    HasColor photo <->
    exists c, In c (concat photo) /\ (c = 67 \/ c = 77 \/ c = 89).
Proof.
  intros photo.
  split.
  - intros [row [c [Hrow [Hc Hcolor]]]].
    exists c.
    split; [| exact Hcolor].
    apply in_concat.
    exists row.
    split; assumption.
  - intros [c [Hc Hcolor]].
    apply in_concat in Hc.
    destruct Hc as [row [Hrow Hc]].
    exists row, c.
    repeat split; assumption.
Qed.
Lemma Znth_In_range__results :
  forall {A : Type} (l : list A) i (d : A),
    0 <= i < Zlength l ->
    In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma In_Znth_Zlength__results :
  forall {A : Type} (l : list A) (x d : A),
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  pose proof (@In_nth A l x d Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    exact Hnth.
Qed.
