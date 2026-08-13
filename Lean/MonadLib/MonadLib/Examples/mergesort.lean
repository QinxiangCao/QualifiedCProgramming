import MonadLib.StateRelMonad.safeexec_lib
import AUXLib.ListLib.Base

namespace MonadLib.Examples.mergesort

open FP AUXLib
open MonadLib StateRelMonad
open scoped MonadNotation StateRelMonadNotation

def merge_body :
    List Int × List Int × List Int ->
      MONAD (CntOrBrk (List Int × List Int × List Int) (List Int)) :=
  fun (l1, l2, l3) =>
    match l1, l2 with
    | [], _ => ret (.by_break (l3 ++ l2))
    | _, [] => ret (.by_break (l3 ++ l1))
    | x :: l1', y :: l2' =>
        choice
          (test' (x <= y) ;; ret (.by_continue (l1', l2, l3 ++ [x])))
          (test' (y <= x) ;; ret (.by_continue (l1, l2', l3 ++ [y])))

def merge_rel (l l0 : List Int) : MONAD (List Int) :=
  repeat_break merge_body (l, l0, [])

def merge_from_mid_rel (l1 l2 l3 : List Int) : MONAD (List Int) :=
  repeat_break merge_body (l1, l2, l3)

def reversepair : List Int × List Int -> MONAD (List Int × List Int) :=
  fun (p, q) => ret (q, p)

def split_rec_rel_f
    (W : List Int × List Int × List Int -> MONAD (List Int × List Int)) :
    List Int × List Int × List Int -> MONAD (List Int × List Int) :=
  fun (x, p, q) =>
    match x with
    | [] => ret (p, q)
    | xh :: x' =>
        x <- W (x', q, xh :: p) ;;
        reversepair x

def split_rec_rel' :
    List Int × List Int × List Int -> MONAD (List Int × List Int) :=
  Lfix split_rec_rel_f

def split_rec_rel (l1 l2 l3 : List Int) : MONAD (List Int × List Int) :=
  split_rec_rel' (l1, l2, l3)

def split_rel (x : List Int) : MONAD (List Int × List Int) :=
  split_rec_rel' (x, [], [])

theorem split_rec_rel_unfold :
    Sets.equiv split_rec_rel' (split_rec_rel_f split_rec_rel') := by
  unfold split_rec_rel'
  apply Lfix_fixpoint'
  unfold split_rec_rel_f
  state_mono_cont_auto

theorem split_rec_rel_eval_xnil (p q : List Int) (P : Unit -> Prop) :
    hs_eval (split_rec_rel' ([], p, q)) P P (p, q) := by
  apply hs_eval_proequiv
    (ret (p, q)) (split_rec_rel' ([], p, q)) P P (p, q)
  · exact fun s a s' =>
      (show Sets.equiv (split_rec_rel' ([], p, q)) (ret (p, q)) from
        by simpa [split_rec_rel_f] using split_rec_rel_unfold ([], p, q)) s a s' |>.symm
  · exact highret_eval2 P (p, q)

theorem split_rel_eval_xnotnil (z : Int) (x p q : List Int)
    (P : Unit -> Prop) (X : (List Int × List Int) -> Unit -> Prop) :
    safeExec P (split_rec_rel' (z :: x, p, q)) X ->
      safeExec P
        (r <- split_rec_rel' (x, q, z :: p) ;; reversepair r) X := by
  intro h
  apply safeExec_proequiv
    (split_rec_rel' (z :: x, p, q))
    (r <- split_rec_rel' (x, q, z :: p) ;; reversepair r) P X
  · simpa [split_rec_rel_f] using split_rec_rel_unfold (z :: x, p, q)
  · exact h

theorem bind_2_reversepair_equiv_Id :
    Sets.equiv (fun p => z <- reversepair p ;; reversepair z)
      (fun p => ret p) := by
  rintro ⟨x, y⟩ s ⟨u, v⟩ s'
  constructor
  · rintro ⟨z, s0, hz, hr⟩
    change z = (y, x) /\ s = s0 at hz
    change (u, v) = (z.2, z.1) /\ s0 = s' at hr
    change (u, v) = (x, y) /\ s = s'
    exact ⟨by simpa [hz.1] using hr.1, hz.2.trans hr.2⟩
  · intro h
    change (u, v) = (x, y) /\ s = s' at h
    refine ⟨(y, x), s, ⟨rfl, rfl⟩, ?_⟩
    change (u, v) = (x, y) /\ s = s'
    exact h

def mergesortrec_f (W : List Int -> MONAD (List Int)) :
    List Int -> MONAD (List Int) :=
  fun x =>
    (p1, q1) <- split_rel x ;;
    match q1 with
    | [] => ret p1
    | _ :: _ =>
        p2 <- W p1 ;;
        q2 <- W q1 ;;
        merge_rel p2 q2

def mergesortrec : List Int -> MONAD (List Int) :=
  Lfix mergesortrec_f

def mergesortrec_loc0 : List Int × List Int -> MONAD (List Int) :=
  fun (p1, q1) =>
    match q1 with
    | [] => ret p1
    | _ :: _ =>
        p2 <- mergesortrec p1 ;;
        q2 <- mergesortrec q1 ;;
        merge_rel p2 q2

def mergesortrec_loc1 (q1 : List Int) : List Int -> MONAD (List Int) :=
  fun p2 => q2 <- mergesortrec q1 ;; merge_rel p2 q2

def mergesortrec_loc2 (p2 : List Int) : List Int -> MONAD (List Int) :=
  fun q2 => merge_rel p2 q2

theorem mergesortrec_unfold :
    Sets.equiv mergesortrec (mergesortrec_f mergesortrec) := by
  unfold mergesortrec
  apply Lfix_fixpoint'
  unfold mergesortrec_f
  state_mono_cont_auto

def incr_aux : List Int -> Int -> Prop
  | [], _ => True
  | y :: l, x => x <= y /\ incr_aux l y

def incr : List Int -> Prop
  | [] => True
  | x :: l => incr_aux l x

def ext_sort (l : List Int) : MONAD (List Int) :=
  fun _ l' _ => Permutation l l' /\ incr l'

def ext_split (l : List Int) : MONAD (List Int × List Int) :=
  fun _ pair _ => Permutation l (pair.1 ++ pair.2)

def gmergesortrec_f (W : List Int -> MONAD (List Int)) :
    List Int -> MONAD (List Int) :=
  fun x => choice
    (ext_sort x)
    (test' (Zlength x >= 2) ;;
      (p1, q1) <- ext_split x ;;
      p2 <- W p1 ;;
      q2 <- W q1 ;;
      merge_rel p2 q2)

def gmergesortrec : List Int -> MONAD (List Int) :=
  Lfix gmergesortrec_f

def gmergesortrec_loc0 : List Int × List Int -> MONAD (List Int) :=
  fun (p1, q1) =>
    p2 <- gmergesortrec p1 ;;
    q2 <- gmergesortrec q1 ;;
    merge_rel p2 q2

def gmergesortrec_loc1 (q1 : List Int) : List Int -> MONAD (List Int) :=
  fun p2 => q2 <- gmergesortrec q1 ;; merge_rel p2 q2

theorem gmergesortrec_unfold :
    Sets.equiv gmergesortrec (gmergesortrec_f gmergesortrec) := by
  unfold gmergesortrec
  apply Lfix_fixpoint'
  unfold gmergesortrec_f
  state_mono_cont_auto

theorem incr_app_cons (l1 : List Int) (x : Int) (l2 : List Int) :
    incr (l1 ++ [x]) -> incr (x :: l2) -> incr (l1 ++ x :: l2) := by
  intro h1 h2
  cases l1 with
  | nil => exact h2
  | cons a rest =>
      simp only [List.cons_append, incr] at h1 ⊢
      induction rest generalizing a with
      | nil => simpa [incr_aux] using And.intro h1.1 h2
      | cons b rest ih =>
          exact ⟨h1.1, ih b h1.2⟩

theorem incr_app_cons_inv1 (l1 : List Int) (x : Int) (l2 : List Int) :
    incr (l1 ++ x :: l2) -> incr (l1 ++ [x]) := by
  intro h
  cases l1 with
  | nil => trivial
  | cons a rest =>
      simp only [List.cons_append, incr] at h ⊢
      induction rest generalizing a with
      | nil => simpa [incr_aux] using h.1
      | cons b rest ih =>
          exact ⟨h.1, ih b h.2⟩

theorem incr_app_cons_inv2 (l1 : List Int) (x : Int) (l2 : List Int) :
    incr (l1 ++ x :: l2) -> incr (x :: l2) := by
  induction l1 with
  | nil => exact fun h => h
  | cons a rest ih =>
      intro h
      cases rest with
      | nil => simpa [incr, incr_aux] using h.2
      | cons b rest =>
          apply ih
          simpa [incr, incr_aux] using h.2

theorem merge_perm (l1 l2 : List Int) :
    Hoare (fun _ : Unit => True) (merge_rel l1 l2)
      (fun r _ => Permutation (l1 ++ l2) r) := by
  unfold merge_rel
  let Inv : List Int × List Int × List Int -> Unit -> Prop :=
    fun (a, b, acc) _ => Permutation (l1 ++ l2) (a ++ b ++ acc)
  apply Hoare_conseq_pre (P2 := Inv (l1, l2, []))
  · intro _ _
    simp [Inv]
  · refine Hoare_repeat_break merge_body Inv
      (fun r _ => Permutation (l1 ++ l2) r) ?_ (l1, l2, [])
    rintro ⟨a, b, acc⟩
    unfold merge_body
    cases a with
    | nil =>
        simp only
        apply Hoare_ret'
        intro _ h
        dsimp [Inv] at h ⊢
        exact h.trans List.perm_append_comm
    | cons x atail =>
        cases b with
        | nil =>
            simp only
            apply Hoare_ret'
            intro _ h
            dsimp [Inv] at h ⊢
            have h' : Permutation (l1 ++ l2) ((x :: atail) ++ acc) := by
              simpa using h
            exact h'.trans List.perm_append_comm
        | cons y btail =>
            simp only
            apply Hoare_choice
            · apply Hoare_assume_bind'
              intro _
              apply Hoare_ret'
              intro _ h
              dsimp [Inv] at h ⊢
              have hp := (@List.perm_append_singleton Int x
                (atail ++ y :: btail ++ acc)).symm
              simpa only [List.append_assoc] using h.trans hp
            · apply Hoare_assume_bind'
              intro _
              apply Hoare_ret'
              intro _ h
              dsimp [Inv] at h ⊢
              have hp0 := (@List.perm_append_singleton Int y (btail ++ acc)).symm
              have hp := hp0.append_left (x :: atail)
              have h' : Permutation (l1 ++ l2)
                  ((x :: atail) ++ y :: (btail ++ acc)) := by
                simpa only [List.append_assoc] using h
              simpa only [List.append_assoc] using h'.trans hp

theorem merge_incr (l1 l2 : List Int) (h1 : incr l1) (h2 : incr l2) :
    Hoare (fun _ : Unit => True) (merge_rel l1 l2) (fun r _ => incr r) := by
  unfold merge_rel
  let Inv : List Int × List Int × List Int -> Unit -> Prop :=
    fun (a, b, acc) _ => incr (acc ++ a) /\ incr (acc ++ b)
  apply Hoare_conseq_pre (P2 := Inv (l1, l2, []))
  · intro _ _
    simpa [Inv] using And.intro h1 h2
  · refine Hoare_repeat_break merge_body Inv (fun r _ => incr r) ?_ (l1, l2, [])
    rintro ⟨a, b, acc⟩
    unfold merge_body
    cases a with
    | nil =>
        simp only
        apply Hoare_ret'
        intro _ h
        dsimp [Inv] at h ⊢
        exact h.2
    | cons x atail =>
        cases b with
        | nil =>
            simp only
            apply Hoare_ret'
            intro _ h
            dsimp [Inv] at h ⊢
            exact h.1
        | cons y btail =>
            simp only
            apply Hoare_choice
            · apply Hoare_assume_bind'
              intro hxy
              apply Hoare_ret'
              intro _ h
              dsimp [Inv] at h ⊢
              rcases h with ⟨ha, hb⟩
              constructor
              · simpa only [List.append_assoc] using ha
              · rw [List.append_assoc]
                apply incr_app_cons acc x (y :: btail)
                · exact incr_app_cons_inv1 acc x atail ha
                · have hy : incr (y :: btail) := incr_app_cons_inv2 acc y btail hb
                  simpa [incr, incr_aux] using And.intro hxy hy
            · apply Hoare_assume_bind'
              intro hyx
              apply Hoare_ret'
              intro _ h
              dsimp [Inv] at h ⊢
              rcases h with ⟨ha, hb⟩
              constructor
              · rw [List.append_assoc]
                apply incr_app_cons acc y (x :: atail)
                · exact incr_app_cons_inv1 acc y btail hb
                · have hx : incr (x :: atail) := incr_app_cons_inv2 acc x atail ha
                  simpa [incr, incr_aux] using And.intro hyx hx
              · simpa only [List.append_assoc] using hb

theorem functional_correctness_merge (l1 l2 : List Int)
    (h1 : incr l1) (h2 : incr l2) :
    Hoare (fun _ : Unit => True) (merge_rel l1 l2)
      (fun r _ => Permutation (l1 ++ l2) r /\ incr r) := by
  apply Hoare_conj
  · exact merge_perm l1 l2
  · exact merge_incr l1 l2 h1 h2

def split_post (input : List Int × List Int × List Int)
    (pair : List Int × List Int) : Prop :=
  let (x, p, q) := input
  Permutation (x ++ p ++ q) (pair.1 ++ pair.2) /\
    p.length <= pair.1.length /\
    q.length <= pair.2.length /\
    pair.2.length - q.length <= pair.1.length - p.length /\
    pair.1.length - p.length <= pair.2.length - q.length + 1

theorem functional_correctness_split (l : List Int) :
    Hoare (fun _ : Unit => True) (split_rel l)
      (fun pair _ =>
        Permutation l (pair.1 ++ pair.2) /\
          0 <= pair.1.length - pair.2.length /\
          pair.1.length - pair.2.length <= 1) := by
  unfold split_rel split_rec_rel'
  apply Hoare_conseq_post
    (Q2 := fun pair _ => split_post (l, [], []) pair)
  · rintro ⟨l1, l2⟩ _ h
    unfold split_post at h
    simp only [List.append_nil, Prod.fst, Prod.snd, List.length_nil,
      Nat.sub_zero] at h ⊢
    exact ⟨h.1, by omega⟩
  · state_hoare_fix_nolv_auto (List Int × List Int × List Int)
    intro W hW
    rintro ⟨x, p, q⟩
    unfold split_rec_rel_f
    cases x with
    | nil =>
        apply Hoare_ret'
        intro _ _
        unfold split_post
        simp
    | cons z x =>
        apply Hoare_bind (Q := fun pair _ => split_post (x, q, z :: p) pair)
        · simpa using hW (x, q, z :: p)
        · rintro ⟨p', q'⟩
          unfold reversepair
          apply Hoare_ret'
          intro _ h
          unfold split_post at h ⊢
          simp only [Prod.fst, Prod.snd, List.length_cons] at h ⊢
          rcases h with ⟨hp, hq, hpLen, hlo, hhi⟩
          constructor
          · have hrotate : Permutation (z :: x ++ p ++ q) (x ++ q ++ z :: p) := by
              have h1 : Permutation (z :: x ++ p ++ q)
                  (x ++ (p ++ q ++ [z])) := by
                simpa only [List.cons_append, List.append_assoc] using
                  (List.perm_append_singleton z (x ++ p ++ q)).symm
              have h2 : Permutation (x ++ (p ++ q ++ [z]))
                  (x ++ (q ++ [z] ++ p)) := by
                have hcomm : Permutation (p ++ (q ++ [z])) ((q ++ [z]) ++ p) :=
                  List.perm_append_comm
                simpa only [List.append_assoc] using hcomm.append_left x
              exact h1.trans (by simpa only [List.append_assoc] using h2)
            exact hrotate.trans (hp.trans List.perm_append_comm)
          · omega

theorem split_rel_refine_ext_split (l : List Int) :
    Sets.included (split_rel l) (ext_split l) := by
  intro s pair s' h
  exact (functional_correctness_split l s pair s' trivial h).1

theorem functional_correctness_mergesort (l : List Int) :
    Hoare ATrue (mergesortrec l)
      (fun l0 _ => Permutation l l0 /\ incr l0) := by
  unfold mergesortrec
  state_hoare_fix_nolv_auto (List Int)
  intro W hW x
  unfold mergesortrec_f
  apply Hoare_bind
    (Q := fun pair _ =>
      Permutation x (pair.1 ++ pair.2) /\
        0 <= pair.1.length - pair.2.length /\
        pair.1.length - pair.2.length <= 1)
  · exact functional_correctness_split x
  · rintro ⟨l1, l2⟩
    cases l2 with
    | nil =>
        apply Hoare_ret'
        intro _ h
        rcases h with ⟨hp, hbalance⟩
        constructor
        · simpa using hp
        · cases l1 with
          | nil => trivial
          | cons a tail =>
              cases tail with
              | nil => trivial
              | cons b tail => simp at hbalance
    | cons a l2 =>
        apply Hoare_stateless
        intro hsplit
        apply Hoare_bind (Q := fun lp _ => Permutation l1 lp /\ incr lp)
        · exact hW l1
        · intro lp
          apply Hoare_stateless
          intro hp
          apply Hoare_bind (Q := fun lq _ => Permutation (a :: l2) lq /\ incr lq)
          · exact hW (a :: l2)
          · intro lq
            apply Hoare_stateless
            intro hq
            apply Hoare_conseq_post
              (Q2 := fun lr _ => Permutation (lp ++ lq) lr /\ incr lr)
            · intro lr _ h
              exact ⟨hsplit.1.trans ((hp.1.append hq.1).trans h.1), h.2⟩
            · exact functional_correctness_merge lp lq hp.2 hq.2

theorem ext_sort_fact (l : List Int) :
    Hoare ATrue (ext_sort l)
      (fun l0 _ => Permutation l l0 /\ incr l0) := by
  intro _ l0 _ _ h
  exact h

theorem ext_split_fact (l : List Int) :
    Hoare ATrue (ext_split l)
      (fun pair _ => Permutation l (pair.1 ++ pair.2)) := by
  intro _ pair _ _ h
  exact h

theorem functional_correctness_gmergesort (l : List Int) :
    Hoare ATrue (gmergesortrec l)
      (fun l0 _ => Permutation l l0 /\ incr l0) := by
  unfold gmergesortrec
  state_hoare_fix_nolv_auto (List Int)
  intro W hW x
  unfold gmergesortrec_f
  apply Hoare_choice
  · exact ext_sort_fact x
  · apply Hoare_assume_bind'
    intro _
    apply Hoare_bind (Q := fun pair _ => Permutation x (pair.1 ++ pair.2))
    · exact ext_split_fact x
    · rintro ⟨l1, l2⟩
      apply Hoare_stateless
      intro hsplit
      apply Hoare_bind (Q := fun lp _ => Permutation l1 lp /\ incr lp)
      · exact hW l1
      · intro lp
        apply Hoare_stateless
        intro hp
        apply Hoare_bind (Q := fun lq _ => Permutation l2 lq /\ incr lq)
        · exact hW l2
        · intro lq
          apply Hoare_stateless
          intro hq
          apply Hoare_conseq_post
            (Q2 := fun lr _ => Permutation (lp ++ lq) lr /\ incr lr)
          · intro lr _ h
            exact ⟨hsplit.trans ((hp.1.append hq.1).trans h.1), h.2⟩
          · exact functional_correctness_merge lp lq hp.2 hq.2

end MonadLib.Examples.mergesort
