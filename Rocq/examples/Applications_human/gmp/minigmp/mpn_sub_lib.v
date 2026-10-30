Require Export SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.


Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Psatz.
Lemma mpd_partition__partition : forall p v n m,
  (0 <= n <= m)%Z ->
  SeparationLogic.naive_C_Rules.derivable1 (mpd_store_Z UINT_MOD p v m)
   (SeparationLogic.naive_C_Rules.exp (fun hi =>
    SeparationLogic.naive_C_Rules.exp (fun lo =>
     SeparationLogic.naive_C_Rules.andp
      (SeparationLogic.naive_C_Rules.coq_prop (v = lo + hi * UINT_MOD ^ n)%Z)
      (SeparationLogic.naive_C_Rules.sepcon
       (mpd_store_Z UINT_MOD p lo n)
       (mpd_store_Z UINT_MOD (p + n * SeparationLogic.naive_C_Rules.sizeof_front_end_type CNotation.FET_uint)%Z hi (m-n)%Z))))).
Proof.
  Import SeparationLogic CommonAssertion naive_C_Rules.
  Local Open Scope Z_scope.
  Local Open Scope sac.
  intros p v n m Hnm.
  unfold mpd_store_Z at 1.
  Intros data.
  rename H into Hvalue. rename H0 into Hsize.
  destruct Hvalue as [Hvalue Hbound].
  unfold mpd_store_list.
  assert (Hlo : Zlength (Positional.sublist 0 n data) = n).
  { rewrite Length.Zlength_sublist by lia. lia. }
  assert (Hhi : Zlength (Positional.sublist n m data) = m-n).
  { rewrite Length.Zlength_sublist by lia. lia. }
  assert (Blo : list_within_bound UINT_MOD (Positional.sublist 0 n data)).
  { apply list_within_bound_sublist; try lia; assumption. }
  assert (Bhi : list_within_bound UINT_MOD (Positional.sublist n m data)).
  { apply list_within_bound_sublist; try lia; assumption. }
  assert (Heq : v = list_to_Z UINT_MOD (Positional.sublist 0 n data) +
                   list_to_Z UINT_MOD (Positional.sublist n m data) * UINT_MOD ^ n).
  { rewrite <- Hvalue.
    rewrite <- (Length.sublist_self data m) at 1 by lia.
    rewrite (Length.sublist_split 0 m n data) by lia.
    rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite Hlo. reflexivity. }
  rewrite <- Hsize.
  sep_apply (UIntArray.full_split_to_full p n m data Hnm).
  sep_apply (UIntArray_full_to_mpd_store_Z_exact p n
    (Positional.sublist 0 n data) (list_to_Z UINT_MOD (Positional.sublist 0 n data))
    Hlo eq_refl Blo).
  sep_apply (UIntArray_full_to_mpd_store_Z_exact (p+n*sizeof(UINT)) (m-n)
    (Positional.sublist n m data) (list_to_Z UINT_MOD (Positional.sublist n m data))
    Hhi eq_refl Bhi).
  Exists (list_to_Z UINT_MOD (Positional.sublist n m data))
         (list_to_Z UINT_MOD (Positional.sublist 0 n data)).
  split_pure_spatial; [cancel | dump_pre_spatial; exact Heq].
Qed.
