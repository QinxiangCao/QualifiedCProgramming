From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.stdlib.glibc Require Import memmove_contract_lib.
Local Open Scope Z_scope.
Local Open Scope monad.

(** The same zero check and unsigned direction choice as the C entry. *)
Definition mm_byte_program (s d n : Z) : program mm_memory Z :=
 if Z.eqb n 0 then ret d
 else (if Z.leb n (unsigned_last_nbits (d-s) 64)
       then mm_forward s d 0 (Z.to_nat n)
       else mm_backward s d (Z.to_nat n));; ret d.

Theorem mm_byte_program_correct : forall m s d n,
 0<=n -> (n=0 \/ (0<=s /\ s+n<=18446744073709551615 /\
                  0<=d /\ d+n<=18446744073709551615)) ->
 Hoare (fun st => st=m) (mm_byte_program s d n)
       (fun r st => r=d /\ st=mm_snapshot m s d n).
Proof.
 intros m s d n Hn Hb; unfold mm_byte_program.
 destruct (Z.eqb_spec n 0) as [->|Hnz].
 - rewrite mm_snapshot_zero. apply Hoare_ret; auto.
 - destruct Hb as [Hz|[Hs [Hsn [Hd Hdn]]]]; [contradiction|].
   eapply Hoare_bind with (Q:=fun _ st => st=mm_snapshot m s d n).
   + destruct (Z.leb_spec n (unsigned_last_nbits (d-s) 64)).
     * pose proof (mm_forward_correct (Z.to_nat n) m s d 0 n ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
         (mm_direction_forward s d n Hs Hsn Hd Hdn Hn ltac:(lia))) as E.
       rewrite mm_snapshot_zero in E. exact E.
     * pose proof (mm_backward_correct (Z.to_nat n) m s d n
         (mm_direction_backward s d n Hs Hsn Hd Hdn Hn ltac:(lia)) ltac:(rewrite Z2Nat.id by lia; lia)) as E.
       rewrite Z2Nat.id, Z.sub_diag, mm_snapshot_zero in E by lia. exact E.
   + intros []; apply Hoare_ret; auto.
Qed.
