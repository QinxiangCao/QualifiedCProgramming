Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.
(* Already exported by gmp_udiv_qr_3by2_proof_auto.v.
Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_7_4 : gmp_udiv_qr_3by2_entail_wit_7_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  assert (Hminus: unsigned_last_nbits (-1) 32 = 4294967295).
  { replace (-1) with (4294967295 - 4294967296) by ring.
    apply unsigned_last_nbits_underflow_32; lia. }
  assert (Heq_uint: n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre =
                      4294967296 * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
  { rewrite PreH3 in PreH28. exact PreH28. }
  Exists 4294967296.
  split_pure_spatial.
  2: {
    split_pures.
    all: try (dump_pre_spatial;
              first [ rewrite ?Hminus; reflexivity
                    | exact PreH2 | reflexivity | exact PreH4 | exact PreH5 | exact PreH6 |
                      exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 |
                      exact PreH12 | exact PreH13 | exact PreH14 | exact PreH15 | exact PreH16 |
                      exact PreH17 | exact PreH18 | exact PreH21 | exact PreH22 | exact PreH23 |
                       exact PreH24 | exact PreH25 | exact PreH26 | exact Heq_uint |
                      lia ]).
  }
  all: try (repeat cancel).
Qed.
*)

(* Already exported by gmp_udiv_qr_3by2_proof_auto.v.
Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_7_5 : gmp_udiv_qr_3by2_entail_wit_7_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  change (4294967296 ÷ 2) with 2147483648 in *.
  assert (Hminus: unsigned_last_nbits (-1) 32 = 4294967295).
  { replace (-1) with (4294967295 - 4294967296) by ring.
    apply unsigned_last_nbits_underflow_32; lia. }
  assert (Heq_uint: n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre + 4294967296 ^ 2 =
                      4294967296 * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
  { rewrite PreH3 in PreH29. exact PreH29. }
  Right.
  Exists 4294967296.
  split_pure_spatial.
  2: {
    split_pures.
    all: try (dump_pre_spatial;
              first [ rewrite ?Hminus; reflexivity
                    | exact PreH2 | reflexivity | exact PreH4 | exact PreH5 | exact PreH6 |
                      exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 |
                      exact PreH12 | exact PreH13 | exact PreH14 | exact PreH15 | exact PreH16 |
                      exact PreH17 | exact PreH18 | exact PreH21 | exact PreH22 | exact PreH23 |
                       exact PreH24 | exact PreH25 | exact PreH26 | exact PreH28 | exact Heq_uint |
                      lia ]).
  }
  all: try (repeat cancel).
Qed.
*)

(* Already exported by gmp_udiv_qr_3by2_proof_auto.v.
Lemma proof_of_gmp_udiv_qr_3by2_entail_wit_7_6 : gmp_udiv_qr_3by2_entail_wit_7_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  change UINT_MOD with 4294967296 in *.
  change UINT_MAX with 4294967295 in *.
  assert (Hminus: unsigned_last_nbits (-1) 32 = 4294967295).
  { replace (-1) with (4294967295 - 4294967296) by ring.
    apply unsigned_last_nbits_underflow_32; lia. }
  change (4294967296 ÷ 2) with 2147483648 in *.
  assert (Heq_uint: n2_pre * 4294967296 ^ 2 + n1_pre * 4294967296 + n0_pre =
                     4294967296 * (d1_pre * 4294967296 + d0_pre) + rpre1 * 4294967296 + rpre0).
  { rewrite PreH3 in PreH29. exact PreH29. }
  Right.
  Exists 4294967296.
  split_pure_spatial.
  2: {
    split_pures.
    all: try (dump_pre_spatial;
              first [ rewrite ?Hminus; reflexivity
                    | exact PreH2 | exact PreH4 | exact PreH5 | exact PreH6 |
                      exact PreH7 | exact PreH8 | exact PreH9 | exact PreH10 | exact PreH11 |
                      exact PreH12 | exact PreH13 | exact PreH14 | exact PreH15 | exact PreH16 |
                      exact PreH17 | exact PreH18 | exact PreH21 | exact PreH22 | exact PreH23 |
                      exact PreH24 | exact PreH25 | exact PreH26 | exact PreH27 | exact Heq_uint |
                      lia ]).
  }
  all: try (repeat cancel).
Qed.
*)
