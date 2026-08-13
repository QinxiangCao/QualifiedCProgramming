Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap ListLib.
From compcert.lib Require Import Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem CommonAssertion StoreAux ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type StringLibSig (Arch : CArchSig) (Endian : CEndianSig) (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig Arch Endian CRules) (SLibSig : StoreLibSig Arch Endian CRules DePredSig) (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig).

Import CRules.
Import DePredSig.
Import SLibSig.
Import ALibSig.
Local Open Scope sac.

Definition AsciiToZ (c : ascii) : Z :=
  Z.of_N (N_of_ascii c).

Definition ZToAscii (z : Z) : ascii :=
  ascii_of_N (Z.to_N (z mod 256)).

Definition string_length (s : list Z) : Z :=
  Zlength s.

Definition c_string (s : list Z) : list Z :=
  s ++ [0].

Definition valid_char (z : Z) : Prop :=
  0 < z < 256.

Definition valid_string (s : list Z) : Prop :=
  Forall valid_char s.

Definition StringLength (s : string) : Z :=
  Z.of_nat (String.length s).

Fixpoint StringToList_nat (s : string) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' =>
      match s with
      | EmptyString => 0 :: StringToList_nat EmptyString n'
      | String c s' => AsciiToZ c :: StringToList_nat s' n'
      end
  end.

Definition StringToList (s : string) (n : Z) : list Z :=
  StringToList_nat s (Z.to_nat n).

Fixpoint ListToString (s : list Z) : string :=
  match s with
  | [] => EmptyString
  | c :: s' => String (ZToAscii c) (ListToString s')
  end.

Lemma ZToAscii_AsciiToZ :
  forall c, ZToAscii (AsciiToZ c) = c.
Proof.
  intros.
  unfold ZToAscii, AsciiToZ.
  pose proof (N_ascii_bounded c).
  rewrite Z.mod_small by lia.
  rewrite N2Z.id.
  apply ascii_N_embedding.
Qed.

Lemma ListToString_StringToList_nat_full :
  forall s, ListToString (StringToList_nat s (String.length s)) = s.
Proof.
  induction s; simpl.
  - reflexivity.
  - rewrite ZToAscii_AsciiToZ.
    rewrite IHs.
    reflexivity.
Qed.

Lemma ListToString_StringToList :
  forall s, ListToString (StringToList s (StringLength s)) = s.
Proof.
  intros.
  unfold StringToList, StringLength.
  rewrite Nat2Z.id.
  apply ListToString_StringToList_nat_full.
Qed.

Definition valid_stringLit (s : string) : Prop :=
  valid_string (StringToList s (StringLength s)).

Definition store_string (x : addr) (s : list Z) : Assertion :=
  “ valid_string s ” &&
  CharArray.full x (string_length s + 1) (c_string s).

Definition store_stringLit (x : addr) (s : string) : Assertion :=
  “ valid_stringLit s ” &&
  CharArray.full x (StringLength s + 1) (StringToList s (StringLength s + 1)).

Parameter GlobalStrings : (string -> addr) -> Assertion.
Parameter GlobalStrings_missing : (string -> addr) -> list string -> Assertion.

Axiom GlobalStrings_split :
  forall (LitMap : string -> addr) (s : string),
    GlobalStrings LitMap |--
    GlobalStrings_missing LitMap [s] ** store_stringLit (LitMap s) s.

Axiom GlobalStrings_merge :
  forall (LitMap : string -> addr) (s : string),
    GlobalStrings_missing LitMap [s] ** store_stringLit (LitMap s) s |--
    GlobalStrings LitMap.

Axiom GlobalStrings_missing_split :
  forall (LitMap : string -> addr) (l : list string) (s : string),
    ~ In s l ->
    GlobalStrings_missing LitMap l |--
    GlobalStrings_missing LitMap (s :: l) ** store_stringLit (LitMap s) s.

Axiom GlobalStrings_missing_merge :
  forall (LitMap : string -> addr) (l : list string) (s : string),
    GlobalStrings_missing LitMap (s :: l) ** store_stringLit (LitMap s) s |--
    GlobalStrings_missing LitMap l.

Axiom GlobalStrings_split_existing :
  forall (LitMap : string -> addr) (s : string),
    store_stringLit (LitMap s) s ** GlobalStrings LitMap |--
    store_stringLit (LitMap s) s ** GlobalStrings_missing LitMap [s].

Lemma c_string_Zlength :
  forall s, Zlength (c_string s) = string_length s + 1.
Proof.
  intros.
  unfold c_string, string_length.
  rewrite Zlength_app.
  rewrite Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma StringToList_nat_length :
  forall s n, length (StringToList_nat s n) = n.
Proof.
  intros s n.
  revert s.
  induction n; intros s; simpl; auto.
  destruct s as [| c s']; simpl.
  - rewrite (IHn EmptyString); auto.
  - rewrite (IHn s'); auto.
Qed.

Lemma StringToList_length :
  forall s n, 0 <= n -> Zlength (StringToList s n) = n.
Proof.
  intros.
  unfold StringToList.
  rewrite Zlength_correct.
  rewrite StringToList_nat_length.
  lia.
Qed.

Lemma StringToList_c_length :
  forall s, Zlength (StringToList s (StringLength s + 1)) = StringLength s + 1.
Proof.
  intros.
  apply StringToList_length.
  unfold StringLength.
  lia.
Qed.

Lemma store_string_length :
  forall x s, store_string x s |-- “ Zlength (c_string s) = string_length s + 1 ”.
Proof.
  intros.
  unfold store_string.
  entailer!.
  apply c_string_Zlength.
Qed.

Lemma store_stringLit_length :
  forall x s,
    store_stringLit x s |--
    “ Zlength (StringToList s (StringLength s + 1)) = StringLength s + 1 ”.
Proof.
  intros.
  unfold store_stringLit.
  entailer!.
  apply StringToList_c_length.
Qed.

Lemma store_string_split_to_missing_i :
  forall x i s,
    0 <= i < string_length s + 1 ->
    store_string x s |--
    ((x + i * sizeof(CHAR)) # Char |-> Znth i (c_string s) 0) **
    CharArray.missing_i x i 0 (string_length s + 1) (c_string s).
Proof.
  intros.
  unfold store_string.
  entailer!.
  sep_apply (CharArray.full_split_to_missing_i x i (string_length s + 1) (c_string s) 0); auto.
  entailer!.
Qed.

Lemma store_stringLit_split_to_missing_i :
  forall x i s,
    0 <= i < StringLength s + 1 ->
    store_stringLit x s |--
    ((x + i * sizeof(CHAR)) # Char |-> Znth i (StringToList s (StringLength s + 1)) 0) **
    CharArray.missing_i x i 0 (StringLength s + 1) (StringToList s (StringLength s + 1)).
Proof.
  intros.
  unfold store_stringLit.
  entailer!.
  sep_apply (CharArray.full_split_to_missing_i x i (StringLength s + 1) (StringToList s (StringLength s + 1)) 0); auto.
  entailer!.
Qed.

Lemma AsciiToZ_range :
  forall c, 0 <= AsciiToZ c < 256.
Proof.
  intros.
  unfold AsciiToZ.
  pose proof (N_ascii_bounded c).
  lia.
Qed.

End StringLibSig.
