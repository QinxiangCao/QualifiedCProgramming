From SimpleC.Verification Require Export VCPrelude.

(** Case-local instantiation of the EXISTING proved memory libraries.
    No change to the QCP memory model or its access rules. *)
Module StrlenLittleEndian <: SeparationLogicSig.
  Include FunAssertion.SL.
  Include DerivedPredSig Arch64 LittleEndian.
  Include StoreLibSig Arch64 LittleEndian.
  Include ArrayLibSig Arch64 LittleEndian.
  Include Array2LibSig Arch64 LittleEndian.
  Include Array3LibSig Arch64 LittleEndian.
  Include PtrArray2LibSig Arch64 LittleEndian.
  Include MapLibSig Arch64 LittleEndian.
  Include StringLibSig Arch64 LittleEndian.
  Export SimpleCtypeNotations.
End StrlenLittleEndian.
Export StrlenLittleEndian.

Example strlen_endian_check :
  @LittleEndian.n_bytes_to_Z 2 (Vector.cons Z 1 1 (Vector.cons Z 2 0 (Vector.nil Z))) = 513.
Proof. reflexivity. Qed.
