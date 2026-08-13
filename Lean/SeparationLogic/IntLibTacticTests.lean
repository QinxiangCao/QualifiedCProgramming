import SimpleC.SL.IntLib

open SimpleC.SL.IntLib

section UnsignedUnsigned

variable (x y z n : Int) (hn : n > 0)

example : unsigned_last_nbits (unsigned_last_nbits x n + y) n =
    unsigned_last_nbits (x + y) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x + unsigned_last_nbits y n) n =
    unsigned_last_nbits (x + y) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n - y) n =
    unsigned_last_nbits (x - y) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x - unsigned_last_nbits y n) n =
    unsigned_last_nbits (x - y) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n * y) n =
    unsigned_last_nbits (x * y) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x * unsigned_last_nbits y n) n =
    unsigned_last_nbits (x * y) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n) n =
    unsigned_last_nbits x n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n * y + z) n =
    unsigned_last_nbits (x * y + z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x * unsigned_last_nbits y n + z) n =
    unsigned_last_nbits (x * y + z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n * y - z) n =
    unsigned_last_nbits (x * y - z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x * unsigned_last_nbits y n - z) n =
    unsigned_last_nbits (x * y - z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n + y - z) n =
    unsigned_last_nbits (x + y - z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x + unsigned_last_nbits y n - z) n =
    unsigned_last_nbits (x + (y - z)) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n * y * z) n =
    unsigned_last_nbits (x * y * z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x * unsigned_last_nbits y n * z) n =
    unsigned_last_nbits (x * (y * z)) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n + y + z) n =
    unsigned_last_nbits (x + y + z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x + unsigned_last_nbits y n + z) n =
    unsigned_last_nbits (x + (y + z)) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x + unsigned_last_nbits y n * z) n =
    unsigned_last_nbits (x + y * z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x + y * unsigned_last_nbits z n) n =
    unsigned_last_nbits (x + y * z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x - unsigned_last_nbits y n * z) n =
    unsigned_last_nbits (x - y * z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x - y * unsigned_last_nbits z n) n =
    unsigned_last_nbits (x - y * z) n := by unsigned_unsigned_simpl

example : unsigned_last_nbits (x + 0) n = unsigned_last_nbits x n := by
  unsigned_unsigned_simpl

end UnsignedUnsigned

section SignedSigned

variable (x y n : Int) (hn : n > 0)

example : signed_last_nbits (signed_last_nbits x n + y) n =
    signed_last_nbits (x + y) n := by signed_signed_simpl

example : signed_last_nbits (x + signed_last_nbits y n) n =
    signed_last_nbits (x + y) n := by signed_signed_simpl

example : signed_last_nbits (signed_last_nbits x n - y) n =
    signed_last_nbits (x - y) n := by signed_signed_simpl

example : signed_last_nbits (x - signed_last_nbits y n) n =
    signed_last_nbits (x - y) n := by signed_signed_simpl

example : signed_last_nbits (signed_last_nbits x n * y) n =
    signed_last_nbits (x * y) n := by signed_signed_simpl

example : signed_last_nbits (x * signed_last_nbits y n) n =
    signed_last_nbits (x * y) n := by signed_signed_simpl

example : signed_last_nbits (signed_last_nbits x n) n =
    signed_last_nbits x n := by signed_signed_simpl

example : signed_last_nbits (x + 0) n = signed_last_nbits x n := by
  signed_signed_simpl

end SignedSigned

section UnsignedSigned

variable (x y n : Int) (hn : n > 0)

example : unsigned_last_nbits (signed_last_nbits x n + y) n =
    unsigned_last_nbits (x + y) n := by unsigned_signed_simpl

example : unsigned_last_nbits (x + signed_last_nbits y n) n =
    unsigned_last_nbits (x + y) n := by unsigned_signed_simpl

example : unsigned_last_nbits (signed_last_nbits x n - y) n =
    unsigned_last_nbits (x - y) n := by unsigned_signed_simpl

example : unsigned_last_nbits (x - signed_last_nbits y n) n =
    unsigned_last_nbits (x - y) n := by unsigned_signed_simpl

example : unsigned_last_nbits (signed_last_nbits x n * y) n =
    unsigned_last_nbits (x * y) n := by unsigned_signed_simpl

example : unsigned_last_nbits (x * signed_last_nbits y n) n =
    unsigned_last_nbits (x * y) n := by unsigned_signed_simpl

example : unsigned_last_nbits (signed_last_nbits x n) n =
    unsigned_last_nbits x n := by unsigned_signed_simpl

end UnsignedSigned

section SignedUnsigned

variable (x y n : Int) (hn : n > 0)

example : signed_last_nbits (unsigned_last_nbits x n + y) n =
    signed_last_nbits (x + y) n := by signed_unsigned_simpl

example : signed_last_nbits (x + unsigned_last_nbits y n) n =
    signed_last_nbits (x + y) n := by signed_unsigned_simpl

example : signed_last_nbits (unsigned_last_nbits x n - y) n =
    signed_last_nbits (x - y) n := by signed_unsigned_simpl

example : signed_last_nbits (x - unsigned_last_nbits y n) n =
    signed_last_nbits (x - y) n := by signed_unsigned_simpl

example : signed_last_nbits (unsigned_last_nbits x n * y) n =
    signed_last_nbits (x * y) n := by signed_unsigned_simpl

example : signed_last_nbits (x * unsigned_last_nbits y n) n =
    signed_last_nbits (x * y) n := by signed_unsigned_simpl

example : signed_last_nbits (unsigned_last_nbits x n) n =
    signed_last_nbits x n := by signed_unsigned_simpl

end SignedUnsigned

section Dispatch

variable (x y z n : Int) (hn : n > 0)

example : unsigned_last_nbits
    (unsigned_last_nbits (unsigned_last_nbits x n + y) n + z) n =
    unsigned_last_nbits (x + y + z) n := by
  lastnbits_simpl

example : unsigned_last_nbits (signed_last_nbits x n + y) n =
    unsigned_last_nbits (x + y) n := by lastnbits_simpl

example : signed_last_nbits (unsigned_last_nbits x n + y) n =
    signed_last_nbits (x + y) n := by lastnbits_simpl

example : signed_last_nbits (signed_last_nbits x n + y) n =
    signed_last_nbits (x + y) n := by lastnbits_simpl

example : unsigned_last_nbits (unsigned_last_nbits x n + 0) n =
    unsigned_last_nbits x n := by lastnbits_simpl

-- Documented broader success boundary of the Lean dispatcher.
example : unsigned_last_nbits (x + 0) n = unsigned_last_nbits x n := by
  lastnbits_simpl

example : signed_last_nbits (x + 0) n = signed_last_nbits x n := by
  lastnbits_simpl

example (hx : 0 <= x ∧ x < Z.pow 2 n) :
    unsigned_last_nbits x n = x := by
  lastnbits_eq_step unsigned_last_nbits x n

example (hx : -Z.pow 2 (n - 1) <= x ∧ x < Z.pow 2 (n - 1)) :
    signed_last_nbits x n = x := by
  lastnbits_eq_step signed_last_nbits x n

example (hx : 0 <= x ∧ x < Z.pow 2 n)
    (hy : -Z.pow 2 (n - 1) <= y ∧ y < Z.pow 2 (n - 1)) :
    unsigned_last_nbits x n + signed_last_nbits y n = x + y := by
  lastnbits_eq

end Dispatch

example (P : Prop) (h : P) : P := by
  unsigned_unsigned_simpl
  signed_signed_simpl
  unsigned_signed_simpl
  signed_unsigned_simpl
  lastnbits_simpl
  lastnbits_eq
  exact h

example : True := by
  fail_if_success lastnbits_eq_step (1 : Int)
  trivial
