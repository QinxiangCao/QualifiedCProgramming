Require Import MonadLib.Monad.
Import MonadNotation.
Local Open Scope monad_scope.

(* Testing Monad notation *)
Module TestMonadNotation.

Declare Instance Option_Monad : Monad option.

(* Test return, bind and long sequences *)
Example test1 : option nat := return 5.
Print test1.

Example test2 : option nat :=
  x <- Some 3 ;; return (x + 2).
Print test2.

Example test3 : option nat :=
  x <- Some 2 ;; y <- Some 3 ;; return (x + y).
Print test3.

Example test4 : option nat :=
  a <- Some 1 ;;
  b <- Some 2 ;;
  c <- Some 3 ;;
  d <- Some 4 ;;
  e <- Some 5 ;;
  f <- Some 6 ;;
  g <- Some 7 ;;
  return (a + b + c + d + e + f + g).
Print test4.

Example test5 : option nat :=
  x <- (a <- Some 1 ;;
        b <- Some 2 ;;
        c <- Some 3 ;;
        d <- Some 4 ;;
        return (a + b + c + d)) ;;
  y <- (c <- Some 3 ;;
        d <- Some 4 ;;
        return (c * d)) ;;
  return (x + y).
Print test5.

Example test6 : option nat := Eval cbv delta [test5] in
  a <- test5 ;;
  b <- test5 ;;
  return (a * b).
Print test6.

(* Test pattern matching in bind *)
Example test_pat1 : option nat :=
  '(a, b) <- Some (1, 2) ;;
  return (a + b).
Print test_pat1.

Example test_pat2 : option nat :=
  '(a, b, c) <- Some (1, 2, 3) ;;
  return (a + b + c).
Print test_pat2.

Example test_pat3 : option (nat * nat) :=
  '(a, b) <- Some (1, 2) ;;
  '(c, d) <- Some (3, 4) ;;
  return (a + c, b + d).
Print test_pat3.

(* Test sequential composition without binding *)
Example test_seq1 : option nat :=
  Some 1 ;;
  Some 2 ;;
  return 3.
Print test_seq1.

Example test_seq2 x : option nat :=
  Some (x + 5) ;;
  Some (x * 2) ;;
  Some (x - 3) ;;
  Some (x + x) ;;
  Some (x + x) ;;
  return (x - 3).
Print test_seq2.

End TestMonadNotation.
