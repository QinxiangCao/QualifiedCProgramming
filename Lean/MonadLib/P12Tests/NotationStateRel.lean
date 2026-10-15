import MonadLib.StateRelMonad.StateRelMonad

namespace P12Tests.NotationStateRel

open MonadLib.StateRelMonad
open scoped MonadLib.MonadNotation
open scoped MonadLib.StateRelMonad.StateRelMonadNotation
open scoped MonadLib.StateRelMonad.prog_scope

structure St where
  i : Int
  sum : Int
  deriving Repr

def seti (s : St) (v : Int) : St := { i := v, sum := s.sum }
def setsum (s : St) (v : Int) : St := { i := s.i, sum := v }

def sum_upto (n : Int) : program St Unit :=
  UPDATE s := seti s 0 ;;
  UPDATE s := setsum s 0 ;;
  WHILE s, s.i < n DO
    UPDATE s := setsum s (s.sum + s.i) ;;
    UPDATE s := seti s (s.i + 1)
  END

example (n : Int) :
    sum_upto n =
      (update' (fun s => seti s 0) ;;
       update' (fun s => setsum s 0) ;;
       whileP (fun s => s.i < n)
         (update' (fun s => setsum s (s.sum + s.i)) ;;
          update' (fun s => seti s (s.i + 1)))) := rfl

def sum_evens (n : Int) : program St Unit :=
  UPDATE s := setsum s 0 ;;
  FOR k FROM 0 TO n DO
    WHEN s, k % 2 = 0 THEN
      UPDATE s := setsum s (s.sum + k)
    END
  END

def first_i_reaching_10 : program St Int :=
  LOOP
    IF s, s.i >= 10 THEN
      r <- get' (fun s => s.sum) ;;
      BREAK r
    ELSE
      UPDATE s := setsum s (s.sum + s.i) ;;
      UPDATE s := seti s (s.i + 1) ;;
      CONTINUE
    FI
  END

def guess_bit : program St Unit :=
  CHOOSE {
    UPDATE s := seti s 0
  | UPDATE s := seti s 1
  }

example : guess_bit =
    choice (update' (fun s => seti s 0)) (update' (fun s => seti s 1)) := rfl

def sum_upto_pure (n : Int) : MONAD Int :=
  REPEAT (k, acc) FROM (0, 0) DO
    CHOOSE {
      assume!! (k <= n) ;; NEXT (k + 1, acc + k)
    | assume!! (k > n) ;; BREAK acc
    }
  END

example (n : Int) :
    sum_upto_pure n =
      repeat_break
        (fun (k, acc) =>
          choice (assume!! (k <= n) ;; «continue» (k + 1, acc + k))
            (assume!! (k > n) ;; «break» acc))
        (0, 0) := rfl

end P12Tests.NotationStateRel
