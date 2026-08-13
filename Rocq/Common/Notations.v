(** Copied from CompCert cfrontend/Cexec.v *)

Declare Scope option_monad_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => None end)
  (at level 200, X name, Y name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => None end)
  (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z , W <- A ; B" := (match A with Some (X, Y, Z, W) => B | None => None end)
  (at level 200, X name, Y name, Z name, W name, A at level 100, B at level 200)
  : option_monad_scope.

Notation " 'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.
