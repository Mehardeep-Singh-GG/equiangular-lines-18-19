module

/-!
# Pure-Kernel Integer Farkas Checker Core

Defines `dotZ` and `checkCertZ` in pure Lean 4 core (no Mathlib imports, `by decide` only).
-/

@[expose] public section

namespace EquiangularLines.Certs

def dotZ : List Int → List Int → Int
  | [], [] => 0
  | a :: as, b :: bs => a * b + dotZ as bs
  | _, _ => 0

def checkCertZ (rhs y : List Int) (cols : List (List Int)) : Bool :=
  y.length == rhs.length &&
  decide (dotZ y rhs < 0) &&
  cols.all (fun col => col.length == y.length && decide (0 ≤ dotZ y col))

end EquiangularLines.Certs

end
