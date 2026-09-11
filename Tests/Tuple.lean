import Graded.Tuple
import Examples.Validation

/-! Examples instantiating every `Graded.Tuple` theorem at a concrete
    error type, plus a `#guard` that heterogeneous `sequence` computes.

    The `joinAll` examples moved to `Tests/GradeFold.lean` with the code,
    at [module-split] — and took this file's only computing check with
    them, which `make test-coverage` caught immediately. The replacement
    below exercises `sequence` itself, which is what this module is
    actually about. -/

namespace Tests

open Graded Examples.Validation List

example : sequence (Err := E) GList.nil = Graded.pure HList.nil :=
  sequence_nil

example (x : Graded ({E.parse} : Grade E) Nat)
    (xs : GList ([] : List (Grade E)) ([] : List (Type))) :
    sequence (GList.cons x xs) = map2 HList.cons x (sequence xs) :=
  sequence_cons x xs

-- ---------------------------------------------------------------------
-- `sequence` computes, on a genuinely heterogeneous tuple: two distinct
-- payload types (`Nat` and `String`) at two distinct grades, which is the
-- fixture `docs/RULES.md#tests` asks for here — a homogeneous pair would
-- pass against a `sequence` that ignored one index.

/-- A two-slot tuple: a `Nat` at `{parse}` and a `String` at `{range}`. -/
def pairGL : GList ([{E.parse}, {E.range}] : List (Grade E)) [Nat, String] :=
  GList.cons (Graded.ok 7) (GList.cons (Graded.ok "hi") GList.nil)

def renderPairGL : Graded (joinAll ([{E.parse}, {E.range}] : List (Grade E)))
    (HList [Nat, String]) → String
  -- `HList` is a recursive `def` down to nested `Prod`, not an
  -- inductive, so its `cons` is not a pattern; match the pair directly.
  | .ok (n, s, _) => s!"ok ({n}, {s})"
  | .err e _ => s!"err {repr e}"

#guard renderPairGL (sequence pairGL) = "ok (7, hi)"

end Tests
