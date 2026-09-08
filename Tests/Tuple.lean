import Graded.Tuple
import Examples.Validation

/-! Examples instantiating every `Graded.Tuple` theorem at a concrete error
    type, plus a `decide` that `joinAll` computes and is order-independent
    — the concrete instance of `joinAll_perm` this codebase's `decide`
    convention (`docs/RULES.md#tests`) asks for. -/

namespace Tests

open Graded Examples.Validation List

-- `joinAll` computes, and is order-independent: folding `{E.parse}` then
-- `{E.range}` gives the same grade as folding them the other way round —
-- exactly the C++ `error_set<parse, range>` ≡ `error_set<range, parse>`
-- claim, here checked by `decide` rather than merely asserted.
example : joinAll ([{E.parse}, {E.range}] : List (Grade E)) =
    joinAll ([{E.range}, {E.parse}] : List (Grade E)) := by decide

example (h : ([{E.parse}, {E.range}] : List (Grade E)) ~ [{E.range}, {E.parse}]) :
    joinAll ([{E.parse}, {E.range}] : List (Grade E)) =
      joinAll ([{E.range}, {E.parse}] : List (Grade E)) :=
  joinAll_perm h

example : joinAll (([{E.parse}, {E.parse}, {E.range}] : List (Grade E)).dedup) =
    joinAll ([{E.parse}, {E.parse}, {E.range}] : List (Grade E)) :=
  joinAll_dedup _

example : sequence (Err := E) GList.nil = Graded.pure HList.nil :=
  sequence_nil

example (x : Graded ({E.parse} : Grade E) Nat)
    (xs : GList ([] : List (Grade E)) ([] : List (Type))) :
    sequence (GList.cons x xs) = map2 HList.cons x (sequence xs) :=
  sequence_cons x xs

end Tests
