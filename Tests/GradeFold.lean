import Graded.GradeFold
import Examples.Validation

/-! Examples for `Graded.GradeFold`, moved here from `Tests/Tuple.lean` by
    [module-split] when `joinAll` moved out of `Graded/Tuple.lean`. The
    tests follow the code: a module that has its own file has its own test
    file, which is also what keeps `make test-coverage`'s
    reduction-lemma rule pointing at the right place. -/

namespace Tests.GradeFold

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

-- `join_mem_eq`: a grade already in the list is absorbed by the fold.
-- Instantiated at a three-grade list with the member in the middle, so
-- the proof has to walk past one element and absorb into a nonempty
-- tail — a singleton list would hold for a fold that ignored its tail.
example (hmem : ({E.range} : Grade E) ∈ [({E.parse} : Grade E), {E.range}, {E.io}]) :
    Grade.join ({E.range} : Grade E) (joinAll [({E.parse} : Grade E), {E.range}, {E.io}])
      = joinAll [({E.parse} : Grade E), {E.range}, {E.io}] :=
  join_mem_eq hmem

example : joinAll ([] : List (Grade E)) = Grade.bot := joinAll_nil

example (g : Grade E) (gs : List (Grade E)) :
    joinAll (g :: gs) = Grade.join g (joinAll gs) := joinAll_cons g gs

-- `joinAll_le_of_mem`: a slot's own grade sits inside the fold. At a
-- three-grade list with the member in the middle, so the inclusion is
-- not the whole fold trivially.
example (hmem : ({E.range} : Grade E) ∈ [({E.parse} : Grade E), {E.range}, {E.io}]) :
    ({E.range} : Grade E) ⊆ joinAll [({E.parse} : Grade E), {E.range}, {E.io}] :=
  joinAll_le_of_mem hmem

#guard joinAll [({E.parse} : Grade E), {E.range}, {E.io}] = {E.parse, E.range, E.io}
#guard joinAll ([] : List (Grade E)) = (Grade.bot : Grade E)

end Tests.GradeFold
