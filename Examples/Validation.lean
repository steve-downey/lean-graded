import Graded.Carrier
import Graded.Widen
import Graded.Monad
import Graded.Applicative
import Graded.Accum

/-! The first consumer of `Graded`: a two-stage validation modelling
    `expected<int, error_set<parse, range>> validate(std::string)`. The two
    stages are composed with `bind` ([monad-laws]); a third stage,
    `validateAndLog`, composes them with nested `bind`. -/

namespace Examples.Validation

open Graded

inductive E | parse | range | io
  deriving DecidableEq, Repr

/-- Parse a string as a `Nat`, failing with `E.parse` on a bad string. -/
def parseNat (s : String) : Graded ({E.parse} : Grade E) Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .err E.parse (Finset.mem_singleton_self E.parse)

/-- Accept `n` only when it is at most 100, failing with `E.range` above
    that. -/
def checkRange (n : Nat) : Graded ({E.range} : Grade E) Nat :=
  if n ≤ 100 then .ok n else .err E.range (Finset.mem_singleton_self E.range)

/-- Parse then range-check, composed by `bind`: the result's union grade
    and each `err`'s membership proof are assembled by `bind` itself
    rather than at this call site. -/
def validate (s : String) : Graded ({E.parse, E.range} : Grade E) Nat :=
  bind (parseNat s) checkRange

/-- Render a validation result for `#eval`. -/
def render : Graded ({E.parse, E.range} : Grade E) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#eval render (validate "42")    -- ok 42
#eval render (validate "abc")   -- err E.parse : unparsable
#eval render (validate "9999")  -- err E.range : out of range

/-- A third stage that only ever logs, modelling a call that carries an
    `E.io` grade but cannot itself fail otherwise. -/
def logIt (_ : Nat) : Graded ({E.io} : Grade E) Unit := .ok ()

/-- All three stages, composed by nested `bind`: parse, then range-check,
    then log. Models `parse(s).and_then(check_range).and_then(log_it)`. -/
def validateAndLog (s : String) : Graded ({E.parse, E.range, E.io} : Grade E) Unit :=
  bind (bind (parseNat s) checkRange) logIt

/-- Render a log-and-validate result for `#eval`. -/
def renderLog : Graded ({E.parse, E.range, E.io} : Grade E) Unit → String
  | .ok () => "ok ()"
  | .err e _ => s!"err {repr e}"

#eval renderLog (validateAndLog "42")    -- ok ()
#eval renderLog (validateAndLog "abc")   -- err E.parse
#eval renderLog (validateAndLog "9999")  -- err E.range

-- The nested-`bind` three-stage composition produces the same outcome as
-- the two-stage `validate`, up to `logIt` never failing: success and each
-- failure kind agree.
#guard renderLog (validateAndLog "42") = "ok ()"
#guard renderLog (validateAndLog "abc") = "err Examples.Validation.E.parse"
#guard renderLog (validateAndLog "9999") = "err Examples.Validation.E.range"

-- Widening `parseNat`'s failure from grade `{E.parse}` into the union
-- grade `{E.parse, E.range, E.io}` (as if it were composed with
-- `checkRange` and `logIt`) agrees with constructing the same failure
-- directly at that wider grade. This is the C++ implicit-conversion
-- chain made into a checked, computed equality rather than an assumed
-- one.
#guard
  widen (g' := ({E.parse, E.range, E.io} : Grade E)) (by decide) (parseNat "abc") =
    (.err E.parse (by decide) : Graded ({E.parse, E.range, E.io} : Grade E) Nat)

/-- Two *independent* validations, combined with `map2` rather than
    `bind`: `sumTwo` never lets `s2`'s parse depend on `s1`'s result, the
    way `validate` above threads its `Nat` payload from stage to stage.
    Models summing two independently-parsed inputs — the shape a C++
    caller reaches for `liftA2`/`map2` instead of `and_then` for. Both
    stages share the grade `{E.parse}`, so the result grade is `{E.parse}`
    too (`Grade.join_idem`, unlike `validate`'s `{E.parse, E.range}`). -/
def sumTwo (s1 s2 : String) : Graded ({E.parse} : Grade E) Nat :=
  map2 (· + ·) (parseNat s1) (parseNat s2)

/-- Render a `sumTwo` result for `#eval`. -/
def renderSum : Graded ({E.parse} : Grade E) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#eval renderSum (sumTwo "3" "4")      -- ok 7
#eval renderSum (sumTwo "abc" "4")    -- err E.parse : s1 failed
#eval renderSum (sumTwo "3" "xyz")    -- err E.parse : s2 failed
#eval renderSum (sumTwo "abc" "xyz")  -- err E.parse : both failed

#guard renderSum (sumTwo "3" "4") = "ok 7"

-- Both stages parse with the same error kind, so this `#guard` cannot
-- distinguish *which* argument failed from the value alone — that
-- distinction needs two different error kinds, which is exactly what
-- `Tests/Applicative.lean`'s both-errors counterexample uses `parseNat`
-- and a range check for. What this does show is that `map2`, like `ap`,
-- short-circuits: whenever either argument fails, the combination fails
-- with `E.parse`, and only when both succeed does it add the two
-- payloads.
#guard renderSum (sumTwo "abc" "4") = "err Examples.Validation.E.parse"
#guard renderSum (sumTwo "3" "xyz") = "err Examples.Validation.E.parse"
#guard renderSum (sumTwo "abc" "xyz") = "err Examples.Validation.E.parse"

-- ---------------------------------------------------------------------
-- `Accum` versions: the same two fields, but validated so that *both*
-- failures survive instead of stopping at the first — the shape a form
-- with two independent fields wants (report every bad field at once),
-- which `Graded`'s one-error carrier cannot give.

/-- `Accum` version of `parseNat`: same failure, same grade, through the
    accumulating carrier. -/
def parseNatAccum (s : String) : Accum ({E.parse} : Grade E) Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .errs [E.parse] (by simp) (by simp)

/-- A second, independent field check with its *own* error kind
    (`E.range`), so a "both fields bad" example shows two visibly
    different errors — `parseNatAccum` alone shares one error kind with
    itself and a "both bad" run of it can't be told apart from "one bad"
    (the same limitation `sumTwo` above has). -/
def checkNonEmptyAccum (s : String) : Accum ({E.range} : Grade E) String :=
  if s.isEmpty then .errs [E.range] (by simp) (by simp) else .ok s

/-- Two independent fields, combined with `Accum.map2`: unlike `sumTwo`'s
    `map2` (which shares its short-circuit-to-one-error limit with
    `Graded.ap`), both fields' errors survive when both fail. -/
def validateTwoFields (s1 s2 : String) :
    Accum (Grade.join ({E.parse} : Grade E) ({E.range} : Grade E)) (Nat × String) :=
  Accum.map2 Prod.mk (parseNatAccum s1) (checkNonEmptyAccum s2)

/-- Render an error list for `#eval`/`#guard`. -/
def renderErrs (es : List E) : String :=
  String.intercalate ", " (es.map (fun e => s!"{repr e}"))

/-- Render a `validateTwoFields` result. -/
def renderPair :
    Accum (Grade.join ({E.parse} : Grade E) ({E.range} : Grade E)) (Nat × String) → String
  | .ok (n, s) => s!"ok ({n}, {s})"
  | .errs es _ _ => s!"errs [{renderErrs es}]"

#eval renderPair (validateTwoFields "3" "hi")     -- ok (3, hi)
#eval renderPair (validateTwoFields "abc" "hi")   -- errs [E.parse] : field 1 bad
#eval renderPair (validateTwoFields "3" "")       -- errs [E.range] : field 2 bad
#eval renderPair (validateTwoFields "abc" "")     -- errs [E.parse, E.range] : both bad

#guard renderPair (validateTwoFields "3" "hi") = "ok (3, hi)"
#guard renderPair (validateTwoFields "abc" "hi") = "errs [Examples.Validation.E.parse]"
#guard renderPair (validateTwoFields "3" "") = "errs [Examples.Validation.E.range]"

-- The substantive deliverable: both fields bad, both errors present —
-- exactly what `Graded`'s one-error carrier cannot show (compare
-- `sumTwo "abc" "xyz"` above, which can only ever report `E.parse`, the
-- one error `Graded.ap`'s carrier has room for).
#guard renderPair (validateTwoFields "abc" "") =
  "errs [Examples.Validation.E.parse, Examples.Validation.E.range]"

end Examples.Validation
