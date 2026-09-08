import Graded.Carrier
import Graded.Widen
import Graded.Monad

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

end Examples.Validation
