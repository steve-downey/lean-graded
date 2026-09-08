import Graded.Carrier

/-! The first consumer of `Graded`: a two-stage validation modelling
    `expected<int, error_set<parse, range>> validate(std::string)`. The two
    stages are composed by hand with a `match`, since no `bind` exists yet
    ([monad-laws] introduces it and replaces this composition). -/

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

/-- Parse then range-check. Composed by hand: with no `bind` yet, the
    result's union grade `{E.parse, E.range}` and each `err`'s membership
    proof are assembled explicitly at the call site. -/
-- REPLACED-BY: bind
def validate (s : String) : Graded ({E.parse, E.range} : Grade E) Nat :=
  match parseNat s with
  | .err e he =>
      .err e (by
        have h : e = E.parse := Finset.mem_singleton.mp he
        subst h
        exact Finset.mem_insert_self _ _)
  | .ok n =>
    match checkRange n with
    | .err e he => .err e (Finset.mem_insert_of_mem he)
    | .ok m => .ok m

/-- Render a validation result for `#eval`. -/
def render : Graded ({E.parse, E.range} : Grade E) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#eval render (validate "42")    -- ok 42
#eval render (validate "abc")   -- err E.parse : unparsable
#eval render (validate "9999")  -- err E.range : out of range

end Examples.Validation
