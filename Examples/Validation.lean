import Graded.Carrier
import Graded.Widen
import Graded.Monad
import Graded.Sufficient
import Graded.Applicative
import Graded.Accum
import Graded.Traverse
import Graded.Tuple
import Graded.Compose
import Graded.ComposeApp
import Graded.Morphism

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

/-- The same two-stage validation, spelled through `bindK` at the literal
    grade `{E.parse, E.range}` instead of `bind`'s computed union — here
    the two happen to coincide, since `{E.parse, E.range}` *is*
    `Grade.join {E.parse} {E.range}`, so both spellings exist and agree.
    `validate` above is left untouched: this is a second view of the same
    operation, not a replacement for it. -/
def validateK (s : String) : Graded ({E.parse, E.range} : Grade E) Nat :=
  bindK (by decide) (by decide) (parseNat s) checkRange

-- `validate` and `validateK` render identically on every input: the
-- union-graded `bind` and the sufficient-grade `bindK`, instantiated at
-- the same grade, are the same operation (`bind_eq_bindK`).
#guard render (validateK "42") = render (validate "42")
#guard render (validateK "abc") = render (validate "abc")
#guard render (validateK "9999") = render (validate "9999")

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

-- ---------------------------------------------------------------------
-- `traverse`: parsing a whole `List String` with the uniform `parseNat`,
-- at the *uniform* grade `{E.parse}` regardless of the list's length —
-- the C++ `traverse` signature this step's theorems make typeable.

/-- Render a `traverse parseNat` result for `#eval`/`#guard`. -/
def renderNats : Graded ({E.parse} : Grade E) (List Nat) → String
  | .ok ns => s!"ok {ns}"
  | .err e _ => s!"err {repr e}"

#eval renderNats (traverse parseNat ["1", "2", "3"])   -- ok [1, 2, 3]
#eval renderNats (traverse parseNat ["1", "2", "x"])   -- err E.parse
#eval renderNats (traverse parseNat ([] : List String)) -- ok []

#guard renderNats (traverse parseNat ["1", "2", "3"]) = "ok [1, 2, 3]"
#guard renderNats (traverse parseNat ["1", "2", "x"]) = "err Examples.Validation.E.parse"

-- The empty list traverses to `fromEmpty []` (`traverse_nil`): compared
-- through `renderNats`, per the `#guard`-on-`Graded` detour every
-- consumer in this codebase has needed since [monad-laws].
#guard renderNats (traverse parseNat ([] : List String)) =
  renderNats (fromEmpty [] : Graded ({E.parse} : Grade E) (List Nat))

-- ---------------------------------------------------------------------
-- `sequence`: a heterogeneous 3-tuple — `parseNat s` (`Nat`, grade
-- `{E.parse}`), `checkRange n` (`Nat`, grade `{E.range}`), `logIt n`
-- (`Unit`, grade `{E.io}`) — combined into one graded `HList [Nat, Nat,
-- Unit]`. Unlike `traverse`'s uniform-grade `List`, every element here
-- has its *own* grade and its *own* payload type: this is the C++
-- `transpose(tuple<expected<int, error_set<parse>>, expected<int,
-- error_set<range>>, expected<Unit, error_set<io>>>)` case, and the
-- result grade below is the *union* `{E.parse, E.range, E.io}`, computed
-- once from the tuple's shape rather than folded at runtime.

/-- Three independent validations, combined by `sequence` into one graded
    heterogeneous tuple. The result grade is `joinAll [{E.parse},
    {E.range}, {E.io}]`, which the type ascription below states as the
    literal union `{E.parse, E.range, E.io}` — accepted by Lean
    definitionally, the same way `validate`'s `bind`-computed grade above
    is accepted against its own literal-union ascription. -/
def validateTuple (s : String) (n : Nat) :
    Graded ({E.parse, E.range, E.io} : Grade E) (HList ([Nat, Nat, Unit] : List (Type))) :=
  sequence (GList.cons (parseNat s) (GList.cons (checkRange n) (GList.cons (logIt n) GList.nil)))

-- The result grade, displayed by `#check` as the union of the three
-- element grades — the C++ `error_set<parse, range, io>` this tuple's
-- `transpose` would produce.
#check (validateTuple "42" 50 :
  Graded ({E.parse, E.range, E.io} : Grade E) (HList ([Nat, Nat, Unit] : List (Type))))

/-- Render a `validateTuple` result for `#eval`/`#guard`. -/
def renderTuple :
    Graded ({E.parse, E.range, E.io} : Grade E) (HList ([Nat, Nat, Unit] : List (Type))) → String
  | .ok (a, b, _) => s!"ok ({a}, {b})"
  | .err e _ => s!"err {repr e}"

#eval renderTuple (validateTuple "42" 50)     -- ok (42, 50): all three succeed
#eval renderTuple (validateTuple "42" 9999)   -- err E.range: the *middle* element fails
#eval renderTuple (validateTuple "abc" 50)    -- err E.parse: the first element fails

#guard renderTuple (validateTuple "42" 50) = "ok (42, 50)"

-- The failure-in-the-middle-element case: `parseNat "42"` succeeds,
-- `checkRange 9999` fails (`9999 > 100`), `logIt` is never in question
-- (it cannot fail) — the whole tuple reports `E.range`, the middle
-- element's error, exactly as a C++ `transpose` short-circuiting on the
-- second field would.
#guard renderTuple (validateTuple "42" 9999) = "err Examples.Validation.E.range"

-- ---------------------------------------------------------------------
-- `flatten`: a stage that returns a graded value *inside* a graded
-- value — `lookup s` first performs an I/O-graded fetch (which can fail
-- with `E.io`, e.g. "not found"), and, on success, hands back a
-- `parseNat`-graded `Nat` (which can fail with `E.parse`) without having
-- committed to a union grade yet. This is the C++
-- `expected<expected<int, error_set<parse>>, error_set<io>> lookup(std::string)`
-- shape [compose-flatten] collapses via `flatten` to a single
-- `expected<int, error_set<io, parse>>`.

/-- Fetch `s`, modelling an I/O stage that fails with `E.io` on the empty
    string and otherwise hands back an *unflattened* `parseNat` result. -/
def lookup (s : String) : Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat) :=
  if s = "" then .err E.io (Finset.mem_singleton_self E.io)
  else .ok (parseNat s)

/-- Render a `flatten (lookup s)` result for `#eval`/`#guard`. -/
def renderLookup : Graded ({E.io, E.parse} : Grade E) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#eval renderLookup (flatten (lookup "42"))   -- ok 42: the I/O fetch and the parse both succeed
#eval renderLookup (flatten (lookup ""))     -- err E.io: the I/O fetch itself fails
#eval renderLookup (flatten (lookup "abc"))  -- err E.parse: the fetch succeeds, the parse fails

#guard renderLookup (flatten (lookup "42")) = "ok 42"
#guard renderLookup (flatten (lookup "")) = "err Examples.Validation.E.io"
#guard renderLookup (flatten (lookup "abc")) = "err Examples.Validation.E.parse"

-- ---------------------------------------------------------------------
-- `rename`: coarsening `error_set<parse, range>` down to a single error
-- kind, the C++ `transform_error`-style operation this step gives laws
-- to. `coarsen` sends *both* `E.parse` and `E.range` to the same target
-- `E'.bad` — a genuinely non-injective renaming, the case
-- `Grade.rename`/`rename` were built to allow without any extra
-- hypothesis.

/-- The coarsened error universe: every source kind collapses to this
    one kind. Models a C++ caller who doesn't care *which* validation
    step failed, only that one did. -/
inductive E' | bad
  deriving DecidableEq, Repr

/-- Send every `E` to the one target kind `E'.bad` — non-injective, since
    both `E.parse` and `E.range` map to it. -/
def coarsen (_ : E) : E' := E'.bad

-- The renamed grade collapses `{E.parse, E.range}` to the singleton
-- `{E'.bad}`, regardless of `coarsen` not being injective — the
-- homomorphism (`Grade.rename_join`/`Grade.rename_bot`) is what makes
-- this a `Finset.image` computation rather than a proof obligation.
#check (Grade.rename coarsen ({E.parse, E.range} : Grade E) : Grade E')

#guard Grade.rename coarsen ({E.parse, E.range} : Grade E) = ({E'.bad} : Grade E')

/-- Render a coarsened `validate` result for `#eval`/`#guard`. -/
def renderCoarse : Graded (Grade.rename coarsen ({E.parse, E.range} : Grade E)) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#eval renderCoarse (rename coarsen (validate "42"))    -- ok 42: no error to rename
#eval renderCoarse (rename coarsen (validate "abc"))   -- err E'.bad: was E.parse
#eval renderCoarse (rename coarsen (validate "9999"))  -- err E'.bad: was E.range

-- Two source errors, one target kind: `coarsen` really does lose the
-- distinction between "which validation step failed" that `validate`'s
-- own grade `{E.parse, E.range}` still carries — this is the C++ reader's
-- payoff, not a limitation of the model.
#guard renderCoarse (rename coarsen (validate "42")) = "ok 42"
#guard renderCoarse (rename coarsen (validate "abc")) = "err Examples.Validation.E'.bad"
#guard renderCoarse (rename coarsen (validate "9999")) = "err Examples.Validation.E'.bad"

-- ---------------------------------------------------------------------
-- `traverseComp`: the two-stage pipeline run through the composed
-- applicative *without* flattening — `parseNat` supplies the outer layer,
-- `checkRange` (lifted via `map`) the inner. This is the structure
-- [compose-flatten] never built: `Graded {E.parse} (Graded {E.range} Nat)`
-- per element, kept nested all the way to `Comp {E.parse} {E.range}
-- (List Nat)`, not collapsed to a single flat grade.

/-- Render a `Comp {E.parse} {E.range} (List Nat)` result for
    `#eval`/`#guard`. -/
def renderComposed :
    Comp ({E.parse} : Grade E) ({E.range} : Grade E) (List Nat) → String
  | .ok (.ok ns) => s!"ok (ok {ns})"
  | .ok (.err e _) => s!"ok (err {repr e})"
  | .err e _ => s!"err {repr e}"

#eval renderComposed
    (traverseComp (fun s => Graded.map checkRange (parseNat s)) ["1", "2", "3"])
  -- ok (ok [1, 2, 3]): every element's outer parse and inner range check succeed
#eval renderComposed
    (traverseComp (fun s => Graded.map checkRange (parseNat s)) ["1", "9999", "3"])
  -- ok (err E.range): every element parses; the middle one is out of range
#eval renderComposed
    (traverseComp (fun s => Graded.map checkRange (parseNat s)) ["1", "x", "3"])
  -- err E.parse: the middle element fails to parse; the range check is
  -- never reached for any element, since the outer layer short-circuits

#guard renderComposed
    (traverseComp (fun s => Graded.map checkRange (parseNat s)) ["1", "2", "3"]) =
  "ok (ok [1, 2, 3])"
#guard renderComposed
    (traverseComp (fun s => Graded.map checkRange (parseNat s)) ["1", "9999", "3"]) =
  "ok (err Examples.Validation.E.range)"
#guard renderComposed
    (traverseComp (fun s => Graded.map checkRange (parseNat s)) ["1", "x", "3"]) =
  "err Examples.Validation.E.parse"

-- `traverseComp_eq` on the same inputs: the composed traversal equals
-- `map (traverse checkRange) (traverse parseNat xs)`, computed the other
-- way.
#guard renderComposed
    (traverseComp (fun s => Graded.map checkRange (parseNat s)) ["1", "9999", "3"]) =
  renderComposed (Graded.map (traverse checkRange) (traverse parseNat ["1", "9999", "3"]))

-- ---------------------------------------------------------------------
-- On one screen: the flattened composition and the interleaved
-- per-element composition disagree, exactly as [compose-flatten] found —
-- and `traverseComp` is the explanation, not just a witness. `checkRange`
-- fails *early* (position 0: "9999" parses but is out of range) while
-- `parseNat` fails *late* (position 1: "x" does not parse at all) — the
-- shape [compose-flatten]'s own counterexample needed.

def counterXs : List String := ["9999", "x"]

/-- Render a flattened `{E.parse, E.range}`-graded result. -/
def renderFlat : Graded ({E.parse, E.range} : Grade E) (List Nat) → String
  | .ok ns => s!"ok {ns}"
  | .err e _ => s!"err {repr e}"

-- The naive law's left side: `flatten (traverseComp (fun a => map k (f
-- a)) xs)`, which by `traverseComp_eq` is `flatten (map (traverse
-- checkRange) (traverse parseNat xs))` — committing to *all* of
-- `parseNat` before ever consulting `checkRange`. `parseNat` fails at the
-- *later* position (1, "x"), so that is the error this side reports.
#eval renderFlat (flatten (traverseComp (fun s => Graded.map checkRange (parseNat s)) counterXs))
  -- err E.parse: the late `parseNat` failure, from committing to the
  -- outer layer across the whole list first

/-- The per-element composed-then-flattened function: exactly
    [compose-flatten]'s `fun a => flatten (map k (f a))`. -/
def parseThenRange (s : String) : Graded ({E.parse, E.range} : Grade E) Nat :=
  flatten (Graded.map checkRange (parseNat s))

-- The naive law's right side: `traverse (fun a => flatten (map k (f a)))
-- xs`, which flattens each element before `traverse`'s own left-to-right
-- short circuit ever sees it. `checkRange` fails at the *earlier*
-- position (0, "9999"), so that is the error this side reports —
-- different from the left side above, though both inputs are identical.
#eval renderFlat (traverse parseThenRange counterXs)
  -- err E.range: the early `checkRange` failure, from flattening each
  -- element before traversing

#guard renderFlat (flatten (traverseComp (fun s => Graded.map checkRange (parseNat s)) counterXs))
  = "err Examples.Validation.E.parse"
#guard renderFlat (traverse parseThenRange counterXs) = "err Examples.Validation.E.range"

-- The two sides disagree on the *same* input: flattening early
-- (per-element) versus flattening late (after the whole composed
-- traversal) are genuinely different operations, and only the *unflattened*
-- `traverseComp` — reporting its own outer/inner grades separately, as
-- `renderComposed` above shows — states unambiguously which layer failed.
-- `flatten` is what erases that distinction, in either order.

end Examples.Validation
