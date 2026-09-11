import Graded.Carrier

/-! A signature whose errors carry data, which is what `ExpectedG` exists
    for. `Examples/Validation.lean` uses the tag-only specialization
    throughout and stays that way — it is the compatibility evidence that
    nothing regressed. This file is the other half: a signature where
    each kind carries a different payload type, exercised end to end.

    `docs/design.md#cpp-counterpart` has always said an `error_set`
    instance "holds **one** error value, whose type is in the set". Until
    [payload-carrier] the model held the *type* and not the value, so no
    law about a parse location or a range bound was statable. -/

namespace Examples.Payload

open Graded

/-- Three kinds, carrying three different things. -/
inductive PK | parse | range | io
  deriving DecidableEq, Repr

/-- What each kind carries: a parse failure knows where it stopped, a
    range failure knows the bound it exceeded, an I/O failure knows an
    errno. The payload types are genuinely different, so a proof that
    treated them uniformly would not typecheck. -/
abbrev PPayload : PK → Type
  | .parse => Nat        -- byte offset
  | .range => Nat × Nat  -- (bound, actual)
  | .io    => String     -- errno name

abbrev PSig : ErrorSignature := ⟨PK, PPayload⟩

/-- The per-signature obligation. `ExpectedG`'s `DecidableEq` needs one
    for **each** member of the payload family, and instance search cannot
    assemble it from the pieces: this dependent instance is what a
    concrete signature owes, and every `#guard` below reduces through
    it. -/
instance : ∀ k, DecidableEq (PPayload k)
  | .parse => inferInstanceAs (DecidableEq Nat)
  | .range => inferInstanceAs (DecidableEq (Nat × Nat))
  | .io    => inferInstanceAs (DecidableEq String)

instance : ∀ k, Repr (PPayload k)
  | .parse => inferInstanceAs (Repr Nat)
  | .range => inferInstanceAs (Repr (Nat × Nat))
  | .io    => inferInstanceAs (Repr String)

abbrev PGrade : Grade PK := {PK.parse, PK.range}

/-- Parse a decimal string, reporting *where* it failed. -/
def parseAt (s : String) : ExpectedG PSig PGrade Nat :=
  match s.toNat? with
  | some n => .ok n
  | none   => .err PK.parse s.length (by decide)

/-- Check a bound, reporting both the bound and what was seen. -/
def checkBound (bound n : Nat) : ExpectedG PSig PGrade Nat :=
  if n ≤ bound then .ok n else .err PK.range (bound, n) (by decide)

def render : ExpectedG PSig PGrade Nat → String
  | .ok n => s!"ok {n}"
  | .err PK.parse off _ => s!"parse at {off}"
  | .err PK.range (b, a) _ => s!"range {a} > {b}"
  | .err PK.io e _ => s!"io {e}"

-- The payload survives, and it is the payload the failure produced.
#guard render (parseAt "42") = "ok 42"
#guard render (parseAt "4x2") = "parse at 3"
#guard render (parseAt "nope") = "parse at 4"
#guard render (checkBound 100 7) = "ok 7"
#guard render (checkBound 100 250) = "range 250 > 100"

-- Two failures of the same kind carrying different payloads are
-- different values. This is the whole point, and it is the statement the
-- tag-only carrier could not make: there, both are `err parse`.
#guard parseAt "4x2" ≠ parseAt "nope"
#guard checkBound 100 250 ≠ checkBound 10 250

-- And the same payload gives the same value.
#guard parseAt "4x2" = parseAt "1y2"

/-- The membership proof stays proof-irrelevant with a payload in play:
    two errors of the same kind carrying the same payload are the same
    value, whichever witness each was built with. `toSum` forgetting the
    witness is sound for exactly this reason. -/
example (k : PK) (p : PPayload k) (h h' : k ∈ PGrade) :
    (ExpectedG.err k p h : ExpectedG PSig PGrade Nat)
      = (ExpectedG.err k p h' : ExpectedG PSig PGrade Nat) := rfl

end Examples.Payload
