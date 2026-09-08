import Graded.Applicative
import Examples.Validation

/-! Examples instantiating every `Graded.Applicative` theorem at a concrete
    error type, plus a `#guard` that computes via `decide`, and — the
    substantive deliverable of this step — a **counterexample** showing
    `ap` and `apFlipped` disagree as *values* when both arguments are
    errors: they agree on the *grade* (via `Grade.join_comm`, `ap_flip`'s
    cast) but not on *which* error survives. This is the content of the
    C++ "the applicative instance is identical to the monad instance"
    claim: identical in grade, identical in value only under a condition
    (at most one side fails) that the C++ claim never states. -/

namespace Tests

open Graded Examples.Validation

/-- Render a `Nat`-valued result at any grade, for `#guard`. Routed through
    `String` rather than compared directly (per the `#guard`-on-`Graded`
    trouble already hit in [monad-laws]'s handoff). -/
def renderN {g : Grade E} : Graded g Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

example (x : Graded ({E.parse} : Grade E) Nat) :
    cast (Grade.bot_join _) (ap (Graded.pure (@id Nat)) x) = x :=
  ap_pure_id x

example (f : Nat → Nat) (a : Nat) :
    cast (Grade.bot_join Grade.bot)
        (ap (Graded.pure f : Graded (Grade.bot : Grade E) (Nat → Nat)) (Graded.pure a)) =
      (Graded.pure (f a) : Graded (Grade.bot : Grade E) Nat) :=
  ap_pure_pure f a

example (u : Graded ({E.parse} : Grade E) (Nat → Nat)) (a : Nat) :
    cast (Grade.join_bot _) (ap u (Graded.pure a)) =
      cast (Grade.bot_join _) (ap (Graded.pure (fun f => f a)) u) :=
  ap_interchange u a

example (u : Graded ({E.parse} : Grade E) (Nat → Nat))
    (v : Graded ({E.range} : Grade E) (Nat → Nat)) (w : Graded ({E.io} : Grade E) Nat) :
    cast (by rw [Grade.bot_join, Grade.join_assoc] :
        Grade.join (Grade.join (Grade.join Grade.bot ({E.parse} : Grade E)) {E.range}) {E.io} =
          Grade.join {E.parse} (Grade.join {E.range} {E.io}))
        (ap (ap (ap (Graded.pure Function.comp :
            Graded (Grade.bot : Grade E) ((Nat → Nat) → (Nat → Nat) → Nat → Nat)) u) v) w) =
      ap u (ap v w) :=
  ap_comp u v w

-- `ap_flip` needs at most one side to be an error; here the value `x` is
-- `ok`, so the hypothesis is satisfied trivially.
example (f : Graded ({E.parse} : Grade E) (Nat → Nat)) (a : Nat) :
    ap f (Graded.ok a : Graded ({E.range} : Grade E) Nat) =
      cast (Grade.join_comm _ _) (apFlipped f (Graded.ok a)) :=
  ap_flip f (Graded.ok a) (Or.inr ⟨a, rfl⟩)

-- `ap` computes.
#guard renderN (ap (Graded.ok (· + 1) : Graded ({E.parse} : Grade E) (Nat → Nat))
    (Graded.ok 41 : Graded ({E.range} : Grade E) Nat)) = "ok 42"

-- ---------------------------------------------------------------------
-- The both-errors counterexample.
--
-- `f` fails with `E.parse`, `x` fails with `E.range`. `ap f x` sequences
-- `f` first (it is `bind`-derived, so it *is* the monad's own sequencing)
-- and reports `f`'s error; `apFlipped f x` sequences `x` first and
-- reports `x`'s error. The two grades agree (both are `{E.parse,
-- E.range}`, via `Grade.join_comm`) but the two *values* disagree about
-- which error survives — exactly the gap in the C++ "applicative is
-- identical to the monad" claim, which states the grade-level fact and
-- is silent about this one.

def bothErrF : Graded ({E.parse} : Grade E) (Nat → Nat) :=
  .err E.parse (by decide)

def bothErrX : Graded ({E.range} : Grade E) Nat :=
  .err E.range (by decide)

-- `ap` keeps the function's error: `f` runs first.
#guard renderN (ap bothErrF bothErrX) = "err Examples.Validation.E.parse"

-- `apFlipped` keeps the value's error: `x` runs first.
#guard renderN (apFlipped bothErrF bothErrX) = "err Examples.Validation.E.range"

-- Both errors are drawn from the *same* grade `{E.parse, E.range}` (the
-- two renders above type-check against a common `renderN`), so this is
-- not a grade mismatch masquerading as a value one: `ap` and `apFlipped`
-- genuinely disagree on which error a caller sees, whenever both sides
-- would have failed.

end Tests
