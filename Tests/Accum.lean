import Graded.Accum
import Examples.Validation

/-! Examples instantiating every `Graded.Accum` theorem at the concrete
    error type `E`, plus a `#guard` that computes, and the `notMonad`
    witness instantiated at `E.parse`/`E.range`. Routed through `String`
    rather than compared directly, per the `#guard`-on-`Graded`/`Accum`
    trouble already hit in [monad-laws]'s and
    [applicative-from-monad]'s handoffs. -/

namespace Tests

open Graded Graded.Accum Examples.Validation

/-- Render an `Accum` result at any grade, for `#guard`. -/
def renderAccumN {g : Grade E} : Accum g Nat → String
  | .ok n => s!"ok {n}"
  | .errs es _ _ => s!"errs [{renderErrs es}]"

example (x : Accum ({E.parse} : Grade E) Nat) :
    cast (Grade.bot_join _) (ap (Accum.pure (@id Nat)) x) = x :=
  ap_pure_id x

example (f : Nat → Nat) (a : Nat) :
    cast (Grade.bot_join Grade.bot)
        (ap (Accum.pure f : Accum (Grade.bot : Grade E) (Nat → Nat)) (Accum.pure a)) =
      (Accum.pure (f a) : Accum (Grade.bot : Grade E) Nat) :=
  ap_pure_pure f a

example (u : Accum ({E.parse} : Grade E) (Nat → Nat)) (a : Nat) :
    cast (Grade.join_bot _) (ap u (Accum.pure a)) =
      cast (Grade.bot_join _) (ap (Accum.pure (fun f => f a)) u) :=
  ap_interchange u a

example (u : Accum ({E.parse} : Grade E) (Nat → Nat))
    (v : Accum ({E.range} : Grade E) (Nat → Nat)) (w : Accum ({E.io} : Grade E) Nat) :
    cast (by rw [Grade.bot_join, Grade.join_assoc] :
        Grade.join (Grade.join (Grade.join Grade.bot ({E.parse} : Grade E)) {E.range}) {E.io} =
          Grade.join {E.parse} (Grade.join {E.range} {E.io}))
        (ap (ap (ap (Accum.pure Function.comp :
            Accum (Grade.bot : Grade E) ((Nat → Nat) → (Nat → Nat) → Nat → Nat)) u) v) w) =
      ap u (ap v w) :=
  ap_comp u v w

-- `ap` computes.
#guard renderAccumN (ap (Accum.ok (· + 1) : Accum ({E.parse} : Grade E) (Nat → Nat))
    (Accum.ok 41 : Accum ({E.range} : Grade E) Nat)) = "ok 42"

-- ---------------------------------------------------------------------
-- The both-errors accumulation: unlike `Graded.ap`, both errors survive,
-- function's error first.

def bothErrFAccum : Accum ({E.parse} : Grade E) (Nat → Nat) :=
  .errs [E.parse] (by simp) (by simp)

def bothErrXAccum : Accum ({E.range} : Grade E) Nat :=
  .errs [E.range] (by simp) (by simp)

#guard renderAccumN (ap bothErrFAccum bothErrXAccum) =
  "errs [Examples.Validation.E.parse, Examples.Validation.E.range]"

-- ---------------------------------------------------------------------
-- `toGraded_grade`: the one-sided version (`ap_flip`'s own condition),
-- instantiated where `x` is `ok` so the hypothesis holds trivially.

example (f : Accum ({E.parse} : Grade E) (Nat → Nat)) (a : Nat) :
    toGraded (ap f (Accum.ok a : Accum ({E.range} : Grade E) Nat)) =
      Graded.ap (toGraded f) (toGraded (Accum.ok a)) :=
  toGraded_grade f (Accum.ok a) (Or.inr ⟨a, rfl⟩)

-- `toGraded_grade'`: the unconditional strengthening, instantiated at the
-- both-errors witness above — `toGraded` of the accumulated pair keeps
-- the *function's* error, matching `Graded.ap`'s own short-circuit
-- priority (`ap_err_left`).
example :
    toGraded (ap bothErrFAccum bothErrXAccum) =
      Graded.ap (toGraded bothErrFAccum) (toGraded bothErrXAccum) :=
  toGraded_grade' bothErrFAccum bothErrXAccum

-- `Accum` is not a monad: instantiated at `E.parse`/`E.range`.
example : ¬ ∃ (bind : ∀ {g' h' : Grade E} {α β : Type},
      Accum g' α → (α → Accum h' β) → Accum (Grade.join g' h') β),
    ∀ {g' h' : Grade E} {α β : Type} (f : Accum g' (α → β)) (x : Accum h' α),
      cast (congrArg (Grade.join g') (Grade.join_bot h'))
          (bind f (fun f' => bind x (fun a => Accum.pure (f' a)))) = ap f x :=
  notMonad E.parse E.range

-- ---------------------------------------------------------------------
-- The transport lemmas and the list-equality lemma. Same fixture rule as
-- `Tests/Monad.lean`: a nontrivial grade equality, not `g = g`.

private theorem hUA :
    Grade.join ({E.parse} : Grade E) {E.range} = ({E.parse, E.range} : Grade E) := by decide

example (a : Nat) :
    Accum.cast hUA (Accum.ok a : Accum (Grade.join ({E.parse} : Grade E) {E.range}) Nat)
      = Accum.ok a :=
  Accum.cast_ok hUA a

example (hne : [E.parse] ≠ [])
    (hmem : ∀ x ∈ [E.parse], x ∈ Grade.join ({E.parse} : Grade E) {E.range}) :
    Accum.cast hUA
        (Accum.errs [E.parse] hne hmem : Accum (Grade.join ({E.parse} : Grade E) {E.range}) Nat)
      = Accum.errs [E.parse] hne (hUA ▸ hmem) :=
  Accum.cast_errs hUA [E.parse] hne hmem

-- Two error lists that are equal as lists, carrying *different* proofs:
-- the theorem says the proofs cannot make the values differ.
example (hne hne' : [E.parse, E.range] ≠ [])
    (hmem hmem' : ∀ e ∈ [E.parse, E.range], e ∈ ({E.parse, E.range} : Grade E)) :
    (Accum.errs [E.parse, E.range] hne hmem : Accum ({E.parse, E.range} : Grade E) Nat)
      = Accum.errs [E.parse, E.range] hne' hmem' :=
  Accum.errs_eq_of_list_eq rfl

end Tests
