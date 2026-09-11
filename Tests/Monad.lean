import Graded.Monad
import Examples.Validation

/-! Examples instantiating every `Graded.Monad` theorem at a concrete error
    type, plus a `#guard` that computes via `decide`. `bind_assoc` is
    instantiated at three *distinct* concrete grades (`{parse}`, `{range}`,
    `{io}`) so the `cast` it produces is genuinely a transport, not
    `cast rfl`. -/

namespace Tests

open Graded Examples.Validation

example (a : Nat) (f : Nat → Graded ({E.range} : Grade E) Nat) :
    cast (Grade.bot_join _) (bind (pure a) f) = f a :=
  bind_pure_left a f

example (x : Graded ({E.parse} : Grade E) Nat) :
    cast (Grade.join_bot _) (bind x (pure : Nat → Graded (Grade.bot : Grade E) Nat)) = x :=
  bind_pure_right x

example :
    cast (Grade.join_assoc ({E.parse} : Grade E) {E.range} {E.io})
        (bind (bind (parseNat "5") checkRange) logIt) =
      bind (parseNat "5") (fun a => bind (checkRange a) logIt) :=
  bind_assoc (parseNat "5") checkRange logIt

example (f : Nat → Nat) (x : Graded ({E.parse} : Grade E) Nat) :
    cast (Grade.join_bot _) (bind x (pure ∘ f)) = map f x :=
  bind_map f x

example (h₁ : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) (f : Nat → Graded ({E.io} : Grade E) Nat) :
    bind (widen h₁ x) f = widen (Grade.join_mono h₁ (Grade.le_refl' _)) (bind x f) :=
  bind_widen h₁ x f

-- `bind` computes: the two-stage validation built from `parseNat` and
-- `checkRange` via `bind` reduces to the expected value.
#guard render (bind (parseNat "42") checkRange) = "ok 42"

-- ---------------------------------------------------------------------
-- The three transport lemmas, at a **nontrivial** grade equality: the
-- computed union `{parse} ∪ {range}` against the literal `{parse, range}`.
-- `cast rfl` would satisfy all three of these for a broken `cast`, so the
-- fixture matters more than the statement.

private theorem hU :
    Grade.join ({E.parse} : Grade E) {E.range} = ({E.parse, E.range} : Grade E) := by decide

example (a : Nat) :
    Graded.cast hU (Graded.ok a : Graded (Grade.join ({E.parse} : Grade E) {E.range}) Nat)
      = Graded.ok a :=
  cast_ok hU a

example (he : E.parse ∈ Grade.join ({E.parse} : Grade E) {E.range}) :
    Graded.cast hU (Graded.err E.parse he
        : Graded (Grade.join ({E.parse} : Grade E) {E.range}) Nat)
      = Graded.err E.parse (hU ▸ he) :=
  cast_err hU E.parse he

example (h₁ : ({E.parse} : Grade E) ⊆ Grade.join ({E.parse} : Grade E) {E.range})
    (x : Graded ({E.parse} : Grade E) Nat) :
    Graded.cast hU (widen h₁ x) = widen (hU ▸ h₁) x :=
  cast_widen h₁ hU x

end Tests
