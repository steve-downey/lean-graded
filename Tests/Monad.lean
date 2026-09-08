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

end Tests
