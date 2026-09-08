import Graded.Compose
import Examples.Validation

/-! Examples instantiating every `Graded.Compose` theorem at a concrete
    error type, plus `#guard`s that `flatten` computes on each shape
    (`ok (ok _)`, `ok (err _ _)`, `err _ _`), so the definitions are known
    to reduce and not just typecheck. -/

namespace Tests

open Graded Examples.Validation

/-- Render a `Graded g Nat` result for `#guard`, at any grade. -/
def renderCompose {g : Grade E} : Graded g Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

example (x : Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat)) :
    flatten x =
      bind x (fun y => y :
        Graded ({E.range} : Grade E) Nat → Graded ({E.range} : Grade E) Nat) :=
  flatten_eq_bind_id x

example (x : Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat)) :
    flatten ((map (map (· + 1)) x :
        Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat))) =
      map (· + 1) (flatten x) :=
  flatten_map (· + 1) x

example (y : Graded ({E.range} : Grade E) Nat) :
    cast (Grade.bot_join _) (flatten (Graded.pure y)) = y :=
  flatten_pure_outer y

example (x : Graded ({E.parse} : Grade E) Nat) :
    cast (Grade.join_bot _) (flatten (map Graded.pure x)) = x :=
  flatten_pure_inner x

example (x : Graded ({E.parse} : Grade E)
    (Graded ({E.range} : Grade E) (Graded ({E.io} : Grade E) Nat))) :
    cast (Grade.join_assoc _ _ _) (flatten (flatten x)) = flatten (map flatten x) :=
  flatten_flatten x

example (h₁ : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.parse} : Grade E) (Graded ({E.io} : Grade E) Nat)) :
    flatten (widen h₁ x) = widen (Grade.join_mono h₁ (Grade.le_refl' _)) (flatten x) :=
  flatten_widen_outer h₁ x

example (h₂ : ({E.range} : Grade E) ⊆ ({E.range, E.io} : Grade E))
    (x : Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat)) :
    flatten ((map (widen h₂) x :
        Graded ({E.parse} : Grade E) (Graded ({E.range, E.io} : Grade E) Nat))) =
      widen (Grade.join_mono (Grade.le_refl' _) h₂) (flatten x) :=
  flatten_widen_inner h₂ x

-- `flatten_comm` needs *no* hypothesis: unlike `ap`/`apFlipped` (two
-- independent values, either of which can independently be an error),
-- `Graded g (Graded h α)` is a single nested value that holds at most
-- one error already, by construction.
example (x : Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat)) :
    flatten x = cast (Grade.join_comm _ _) (flatten (swap x)) :=
  flatten_comm x

-- `flatten` computes: all three shapes.
#guard renderCompose (flatten (Graded.ok (Graded.ok 7) :
    Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat))) = "ok 7"

#guard renderCompose (flatten (Graded.ok
    (Graded.err E.range (Finset.mem_singleton_self E.range)) :
    Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat))) =
  "err Examples.Validation.E.range"

#guard renderCompose (flatten
    (Graded.err E.parse (Finset.mem_singleton_self E.parse) :
      Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat))) =
  "err Examples.Validation.E.parse"

end Tests
