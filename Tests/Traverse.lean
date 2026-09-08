import Graded.Traverse
import Examples.Validation

/-! Examples instantiating every `Graded.Traverse` theorem at a concrete
    error type, plus a `decide` that `foldGrade` computes and a `#guard`
    that `traverse` computes via `renderNats`. -/

namespace Tests

open Graded Examples.Validation

-- `foldGrade` computes: folding `{E.parse}` over a three-element list
-- collapses back to `{E.parse}` — the concrete instance of
-- `foldGrade_cons_ne_nil` that this codebase's `decide`-computes
-- convention (`docs/RULES.md#tests`) asks for.
example : foldGrade ({E.parse} : Grade E) [1, 2, 3] = ({E.parse} : Grade E) := by decide

example (xs : List Nat) : foldGrade ({E.parse} : Grade E) xs ⊆ ({E.parse} : Grade E) :=
  foldGrade_le xs

example (h : ([1, 2, 3] : List Nat) ≠ []) :
    foldGrade ({E.parse} : Grade E) [1, 2, 3] = ({E.parse} : Grade E) :=
  foldGrade_cons_ne_nil [1, 2, 3] h

example : traverse parseNat ([] : List String) = fromEmpty [] :=
  traverse_nil parseNat

example (s : String) (ss : List String) :
    traverse parseNat (s :: ss) =
      cast (Grade.join_idem _) (map2 (· :: ·) (parseNat s) (traverse parseNat ss)) :=
  traverse_cons parseNat s ss

example (ss : List Nat) :
    traverse parseNat (ss.map toString) = traverse (parseNat ∘ toString) ss :=
  traverse_map parseNat toString ss

example (ss : List String) :
    traverse (fromEmpty : String → Graded ({E.parse} : Grade E) String) ss = fromEmpty ss :=
  traverse_fromEmpty ss

example (l : List Nat) (h : traverse parseNat ["1", "2", "3"] = Graded.ok l) :
    l.length = 3 :=
  traverse_length parseNat ["1", "2", "3"] l h

-- `traverse` computes.
#guard renderNats (traverse parseNat ["1", "2", "3"]) = "ok [1, 2, 3]"
#guard renderNats (traverse parseNat ["1", "2", "x"]) = "err Examples.Validation.E.parse"

end Tests
