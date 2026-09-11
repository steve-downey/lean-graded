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

-- ---------------------------------------------------------------------
-- The three `traverse_cons_*` case lemmas, each instantiated with the
-- hypothesis it needs actually discharged rather than assumed: `f` is a
-- concrete check, so the `f x = ok b` / `f x = err e he` premises are
-- supplied by `rfl`-level facts about it and not by a free variable.

/-- Succeeds on everything: the all-ok fixture. -/
private def okCheck (n : Nat) : Graded ({E.parse} : Grade E) Nat := Graded.ok (n + 1)

/-- Fails on everything, with the one kind its grade admits. -/
private def badCheck (_ : Nat) : Graded ({E.parse} : Grade E) Nat :=
  Graded.err E.parse (by decide)

/-- Succeeds on the head and fails further down: the fixture
    `traverse_cons_ok_err` actually needs, where one `f` does both. -/
private def mixedCheck (n : Nat) : Graded ({E.parse} : Grade E) Nat :=
  if n = 0 then Graded.err E.parse (by decide) else Graded.ok (n + 1)

example (hxs : traverse okCheck [2, 3] = Graded.ok [3, 4]) :
    traverse okCheck (1 :: [2, 3]) = Graded.ok (2 :: [3, 4]) :=
  traverse_cons_ok_ok okCheck 1 [2, 3] 2 [3, 4] rfl hxs

example : ∃ he', traverse badCheck (1 :: [2, 3]) = Graded.err E.parse he' :=
  traverse_cons_err_left badCheck 1 [2, 3] E.parse (by decide) rfl

-- Head succeeds, tail fails: the `0` is in the tail, so this is not
-- `traverse_cons_err_left` with the arguments relabelled.
example (he : E.parse ∈ ({E.parse} : Grade E))
    (hxs : traverse mixedCheck [0, 3] = Graded.err E.parse he) :
    ∃ he', traverse mixedCheck (1 :: [0, 3]) = Graded.err E.parse he' :=
  traverse_cons_ok_err mixedCheck 1 [0, 3] 2 E.parse he rfl hxs

-- And the fixtures compute the way the lemmas say they do.
#guard renderNats (traverse okCheck [1, 2, 3]) = "ok [2, 3, 4]"
#guard renderNats (traverse mixedCheck [1, 0, 3]) = "err Examples.Validation.E.parse"

end Tests
