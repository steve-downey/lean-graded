import Graded.AccumTraverse
import Examples.Validation

/-! Examples instantiating every theorem of `Graded.AccumTraverse` at the
    concrete error type `E`, with the accumulating traversal exercised at
    **zero, one, and several** failures, the several-failure case using
    two distinguishable kinds so the source-order claim in
    `errsOf_traverseK` is actually witnessed rather than merely stated.

    The nominated grade `k` is a *strict* superset of the check's own
    grade, so `hg` is a real inclusion rather than `Grade.le_refl'` — a
    reflexive witness would let a broken `traverseK` pass. -/

namespace Tests.AccumTraverse

open Graded Graded.Accum Examples.Validation

/-- The check's own grade: parse and range. -/
abbrev GK : Grade E := {E.parse, E.range}

/-- The nominated grade: strictly larger, so `hgk` below is not
    reflexivity. -/
abbrev KK : Grade E := {E.parse, E.range, E.io}

theorem hgk : GK ⊆ KK := by decide

/-- A check with two distinguishable failures: `0` is a parse failure,
    anything over 100 is a range failure, everything else succeeds. -/
def checkAccum (n : Nat) : Accum GK Nat :=
  if n = 0 then .errs [E.parse] (by simp) (by intro e he; simp at he; simp [he])
  else if 100 < n then .errs [E.range] (by simp) (by intro e he; simp at he; simp [he])
  else .ok n

/-- The short-circuiting counterpart, for the commutation examples. -/
def checkGraded (n : Nat) : Graded GK Nat := toGraded (checkAccum n)

/-- Short names for the three kinds. `repr` spells them fully qualified,
    which makes the expected strings below unreadable. -/
def showE : E → String
  | .parse => "parse"
  | .range => "range"
  | .io    => "io"

/-- Render an accumulating traversal result, for `#guard`. -/
def renderT : Accum KK (List Nat) → String
  | .ok ns => s!"ok {ns}"
  | .errs es _ _ => s!"errs [{String.intercalate ", " (es.map showE)}]"

-- ---------------------------------------------------------------------
-- Zero, one, and several failures. The several-failure cases are the
-- point: both kinds appear, and they appear in source order.

#guard renderT (traverseK hgk checkAccum [1, 2, 3]) = "ok [1, 2, 3]"
#guard renderT (traverseK hgk checkAccum [1, 0, 3]) = "errs [parse]"
#guard renderT (traverseK hgk checkAccum [1, 200, 3]) = "errs [range]"
#guard renderT (traverseK hgk checkAccum [0, 5, 200]) = "errs [parse, range]"

-- Order is observable, and it is source order, not kind order: swapping
-- the two failing positions swaps the two errors.
#guard renderT (traverseK hgk checkAccum [200, 5, 0]) = "errs [range, parse]"

-- Three failures, so "every failing position contributes" is witnessed
-- beyond a pair.
#guard renderT (traverseK hgk checkAccum [0, 200, 0]) = "errs [parse, range, parse]"

#guard renderT (traverseK hgk checkAccum []) = "ok []"

-- ---------------------------------------------------------------------
-- `errsOf_traverseK`: the concatenation law, instantiated and computed.

example (xs : List Nat) :
    errsOf (traverseK hgk checkAccum xs) = xs.flatMap (fun x => errsOf (checkAccum x)) :=
  errsOf_traverseK hgk checkAccum xs

#guard errsOf (traverseK hgk checkAccum [0, 5, 200]) = [E.parse, E.range]
example : errsOf (traverseK hgk checkAccum [0, 5, 200])
    = ([0, 5, 200] : List Nat).flatMap (fun x => errsOf (checkAccum x)) := by decide

-- `traverseK_ok`: success is `List.map`, instantiated at the always-ok
-- check `fun n => .ok (n + 1)`.
example (xs : List Nat) :
    traverseK hgk (fun n => (Accum.ok (n + 1) : Accum GK Nat)) xs
      = Accum.ok (xs.map (fun n => n + 1)) :=
  traverseK_ok hgk _ (fun n => n + 1) (fun _ => rfl) xs

#guard renderT (traverseK hgk (fun n => (Accum.ok (n + 1) : Accum GK Nat)) [1, 2, 3])
  = "ok [2, 3, 4]"

-- ---------------------------------------------------------------------
-- The reduction lemmas and the union-graded bridge.

example (f : Nat → Nat) (a : Nat) :
    apK hgk hgk (Accum.ok f : Accum GK (Nat → Nat)) (Accum.ok a : Accum GK Nat)
      = Accum.ok (f a) :=
  apK_ok_ok hgk hgk f a

example (f : Accum GK (Nat → Nat)) (x : Accum GK Nat) :
    ap f x = apK (Grade.le_join_left GK GK) (Grade.le_join_right GK GK) f x :=
  ap_eq_apK f x

example (f : Nat → Nat) (x : Accum GK Nat) : errsOf (map f x) = errsOf x :=
  errsOf_map f x

example (f : Accum GK (Nat → Nat)) (x : Accum GK Nat) :
    errsOf (apK hgk hgk f x) = errsOf f ++ errsOf x :=
  errsOf_apK hgk hgk f x

-- ---------------------------------------------------------------------
-- The payoff: taking the first error commutes with traversal. Checked at
-- a list where *both* kinds fail, so the theorem is not vacuously about
-- a single error.

example (xs : List Nat) :
    toGraded (traverseK hgk checkAccum xs)
      = Graded.traverseK hgk (fun n => toGraded (checkAccum n)) xs :=
  toGraded_traverseK hgk checkAccum xs

/-- Render a short-circuiting result, to see which error survived. -/
def renderG : Graded KK (List Nat) → String
  | .ok ns => s!"ok {ns}"
  | .err e _ => s!"err {showE e}"

-- The accumulating traversal collected both; the projection keeps the
-- first, which is the source-order-first failure, not the smaller kind.
#guard renderG (toGraded (traverseK hgk checkAccum [0, 5, 200])) = "err parse"
#guard renderG (toGraded (traverseK hgk checkAccum [200, 5, 0])) = "err range"
#guard renderG (Graded.traverseK hgk checkGraded [200, 5, 0]) = "err range"

example : toGraded (traverseK hgk checkAccum [0, 5, 200])
    = Graded.traverseK hgk checkGraded [0, 5, 200] :=
  toGraded_traverseK hgk checkAccum [0, 5, 200]

example (a : Nat) : toGraded (pureK a : Accum KK Nat) = Graded.pureK a :=
  toGraded_pureK a

example (f : Nat → Nat) (x : Accum GK Nat) :
    toGraded (map f x) = Graded.map f (toGraded x) :=
  toGraded_map f x

example (f : Accum GK (Nat → Nat)) (x : Accum GK Nat) :
    toGraded (apK hgk hgk f x) = Graded.apK hgk hgk (toGraded f) (toGraded x) :=
  toGraded_apK hgk hgk f x

example (f : Nat → Nat → Nat) (x : Accum GK Nat) (y : Accum GK Nat) :
    toGraded (map2K hgk hgk f x y) = Graded.map2K hgk hgk f (toGraded x) (toGraded y) :=
  toGraded_map2K hgk hgk f x y

end Tests.AccumTraverse
