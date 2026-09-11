import Graded.AccumKinds
import Tests.AccumTraverse

/-! Examples instantiating every theorem of `Graded.AccumKinds` at the
    concrete error type `E`, reusing [accum-traverse]'s fixture so the
    same list of checks is run through both carriers: the source-ordered
    list and the per-kind set. The `#guard`s put the two side by side
    where they differ — a swapped pair of failures changes the list and
    not the set, a repeated kind lengthens the list and not the set — and
    `Kinds.noFirstError` is instantiated at the two kinds that make that
    difference visible. -/

namespace Tests.AccumKinds

open Graded Graded.Accum Examples.Validation Tests.AccumTraverse

/-- The per-kind check, the projection of the list check. -/
def checkKinds (n : Nat) : Kinds GK Nat := Kinds.ofAccum (checkAccum n)

/-- Render a per-kind result, for `#guard`. Kinds print in a fixed order
    regardless of failure order, which is the point. -/
def renderK : Kinds KK (List Nat) → String
  | .ok ns => s!"ok {ns}"
  | .failed ks _ _ =>
      s!"failed [{String.intercalate ", " (([E.parse, E.range, E.io].filter (· ∈ ks)).map showE)}]"

-- ---------------------------------------------------------------------
-- Zero, one, and several failures, through the per-kind traversal.

#guard renderK (Kinds.traverseK hgk checkKinds [1, 2, 3]) = "ok [1, 2, 3]"
#guard renderK (Kinds.traverseK hgk checkKinds [1, 0, 3]) = "failed [parse]"
#guard renderK (Kinds.traverseK hgk checkKinds [1, 200, 3]) = "failed [range]"
#guard renderK (Kinds.traverseK hgk checkKinds [0, 5, 200]) = "failed [parse, range]"

-- Order is NOT observable here: the list carrier gives "errs [range,
-- parse]" for this input (Tests/AccumTraverse.lean); the set carrier gives
-- the same set as for [0, 5, 200].
#guard renderK (Kinds.traverseK hgk checkKinds [200, 5, 0]) = "failed [parse, range]"

-- A repeated kind is present once: the list carrier gives three entries.
#guard renderK (Kinds.traverseK hgk checkKinds [0, 200, 0]) = "failed [parse, range]"

#guard renderK (Kinds.traverseK hgk checkKinds []) = "ok []"

-- ---------------------------------------------------------------------
-- The observation and its reduction lemmas.

example (a : Nat) : Kinds.kindsOf (Kinds.ok a : Kinds GK Nat) = Grade.bot := Kinds.kindsOf_ok a

example (ks : Grade E) (hne : ks.Nonempty) (hmem : ks ⊆ GK) :
    Kinds.kindsOf (Kinds.failed ks hne hmem : Kinds GK Nat) = ks :=
  Kinds.kindsOf_failed ks hne hmem

example {hne : ({E.parse, E.range} : Grade E).Nonempty}
    {hne' : ({E.range, E.parse} : Grade E).Nonempty}
    {hmem : ({E.parse, E.range} : Grade E) ⊆ KK} {hmem' : ({E.range, E.parse} : Grade E) ⊆ KK} :
    (Kinds.failed {E.parse, E.range} hne hmem : Kinds KK Nat)
      = Kinds.failed {E.range, E.parse} hne' hmem' :=
  Kinds.failed_eq_of_kinds_eq (Finset.pair_comm E.parse E.range)

example (f : Nat → Nat) (x : Kinds GK Nat) :
    Kinds.kindsOf (Kinds.map f x) = Kinds.kindsOf x := Kinds.kindsOf_map f x

example (x : Kinds GK Nat) :
    Kinds.kindsOf (Kinds.widen hgk x) = Kinds.kindsOf x := Kinds.kindsOf_widen hgk x

#guard Kinds.kindsOf (Kinds.widen hgk (checkKinds 0)) = {E.parse}
#guard Kinds.kindsOf (Kinds.widen hgk (checkKinds 5)) = Grade.bot

-- ---------------------------------------------------------------------
-- Application: the evidence is the join. Checked at a both-fail pair of
-- *distinct* kinds, and at a both-fail pair of the *same* kind, where the
-- join is idempotent and the list would have grown.

example (f : Kinds GK (Nat → Nat)) (x : Kinds GK Nat) :
    Kinds.kindsOf (Kinds.apK hgk hgk f x) = Grade.join (Kinds.kindsOf f) (Kinds.kindsOf x) :=
  Kinds.kindsOf_apK hgk hgk f x

example (f : Nat → Nat → Nat) (x y : Kinds GK Nat) :
    Kinds.kindsOf (Kinds.map2K hgk hgk f x y) = Grade.join (Kinds.kindsOf x) (Kinds.kindsOf y) :=
  Kinds.kindsOf_map2K hgk hgk f x y

def failP : Kinds GK (Nat → Nat) := Kinds.map (fun _ => id) (checkKinds 0)
def failR : Kinds GK Nat := checkKinds 200

#guard Kinds.kindsOf (Kinds.apK hgk hgk failP failR) = {E.parse, E.range}
#guard Kinds.kindsOf (Kinds.apK hgk hgk failP (checkKinds 0)) = {E.parse}
#guard Kinds.kindsOf (Kinds.apK hgk hgk (Kinds.ok (· + 1)) (checkKinds 41)) = Grade.bot
#guard renderK (Kinds.map (fun n => [n]) (Kinds.apK hgk hgk (Kinds.ok (· + 1)) (checkKinds 41)))
  = "ok [42]"

-- The four applicative laws, at three distinct nonempty grades for
-- composition.

example (x : Kinds GK Nat) :
    Kinds.apK (Grade.le_refl' KK) hgk (Kinds.pureK (@id Nat) : Kinds KK (Nat → Nat)) x
      = Kinds.widen hgk x :=
  Kinds.apK_pure_id hgk x

example (f : Nat → Nat) (a : Nat) :
    Kinds.apK (Grade.le_refl' KK) (Grade.le_refl' KK) (Kinds.pureK f : Kinds KK (Nat → Nat))
        (Kinds.pureK a)
      = (Kinds.pureK (f a) : Kinds KK Nat) :=
  Kinds.apK_pure_pure f a

example (u : Kinds GK (Nat → Nat)) (a : Nat) :
    Kinds.apK hgk (Grade.le_refl' KK) u (Kinds.pureK a : Kinds KK Nat)
      = Kinds.apK (Grade.le_refl' KK) hgk
          (Kinds.pureK (fun f => f a) : Kinds KK ((Nat → Nat) → Nat)) u :=
  Kinds.apK_interchange hgk u a

theorem hp : ({E.parse} : Grade E) ⊆ KK := by decide
theorem hr : ({E.range} : Grade E) ⊆ KK := by decide
theorem hi : ({E.io} : Grade E) ⊆ KK := by decide

example (u : Kinds ({E.parse} : Grade E) (Nat → Nat))
    (v : Kinds ({E.range} : Grade E) (Nat → Nat)) (w : Kinds ({E.io} : Grade E) Nat) :
    Kinds.apK (Grade.le_refl' KK) hi (Kinds.apK (Grade.le_refl' KK) hr
        (Kinds.apK (Grade.le_refl' KK) hp
          (Kinds.pureK Function.comp : Kinds KK ((Nat → Nat) → (Nat → Nat) → Nat → Nat)) u)
        v) w
      = Kinds.apK hp (Grade.le_refl' KK) u (Kinds.apK hr hi v w) :=
  Kinds.apK_comp hp hr hi u v w

-- ---------------------------------------------------------------------
-- Traversal: the fold form, the membership form, and success.

example (f : Nat → Kinds GK Nat) : Kinds.traverseK hgk f [] = Kinds.pureK [] :=
  Kinds.traverseK_nil hgk f

example (f : Nat → Kinds GK Nat) (x : Nat) (xs : List Nat) :
    Kinds.traverseK hgk f (x :: xs)
      = Kinds.map2K hgk (Grade.le_refl' KK) (fun b bs => b :: bs) (f x)
          (Kinds.traverseK hgk f xs) :=
  Kinds.traverseK_cons hgk f x xs

example (xs : List Nat) :
    Kinds.kindsOf (Kinds.traverseK hgk checkKinds xs)
      = xs.foldr (fun x acc => Grade.join (Kinds.kindsOf (checkKinds x)) acc) Grade.bot :=
  Kinds.kindsOf_traverseK hgk checkKinds xs

example (xs : List Nat) (e : E) :
    e ∈ Kinds.kindsOf (Kinds.traverseK hgk checkKinds xs)
      ↔ ∃ x ∈ xs, e ∈ Kinds.kindsOf (checkKinds x) :=
  Kinds.mem_kindsOf_traverseK hgk checkKinds xs e

-- Every failing kind is present, nothing else is: parse and range at
-- positions 0 and 200, and io never.
#guard Kinds.kindsOf (Kinds.traverseK hgk checkKinds [0, 5, 200]) = {E.parse, E.range}
#guard decide (E.io ∉ Kinds.kindsOf (Kinds.traverseK hgk checkKinds [0, 5, 200]))

example (xs : List Nat) :
    Kinds.traverseK hgk (fun n => (Kinds.ok (n + 1) : Kinds GK Nat)) xs
      = Kinds.ok (xs.map (fun n => n + 1)) :=
  Kinds.traverseK_ok hgk _ (fun n => n + 1) (fun _ => rfl) xs

-- ---------------------------------------------------------------------
-- The projection from the list carrier.

example (a : Nat) : Kinds.ofAccum (Accum.ok a : Accum GK Nat) = Kinds.ok a := Kinds.ofAccum_ok a

example (es : List E) (hne : es ≠ []) (hmem : ∀ e ∈ es, e ∈ GK) :
    Kinds.ofAccum (Accum.errs es hne hmem : Accum GK Nat)
      = Kinds.failed es.toFinset ⟨es.head hne, List.mem_toFinset.mpr (List.head_mem hne)⟩
          (fun e he => hmem e (List.mem_toFinset.mp he)) :=
  Kinds.ofAccum_errs es hne hmem

example (x : Accum GK Nat) : Kinds.kindsOf (Kinds.ofAccum x) = (errsOf x).toFinset :=
  Kinds.kindsOf_ofAccum x

example (f : Nat → Nat) (x : Accum GK Nat) :
    Kinds.ofAccum (Accum.map f x) = Kinds.map f (Kinds.ofAccum x) := Kinds.ofAccum_map f x

example (x : Accum GK Nat) :
    Kinds.ofAccum (Accum.widen hgk x) = Kinds.widen hgk (Kinds.ofAccum x) :=
  Kinds.ofAccum_widen hgk x

example (a : Nat) : Kinds.ofAccum (Accum.pureK a : Accum KK Nat) = Kinds.pureK a :=
  Kinds.ofAccum_pureK a

example (f : Accum GK (Nat → Nat)) (x : Accum GK Nat) :
    Kinds.ofAccum (Accum.apK hgk hgk f x)
      = Kinds.apK hgk hgk (Kinds.ofAccum f) (Kinds.ofAccum x) :=
  Kinds.ofAccum_apK hgk hgk f x

example (f : Nat → Nat → Nat) (x y : Accum GK Nat) :
    Kinds.ofAccum (Accum.map2K hgk hgk f x y)
      = Kinds.map2K hgk hgk f (Kinds.ofAccum x) (Kinds.ofAccum y) :=
  Kinds.ofAccum_map2K hgk hgk f x y

example (xs : List Nat) :
    Kinds.ofAccum (Accum.traverseK hgk checkAccum xs) = Kinds.traverseK hgk checkKinds xs :=
  Kinds.ofAccum_traverseK hgk checkAccum xs

-- Forgetting the order after, or from the start: the same set, computed.
#guard Kinds.kindsOf (Kinds.ofAccum (Accum.traverseK hgk checkAccum [200, 5, 0]))
  = Kinds.kindsOf (Kinds.traverseK hgk checkKinds [200, 5, 0])
-- ...and the list they came from was ordered the other way.
#guard errsOf (Accum.traverseK hgk checkAccum [200, 5, 0]) = [E.range, E.parse]

-- ---------------------------------------------------------------------
-- What the short-circuiting projection says about the set, and the one
-- thing it cannot say.

example (x : Accum GK Nat) (e : E) (he : e ∈ GK) (hx : toGraded x = Graded.err e he) :
    e ∈ Kinds.kindsOf (Kinds.ofAccum x) :=
  Kinds.toGraded_mem x e he hx

-- The short-circuit error of [200, 5, 0] is range; range is in the set.
#guard renderG (toGraded (Accum.traverseK hgk checkAccum [200, 5, 0])) = "err range"
#guard decide (E.range ∈ Kinds.kindsOf (Kinds.ofAccum (Accum.traverseK hgk checkAccum [200, 5, 0])))

example (x : Accum GK Nat) (e : E) (hk : Kinds.kindsOf (Kinds.ofAccum x) = {e}) :
    ∃ he : e ∈ GK, toGraded x = Graded.err e he :=
  Kinds.toGraded_of_kindsOf_singleton x e hk

-- One failing position: the set is a singleton and the two carriers agree.
#guard Kinds.kindsOf (Kinds.ofAccum (Accum.traverseK hgk checkAccum [1, 200, 3])) = {E.range}
#guard renderG (toGraded (Accum.traverseK hgk checkAccum [1, 200, 3])) = "err range"

-- No `first_error`: instantiated at the two kinds the swapped-order
-- `#guard`s above already showed collapsing to one set.
example : ¬ ∃ proj : ∀ {g : Grade E} {α : Type}, Kinds g α → Graded g α,
    ∀ {g : Grade E} {α : Type} (x : Accum g α), proj (Kinds.ofAccum x) = toGraded x :=
  Kinds.noFirstError E.parse E.range (by decide)

end Tests.AccumKinds
