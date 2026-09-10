import Graded.Sufficient
import Examples.Validation

/-! Examples instantiating every `Graded.Sufficient` theorem at a concrete
    error type, plus a `#guard` that computes via `decide`, and one example
    at a `k` strictly larger than the join — the case `bindK` exists for
    and `bind` cannot express, since `bind`'s result grade is always
    exactly the union. -/

namespace Tests

open Graded Examples.Validation

example (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) (a : Nat)
    (f : Nat → Graded ({E.range} : Grade E) Nat) :
    bindK (Grade.bot_le ({E.parse, E.range} : Grade E)) hh (Graded.pure a) f = widen hh (f a) :=
  bindK_pure_left hh a f

example (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) :
    bindK hg (Grade.bot_le _) x (Graded.pure : Nat → Graded (Grade.bot : Grade E) Nat) =
      widen hg x :=
  bindK_pure_right hg x

example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (hj : ({E.io} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) (f : Nat → Graded ({E.range} : Grade E) Nat)
    (kk : Nat → Graded ({E.io} : Grade E) Nat) :
    bindK (Grade.le_refl' _) hj (bindK hg hh x f) kk =
      bindK hg (Grade.le_refl' _) x (fun a => bindK hh hj (f a) kk) :=
  bindK_assoc hg hh hj x f kk

example
    (h₁ : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hg' : ({E.parse, E.range} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) (f : Nat → Graded ({E.range} : Grade E) Nat) :
    bindK hg' hh (widen h₁ x) f = bindK (Grade.le_trans' h₁ hg') hh x f :=
  bindK_widen h₁ hg' hh x f

example
    (hg hg' : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh hh' : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) (f : Nat → Graded ({E.range} : Grade E) Nat) :
    bindK hg hh x f = bindK hg' hh' x f :=
  bindK_irrel hg hg' hh hh' x f

example (x : Graded ({E.parse} : Grade E) Nat) (f : Nat → Graded ({E.range} : Grade E) Nat) :
    bind x f = bindK (Grade.le_join_left _ _) (Grade.le_join_right _ _) x f :=
  bind_eq_bindK x f

-- `bindK`'s own reduction lemmas, which `bindK_assoc`/`bindK_widen` above
-- lean on.
example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) (a : Nat)
    (f : Nat → Graded ({E.range} : Grade E) Nat) :
    bindK hg hh (Graded.ok a) f = widen hh (f a) :=
  bindK_ok hg hh a f

example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (f : Nat → Graded ({E.range} : Grade E) Nat) :
    bindK hg hh (Graded.err E.parse (by decide)) f = Graded.err E.parse (by decide) :=
  bindK_err hg hh E.parse (by decide) f

-- `widen`'s own reduction lemmas.
example (h : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) (a : Nat) :
    (widen h (Graded.ok a) : Graded ({E.parse, E.range} : Grade E) Nat) = Graded.ok a :=
  widen_ok h a

example (h : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) :
    widen h (Graded.err E.parse (by decide) : Graded ({E.parse} : Grade E) Nat) =
      Graded.err E.parse (by decide) :=
  widen_err h E.parse (by decide)

-- `pureK`, reusing `fromEmpty`: renders exactly like `Graded.pure` widened
-- to the same grade.
def renderPureK : Graded ({E.parse} : Grade E) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#guard renderPureK (pureK (3 : Nat) : Graded ({E.parse} : Grade E) Nat) = "ok 3"

-- The substantive case `bind` cannot express: `bindK` at a `k` strictly
-- larger than `Grade.join {E.parse} {E.range}` — no cast, since there is
-- no equation between two spellings of the union to transport across,
-- only a wider bound supplied once for both sides.
def renderK : Graded ({E.parse, E.range, E.io} : Grade E) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#guard renderK
    (bindK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
      (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide)
      (parseNat "5") checkRange) = "ok 5"

#guard renderK
    (bindK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
      (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide)
      (parseNat "abc") checkRange) = "err Examples.Validation.E.parse"

-- ---------------------------------------------------------------------
-- `apK`/`map2K` and their laws.

example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) (f' : Nat → Nat) (a : Nat) :
    apK hg hh (Graded.ok f' : Graded ({E.parse} : Grade E) (Nat → Nat))
        (Graded.ok a : Graded ({E.range} : Grade E) Nat) = Graded.ok (f' a) :=
  apK_ok_ok hg hh f' a

example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.range} : Grade E) Nat) :
    apK hg hh (Graded.err E.parse (by decide) : Graded ({E.parse} : Grade E) (Nat → Nat)) x =
      Graded.err E.parse (by decide) :=
  apK_err_left hg hh E.parse (by decide) x

example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) (f' : Nat → Nat) :
    apK hg hh (Graded.ok f' : Graded ({E.parse} : Grade E) (Nat → Nat))
        (Graded.err E.range (by decide) : Graded ({E.range} : Grade E) Nat) =
      Graded.err E.range (by decide) :=
  apK_ok_err hg hh f' E.range (by decide)

example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) (f' : Nat → Nat) (a : Nat) :
    apFlippedK hg hh (Graded.ok f' : Graded ({E.parse} : Grade E) (Nat → Nat))
        (Graded.ok a : Graded ({E.range} : Grade E) Nat) = Graded.ok (f' a) :=
  apFlippedK_ok_ok hg hh f' a

example
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.range} : Grade E) Nat) :
    apK (Grade.le_refl' ({E.parse, E.range} : Grade E)) hh
        (pureK (@id Nat) : Graded ({E.parse, E.range} : Grade E) (Nat → Nat)) x = widen hh x :=
  apK_pure_id hh x

example (f' : Nat → Nat) (a : Nat) :
    apK (Grade.le_refl' ({E.parse} : Grade E)) (Grade.le_refl' ({E.parse} : Grade E))
        (pureK f' : Graded ({E.parse} : Grade E) (Nat → Nat))
        (pureK a : Graded ({E.parse} : Grade E) Nat) =
      (pureK (f' a) : Graded ({E.parse} : Grade E) Nat) :=
  apK_pure_pure f' a

-- `apK_interchange`: no `Grade.join_bot`/`Grade.bot_join` needed, unlike
-- `ap_interchange`.
example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (u : Graded ({E.parse} : Grade E) (Nat → Nat)) (a : Nat) :
    apK hg (Grade.le_refl' ({E.parse, E.range} : Grade E)) u
        (pureK a : Graded ({E.parse, E.range} : Grade E) Nat) =
      apK (Grade.le_refl' ({E.parse, E.range} : Grade E)) hg
        (pureK (fun f => f a) : Graded ({E.parse, E.range} : Grade E) ((Nat → Nat) → Nat)) u :=
  apK_interchange hg u a

-- `apK_flip`: the finding this step exists to make — no `Grade.join_comm`
-- anywhere, at a common sufficient grade.
example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (f' : Nat → Nat) (x : Graded ({E.range} : Grade E) Nat) :
    apK hg hh (Graded.ok f' : Graded ({E.parse} : Grade E) (Nat → Nat)) x =
      apFlippedK hg hh (Graded.ok f') x :=
  apK_flip hg hh (Graded.ok f') x (Or.inl ⟨f', rfl⟩)

-- `ap_eq_apK`: instantiating `apK` at the exact union recovers `ap`.
example (f : Graded ({E.parse} : Grade E) (Nat → Nat)) (x : Graded ({E.range} : Grade E) Nat) :
    ap f x = apK (Grade.le_join_left _ _) (Grade.le_join_right _ _) f x :=
  ap_eq_apK f x

-- The substantive case `ap` cannot express: `apK` at a `k` strictly
-- larger than `Grade.join {E.parse} {E.range}` — no cast, same shape as
-- `renderK` above for `bindK`.
#guard renderK
    (apK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
      (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide)
      (Graded.ok (· + 1) : Graded ({E.parse} : Grade E) (Nat → Nat))
      (Graded.ok 5 : Graded ({E.range} : Grade E) Nat)) = "ok 6"

#guard renderK
    (apK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
      (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide)
      (Graded.ok (· + 1) : Graded ({E.parse} : Grade E) (Nat → Nat))
      (Graded.err E.range (by decide) : Graded ({E.range} : Grade E) Nat)) =
    "err Examples.Validation.E.range"

-- ---------------------------------------------------------------------
-- `traverseK`: the [obligation-layering] probe — computes at a `k`
-- strictly larger than the element grade `g`, with no cast (contrast
-- `traverse_cons`'s cast along `Grade.join_idem`).

def renderListK : Graded ({E.parse, E.range, E.io} : Grade E) (List Nat) → String
  | .ok l => s!"ok {l}"
  | .err e _ => s!"err {repr e}"

#guard renderListK
    (traverseK (g := ({E.parse} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (fun n => (Graded.ok (n + 1) : Graded ({E.parse} : Grade E) Nat))
      [1, 2, 3]) = "ok [2, 3, 4]"

#guard renderListK
    (traverseK (g := ({E.parse} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
      (by decide)
      (fun n => if n = 2 then (Graded.err E.parse (by decide) : Graded ({E.parse} : Grade E) Nat)
        else Graded.ok (n + 1))
      [1, 2, 3]) = "err Examples.Validation.E.parse"

-- `traverseK_irrel`: which proof of `g ⊆ k` justifies `traverseK`
-- doesn't matter, the mirror of `bindK_irrel` above.
example
    (hg hg' : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (f : Nat → Graded ({E.parse} : Grade E) Nat) (xs : List Nat) :
    traverseK hg f xs = traverseK hg' f xs :=
  traverseK_irrel hg hg' f xs

-- `traverseK_map`: reindexing before `traverseK` agrees with `traverseK`ing
-- the reindexed function — no cast to cancel, unlike `traverse_map`.
example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (f : Nat → Graded ({E.parse} : Grade E) Nat) (h : Nat → Nat) (xs : List Nat) :
    traverseK hg f (xs.map h) = traverseK hg (f ∘ h) xs :=
  traverseK_map hg f h xs

#guard renderListK
    (traverseK (g := ({E.parse} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (fun n => (Graded.ok (n + 1) : Graded ({E.parse} : Grade E) Nat))
      ([1, 2, 3].map (· + 10))) =
  renderListK
    (traverseK (g := ({E.parse} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (fun n => (Graded.ok (n + 11) : Graded ({E.parse} : Grade E) Nat))
      [1, 2, 3])

-- `traverseK_fromEmpty`: the identity law, cast-free — unlike
-- `traverse_fromEmpty`, which delegates to `traverse_cons`'s cast.
example (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E)) (xs : List Nat) :
    traverseK hg (fromEmpty : Nat → Graded ({E.parse} : Grade E) Nat) xs = fromEmpty xs :=
  traverseK_fromEmpty hg xs

#guard renderListK
    (traverseK (g := ({E.parse} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (fromEmpty : Nat → Graded ({E.parse} : Grade E) Nat) [1, 2, 3]) =
  renderListK (fromEmpty [1, 2, 3] : Graded ({E.parse, E.range, E.io} : Grade E) (List Nat))

-- `traverseK_length`: shape preservation, at a `k` strictly larger than
-- the element grade.
example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (f : Nat → Graded ({E.parse} : Grade E) Nat) (xs : List Nat) (l : List Nat)
    (h : traverseK hg f xs = Graded.ok l) :
    l.length = xs.length :=
  traverseK_length hg f xs l h

#guard
  (match (traverseK (g := ({E.parse} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (fun n => (Graded.ok (n + 1) : Graded ({E.parse} : Grade E) Nat))
      [1, 2, 3]) with
    | .ok l => l.length
    | .err _ _ => 0) = 3

-- `traverse_eq_traverseK`: the bridge — instantiating `traverseK` at the
-- tightest sufficient grade `g` itself recovers `traverse`.
example (f : Nat → Graded ({E.parse} : Grade E) Nat) (xs : List Nat) :
    traverse f xs = traverseK (Grade.le_refl' ({E.parse} : Grade E)) f xs :=
  traverse_eq_traverseK f xs

#guard renderNats (traverse parseNat ["1", "2", "3"]) =
  renderNats (traverseK (Grade.le_refl' ({E.parse} : Grade E)) parseNat ["1", "2", "3"])
#guard renderNats (traverse parseNat ["1", "2", "x"]) =
  renderNats (traverseK (Grade.le_refl' ({E.parse} : Grade E)) parseNat ["1", "2", "x"])
#guard renderNats (traverse parseNat ([] : List String)) =
  renderNats (traverseK (Grade.le_refl' ({E.parse} : Grade E)) parseNat ([] : List String))

-- ---------------------------------------------------------------------
-- `flattenK`: the nested carrier at a sufficient grade.

example
    (hg : ({E.io} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (hh : ({E.parse} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (y : Graded ({E.parse} : Grade E) Nat) :
    flattenK hg hh (Graded.ok y : Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat)) =
      widen hh y :=
  flattenK_ok hg hh y

example
    (hg : ({E.io} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (hh : ({E.parse} : Grade E) ⊆ ({E.io, E.parse} : Grade E)) :
    flattenK hg hh
        (Graded.err E.io (by decide) :
          Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat)) =
      Graded.err E.io (by decide) :=
  flattenK_err hg hh E.io (by decide)

-- `flattenK_map`: naturality, cast-free.
example
    (hg : ({E.io} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (hh : ({E.parse} : Grade E) ⊆ ({E.io, E.parse} : Grade E)) (f : Nat → Nat)
    (x : Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat)) :
    flattenK hg hh ((Graded.map (Graded.map f) x :
        Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat))) =
      Graded.map f (flattenK hg hh x) :=
  flattenK_map hg hh f x

-- `flattenK_pure_outer`/`flattenK_pure_inner`: the two unit laws, cast-free.
example (hh : ({E.parse} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (y : Graded ({E.parse} : Grade E) Nat) :
    flattenK (Grade.bot_le ({E.io, E.parse} : Grade E)) hh (Graded.pure y) = widen hh y :=
  flattenK_pure_outer hh y

example (hg : ({E.io} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (x : Graded ({E.io} : Grade E) Nat) :
    flattenK hg (Grade.bot_le ({E.io, E.parse} : Grade E)) (Graded.map Graded.pure x) =
      widen hg x :=
  flattenK_pure_inner hg x

-- `flattenK_flattenK`: associativity, cast-free — both sides already land
-- in `Graded k Nat`, so `Grade.le_refl' k` (reused twice) replaces
-- `Grade.join_assoc`.
example
    (hg : ({E.io} : Grade E) ⊆ ({E.io, E.parse, E.range} : Grade E))
    (hh : ({E.parse} : Grade E) ⊆ ({E.io, E.parse, E.range} : Grade E))
    (hj : ({E.range} : Grade E) ⊆ ({E.io, E.parse, E.range} : Grade E))
    (x : Graded ({E.io} : Grade E)
      (Graded ({E.parse} : Grade E) (Graded ({E.range} : Grade E) Nat))) :
    flattenK (Grade.le_refl' _) hj (flattenK hg hh x) =
      flattenK hg (Grade.le_refl' _) (Graded.map (flattenK hh hj) x) :=
  flattenK_flattenK hg hh hj x

-- `flattenK_widen_outer`/`flattenK_widen_inner`: the order laws, via
-- `Grade.le_trans'` instead of `Grade.join_mono`.
example
    (h₁ : ({E.io} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (hg' : ({E.io, E.parse} : Grade E) ⊆ ({E.io, E.parse, E.range} : Grade E))
    (hh : ({E.parse} : Grade E) ⊆ ({E.io, E.parse, E.range} : Grade E))
    (x : Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat)) :
    flattenK hg' hh (widen h₁ x) = flattenK (Grade.le_trans' h₁ hg') hh x :=
  flattenK_widen_outer h₁ hg' hh x

example
    (h₂ : ({E.parse} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (hg : ({E.io} : Grade E) ⊆ ({E.io, E.parse, E.range} : Grade E))
    (hh' : ({E.io, E.parse} : Grade E) ⊆ ({E.io, E.parse, E.range} : Grade E))
    (x : Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat)) :
    flattenK hg hh' ((Graded.map (widen h₂) x :
        Graded ({E.io} : Grade E) (Graded ({E.io, E.parse} : Grade E) Nat))) =
      flattenK hg (Grade.le_trans' h₂ hh') x :=
  flattenK_widen_inner h₂ hg hh' x

-- `flattenK_comm`: the finding this leg exists to make — no
-- `Grade.join_comm`, and `rfl` rather than merely cast-free.
example
    (hg : ({E.io} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (hh : ({E.parse} : Grade E) ⊆ ({E.io, E.parse} : Grade E))
    (x : Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat)) :
    flattenK hg hh x = flattenK hh hg (swap x) :=
  flattenK_comm hg hh x

-- `flatten_eq_flattenK`: instantiating `flattenK` at the exact union
-- recovers `flatten`.
example (x : Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat)) :
    flatten x = flattenK (Grade.le_join_left _ _) (Grade.le_join_right _ _) x :=
  flatten_eq_flattenK x

-- The substantive case `flatten` cannot express: `flattenK` at a `k`
-- strictly larger than `Grade.join {E.io} {E.parse}` — no cast, the same
-- shape as `renderK` above for `bindK`. `lookup`/`renderLookup`
-- ([Examples.Validation]) already `#guard` this consumer directly; these
-- exercise `flattenK` on inputs `lookup` itself cannot produce (an outer
-- I/O success wrapping an inner *unparsed* failure at a grade wider than
-- either layer needs).
def renderFlattenK : Graded ({E.io, E.parse, E.range} : Grade E) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

#guard renderFlattenK
    (flattenK (g := ({E.io} : Grade E)) (h := ({E.parse} : Grade E))
      (k := ({E.io, E.parse, E.range} : Grade E)) (by decide) (by decide)
      (Graded.ok (Graded.ok 7) :
        Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat))) = "ok 7"

#guard renderFlattenK
    (flattenK (g := ({E.io} : Grade E)) (h := ({E.parse} : Grade E))
      (k := ({E.io, E.parse, E.range} : Grade E)) (by decide) (by decide)
      (Graded.ok (Graded.err E.parse (by decide)) :
        Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat))) =
  "err Examples.Validation.E.parse"

#guard renderFlattenK
    (flattenK (g := ({E.io} : Grade E)) (h := ({E.parse} : Grade E))
      (k := ({E.io, E.parse, E.range} : Grade E)) (by decide) (by decide)
      (Graded.err E.io (by decide) :
        Graded ({E.io} : Grade E) (Graded ({E.parse} : Grade E) Nat))) =
  "err Examples.Validation.E.io"

-- ---------------------------------------------------------------------
-- `Comp.apK`: the two-coordinate composite at a sufficient grade *pair*,
-- each strictly larger than its own component's join —
-- `{E.parse, E.range}` widened to `{E.parse, E.range, E.io}` in the
-- outer coordinate, `{E.range, E.io}` widened the same way in the inner
-- — the two-coordinate mirror of `renderK` above, and the case the step
-- asked to exercise explicitly.

def renderCompK :
    Comp ({E.parse, E.range, E.io} : Grade E) ({E.parse, E.range, E.io} : Grade E) Nat → String
  | .ok (.ok n) => s!"ok (ok {n})"
  | .ok (.err e _) => s!"ok (err {repr e})"
  | .err e _ => s!"err {repr e}"

-- All four succeed: outer `{E.parse}`/`{E.range}` and inner
-- `{E.range}`/`{E.io}`, both widened to `{E.parse, E.range, E.io}`.
#guard renderCompK
    (Comp.apK (g := ({E.parse} : Grade E)) (g' := ({E.range} : Grade E))
      (h := ({E.range} : Grade E)) (h' := ({E.io} : Grade E))
      (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (by decide) (by decide) (by decide)
      (Graded.ok (Graded.ok (· + 1)) : Comp _ _ (Nat → Nat))
      (Graded.ok (Graded.ok 5) : Comp _ _ Nat)) = "ok (ok 6)"

-- The outer layer fails on the argument's side (`xx`'s outer grade
-- `{E.range}`, widened into `k1`): `Comp.apK_ok_err`.
#guard renderCompK
    (Comp.apK (g := ({E.parse} : Grade E)) (g' := ({E.range} : Grade E))
      (h := ({E.range} : Grade E)) (h' := ({E.io} : Grade E))
      (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (by decide) (by decide) (by decide)
      (Graded.ok (Graded.ok (· + 1)) : Comp _ _ (Nat → Nat))
      (Graded.err E.range (by decide) : Comp _ _ Nat)) = "err Examples.Validation.E.range"

-- The *inner* layer fails (`ff`'s inner grade `{E.range}`), surfacing
-- only once both outer layers are known to succeed.
#guard renderCompK
    (Comp.apK (g := ({E.parse} : Grade E)) (g' := ({E.range} : Grade E))
      (h := ({E.range} : Grade E)) (h' := ({E.io} : Grade E))
      (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (by decide) (by decide) (by decide)
      (Graded.ok (Graded.err E.range (by decide)) : Comp _ _ (Nat → Nat))
      (Graded.ok (Graded.ok 5) : Comp _ _ Nat)) = "ok (err Examples.Validation.E.range)"

-- ---------------------------------------------------------------------
-- `traverseCompK`: the composed traversal at a sufficient grade pair —
-- the same two-coordinate mirror `Comp.apK` above already exercises, now
-- over a list.

def renderComposedK :
    Comp ({E.parse, E.range, E.io} : Grade E) ({E.parse, E.range, E.io} : Grade E) (List Nat) →
      String
  | .ok (.ok ns) => s!"ok (ok {ns})"
  | .ok (.err e _) => s!"ok (err {repr e})"
  | .err e _ => s!"err {repr e}"

#guard renderComposedK
    (traverseCompK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
      (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (by decide)
      (fun s => Graded.map checkRange (parseNat s)) ["1", "2", "3"]) = "ok (ok [1, 2, 3])"

#guard renderComposedK
    (traverseCompK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
      (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (by decide)
      (fun s => Graded.map checkRange (parseNat s)) ["1", "9999", "3"]) =
  "ok (err Examples.Validation.E.range)"

#guard renderComposedK
    (traverseCompK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
      (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (by decide)
      (fun s => Graded.map checkRange (parseNat s)) ["1", "x", "3"]) =
  "err Examples.Validation.E.parse"

-- `traverseCompK_eq`: the confirmation the step file asked for —
-- `traverseComp_eq` held unconditionally at the union-graded layer, and
-- its sufficient-grade analogue holds too, cast-free, with no idempotence
-- to pay in the first place (`traverseCompK_cons` is `rfl`, unlike
-- `Comp.traverseComp_cons`).
example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E)) (xs : List String) :
    traverseCompK hg hh (fun s => Graded.map checkRange (parseNat s)) xs =
      Graded.map (traverseK hh checkRange) (traverseK hg parseNat xs) :=
  traverseCompK_eq hg hh parseNat checkRange xs

#guard renderComposedK
    (traverseCompK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
      (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (by decide)
      (fun s => Graded.map checkRange (parseNat s)) ["1", "9999", "3"]) =
  renderComposedK
    (Graded.map (traverseK (g := ({E.range} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
        (by decide) checkRange)
      (traverseK (g := ({E.parse} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
        (by decide) parseNat ["1", "9999", "3"]))

-- ---------------------------------------------------------------------
-- `flatten_apK`: the value-side hypothesis survives grade nomination.
-- `bothFailFF`/`bothFailXX` are exactly the excluded shape — `ff` outer
-- succeeds with a failing *inner* payload, while `xx`'s outer layer also
-- fails — chosen with `ff`'s inner grade (`{E.io}`) and `xx`'s outer
-- grade (`{E.range}`) disjoint, so the two sides below render as visibly
-- *different* errors, not just different proof terms of the same one.

def bothFailFF : Comp ({E.parse} : Grade E) ({E.io} : Grade E) (Nat → Nat) :=
  Graded.ok (Graded.err E.io (by decide))

def bothFailXX : Comp ({E.range} : Grade E) ({E.parse} : Grade E) Nat :=
  Graded.err E.range (by decide)

def renderFlattenApK : Graded ({E.parse, E.range, E.io} : Grade E) Nat → String
  | .ok n => s!"ok {n}"
  | .err e _ => s!"err {repr e}"

-- Flatten-the-composite-first (`Comp.apK` then `flattenK`): `Comp.apK`
-- never looks past `xx`'s outer failure to notice `ff`'s inner one, so
-- this reports `xx`'s error.
#guard renderFlattenApK
    (flattenK (g := ({E.parse, E.range, E.io} : Grade E))
        (h := ({E.parse, E.range, E.io} : Grade E))
      (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide)
      (Comp.apK (g := ({E.parse} : Grade E)) (g' := ({E.range} : Grade E))
        (h := ({E.io} : Grade E)) (h' := ({E.parse} : Grade E))
        (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
        (by decide) (by decide) (by decide) (by decide) bothFailFF bothFailXX)) =
  "err Examples.Validation.E.range"

-- Flatten-each-piece-first (`flattenK` then `apK`): flattening `ff` alone
-- exposes its inner error immediately, and `apK`'s function-error-first
-- priority then reports it instead.
#guard renderFlattenApK
    (apK (Grade.le_refl' ({E.parse, E.range, E.io} : Grade E))
        (Grade.le_refl' ({E.parse, E.range, E.io} : Grade E))
      (flattenK (g := ({E.parse} : Grade E)) (h := ({E.io} : Grade E))
        (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide) bothFailFF)
      (flattenK (g := ({E.range} : Grade E)) (h := ({E.parse} : Grade E))
        (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide) bothFailXX)) =
  "err Examples.Validation.E.io"

-- The two sides disagree on the same inputs: `flatten_apK`'s hypothesis
-- is not vacuous, at any sufficient grade — it excludes exactly this
-- shape, and excluding it is load-bearing, not decorative.

-- The theorem itself, exercised on a `hcond`-satisfying input (`xx`
-- succeeds outright): both sides agree, and the `Prop`-irrelevant
-- inclusion proofs elaborate at this concrete grade via `by decide`.
example :
    flattenK (g := ({E.parse, E.range, E.io} : Grade E)) (h := ({E.parse, E.range, E.io} : Grade E))
        (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide)
      (Comp.apK (g := ({E.parse} : Grade E)) (g' := ({E.range} : Grade E))
        (h := ({E.io} : Grade E)) (h' := ({E.parse} : Grade E))
        (k1 := ({E.parse, E.range, E.io} : Grade E)) (k2 := ({E.parse, E.range, E.io} : Grade E))
        (by decide) (by decide) (by decide) (by decide) bothFailFF
        (Graded.ok (Graded.ok 5) : Comp ({E.range} : Grade E) ({E.parse} : Grade E) Nat)) =
      apK (Grade.le_refl' _) (Grade.le_refl' _)
        (flattenK (g := ({E.parse} : Grade E)) (h := ({E.io} : Grade E))
          (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide) bothFailFF)
        (flattenK (g := ({E.range} : Grade E)) (h := ({E.parse} : Grade E))
          (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide)
          (Graded.ok (Graded.ok 5) : Comp ({E.range} : Grade E) ({E.parse} : Grade E) Nat)) :=
  flatten_apK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    bothFailFF (Graded.ok (Graded.ok 5) : Comp ({E.range} : Grade E) ({E.parse} : Grade E) Nat)
    (Or.inr (Or.inr ⟨Graded.ok 5, rfl⟩))

-- ---------------------------------------------------------------------
-- `GradedHomK`/`renameHomK`: the morphism leg. `renameHomK coarsen`
-- typechecks at `E → E'`, with the same `gmap`/`hom` as `renameHom
-- coarsen` — the field `renameHomK coarsen |>.gmap` is `Grade.rename
-- coarsen`, computed exactly as `renameHom coarsen |>.gmap` is.

example : (renameHomK coarsen).gmap ({E.parse, E.range} : Grade E) = ({E'.bad} : Grade E') := rfl

#guard renderCoarse ((renameHomK coarsen).hom (validate "42")) = "ok 42"
#guard renderCoarse ((renameHomK coarsen).hom (validate "abc")) = "err Examples.Validation.E'.bad"
#guard renderCoarse ((renameHomK coarsen).hom (validate "9999")) = "err Examples.Validation.E'.bad"

-- `hom_pureK`, `rfl` at the concrete instance: renaming `pureK` changes
-- nothing about the payload.
example (n : Nat) :
    (renameHomK coarsen).hom (pureK n : Graded ({E.parse} : Grade E) Nat) =
      (pureK n : Graded ({E'.bad} : Grade E') Nat) :=
  (renameHomK coarsen).hom_pureK n

-- `hom_bindK`, exercised through `renameHomK` at grades wider than
-- `{E.parse}`/`{E.range}`'s own union, the same "no cast to write down"
-- shape `bindK` itself demonstrates above.
example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) (f : Nat → Graded ({E.range} : Grade E) Nat) :
    (renameHomK coarsen).hom (bindK hg hh x f) =
      bindK ((renameHomK coarsen).gmap_mono hg) ((renameHomK coarsen).gmap_mono hh)
        ((renameHomK coarsen).hom x) (fun a => (renameHomK coarsen).hom (f a)) :=
  (renameHomK coarsen).hom_bindK hg hh x f

-- `rename_apK`/`rename_map2K`/`traverseK_rename`: naturality of `rename`
-- against the sufficient-grade applicative and traversal, cast-free.
example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) (f' : Nat → Nat) (a : Nat) :
    rename coarsen (apK hg hh (Graded.ok f' : Graded ({E.parse} : Grade E) (Nat → Nat))
        (Graded.ok a : Graded ({E.range} : Grade E) Nat)) =
      apK (Grade.rename_mono coarsen hg) (Grade.rename_mono coarsen hh)
        (rename coarsen (Graded.ok f')) (rename coarsen (Graded.ok a)) :=
  rename_apK coarsen hg hh (Graded.ok f') (Graded.ok a)

example
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (f : Nat → Graded ({E.parse} : Grade E) Nat) (xs : List Nat) :
    rename coarsen (traverseK hg f xs) =
      traverseK (Grade.rename_mono coarsen hg) (rename coarsen ∘ f) xs :=
  traverseK_rename coarsen hg f xs

#guard renderListK
    (traverseK (g := ({E.parse} : Grade E)) (k := ({E.parse, E.range, E.io} : Grade E))
      (by decide) (fun n => (Graded.ok (n + 1) : Graded ({E.parse} : Grade E) Nat))
      [1, 2, 3]) = "ok [2, 3, 4]"

-- ---------------------------------------------------------------------
-- `GradedHom.gmap_mono`: the grade half of the bridge, derived from
-- `gmap_join` alone.
example (hgh : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) :
    (renameHom coarsen).gmap ({E.parse} : Grade E) ⊆
      (renameHom coarsen).gmap ({E.parse, E.range} : Grade E) :=
  GradedHom.gmap_mono (renameHom coarsen) hgh

-- ---------------------------------------------------------------------
-- `GradedHom.toGradedHomK`: the bridge in full, at a *nontrivial* pair of
-- grades — `{E.parse}` strictly inside `{E.parse, E.range}`, and a
-- `coarsen` that is genuinely many-to-one, so neither the inclusion nor
-- the renaming is an identity in disguise.

example : GradedHomK E E' := (renameHom coarsen).toGradedHomK

-- The lift changes nothing about what the morphism does: same `gmap`,
-- same `hom`, both by `rfl`.
example (x : Graded ({E.parse} : Grade E) Nat) :
    (renameHomK coarsen).hom x = rename coarsen x :=
  renameHomK_hom coarsen x

example : (renameHomK coarsen).gmap = Grade.rename coarsen := renameHomK_gmap coarsen

example : (renameHomK coarsen).hom
    (Graded.err E.parse (by decide) : Graded ({E.parse} : Grade E) Nat)
      = rename coarsen (Graded.err E.parse (by decide)) := rfl

-- `hom_ok` at a grade that is not `Grade.bot`, which is the case
-- `hom_pure` does not state and `hom_widen` is what supplies.
example (a : Nat) :
    (renameHom coarsen).hom (Graded.ok a : Graded ({E.parse, E.range} : Grade E) Nat)
      = Graded.ok a :=
  GradedHom.hom_ok (renameHom coarsen) a

-- `hom_widen`, the new field, at a real inclusion.
example (h₁ : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (x : Graded ({E.parse} : Grade E) Nat) :
    (renameHom coarsen).hom (widen h₁ x)
      = widen (GradedHom.gmap_mono (renameHom coarsen) h₁) ((renameHom coarsen).hom x) :=
  (renameHom coarsen).hom_widen h₁ _ x

-- `bindK_eq_widen_bind`: the factorisation the lift runs through, at two
-- distinct nonempty grades and a nominated grade above both.
example (x : Graded ({E.parse} : Grade E) Nat)
    (f : Nat → Graded ({E.range} : Grade E) Nat)
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E)) :
    bindK hg hh x f = widen (Grade.join_le hg hh) (bind x f) :=
  bindK_eq_widen_bind hg hh x f

#guard renderK (bindK (g := ({E.parse} : Grade E)) (h := ({E.range} : Grade E))
    (k := ({E.parse, E.range, E.io} : Grade E)) (by decide) (by decide)
    (Graded.err E.parse (by decide))
    (fun n => (Graded.ok n : Graded ({E.range} : Grade E) Nat)))
  = "err Examples.Validation.E.parse"

-- ---------------------------------------------------------------------
-- `constHomK`: the counter-instance. Its `gmap` is monotone (every
-- `GradedHomK` field resolves, `#guard`ed below to compute) but is not a
-- join-semilattice homomorphism — `constHomK_not_gmap_bot` refutes the
-- one field a `GradedHom` would additionally require.

#guard (constHomK (Err := E) (g₀ := ({E'.bad} : Grade E')) E'.bad (by decide)).hom
    (Graded.ok (5 : Nat) : Graded ({E.parse} : Grade E) Nat) = Graded.ok 5

#guard (constHomK (Err := E) (g₀ := ({E'.bad} : Grade E')) E'.bad (by decide)).hom
    (Graded.err E.parse (by decide) : Graded ({E.parse} : Grade E) Nat) =
  Graded.err E'.bad (by decide)

example : (fun (_ : Grade E) => ({E'.bad} : Grade E')) (Grade.bot : Grade E) ≠
    (Grade.bot : Grade E') :=
  constHomK_not_gmap_bot (Err := E) (e₀ := E'.bad) (g₀ := ({E'.bad} : Grade E')) (by decide)

-- ---------------------------------------------------------------------
-- `apK_comp`: the composition law at a sufficient grade, instantiated at
-- **three distinct nonempty source grades** under one nominated grade
-- containing all three. With a shared source grade the three inclusions
-- would coincide and the law would not be exercised at the shape it is
-- stated in.
example (u : Graded ({E.parse} : Grade E) (Nat → Nat))
    (v : Graded ({E.range} : Grade E) (Nat → Nat))
    (w : Graded ({E.io} : Grade E) Nat)
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (hg' : ({E.range} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E))
    (hj : ({E.io} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E)) :
    apK (Grade.le_refl' _) hj
        (apK (Grade.le_refl' _) hg'
          (apK (Grade.le_refl' _) hg
            (pureK Function.comp
              : Graded ({E.parse, E.range, E.io} : Grade E)
                  ((Nat → Nat) → (Nat → Nat) → Nat → Nat)) u) v) w
      = apK hg (Grade.le_refl' _) u (apK hg' hj v w) :=
  apK_comp hg hg' hj u v w

-- `rename_map2K`: naturality of renaming against the sufficient-grade
-- `map2K`, at a genuinely many-to-one `coarsen` and two distinct source
-- grades — an injective renaming or a shared grade would let a broken
-- implementation through.
example (x : Graded ({E.parse} : Grade E) Nat) (y : Graded ({E.range} : Grade E) Nat)
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.range} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.parse, E.range} : Grade E)) :
    rename coarsen (map2K hg hh (· + ·) x y)
      = map2K (Grade.rename_mono coarsen hg) (Grade.rename_mono coarsen hh) (· + ·)
          (rename coarsen x) (rename coarsen y) :=
  rename_map2K coarsen hg hh (· + ·) x y

-- The three `traverseK_cons_*` case lemmas, with the head/tail premises
-- discharged against concrete checks rather than assumed of a variable.

/-- Succeeds on everything. -/
private def okCheckK (n : Nat) : Graded ({E.parse} : Grade E) Nat := Graded.ok (n + 1)

/-- Fails on everything. -/
private def badCheckK (_ : Nat) : Graded ({E.parse} : Grade E) Nat :=
  Graded.err E.parse (by decide)

/-- Succeeds on the head, fails on a `0` further down. -/
private def mixedCheckK (n : Nat) : Graded ({E.parse} : Grade E) Nat :=
  if n = 0 then Graded.err E.parse (by decide) else Graded.ok (n + 1)

private theorem hgK : ({E.parse} : Grade E) ⊆ ({E.parse, E.range, E.io} : Grade E) := by decide

example (hxs : traverseK hgK okCheckK [2, 3] = Graded.ok [3, 4]) :
    traverseK hgK okCheckK (1 :: [2, 3]) = Graded.ok (2 :: [3, 4]) :=
  traverseK_cons_ok_ok hgK okCheckK 1 [2, 3] 2 [3, 4] rfl hxs

example : traverseK hgK badCheckK (1 :: [2, 3]) = Graded.err E.parse (hgK (by decide)) :=
  traverseK_cons_err_left hgK badCheckK 1 [2, 3] E.parse (by decide) rfl

example (he : E.parse ∈ ({E.parse, E.range, E.io} : Grade E))
    (hxs : traverseK hgK mixedCheckK [0, 3] = Graded.err E.parse he) :
    traverseK hgK mixedCheckK (1 :: [0, 3]) = Graded.err E.parse he :=
  traverseK_cons_ok_err hgK mixedCheckK 1 [0, 3] 2 E.parse he rfl hxs

#guard renderListK (traverseK hgK okCheckK [1, 2, 3]) = "ok [2, 3, 4]"
#guard renderListK (traverseK hgK mixedCheckK [1, 0, 3])
  = "err Examples.Validation.E.parse"

-- `Comp.apK_interchange`: the interchange law for the nested carrier at a
-- pair of nominated grades, instantiated at two *different* nominated
-- grades so the outer and inner coordinates are not the same bound.
example (u : Comp ({E.parse} : Grade E) ({E.range} : Grade E) (Nat → Nat)) (a : Nat)
    (hg : ({E.parse} : Grade E) ⊆ ({E.parse, E.io} : Grade E))
    (hh : ({E.range} : Grade E) ⊆ ({E.range, E.io} : Grade E)) :
    Comp.apK hg (Grade.bot_le _) hh (Grade.bot_le _) u (Comp.pure a)
      = Comp.apK (Grade.bot_le _) hg (Grade.bot_le _) hh
          (Comp.pure (fun f => f a) : Comp Grade.bot Grade.bot ((Nat → Nat) → Nat)) u :=
  Comp.apK_interchange hg hh u a

end Tests
