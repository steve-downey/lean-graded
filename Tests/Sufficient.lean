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

end Tests
