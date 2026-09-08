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

end Tests
