import Graded.Sufficient.MonadK
import Graded.Compose

/-! `flattenK`: the nested carrier collapsed at a sufficient grade.

    Split out of the former single `Graded/Sufficient.lean` by
    [module-split]; `Graded.Sufficient` is now a re-export shim over the
    six pieces, so every existing import keeps working. -/

namespace Graded

variable {Err : Type u} [DecidableEq Err]
variable {g h j k : Grade Err} {α β γ : Type v}

-- ---------------------------------------------------------------------
-- `flattenK`: the nested carrier at a sufficient grade. `flatten` is
-- `bind` applied to the identity continuation (`flatten_eq_bind_id`,
-- [compose](../docs/design.md#compose)), so `flattenK` is built the same
-- way, on `bindK` directly rather than by a second pattern match on
-- `Graded`'s constructors: `flattenK hg hh x := bindK hg hh x id`. This
-- file's universe-`u` payloads (the same fix
-- `Graded/Compose.lean`/`Graded/ComposeApp.lean` already need, for the
-- same reason: `Graded h α` is a genuinely higher-universe payload than
-- `α`, and `bindK`'s two payload type-variables share one universe) are
-- local to this section.

section ComposeK

variable {α β γ : Type u}

/-- Collapse a nested carrier to a single one, at any grade `k` known to
    contain both the outer grade `g` (via `hg`) and the inner grade `h`
    (via `hh`) — not necessarily their union. Built on `bindK`, at the
    identity continuation, exactly as `flatten x = bind x id`
    ([compose](../docs/design.md#compose)) says the union-graded operation
    already is. -/
def flattenK (hg : g ⊆ k) (hh : h ⊆ k) (x : Graded g (Graded h α)) : Graded k α :=
  bindK hg hh x (fun y => y)

theorem flattenK_ok (hg : g ⊆ k) (hh : h ⊆ k) (y : Graded h α) :
    flattenK hg hh (Graded.ok y : Graded g (Graded h α)) = widen hh y :=
  bindK_ok hg hh y (fun y => y)

theorem flattenK_err (hg : g ⊆ k) (hh : h ⊆ k) (e : Err) (he : e ∈ g) :
    flattenK hg hh (Graded.err e he : Graded g (Graded h α)) = Graded.err e (hg he) :=
  bindK_err hg hh e he (fun y => y)

/-- Naturality: mapping the inner payload before flattening agrees with
    flattening then mapping outside — the analogue of `flatten_map`,
    cast-free for the same reason every other law here is: both sides
    already land in `Graded k β` before any grade is compared. -/
theorem flattenK_map (hg : g ⊆ k) (hh : h ⊆ k) (f : α → β) (x : Graded g (Graded h α)) :
    flattenK hg hh ((map (map f) x : Graded g (Graded h β))) = map f (flattenK hg hh x) := by
  cases x using Graded.rec' with
  | ok y =>
    cases y using Graded.rec' with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

/-- (unit) Wrapping an already-graded value with `pure` at the outer layer
    and flattening at any sufficient `k` recovers the value, widened along
    `hh` — the same fact `bindK_pure_left` already states, since
    `flattenK`'s continuation *is* `bindK`'s identity continuation. No
    `Grade.bot_join` anywhere: `Grade.bot_le k` is a hypothesis supplied
    once, not a grade computed and then equated to another. -/
theorem flattenK_pure_outer (hh : h ⊆ k) (y : Graded h α) :
    flattenK (Grade.bot_le k) hh (pure y) = widen hh y :=
  bindK_pure_left hh y (fun y => y)

/-- (unit) Wrapping a graded value's payload with `pure` at the inner
    layer and flattening at any sufficient `k` recovers the value, widened
    along `hg` — the analogue of `flatten_pure_inner`, no `Grade.join_bot`
    anywhere. -/
theorem flattenK_pure_inner (hg : g ⊆ k) (x : Graded g α) :
    flattenK hg (Grade.bot_le k) (map pure x) = widen hg x := by
  cases x using Graded.rec' with
  | ok a => rfl
  | err e he => rfl

/-- (associative) Flattening the outer two layers first, then the third,
    or the inner two layers first (via `map flattenK`), then the outer,
    agree — at a common `k` there is only one grade in sight, so both
    sides land in `Graded k α` directly and `Grade.le_refl' k` (reused
    twice, exactly as `bindK_assoc` reuses it) does the associativity
    lemma's job. No `Grade.join_assoc` anywhere, unlike `flatten_flatten`. -/
theorem flattenK_flattenK (hg : g ⊆ k) (hh : h ⊆ k) (hj : j ⊆ k)
    (x : Graded g (Graded h (Graded j α))) :
    flattenK (Grade.le_refl' k) hj (flattenK hg hh x) =
      flattenK hg (Grade.le_refl' k) (map (flattenK hh hj) x) := by
  cases x using Graded.rec' with
  | ok y =>
    cases y using Graded.rec' with
    | ok z =>
      cases z using Graded.rec' with
      | ok a => rfl
      | err e he => rfl
    | err e he => rfl
  | err e he => rfl

/-- (order) Widening the outer layer before flattening agrees with
    folding the widening into the inclusion proof `flattenK` already
    threads, via `Grade.le_trans'` — the analogue of `flatten_widen_outer`,
    and cheaper: no `Grade.join_mono` is needed, the same shape
    `bindK_widen` already found. -/
theorem flattenK_widen_outer (h₁ : g ⊆ g') (hg' : g' ⊆ k) (hh : h ⊆ k)
    (x : Graded g (Graded h α)) :
    flattenK hg' hh (widen h₁ x) = flattenK (Grade.le_trans' h₁ hg') hh x := by
  cases x using Graded.rec' with
  | ok y =>
    cases y using Graded.rec' with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

/-- (order) Widening the inner layer before flattening agrees with folding
    the widening into the second inclusion proof, via `Grade.le_trans'` —
    the analogue of `flatten_widen_inner`, same shape as
    `flattenK_widen_outer` above, one coordinate over. -/
theorem flattenK_widen_inner (h₂ : h ⊆ h') (hg : g ⊆ k) (hh' : h' ⊆ k)
    (x : Graded g (Graded h α)) :
    flattenK hg hh' ((map (widen h₂) x : Graded g (Graded h' α))) =
      flattenK hg (Grade.le_trans' h₂ hh') x := by
  cases x using Graded.rec' with
  | ok y =>
    cases y using Graded.rec' with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

-- ---------------------------------------------------------------------
-- `flattenK_comm`: the finding this leg exists to make for `flatten`.
-- `flatten_comm` already needed no *value*-level hypothesis — `Graded g
-- (Graded h α)` has at most one error by construction (three inhabited
-- shapes, never two), so the "at most one side errs" condition `ap_flip`
-- needs is vacuously true here and was never written down
-- ([compose](../docs/design.md#compose)). What `flatten_comm` still paid
-- was `cast (Grade.join_comm h g)`, to reconcile `flatten`'s grade `join g
-- h` against the swapped `flatten (swap x)`'s grade `join h g` — two
-- spellings of one union. At a common sufficient grade `k`, `flattenK hg
-- hh x` and `flattenK hh hg (swap x)` already land in the *same* `Graded k
-- α`, so there is no second spelling anywhere for `Grade.join_comm` to
-- reconcile: the theorem below needs no hypothesis and no property at
-- all, and is `rfl` in every case — not merely cast-free the way
-- `apK_flip`/`Comp.apK_interchange` are, but with nothing left to prove
-- beyond unfolding `swap`. This is not a vacuous law: `swap` genuinely
-- rearranges which constructor `x` reduces through (`ok (err e he)`
-- becomes a top-level `err e he` at a different grade index, and vice
-- versa), and the theorem says the two sides still compute to the exact
-- same error or the exact same payload.

/-- Flattening agrees with flattening after swapping the two layers, at
    any common sufficient grade `k` — unconditionally, and `rfl`: unlike
    `flatten_comm`, there is no `Grade.join_comm` anywhere, because there
    is no second expression for the same grade left to reconcile. -/
theorem flattenK_comm (hg : g ⊆ k) (hh : h ⊆ k) (x : Graded g (Graded h α)) :
    flattenK hg hh x = flattenK hh hg (swap x) := by
  cases x using Graded.rec' with
  | ok y =>
    cases y using Graded.rec' with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

-- ---------------------------------------------------------------------
-- Instantiating `flattenK` at the exact union `Grade.join g h`, along the
-- same two inclusions `flatten` itself uses
-- (`Grade.le_join_left`/`Grade.le_join_right`), recovers `flatten` — the
-- nested-carrier mirror of `bind_eq_bindK`/`ap_eq_apK`/`traverse_eq_traverseK`.
/-- BRIDGE -/
theorem flatten_eq_flattenK (x : Graded g (Graded h α)) :
    flatten x = flattenK (Grade.le_join_left g h) (Grade.le_join_right g h) x := by
  cases x using Graded.rec' with
  | ok y =>
    cases y using Graded.rec' with
    | ok a => rfl
    | err e he => rfl
  | err e he => rfl

end ComposeK

end Graded
