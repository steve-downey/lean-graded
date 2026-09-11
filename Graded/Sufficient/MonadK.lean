import Graded.Monad

/-! The sufficient-grade layer, beside the union-graded one in
    `Graded.Monad`, not in place of it. `Graded.bind` computes the result
    grade as the *union* `Grade.join g h` — faithful to C++, where
    `and_then` computes `error_set<Es_f ∪ Es_g...>` by canonicalization —
    and its three laws hold only up to the pomonoid equalities that
    canonicalization hides, so they carry `cast`.

    `bindK` instead takes a grade `k` merely *sufficient* to hold both
    inputs, via two `⊆` proofs, and lands there directly. Nothing about
    `k` is computed from `g` and `h`, so there is no equation between two
    different expressions for the same grade to transport across — the
    laws below state with no `cast` at all. `bind_eq_bindK` is the theorem
    that keeps this a second view of the same operation rather than a
    different design: instantiating `k` at the exact union `Grade.join g
    h`, using the two inclusions `bind` itself already needs, recovers
    `bind` by `rfl`.

    **This module is `bindK` and nothing else.** [module-split] broke the
    former single `Graded/Sufficient.lean` into six, and this is the
    first: it imports `Graded.Monad` alone, so a consumer that wants
    sequencing at a nominated grade no longer drags in traversal,
    composition and morphisms behind it. `apK` and its kin live in
    `Graded.Sufficient.ApplicativeK`, traversal in `.TraversableK`,
    flattening in `.ComposeK`, the product-graded composite in `.CompK`,
    and the morphism records in `.MorphismK`. `Graded.Sufficient` remains
    as a re-export shim over all six, so every existing import is
    unaffected. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]
variable {g h j k : Grade Err} {α β γ : Type v}

/-- Sequence a graded computation into a continuation at any grade `k`
    known to contain both `g` (via `hg`) and `h` (via `hh`) — not
    necessarily their union. An `ok` hands its payload to `f` and widens
    the result up to `k` along `hh`; an `err` carries its own membership
    proof along `hg`, exactly as `Graded.bind` does along
    `Grade.le_join_right`/`Grade.le_join_left`, but against a caller-
    supplied bound instead of a computed one. -/
def bindK (hg : g ⊆ k) (hh : h ⊆ k) (x : Graded g α) (f : α → Graded h β) :
    Graded k β :=
  match x with
  | .ok a     => widen hh (f a)
  | .err e he => .err e (hg he)

/-- `pure`, at any grade `k` directly rather than at `Grade.bot`: the
    bare-`T` handoff `fromEmpty` already *is* this, since `Graded.pure`
    itself is `fromEmpty` composed with the (trivial) widening from `∅`.
    Reused, not redefined. -/
def pureK (a : α) : Graded k α := fromEmpty a

-- Reduction lemmas: `bindK` and `widen` both match directly on their
-- carrier argument, so each constructor case is `rfl` — the same pattern
-- `Graded.Ungraded`'s `bindF_ok`/`bindF_err` already established for the
-- fixed-grade layer.

theorem bindK_ok (hg : g ⊆ k) (hh : h ⊆ k) (a : α) (f : α → Graded h β) :
    bindK hg hh (Graded.ok a) f = widen hh (f a) := rfl

theorem bindK_err (hg : g ⊆ k) (hh : h ⊆ k) (e : Err) (he : e ∈ g)
    (f : α → Graded h β) :
    bindK hg hh (Graded.err e he) f = Graded.err e (hg he) := rfl

theorem widen_ok (hg : g ⊆ g') (a : α) :
    (widen hg (Graded.ok a) : Graded g' α) = Graded.ok a := rfl

theorem widen_err (hg : g ⊆ g') (e : Err) (he : e ∈ g) :
    widen hg (Graded.err e he : Graded g α) = Graded.err e (hg he) := rfl

/-- (unit) `pure` (at `Grade.bot`) on the left of `bindK` is the
    continuation, widened up to `k` — cast-free, because `Grade.bot ⊆ k`
    (`Grade.bot_le`) is a hypothesis supplied once, not a grade computed
    and then equated to another. `rfl`: `pure a` is already `.ok a`. -/
theorem bindK_pure_left (hh : h ⊆ k) (a : α) (f : α → Graded h β) :
    bindK (Grade.bot_le k) hh (pure a) f = widen hh (f a) := rfl

/-- (unit) `pure` (at `Grade.bot`) on the right of `bindK` is the
    original value, widened up to `k` along the same inclusion `bindK`
    already carries for `x`. -/
theorem bindK_pure_right (hg : g ⊆ k) (x : Graded g α) :
    bindK hg (Grade.bot_le k) x (pure : α → Graded (Grade.bot : Grade Err) α) =
      widen hg x := by
  cases x using Graded.rec' with
  | ok a => rfl
  | err e he => rfl

/-- (associative) `bindK` re-associates with *no* grade to re-associate:
    every one of `x`, `f`, `k`'s results is bound directly into the same
    `k`, via its own `⊆ k` proof, so both sides land in `Graded k γ`
    without ever computing a `join`. What was `Grade.join_assoc` in
    `Graded.bind_assoc` is here `Grade.le_refl' k` twice over — the
    grade arithmetic has become subsumption, and the order lemma does the
    associativity lemma's job. -/
theorem bindK_assoc (hg : g ⊆ k) (hh : h ⊆ k) (hj : j ⊆ k)
    (x : Graded g α) (f : α → Graded h β) (kk : β → Graded j γ) :
    bindK (Grade.le_refl' k) hj (bindK hg hh x f) kk =
      bindK hg (Grade.le_refl' k) x (fun a => bindK hh hj (f a) kk) := by
  cases x using Graded.rec' with
  | ok a =>
    rw [bindK_ok hg hh a f, bindK_ok hg (Grade.le_refl' k) a (fun a => bindK hh hj (f a) kk)]
    cases hfa : f a using Graded.rec' with
    | ok b =>
      rw [widen_ok, bindK_ok hh hj b kk, bindK_ok (Grade.le_refl' k) hj b kk,
        widen_refl]
    | err e he =>
      rw [widen_err, bindK_err (Grade.le_refl' k) hj e (hh he) kk,
        bindK_err hh hj e he kk, widen_err]
  | err e he =>
    rw [bindK_err hg hh e he f, bindK_err (Grade.le_refl' k) hj e (hg he) kk,
      bindK_err hg (Grade.le_refl' k) e he (fun a => bindK hh hj (f a) kk)]

/-- The analogue of `Graded.bind_widen`, and cheaper: widening the input
    before `bindK` agrees with folding the widening into the inclusion
    proof `bindK` already threads, via `Grade.le_trans'`. No `join_mono`
    is needed — there is no second grade on the other side of a `join` to
    keep fixed while this one moves, the way `bind_widen` needed
    `Grade.le_refl' h` alongside `Grade.join_mono`. -/
theorem bindK_widen (h₁ : g ⊆ g') (hg' : g' ⊆ k) (hh : h ⊆ k)
    (x : Graded g α) (f : α → Graded h β) :
    bindK hg' hh (widen h₁ x) f = bindK (Grade.le_trans' h₁ hg') hh x f := by
  cases x using Graded.rec' with
  | ok a => rfl
  | err e he => rfl

/-- Which proof of `g ⊆ k` (or `h ⊆ k`) justifies `bindK` doesn't matter,
    only that one exists — the mirror of `Graded.widen_irrel`, and what
    makes the threaded `⊆` arguments free at call sites: `Subsingleton`
    on a `Prop`, so `rfl` closes it directly, with no case split at all. -/
theorem bindK_irrel (hg hg' : g ⊆ k) (hh hh' : h ⊆ k)
    (x : Graded g α) (f : α → Graded h β) :
    bindK hg hh x f = bindK hg' hh' x f := rfl

-- ---------------------------------------------------------------------
-- Instantiating `bindK` at the exact union `Grade.join g h`, along the
-- same two inclusions `Graded.bind` itself uses
-- (`Grade.le_join_left`/`Grade.le_join_right`), recovers `bind`: the two
-- layers are one operation, viewed at a computed grade or a merely
-- sufficient one.
/-- BRIDGE -/
theorem bind_eq_bindK (x : Graded g α) (f : α → Graded h β) :
    bind x f = bindK (Grade.le_join_left g h) (Grade.le_join_right g h) x f := by
  cases x using Graded.rec' with
  | ok a => rfl
  | err e he => rfl

end Graded
