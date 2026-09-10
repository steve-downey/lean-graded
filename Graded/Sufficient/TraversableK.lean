import Graded.Sufficient.ApplicativeK
import Graded.Traverse

/-! `traverseK`: uniform list traversal at a sufficient grade.

    Split out of the former single `Graded/Sufficient.lean` by
    [module-split]; `Graded.Sufficient` is now a re-export shim over the
    six pieces, so every existing import keeps working. -/

namespace Graded

variable {Err : Type u} [DecidableEq Err]
variable {g h j k : Grade Err} {α β γ : Type v}

-- ---------------------------------------------------------------------
-- `traverseK`: the [obligation-layering] probe. `Graded.traverse` folds a
-- single repeated grade `g` over a list and widens the result to `g`
-- along `foldGrade_le`, paying a `Grade.join_idem` cast in `traverse_cons`
-- to identify the folded `Grade.join g g` with `g`. At a sufficient grade
-- `k` supplied once by the caller, there is no fold to identify with
-- anything: every element lands at `k` directly, via the same `hg : g ⊆
-- k` reused at every position, so both `traverseK_nil` and
-- `traverseK_cons` below are `rfl`. This is not the traversal migration
-- ([cast-burden-migration-scope](../docs/design.md#cast-burden-migration-scope)) —
-- it is only enough to ask what [obligation-layering] needs: does a
-- uniform list traversal, asked to land in a grade the caller nominates
-- rather than one computed by folding, need idempotence at all? It does
-- not: `traverseK_cons` carries no cast, where `traverse_cons` carries
-- one along `Grade.join_idem`. Length-independence is not a *theorem*
-- here the way `foldGrade_cons_ne_nil` is one for `traverse` — it is a
-- property of `traverseK`'s *signature*, since `Graded k (List β)` is the
-- result type for every list regardless of length, before any theorem is
-- stated about it at all.

/-- The uniform-grade traversal at a sufficient grade `k`: every element's
    image under `f` (at `g`) and the accumulated tail (already at `k`)
    combine via `map2K`, both reusing `hg : g ⊆ k` and `Grade.le_refl' k`
    rather than folding `g` into itself once per element. -/
def traverseK (hg : g ⊆ k) (f : α → Graded g β) : List α → Graded k (List β)
  | []      => pureK []
  | x :: xs => map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x) (traverseK hg f xs)

theorem traverseK_nil (hg : g ⊆ k) (f : α → Graded g β) :
    traverseK hg f ([] : List α) = pureK [] := rfl

theorem traverseK_cons (hg : g ⊆ k) (f : α → Graded g β) (x : α) (xs : List α) :
    traverseK hg f (x :: xs)
      = map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x) (traverseK hg f xs) := rfl

/-- Which proof of `g ⊆ k` justifies `traverseK` doesn't matter, only that
    one exists — the mirror of `bindK_irrel`, and `rfl` for the same
    reason: every hypothesis threaded through the recursion is a `Prop`.
    Unlike `bindK_irrel`, there is only one witness here to be irrelevant
    about, because `traverseK` reuses `Grade.le_refl' k` at every position
    for the accumulated tail rather than threading a second inclusion. -/
theorem traverseK_irrel (hg hg' : g ⊆ k) (f : α → Graded g β) (xs : List α) :
    traverseK hg f xs = traverseK hg' f xs := rfl

-- ---------------------------------------------------------------------
-- The ∅-grade case: `traverseK_nil` above already *is* this, since
-- `pureK` is `fromEmpty` by definition rather than a separate one. Stated
-- explicitly, in the `fromEmpty`-spelling `traverse_nil` uses, so the
-- bridge below and the design doc can compare like with like. Where
-- `traverse_nil` needed `fromEmpty_eq_ok` plus a `widen`/`fromEmpty`
-- proof-irrelevance argument (two different `⊆ ∅ → g`-shaped proofs
-- standing behind each side), there is no fold here to be uniform with in
-- the first place: `traverseK hg f []` never mentions `foldGrade_le` at
-- all, so this is `rfl`.
theorem traverseK_nil_eq_fromEmpty (hg : g ⊆ k) (f : α → Graded g β) :
    traverseK hg f ([] : List α) = fromEmpty [] := rfl

-- ---------------------------------------------------------------------
-- `traverseK_map`: the analogue of `traverse_map`. Reindexing the input
-- before `traverseK` agrees with `traverseK`ing the reindexed function —
-- by induction, `traverseK_nil` at the base and `traverseK_cons` at the
-- step, with no cast anywhere to cancel (contrast `traverse_map`, which
-- reuses `traverse_cons`'s own `Grade.join_idem` cast on each side and
-- relies on it cancelling).

theorem traverseK_map (hg : g ⊆ k) (f : α → Graded g β) (h : γ → α) (xs : List γ) :
    traverseK hg f (xs.map h) = traverseK hg (f ∘ h) xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      change traverseK hg f (h y :: ys.map h) = traverseK hg (f ∘ h) (y :: ys)
      rw [traverseK_cons, traverseK_cons, ih]
      rfl

-- ---------------------------------------------------------------------
-- The identity law: traversing with the "always succeed" function
-- (`fromEmpty`) is the identity — the analogue of `traverse_fromEmpty`,
-- and cheaper: `traverse_fromEmpty` delegates to `traverse_cons`'s
-- `Grade.join_idem` cast at every step; here `map2K`'s `ok`/`ok` case
-- (`apK_ok_ok`, reached through `map`'s own `ok` reduction) already lands
-- directly in `Graded k (List α)`, so there is no cast to delegate to.

theorem traverseK_fromEmpty (hg : g ⊆ k) (xs : List α) :
    traverseK hg (fromEmpty : α → Graded g α) xs = fromEmpty xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      rw [traverseK_cons, fromEmpty_eq_ok, ih, fromEmpty_eq_ok]
      rfl

-- ---------------------------------------------------------------------
-- Reduction lemmas for `traverseK`, in the flavour of `map2K`'s own
-- `ok`/`err` shapes (themselves `apK_ok_ok`/`apK_err_left`/`apK_ok_err`
-- reached through `map`) — used by `traverseK_length` below, exactly as
-- `traverse_cons_ok_ok`/`traverse_cons_err_left`/`traverse_cons_ok_err`
-- are used by `traverse_length`. No cast anywhere: every case is `rfl`
-- once `f x` and `traverseK hg f xs` are pinned to a constructor.

theorem traverseK_cons_ok_ok (hg : g ⊆ k) (f : α → Graded g β) (x : α) (xs : List α)
    (b : β) (l : List β) (hfx : f x = Graded.ok b) (hxs : traverseK hg f xs = Graded.ok l) :
    traverseK hg f (x :: xs) = Graded.ok (b :: l) := by
  rw [traverseK_cons, hfx, hxs]; rfl

theorem traverseK_cons_err_left (hg : g ⊆ k) (f : α → Graded g β) (x : α) (xs : List α)
    (e : Err) (he : e ∈ g) (hfx : f x = Graded.err e he) :
    traverseK hg f (x :: xs) = Graded.err e (hg he) := by
  rw [traverseK_cons, hfx]; rfl

theorem traverseK_cons_ok_err (hg : g ⊆ k) (f : α → Graded g β) (x : α) (xs : List α)
    (b : β) (e : Err) (he : e ∈ k) (hfx : f x = Graded.ok b)
    (hxs : traverseK hg f xs = Graded.err e he) :
    traverseK hg f (x :: xs) = Graded.err e he := by
  rw [traverseK_cons, hfx, hxs]; rfl

/-- Shape preservation: whenever `traverseK hg f xs` succeeds, its payload
    has exactly `xs`'s length — the analogue of `traverse_length`, proved
    from the three `traverseK_cons_*` reduction lemmas exactly as
    `traverse_length` is proved from `traverse_cons`'s. Unlike
    `traverse_length`, length-independence is not *this* theorem's
    subject — it never was one, since `traverseK hg f xs : Graded k (List
    β)` for every `xs` before any theorem is stated (see the module
    docstring above `traverseK`). This is the narrower, still-true fact:
    shape (not grade) is preserved from input list to output list. -/
theorem traverseK_length (hg : g ⊆ k) (f : α → Graded g β) :
    ∀ (xs : List α) (l : List β), traverseK hg f xs = Graded.ok l → l.length = xs.length
  | [], l, h => by
      rw [traverseK_nil_eq_fromEmpty, fromEmpty_eq_ok] at h
      injection h with h'
      subst h'
      rfl
  | x :: xs, l, h => by
      cases hfx : f x using Graded.rec' with
      | err e he =>
          rw [traverseK_cons_err_left hg f x xs e he hfx] at h
          exact absurd h (by simp)
      | ok b =>
          cases hxs : traverseK hg f xs using Graded.rec' with
          | err e he =>
              rw [traverseK_cons_ok_err hg f x xs b e he hfx hxs] at h
              exact absurd h (by simp)
          | ok l' =>
              rw [traverseK_cons_ok_ok hg f x xs b l' hfx hxs] at h
              injection h with h'
              subst h'
              simpa [List.length_cons] using traverseK_length hg f xs l' hxs

-- ---------------------------------------------------------------------
-- `traverse_eq_traverseK`: the bridge. `traverse` is defined at the
-- uniform grade `g` throughout, never at a computed union — so the
-- tightest sufficient grade to instantiate `traverseK` at is `g` itself,
-- along `Grade.le_refl' g`, the same reflexive inclusion `bindK_assoc`
-- above threads for its own "no grade left to compute" cases. This is
-- what keeps `Graded.Traverse`'s account of C++ `traverse` intact beside
-- this layer: the union-graded traversal *is* the sufficient-grade one,
-- at the grade `g` already sufficient for itself.
--
-- The proof cannot simply reuse `ap_eq_apK`/`bind_eq_bindK`, because
-- those bridges instantiate the sufficient-grade side at a computed
-- union (`Grade.join g h`) that is *syntactically* the shared operation's
-- own target grade, needing no further identification. Here the shared
-- target is `g`, but `traverse_cons`'s intermediate step still computes
-- through `map2` at `Grade.join g g` — a *second* expression for `g` that
-- needs `Grade.join_idem` to identify, exactly where `traverse_cons`
-- itself pays it. So the induction step below pays that same cast once,
-- on the union-graded side only, and matches it against `traverseK_cons`,
-- which never introduces a second expression for `g` at all: idempotence
-- is spent identifying `traverse`'s own two expressions for `g`, not
-- reconciling `traverse` against `traverseK`.
/-- BRIDGE -/
theorem traverse_eq_traverseK (f : α → Graded g β) (xs : List α) :
    traverse f xs = traverseK (Grade.le_refl' g) f xs := by
  induction xs with
  | nil => rw [traverse_nil, traverseK_nil_eq_fromEmpty]
  | cons x xs ih =>
      rw [traverseK_cons, ← ih]
      cases hfx : f x using Graded.rec' with
      | err e he =>
          rw [traverse_cons, hfx]
          simp only [map2, map, ap_err_left, cast_err, map2K, apK_err_left]
      | ok b =>
          cases hxs : traverse f xs using Graded.rec' with
          | err e he =>
              rw [traverse_cons, hfx, hxs]
              simp only [map2, map, ap_ok_err, cast_err, map2K, apK_ok_err]
          | ok l =>
              rw [traverse_cons, hfx, hxs]
              simp only [map2, map, ap_ok_ok, cast_ok, map2K, apK_ok_ok]

end Graded
