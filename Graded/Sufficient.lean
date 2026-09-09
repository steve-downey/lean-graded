import Graded.Monad
import Graded.Applicative
import Graded.ComposeApp
import Graded.Morphism

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

    `apK`/`map2K` (below `bindK`'s own laws) extend the same story to the
    applicative, imported from `Graded.Applicative` for the bridge
    `ap_eq_apK` and from `Graded.ComposeApp` for `Comp.apK`, the composite
    at a *pair* of sufficient grades — reusing `Comp` itself rather than
    forking a second nested carrier, since `Comp g h α` already
    generalises over any two grades. -/

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
  cases x with
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
  cases x with
  | ok a =>
    rw [bindK_ok hg hh a f, bindK_ok hg (Grade.le_refl' k) a (fun a => bindK hh hj (f a) kk)]
    cases hfa : f a with
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
  cases x with
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
  cases x with
  | ok a => rfl
  | err e he => rfl

-- ---------------------------------------------------------------------
-- `apK`/`map2K`: the applicative at a sufficient grade, built through
-- `bindK` exactly as `Graded.ap`/`Graded.map2` are built through `bind` —
-- the same "the applicative is the monad's" story, one layer up. Unlike
-- `ap`, which sequences through `bind`'s *computed* union and pays one
-- cast collapsing the inner `h ∪ ∅` back to `h`, `apK` never introduces a
-- `∅` in the first place: `pureK`'s target grade is `k` directly (the
-- same fact `pureK`'s own docstring already established — it *is* `pure`
-- widened to any grade, not `pure` itself), so both of `ap`'s two `bind`
-- calls land at `k` immediately, via `Grade.le_refl' k`, with nothing to
-- collapse.

/-- Combine a graded function and a graded argument at any grade `k`
    known to contain both — `ap`'s own two-step `bind`/`pure` shuffle,
    with `pureK` used in place of `pure` so the intermediate step already
    sits at `k` instead of at `Grade.bot`. The "third obligation" the step
    predicted (one hypothesis per input, plus one for `pure`'s own grade)
    does not merely come out free by proof irrelevance the way `bindK`'s
    two threaded proofs do — it never appears in this signature at all,
    because `pureK` needs no inclusion proof of its own to be a value at
    `k`. -/
def apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β)) (x : Graded h α) :
    Graded k β :=
  bindK hg (Grade.le_refl' k) f
    (fun f' => bindK hh (Grade.le_refl' k) x (fun a => pureK (f' a)))

/-- `map2` at a sufficient grade: `apK` after `map`, exactly as `map2` is
    `ap` after `map`. -/
def map2K (hg : g ⊆ k) (hh : h ⊆ k) (f : α → β → γ) (x : Graded g α) (y : Graded h β) :
    Graded k γ :=
  apK hg hh (map f x) y

-- Reduction lemmas: `apK`'s own ok/err shapes, the mirror of
-- `ap_ok_ok`/`ap_err_left`/`ap_ok_err`, all `rfl` for the same reason
-- `bindK_ok`/`bindK_err` already are — every hypothesis threaded through
-- is a `Prop`, so which one is supplied never affects the reduction.

theorem apK_ok_ok (hg : g ⊆ k) (hh : h ⊆ k) (f' : α → β) (a : α) :
    apK hg hh (Graded.ok f' : Graded g (α → β)) (Graded.ok a : Graded h α) =
      Graded.ok (f' a) := rfl

theorem apK_err_left (hg : g ⊆ k) (hh : h ⊆ k) (e : Err) (he : e ∈ g) (x : Graded h α) :
    apK hg hh (Graded.err e he : Graded g (α → β)) x = Graded.err e (hg he) := rfl

theorem apK_ok_err (hg : g ⊆ k) (hh : h ⊆ k) (f' : α → β) (e : Err) (he : e ∈ h) :
    apK hg hh (Graded.ok f' : Graded g (α → β)) (Graded.err e he : Graded h α) =
      Graded.err e (hh he) := rfl

-- ---------------------------------------------------------------------
-- `apFlippedK`: the other sequencing order, at the *same* sufficient
-- grade `k` — built so `apK_flip` below can ask its question at one
-- grade instead of two.

/-- `apK`, sequenced the other way: the argument first, then the
    function — the sufficient-grade mirror of `apFlipped`, landing at the
    same target grade `k` as `apK` rather than at a second, differently-
    joined grade. -/
def apFlippedK (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β)) (x : Graded h α) :
    Graded k β :=
  bindK hh (Grade.le_refl' k) x
    (fun a => bindK hg (Grade.le_refl' k) f (fun f' => pureK (f' a)))

theorem apFlippedK_ok_ok (hg : g ⊆ k) (hh : h ⊆ k) (f' : α → β) (a : α) :
    apFlippedK hg hh (Graded.ok f' : Graded g (α → β)) (Graded.ok a : Graded h α) =
      Graded.ok (f' a) := rfl

theorem apFlippedK_err_right (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β))
    (e : Err) (he : e ∈ h) :
    apFlippedK hg hh f (Graded.err e he : Graded h α) = Graded.err e (hh he) := rfl

theorem apFlippedK_ok_err (hg : g ⊆ k) (hh : h ⊆ k) (a : α) (e : Err) (he : e ∈ g) :
    apFlippedK hg hh (Graded.err e he : Graded g (α → β)) (Graded.ok a : Graded h α) =
      Graded.err e (hg he) := rfl

-- ---------------------------------------------------------------------
-- The four applicative laws, cast-free. Every one of them mentions only
-- `Grade.le_refl'` — the hypothesis that lets `pureK` land at `k`
-- directly — never a unit or associativity lemma: at a common sufficient
-- grade there is no `∅` anywhere in these statements for a unit law to
-- collapse, and no re-association of a `join` for an associativity law to
-- justify. The property these laws consume is the same "order" tag
-- `bindK`'s own three laws already carry, not a new one.

theorem apK_pure_id (hh : h ⊆ k) (x : Graded h α) :
    apK (Grade.le_refl' k) hh (pureK (@id α) : Graded k (α → α)) x = widen hh x := by
  cases x with
  | ok a => rfl
  | err e he => rfl

theorem apK_pure_pure (f : α → β) (a : α) :
    apK (Grade.le_refl' k) (Grade.le_refl' k) (pureK f : Graded k (α → β))
        (pureK a : Graded k α) =
      (pureK (f a) : Graded k β) := rfl

/-- (interchange) At a common sufficient grade `k` there is only one
    grade in sight, so unlike `ap_interchange` (which needs `Grade.join_bot`
    and `Grade.bot_join` separately, one per side) this needs no property
    beyond `pureK` landing directly at `k` on both sides. -/
theorem apK_interchange (hg : g ⊆ k) (u : Graded g (α → β)) (a : α) :
    apK hg (Grade.le_refl' k) u (pureK a : Graded k α) =
      apK (Grade.le_refl' k) hg (pureK (fun f => f a) : Graded k ((α → β) → β)) u := by
  cases u with
  | ok f' => rfl
  | err e he => rfl

theorem apK_comp (hg : g ⊆ k) (hg' : g' ⊆ k) (hj : j ⊆ k)
    (u : Graded g (β → γ)) (v : Graded g' (α → β)) (w : Graded j α) :
    apK (Grade.le_refl' k) hj
        (apK (Grade.le_refl' k) hg'
          (apK (Grade.le_refl' k) hg
            (pureK Function.comp : Graded k ((β → γ) → (α → β) → α → γ)) u) v) w =
      apK hg (Grade.le_refl' k) u (apK hg' hj v w) := by
  cases u with
  | err e he => rfl
  | ok uf =>
    cases v with
    | err e he => rfl
    | ok vf =>
      cases w with
      | err e he => rfl
      | ok wa => rfl

-- ---------------------------------------------------------------------
-- `apK_flip`: the finding this step exists to make. `ap_flip` needs
-- `Grade.join_comm` *by construction* — it compares `ap`'s grade
-- `Grade.join g h` against `apFlipped`'s `Grade.join h g`, two different
-- expressions for the same grade. At a common sufficient grade `k`,
-- `apK` and `apFlippedK` both already land in `Graded k β`: there is no
-- second expression for the same grade anywhere, so there is nothing for
-- `Grade.join_comm` to relate. This is the one place in this file
-- structurally shaped like the union-graded theorem that *does* need
-- commutativity, and it needs no property at all — commutativity, on this
-- evidence, was a cost of *computing* the grade exactly (so that the two
-- orderings had to be reconciled after the fact), not a requirement of
-- the applicative structure itself.

theorem apK_flip (hg : g ⊆ k) (hh : h ⊆ k) (f : Graded g (α → β)) (x : Graded h α)
    (honeok : (∃ f', f = Graded.ok f') ∨ (∃ a, x = Graded.ok a)) :
    apK hg hh f x = apFlippedK hg hh f x := by
  rcases honeok with ⟨f', rfl⟩ | ⟨a, rfl⟩
  · cases x with
    | ok a => rw [apK_ok_ok, apFlippedK_ok_ok]
    | err e he => rw [apK_ok_err, apFlippedK_err_right]
  · cases f with
    | ok f' => rw [apK_ok_ok, apFlippedK_ok_ok]
    | err e he => rw [apK_err_left, apFlippedK_ok_err]

-- ---------------------------------------------------------------------
-- Instantiating `apK` at the exact union `Grade.join g h`, along the same
-- two inclusions `Graded.ap` itself uses, recovers `ap` — the applicative
-- mirror of `bind_eq_bindK`.
/-- BRIDGE -/
theorem ap_eq_apK (f : Graded g (α → β)) (x : Graded h α) :
    ap f x = apK (Grade.le_join_left g h) (Grade.le_join_right g h) f x := by
  cases f with
  | ok f' =>
    cases x with
    | ok a => rw [ap_ok_ok, apK_ok_ok]
    | err e he => rw [ap_ok_err, apK_ok_err]
  | err e he => rw [ap_err_left, apK_err_left]

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
      cases hfx : f x with
      | err e he =>
          rw [traverseK_cons_err_left hg f x xs e he hfx] at h
          exact absurd h (by simp)
      | ok b =>
          cases hxs : traverseK hg f xs with
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
      cases hfx : f x with
      | err e he =>
          rw [traverse_cons, hfx]
          simp only [map2, map, ap_err_left, cast_err, map2K, apK_err_left]
      | ok b =>
          cases hxs : traverse f xs with
          | err e he =>
              rw [traverse_cons, hfx, hxs]
              simp only [map2, map, ap_ok_err, cast_err, map2K, apK_ok_err]
          | ok l =>
              rw [traverse_cons, hfx, hxs]
              simp only [map2, map, ap_ok_ok, cast_ok, map2K, apK_ok_ok]

-- ---------------------------------------------------------------------
-- `Comp.apK`: the composed applicative at a *pair* of sufficient grades.
-- `Comp g h α` ([compose]) already generalises over any two grades, so no
-- second carrier is needed — "sufficient" here means supplying `Comp`'s
-- own two indices as caller-chosen bounds `k1`/`k2` instead of the
-- componentwise joins `Comp.ap` computes. Built through `map2K`/`apK`
-- exactly as `Comp.ap` is built through `Graded.map2`/`Graded.ap`: outer
-- combine at `k1`, with the *inner* `apK` (at `k2`) threaded through as
-- the combining function.

section CompK

variable {g' h' j' k1 k2 : Grade Err} {α β γ δ : Type u}

/-- The composed applicative at a sufficient grade *pair* `(k1, k2)`. -/
def Comp.apK (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (ff : Comp g h (α → β)) (xx : Comp g' h' α) : Comp k1 k2 β :=
  Graded.map2K hg hg'
    (fun (F : Graded h (α → β)) (X : Graded h' α) => Graded.apK hh hh' F X) ff xx

-- Reduction lemmas: the two-coordinate mirror of `apK_ok_ok`/
-- `apK_err_left`/`apK_ok_err`, all `rfl` for the same reason.

theorem Comp.apK_ok_ok (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (F : Graded h (α → β)) (X : Graded h' α) :
    Comp.apK hg hg' hh hh' (Graded.ok F : Comp g h (α → β)) (Graded.ok X : Comp g' h' α) =
      Graded.ok (Graded.apK hh hh' F X) := rfl

theorem Comp.apK_err_left (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (e : Err) (he : e ∈ g) (xx : Comp g' h' α) :
    Comp.apK hg hg' hh hh' (Graded.err e he : Comp g h (α → β)) xx =
      Graded.err e (hg he) := rfl

theorem Comp.apK_ok_err (hg : g ⊆ k1) (hg' : g' ⊆ k1) (hh : h ⊆ k2) (hh' : h' ⊆ k2)
    (F : Graded h (α → β)) (e : Err) (he : e ∈ g') :
    Comp.apK hg hg' hh hh' (Graded.ok F : Comp g h (α → β)) (Graded.err e he : Comp g' h' α) =
      Graded.err e (hg' he) := rfl

-- ---------------------------------------------------------------------
-- The headline measurement. `Comp.ap_interchange`, stated at the computed
-- componentwise-join grade, needs `Comp.castGH` on both sides — two
-- `Graded.cast`s per side, driven by `Grade.join_bot`/`Grade.bot_join` in
-- each of the two components separately. At a common sufficient grade
-- pair, both sides of `Comp.apK`'s interchange law already land in
-- `Comp k1 k2 β`: **zero** casts, and (unlike `Comp.ap_interchange`,
-- which cites `Graded.ap_interchange` — unit, twice — in its `ok`
-- branch) the fully case-split proof below closes by `rfl` alone: there
-- is no property left to cite.

theorem Comp.apK_interchange (hg : g ⊆ k1) (hh : h ⊆ k2) (u : Comp g h (α → β)) (a : α) :
    Comp.apK hg (Grade.bot_le k1) hh (Grade.bot_le k2) u (Comp.pure a) =
      Comp.apK (Grade.bot_le k1) hg (Grade.bot_le k2) hh
        (Comp.pure (fun f => f a) : Comp Grade.bot Grade.bot ((α → β) → β)) u := by
  cases u with
  | err e he => rfl
  | ok F =>
    cases F with
    | ok f' => rfl
    | err e he => rfl

end CompK

-- ---------------------------------------------------------------------
-- `GradedHomK`: grade morphisms at a sufficient grade. `GradedHom`
-- ([morphisms](../docs/design.md#morphisms)) packages a grade map that is
-- a join-semilattice homomorphism (`gmap_join`, `gmap_bot`), because its
-- `hom_bind` law is stated against `Graded.bind`'s *computed* union grade
-- and needs a cast (`gmap_join g h`) to make both sides of `hom_bind`
-- land in the same type. At a caller-chosen sufficient grade `k` there is
-- nothing to compute: `hom_bindK`'s two sides both land in `Graded (gmap
-- k) β` for any `k` merely known to contain `g` and `h`, so the
-- obligation that makes the record typecheck at all drops from
-- "join-semilattice homomorphism" to plain monotonicity (`gmap_mono`) —
-- the same order-in, algebra-out pattern `bindK`, `apK` and `traverseK`
-- each found one level down, now found one level up: at the level of what
-- a *morphism between graded designs* must satisfy, which P3200 does not
-- currently state at all.

section Morphism

variable {Err' : Type u} [DecidableEq Err']

/-- A graded monad morphism at a sufficient grade: a *monotone* map on
    grades (`gmap_mono`), together with a carrier-level family, natural at
    every grade and payload type, that commutes with `bindK`/`pureK`
    outright — no cast anywhere. `gmap_mono` sends `hg : g ⊆ k` and
    `hh : h ⊆ k` to proofs of `gmap g ⊆ gmap k` and `gmap h ⊆ gmap k`, so
    both sides of `hom_bindK` land in `Graded (gmap k) β` directly: there
    is no second expression for that grade anywhere for a homomorphism law
    to be needed to identify, the same fact `bindK_irrel`/`traverseK_irrel`
    already rest on. This *replaces* `GradedHom`'s `gmap_join`/`gmap_bot`
    fields, it does not sit beside them — a `GradedHomK` is not a
    `GradedHom` with extra fields, it is a different, strictly weaker
    obligation on the same shape of data. -/
structure GradedHomK (Err Err' : Type u) [DecidableEq Err] [DecidableEq Err'] where
  gmap : Grade Err → Grade Err'
  gmap_mono : ∀ {g h : Grade Err}, g ⊆ h → gmap g ⊆ gmap h
  hom : ∀ {g : Grade Err} {α : Type v}, Graded g α → Graded (gmap g) α
  hom_bindK : ∀ {g h k : Grade Err} {α β : Type v} (hg : g ⊆ k) (hh : h ⊆ k)
      (x : Graded g α) (f : α → Graded h β),
      hom (bindK hg hh x f) = bindK (gmap_mono hg) (gmap_mono hh) (hom x) (fun a => hom (f a))
  hom_pureK : ∀ {k : Grade Err} {α : Type v} (a : α),
      hom (pureK a : Graded k α) = pureK a

/-- The one instance the C++ design uses, at the sufficient-grade layer:
    renaming, with the *same* underlying `gmap`/`hom` functions
    `renameHom` packages at the union-graded layer — only the obligation
    each structure asks of them differs. `hom_pureK` is `rfl`: `pureK a`
    is `fromEmpty a` regardless of grade, and `rename` of an `ok` is `ok`
    regardless of grade, so both sides reduce to `Graded.ok a` before any
    grade is even inspected. `hom_bindK`'s `ok` leaf needs `bindK_ok` to
    turn `bindK hg hh (Graded.ok a) f` into `widen hh (f a)` *before*
    `rename_widen` can fire — `rename_widen` talks about `rename φ (widen
    _ _)`, not about the unreduced `bindK`, so the rewrite has to happen in
    that order. -/
def renameHomK (φ : Err → Err') : GradedHomK Err Err' where
  gmap := Grade.rename φ
  gmap_mono := Grade.rename_mono φ
  hom := rename φ
  hom_bindK := by
    intro g h k α β hg hh x f
    cases x with
    | ok a =>
        rw [bindK_ok, rename_ok, bindK_ok, rename_widen]
    | err e he =>
        simp only [bindK_err, rename_err]
  hom_pureK := fun _ => rfl

-- ---------------------------------------------------------------------
-- Naturality of `rename` against `apK`/`map2K`/`traverseK`, cast-free —
-- the sufficient-grade analogues of `rename_ap`/`rename_map2`/
-- `traverse_rename`, one level up. Unlike those three, which each need
-- `Grade.rename_join` to transport a *computed* union grade, `rename_apK`
-- needs only `Grade.rename_mono`: `apK`'s target grade `k` is a bound the
-- caller supplies, not a join `rename` has to distribute over, so there is
-- no equation between two different expressions for the same grade
-- anywhere in these three statements.
--
-- `rename_cast` ([morphisms](../docs/design.md#morphisms)) has **no
-- analogue here, and none is missing** — it exists at the union-graded
-- layer only because that layer's own laws produce `cast`s for `rename`
-- to commute with; the sufficient-grade layer never produces one in the
-- first place, so there is nothing for a `rename`/`cast` commutation
-- lemma to be stated about.

theorem rename_apK (φ : Err → Err') (hg : g ⊆ k) (hh : h ⊆ k)
    (f : Graded g (α → β)) (x : Graded h α) :
    rename φ (apK hg hh f x) =
      apK (Grade.rename_mono φ hg) (Grade.rename_mono φ hh) (rename φ f) (rename φ x) := by
  cases f with
  | ok f' =>
      cases x with
      | ok a => rw [apK_ok_ok, rename_ok, rename_ok, rename_ok, apK_ok_ok]
      | err e he => rw [apK_ok_err, rename_err, rename_ok, rename_err, apK_ok_err]
  | err e he => rw [apK_err_left, rename_err, rename_err, apK_err_left]

theorem rename_map2K (φ : Err → Err') (hg : g ⊆ k) (hh : h ⊆ k)
    (kk : α → β → γ) (x : Graded g α) (y : Graded h β) :
    rename φ (map2K hg hh kk x y) =
      map2K (Grade.rename_mono φ hg) (Grade.rename_mono φ hh) kk (rename φ x) (rename φ y) := by
  unfold map2K
  rw [rename_apK, rename_map]

theorem traverseK_rename (φ : Err → Err') (hg : g ⊆ k) (f : α → Graded g β) (xs : List α) :
    rename φ (traverseK hg f xs) = traverseK (Grade.rename_mono φ hg) (rename φ ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [traverseK_cons, rename_map2K, Function.comp_apply, ih]

-- ---------------------------------------------------------------------
-- The bridge between `GradedHom` and `GradedHomK`. Bridging two
-- *structures* is not the same as bridging two operations
-- (`bind_eq_bindK`, `ap_eq_apK`): those instantiate one operation's
-- sufficient grade at the other's computed one and get `rfl`.
-- `GradedHom`/`GradedHomK` are two different obligations on the same
-- shape of data, and only one direction goes through.
--
-- **Forward: a `GradedHom`'s `gmap` is always monotone.** `gmap_join g h`
-- says `gmap (Grade.join g h) = Grade.join (gmap g) (gmap h)`; given
-- `hgh : g ⊆ h`, `Grade.join_eq_right_of_le hgh` collapses the left side
-- to `gmap h`, and `Grade.le_join_left` on the right recovers `gmap g ⊆
-- gmap h`. This is genuinely the only piece that transfers: it derives
-- `GradedHomK`'s `gmap_mono` field from `GradedHom`'s `gmap_join` field,
-- using nothing about `hom` at all.
--
-- **No converse, and no full structure map either — both for the same
-- reason.** A monotone `gmap` need not preserve `join`/`bot` (the
-- counter-instance below is exactly such a `gmap`), so `GradedHomK →
-- GradedHom` is impossible in general, as the step predicted. What is
-- *not* obvious ahead of time: even the forward direction stops at
-- `gmap_mono` alone. Lifting a full `GradedHom` into a full `GradedHomK`
-- (same `gmap`, same `hom`, reusing `H.hom_bind`/`H.hom_pure` to fill in
-- `hom_bindK`/`hom_pureK`) would need `H.hom` to commute with `widen` at
-- an arbitrary sufficient grade `k`, not merely at the one exact union
-- grade `hom_bind` is stated at — and `widen` ([subsumption](../docs/design.md#carrier))
-- is a primitive of `Graded`, not something `bind`/`pure` define, so
-- `GradedHom`'s two fields (`hom_bind`, `hom_pure`) say nothing about how
-- `hom` treats it. `renameHomK` above only exists because `rename`
-- (a *concrete* function, not an abstract `hom`) happens to satisfy
-- `rename_widen` as a separately proved fact. So the bridge is not just
-- one-directional between the two structures; even its one working
-- direction carries only `gmap`'s obligation, not `hom`'s.
theorem GradedHom.gmap_mono (H : GradedHom Err Err') {g h : Grade Err} (hgh : g ⊆ h) :
    H.gmap g ⊆ H.gmap h := by
  have hj := H.gmap_join g h
  rw [Grade.join_eq_right_of_le hgh] at hj
  rw [hj]
  exact Grade.le_join_left _ _

-- ---------------------------------------------------------------------
-- The counter-instance: a monotone `gmap` that is not a join-semilattice
-- homomorphism, with a working `hom` satisfying every `GradedHomK` field —
-- the concrete witness that the weaker obligation genuinely admits more
-- than the stronger one, in the way `Nat` did for
-- [grade-obligations](../docs/design.md#obligations). `constHomK g₀ e₀
-- he₀` sends *every* grade to the fixed nonempty grade `g₀`, and every
-- carrier to `ok`/`err e₀` according to its own shape, discarding the
-- actual error entirely. It is trivially monotone (`gmap g ⊆ gmap h` is
-- `g₀ ⊆ g₀`, true regardless of `g`, `h`) and it satisfies `gmap_join`
-- unconditionally (`Grade.join g₀ g₀ = g₀` by idempotence, so both sides
-- of `gmap_join` are the literal grade `g₀`) — but it refutes `gmap_bot`
-- whenever `g₀ ≠ Grade.bot`, since `gmap Grade.bot = g₀ ≠ Grade.bot`.
-- So `constHomK`'s `gmap` cannot be completed into a `GradedHom` at all
-- ([grade-obligations]'s `Nat` played the same role one layer down: a
-- concrete inhabitant of the weaker class that refutes a specific field
-- of the stronger one), while `hom_bindK`/`hom_pureK` hold outright,
-- because `hom` throws away enough information that neither side of
-- either law has anything left to distinguish.

section CounterInstance

variable {e₀ : Err'} {g₀ : Grade Err'}

/-- The carrier-level half of the counter-instance: collapse every `ok` to
    itself and every `err` to the one fixed witness `e₀`, regardless of
    the source grade or the actual error carried. -/
def constHom (e₀ : Err') (he₀ : e₀ ∈ g₀) {g : Grade Err} {α : Type v} :
    Graded g α → Graded g₀ α
  | .ok a => .ok a
  | .err _ _ => .err e₀ he₀

/-- The constant-grade morphism: every source grade maps to the fixed
    `g₀`, and `constHom` is the carrier family. Instantiates every
    `GradedHomK` field with `rfl`, because `constHom` never inspects `g`,
    `h`, `k`, or the threaded `⊆` proofs — only whether its argument is
    `ok` or `err`. -/
def constHomK (e₀ : Err') (he₀ : e₀ ∈ g₀) : GradedHomK Err Err' where
  gmap := fun _ => g₀
  gmap_mono := fun _ => Grade.le_refl' g₀
  hom := constHom e₀ he₀
  hom_bindK := by
    intro g h k α β hg hh x f
    cases x with
    | ok a =>
        cases hfa : f a with
        | ok b => simp only [bindK_ok, hfa, widen_ok, constHom]
        | err e he => simp only [bindK_ok, hfa, widen_err, constHom]
    | err e he => simp only [bindK_err, constHom]
  hom_pureK := fun _ => rfl

/-- `constHomK`'s `gmap` cannot be completed into a `GradedHom`: it fails
    the `gmap_bot` field a `GradedHom` would require, whenever the target
    grade `g₀` is nonempty. This is the refutation half of the
    counter-instance — `gmap_mono` alone (which `constHomK` does satisfy)
    is not enough to build a `GradedHom`, confirming the bridge above has
    no converse. -/
theorem constHomK_not_gmap_bot (he₀ : e₀ ∈ g₀) :
    (fun (_ : Grade Err) => g₀) (Grade.bot : Grade Err) ≠ (Grade.bot : Grade Err') := by
  intro h
  have h' : g₀ = (Grade.bot : Grade Err') := h
  rw [h'] at he₀
  exact absurd he₀ (Finset.notMem_empty e₀)

end CounterInstance

end Morphism

end Graded
