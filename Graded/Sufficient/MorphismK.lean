import Graded.Sufficient.TraversableK
import Graded.Morphism

/-! `GradedHomK` and the bridge from `GradedHom`.

    Split out of the former single `Graded/Sufficient.lean` by
    [module-split]; `Graded.Sufficient` is now a re-export shim over the
    six pieces, so every existing import keeps working. -/

namespace Graded

variable {Err : Type u} [DecidableEq Err]
variable {g h j k : Grade Err} {α β γ : Type v}

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
  cases f using Graded.rec' with
  | ok f' =>
      cases x using Graded.rec' with
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
-- **No converse.** A monotone `gmap` need not preserve `join`/`bot` (the
-- counter-instance below is exactly such a `gmap`), so `GradedHomK →
-- GradedHom` is impossible in general, as the step predicted, and
-- `constHomK_not_gmap_bot` is the standing witness.
--
-- **Forward, in full — corrected by [morphism-bridge].** An earlier
-- revision of this comment said the forward direction stops at
-- `gmap_mono` alone: that lifting a whole `GradedHom` to a whole
-- `GradedHomK` would need `hom` to commute with `widen` at an arbitrary
-- sufficient grade, which `hom_bind`/`hom_pure` cannot supply, and that
-- `renameHomK` therefore only existed because `rename` happens to satisfy
-- `rename_widen` as a separately proved fact. The diagnosis was right and
-- the conclusion was wrong. `widen` really is a primitive neither field
-- mentions, so the obligation has to be *stated* — but stating it is one
-- field (`GradedHom.hom_widen`), and with it the lift is total.
-- `GradedHom.toGradedHomK` below is that lift, and `renameHomK` is now
-- its image of `renameHom` rather than an independent construction.
--
-- The route matters, and it is why this was missed. Discharging
-- `hom_bindK` by case-splitting on the carrier exposes its `err` leaf at
-- payload type `β` on one side and `α` on the other, which additionally
-- requires `hom`'s action on errors to be natural in the payload — a
-- second obligation, and the one [migration-review] recorded as
-- necessary. It is not necessary. Going through `bindK_eq_widen_bind`
-- instead never splits: both sides reduce to a `widen` of `hom (bind x
-- f)`, `hom_bind` rewrites underneath, and `widen_cast` absorbs the
-- `cast (gmap_join g h)` the union-graded law carries. Payload
-- naturality is a real property, and it belongs to the payload-bearing
-- work, not to this bridge.

/-- `bindK` is `bind` widened to the nominated grade: sequencing at a
    sufficient `k` is sequencing at the exact union and then subsuming.
    Both sides thread a `Prop` inclusion, so the `ok` case is
    `widen_widen` and the `err` case is `rfl` by proof irrelevance.

    This is a fourth bridge beside `bind_eq_bindK`/`ap_eq_apK`/
    `traverse_eq_traverseK`, and it runs the other way: those instantiate
    a sufficient grade at the computed union, this factors a
    sufficient-grade operation through the computed one. That direction is
    what makes `GradedHom.toGradedHomK` go through without case-splitting
    on the carrier. -/
theorem bindK_eq_widen_bind (hg : g ⊆ k) (hh : h ⊆ k) (x : Graded g α)
    (f : α → Graded h β) :
    bindK hg hh x f = widen (Grade.join_le hg hh) (bind x f) := by
  cases x using Graded.rec' with
  | ok a =>
      change widen hh (f a)
        = widen (Grade.join_le hg hh) (widen (Grade.le_join_right g h) (f a))
      rw [widen_widen]
  | err e he => rfl

theorem GradedHom.gmap_mono (H : GradedHom Err Err') {g h : Grade Err} (hgh : g ⊆ h) :
    H.gmap g ⊆ H.gmap h := by
  have hj := H.gmap_join g h
  rw [Grade.join_eq_right_of_le hgh] at hj
  rw [hj]
  exact Grade.le_join_left _ _

/-- `hom` preserves `ok` at *every* grade, not only at `Grade.bot` where
    `hom_pure` states it. At `bot`, transporting `hom_pure` back across
    `gmap_bot` gives it; at any `k`, `Graded.ok a` is `widen (bot_le k)`
    of the `bot`-graded `ok`, and `hom_widen` carries it up. -/
theorem GradedHom.hom_ok (H : GradedHom Err Err') {k : Grade Err} {α : Type v} (a : α) :
    H.hom (Graded.ok a : Graded k α) = Graded.ok a := by
  have hbot : H.hom (Graded.ok a : Graded (Grade.bot : Grade Err) α) = Graded.ok a := by
    have hp : Graded.cast H.gmap_bot
        (H.hom (Graded.ok a : Graded (Grade.bot : Grade Err) α))
          = (Graded.ok a : Graded (Grade.bot : Grade Err') α) := H.hom_pure a
    have h2 := congrArg (Graded.cast (H.gmap_bot).symm) hp
    rw [cast_cast, cast_ok] at h2
    exact h2
  change H.hom (widen (Grade.bot_le k) (Graded.ok a : Graded (Grade.bot : Grade Err) α))
      = Graded.ok a
  rw [H.hom_widen _ (H.gmap_mono (Grade.bot_le k)), hbot, widen_ok]

/-- **The forward bridge, in full.** Every `GradedHom` is a `GradedHomK`
    over the same `gmap` and the same `hom`: the grade obligation weakens
    from join-semilattice homomorphism to monotonicity (`gmap_mono`), and
    the carrier obligation is discharged from `hom_bind`/`hom_pure`
    together with `hom_widen`.

    Neither law needs a case split. `hom_bindK`: rewrite both sides with
    `bindK_eq_widen_bind`, push `hom` through the outer `widen` with
    `hom_widen`, rewrite the inside with `hom_bind`, and let `widen_cast`
    absorb the `cast (gmap_join g h)` that the union-graded law carries.
    `hom_pureK` is `GradedHom.hom_ok`, since `pureK` is `fromEmpty` is
    `ok` at every grade.

    There is still no converse: `constHomK` below is a `GradedHomK` whose
    `gmap` refutes `gmap_bot`, so it cannot be completed into a
    `GradedHom` at all. -/
def GradedHom.toGradedHomK (H : GradedHom Err Err') : GradedHomK Err Err' where
  gmap := H.gmap
  gmap_mono := H.gmap_mono
  hom := H.hom
  hom_bindK := by
    intro g h k α β hg hh x f
    rw [bindK_eq_widen_bind, H.hom_widen _ (H.gmap_mono (Grade.join_le hg hh)),
      bindK_eq_widen_bind, ← H.hom_bind x f, widen_cast]
  hom_pureK := fun a => H.hom_ok a

/-- The one instance the C++ design uses, at the sufficient-grade layer:
    renaming. **No longer built by hand** — [morphism-bridge] made
    `GradedHom.toGradedHomK` total, so this is the image of `renameHom`
    under that lift, and nothing about renaming is special any more.

    The hand-built version discharged `hom_bindK` by case-splitting on the
    carrier, needing `bindK_ok` to expose a `widen` before `rename_widen`
    could fire on it. The general lift needs no split at all. What used to
    read as "renaming happens to satisfy `rename_widen`, so this one
    morphism can be written" now reads as "renaming satisfies
    `GradedHom.hom_widen`, like every morphism that can be written", which
    is the honest version of the same fact.

    Defined below `GradedHom.toGradedHomK` for that reason; the forward
    reference is why this sits after the bridge rather than beside
    `GradedHomK`. -/
def renameHomK (φ : Err → Err') : GradedHomK Err Err' :=
  (renameHom φ).toGradedHomK

/-- `renameHomK` is `rename` on the nose, lift or no lift: the bridge
    reuses `H.hom` unchanged, so factoring the definition through it
    changed no behaviour. `rfl`, which is the point. -/
theorem renameHomK_hom (φ : Err → Err') {g : Grade Err} {α : Type v} (x : Graded g α) :
    (renameHomK φ).hom x = rename φ x := rfl

/-- And its grade map is `Grade.rename`, likewise unchanged. -/
theorem renameHomK_gmap (φ : Err → Err') : (renameHomK φ).gmap = Grade.rename φ := rfl

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
    cases x using Graded.rec' with
    | ok a =>
        cases hfa : f a using Graded.rec' with
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
