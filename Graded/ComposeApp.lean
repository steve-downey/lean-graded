import Graded.Compose
import Graded.Traverse

/-! The composed applicative: `Graded g` and `Graded h` kept genuinely
    nested, the structure the classical Traversable composition law is
    actually stated against ([compose-flatten] tested only the *flattened*
    form and found it false; see `docs/design.md#graded-traversable-composition`).

    In C++, `expected<expected<T, error_set<Es1...>>, error_set<Es2...>>`
    has two layers, and the design question this module answers is: what is
    the applicative structure of that *nested* type, before anyone chooses
    to collapse it with `flatten`? The natural grade of a nested value is
    the *pair* `(g, h)` — outer and inner, tracked separately in the
    product pomonoid `Grade Err × Grade Err` (componentwise `join`, never
    identified into one `Finset`) — not the union `flatten` computes.
    `Comp g h α := Graded g (Graded h α)` is that nested carrier, indexed by
    both grades at once; `Comp.ap` combines two `Comp` values by running the
    *outer* `Graded.ap` with the *inner* `Graded.ap` lifted inside as the
    combining function, landing at `Comp (g ⊔ g') (h ⊔ h')` — exactly
    `Compose`'s own applicative instance, specialised to this carrier.

    Every definition below fully qualifies the single-layer operations it
    reuses (`Graded.map`, `Graded.ap`, `Graded.map2`, `Graded.widen`,
    `Graded.cast`) rather than writing them bare. Lean's dotted-name
    recursion sugar means a bare `map` inside `def Comp.map := map (map f)`
    resolves to `Comp.map` itself, not `Graded.map` — a real trap this file
    hit on the first attempt, not a style preference.

    Universe note, inherited from `Graded.Compose`: `Graded h α` lives in
    `Type (max u v)`, a genuinely higher universe than the bare payload `α`,
    and `Monad.bind`'s signature ties its two payload type variables to one
    shared universe. `Comp` nests carriers *twice*, so this file pins every
    payload to `Type u` — the same universe as `Err` — exactly as
    `Graded/Compose.lean` already does, for the same reason. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]
variable {g g' h h' j j' : Grade Err} {α β γ δ : Type u}

-- ---------------------------------------------------------------------
-- The composite carrier, and the two double-indexed transport helpers
-- (`Comp.widenGH`, `Comp.castGH`) every law below needs: local plumbing
-- built from `Graded.widen`/`Graded.cast` applied once per layer, not a
-- fork of either.

/-- The composite carrier, with the two grades kept as *separate* indices
    — not joined. `abbrev`, not `def`: Lean's instance search does not see
    through a plain `def` (this cost [canonical-representation] a rebuild;
    `Grade` itself is an `abbrev` for the same reason), and this file's test
    module needs instances to be found through `Comp g h α`. -/
abbrev Comp (g h : Grade Err) (α : Type u) : Type u := Graded g (Graded h α)

/-- The composite `pure`: both layers at grade `⊥`. -/
def Comp.pure (a : α) : Comp (Grade.bot : Grade Err) Grade.bot α :=
  Graded.ok (Graded.ok a)

/-- The composite functor: `Graded.map` lifted through both layers. -/
def Comp.map (f : α → β) : Comp g h α → Comp g h β := Graded.map (Graded.map f)

/-- The composed applicative: outer layers combine with the outer `ap`,
    inner layers with the inner `ap` lifted inside — exactly `Compose`'s
    own instance. The grade is the *pair* `(g ⊔ g', h ⊔ h')`, joined
    componentwise: the product pomonoid. -/
def Comp.ap (ff : Comp g h (α → β)) (xx : Comp g' h' α) :
    Comp (Grade.join g g') (Grade.join h h') β :=
  Graded.map2 (fun f x => Graded.ap f x) ff xx

/-- `Comp`'s own `map2`, built from `Comp.ap`/`Comp.map` exactly as
    `Graded.map2` is built from `ap`/`map`. Used by `traverseComp` below. -/
def Comp.map2 (k : α → β → γ) (x : Comp g h α) (y : Comp g' h' β) :
    Comp (Grade.join g g') (Grade.join h h') γ :=
  Comp.ap (Comp.map k x) y

/-- Widen both components of a `Comp` value independently: `Graded.widen`
    at the outer layer, `Graded.widen` lifted through `Graded.map` at the
    inner layer. Local plumbing, not a new primitive. -/
def Comp.widenGH (hg : g ⊆ g') (hh : h ⊆ h') : Comp g h α → Comp g' h' α :=
  fun x => Graded.widen hg (Graded.map (Graded.widen hh) x)

/-- Cast both components of a `Comp` value independently along grade
    equalities: `Graded.cast` at each layer. Local plumbing, used by every
    applicative law below in place of a single-layer `cast` — the
    "two-cast technique" [applicative-from-monad] used for `ap_interchange`,
    applied once per component. -/
def Comp.castGH (eg : g = g') (eh : h = h') : Comp g h α → Comp g' h' α :=
  fun x => Graded.cast eg (Graded.map (Graded.cast eh) x)

-- ---------------------------------------------------------------------
-- Functor laws: no named property, exactly as `Graded.map_id`/`map_comp`.

theorem Comp.map_id (x : Comp g h α) : Comp.map (@id α) x = x := by
  simp only [Comp.map]
  cases x with
  | ok y => exact congrArg Graded.ok (Graded.map_id y)
  | err e he => rfl

theorem Comp.map_comp (f : α → β) (k : β → γ) (x : Comp g h α) :
    Comp.map (k ∘ f) x = Comp.map k (Comp.map f x) := by
  simp only [Comp.map]
  cases x with
  | ok y => exact congrArg Graded.ok (Graded.map_comp f k y)
  | err e he => rfl

-- ---------------------------------------------------------------------
-- Reduction lemmas: how `Comp.ap` computes on each *outer* shape, leaving
-- the inner `Graded` values opaque. These are `Graded.ap`'s own
-- `ap_ok_ok`/`ap_err_left`/`ap_ok_err` instantiated at the outer layer,
-- with the inner `Graded.ap` call as the payload the outer applicative
-- carries — the inner layer's shape is never inspected here, and does not
-- need to be: every law below reaches the inner layer's own general
-- theorem (`Graded.ap_pure_id`, etc.) without ever case-splitting the
-- inner value.

theorem Comp.ap_ok_ok (F : Graded h (α → β)) (X : Graded h' α) :
    Comp.ap (Graded.ok F : Comp g h (α → β)) (Graded.ok X : Comp g' h' α) =
      Graded.ok (Graded.ap F X) := by
  simp only [Comp.ap, Graded.map2, Graded.map, Graded.ap_ok_ok]

theorem Comp.ap_err_left (e : Err) (he : e ∈ g) (xx : Comp g' h' α) :
    Comp.ap (Graded.err e he : Comp g h (α → β)) xx =
      Graded.err e (Grade.le_join_left g g' he) := by
  simp only [Comp.ap, Graded.map2, Graded.map, Graded.ap_err_left]

theorem Comp.ap_ok_err (F : Graded h (α → β)) (e : Err) (he : e ∈ g') :
    Comp.ap (Graded.ok F : Comp g h (α → β)) (Graded.err e he : Comp g' h' α) =
      Graded.err e (Grade.le_join_right g g' he) := by
  simp only [Comp.ap, Graded.map2, Graded.map, Graded.ap_ok_err]

-- ---------------------------------------------------------------------
-- The four applicative laws. Each is `Graded.ap`'s corresponding law
-- consumed *twice*, once per component, via `Comp.castGH` — but the inner
-- layer's own theorem is cited directly (`Graded.ap_pure_id F`, etc.),
-- never re-derived by case-splitting the inner value: only the *outer*
-- shape of each `Comp` argument is ever cased on. **Finding to record**:
-- no branch below ever needs to relate `g` to `h` (or `g'` to `h'`) —
-- every cast is stated and discharged purely in terms of one component's
-- own grades, citing exactly the property [applicative-from-monad] found
-- for the single-layer law. The two components are independent
-- coordinates of a product, and the proofs confirm it: neither ever
-- reaches across for the other's property.

/-- (identity; unit, in each component independently) -/
theorem Comp.ap_pure_id (x : Comp h j α) :
    Comp.castGH (Grade.bot_join h) (Grade.bot_join j)
        (Comp.ap (Comp.pure (@id α) : Comp Grade.bot Grade.bot (α → α)) x) = x := by
  cases x with
  | ok y =>
    show Comp.castGH (Grade.bot_join h) (Grade.bot_join j)
        (Comp.ap (Comp.pure (@id α)) (Graded.ok y)) = Graded.ok y
    simp only [Comp.pure, Comp.ap_ok_ok, Comp.castGH, Graded.map, Graded.cast_ok]
    exact congrArg Graded.ok (Graded.ap_pure_id y)
  | err e he =>
    show Comp.castGH (Grade.bot_join h) (Grade.bot_join j)
        (Comp.ap (Comp.pure (@id α)) (Graded.err e he : Comp h j α)) = Graded.err e he
    simp only [Comp.pure, Comp.ap_ok_err, Comp.castGH, Graded.map, Graded.cast_err]

/-- (homomorphism; unit, in each component independently) -/
theorem Comp.ap_pure_pure (f : α → β) (a : α) :
    Comp.castGH (Grade.bot_join (Grade.bot : Grade Err)) (Grade.bot_join (Grade.bot : Grade Err))
        (Comp.ap (Comp.pure f : Comp Grade.bot Grade.bot (α → β)) (Comp.pure a)) =
      Comp.pure (f a) := by
  simp only [Comp.pure, Comp.ap_ok_ok, Graded.ap_ok_ok, Comp.castGH, Graded.map, Graded.cast_ok]

/-- (interchange; unit, in each component independently, no `Grade.join_comm`
    anywhere — same finding as [applicative-from-monad]'s single-layer
    `ap_interchange`.) -/
theorem Comp.ap_interchange (u : Comp g h (α → β)) (a : α) :
    Comp.castGH (Grade.join_bot g) (Grade.join_bot h) (Comp.ap u (Comp.pure a)) =
      Comp.castGH (Grade.bot_join g) (Grade.bot_join h)
        (Comp.ap (Comp.pure (fun f => f a) : Comp Grade.bot Grade.bot ((α → β) → β)) u) := by
  cases u with
  | ok F =>
    show Comp.castGH (Grade.join_bot g) (Grade.join_bot h)
        (Comp.ap (Graded.ok F : Comp g h (α → β)) (Comp.pure a)) =
      Comp.castGH (Grade.bot_join g) (Grade.bot_join h)
        (Comp.ap (Comp.pure (fun f => f a)) (Graded.ok F))
    simp only [Comp.pure, Comp.ap_ok_ok, Comp.castGH, Graded.map, Graded.cast_ok]
    exact congrArg Graded.ok (Graded.ap_interchange F a)
  | err e he =>
    show Comp.castGH (Grade.join_bot g) (Grade.join_bot h)
        (Comp.ap (Graded.err e he : Comp g h (α → β)) (Comp.pure a)) =
      Comp.castGH (Grade.bot_join g) (Grade.bot_join h)
        (Comp.ap (Comp.pure (fun f => f a)) (Graded.err e he : Comp g h (α → β)))
    simp only [Comp.pure, Comp.ap_err_left, Comp.ap_ok_err, Comp.castGH, Graded.map,
      Graded.cast_err]

/-- (composition; associative + unit, in each component independently, no
    `Grade.join_comm` anywhere.) -/
theorem Comp.ap_comp (u : Comp g h (β → γ)) (v : Comp g' h' (α → β)) (w : Comp j j' α) :
    Comp.castGH
        (by rw [Grade.bot_join, Grade.join_assoc] :
          Grade.join (Grade.join (Grade.join Grade.bot g) g') j = Grade.join g (Grade.join g' j))
        (by rw [Grade.bot_join, Grade.join_assoc] :
          Grade.join (Grade.join (Grade.join Grade.bot h) h') j' = Grade.join h (Grade.join h' j'))
        (Comp.ap (Comp.ap (Comp.ap
            (Comp.pure Function.comp : Comp Grade.bot Grade.bot ((β → γ) → (α → β) → α → γ))
            u) v) w) =
      Comp.ap u (Comp.ap v w) := by
  cases u with
  | err e he =>
    show Comp.castGH _ _
        (Comp.ap (Comp.ap (Comp.ap (Comp.pure Function.comp)
          (Graded.err e he : Comp g h (β → γ))) v) w) =
      Comp.ap (Graded.err e he : Comp g h (β → γ)) (Comp.ap v w)
    simp only [Comp.pure, Comp.ap_ok_err, Comp.ap_err_left, Comp.castGH, Graded.map,
      Graded.cast_err]
  | ok F =>
    cases v with
    | err e he =>
      show Comp.castGH _ _
          (Comp.ap (Comp.ap (Comp.ap (Comp.pure Function.comp) (Graded.ok F : Comp g h (β → γ)))
            (Graded.err e he : Comp g' h' (α → β))) w) =
        Comp.ap (Graded.ok F : Comp g h (β → γ)) (Comp.ap (Graded.err e he) w)
      simp only [Comp.pure, Comp.ap_ok_ok, Comp.ap_ok_err, Comp.ap_err_left, Comp.castGH,
        Graded.map, Graded.cast_err]
    | ok G =>
      cases w with
      | err e he =>
        show Comp.castGH _ _
            (Comp.ap (Comp.ap (Comp.ap (Comp.pure Function.comp) (Graded.ok F : Comp g h (β → γ)))
              (Graded.ok G : Comp g' h' (α → β))) (Graded.err e he : Comp j j' α)) =
          Comp.ap (Graded.ok F : Comp g h (β → γ)) (Comp.ap (Graded.ok G) (Graded.err e he))
        simp only [Comp.pure, Comp.ap_ok_ok, Comp.ap_ok_err, Comp.castGH, Graded.map,
          Graded.cast_err]
      | ok X =>
        show Comp.castGH _ _
            (Comp.ap (Comp.ap (Comp.ap (Comp.pure Function.comp) (Graded.ok F : Comp g h (β → γ)))
              (Graded.ok G : Comp g' h' (α → β))) (Graded.ok X : Comp j j' α)) =
          Comp.ap (Graded.ok F : Comp g h (β → γ)) (Comp.ap (Graded.ok G) (Graded.ok X))
        simp only [Comp.pure, Comp.ap_ok_ok, Comp.castGH, Graded.map, Graded.cast_ok]
        exact congrArg Graded.ok (Graded.ap_comp F G X)

-- ---------------------------------------------------------------------
-- `traverseComp`: the traversal in the composed applicative, uniform in
-- *both* components. Built exactly the way `Graded.traverse` was: an
-- honest, per-element-folded "raw" traversal (`Comp.traverseRaw`, reusing
-- `Graded.foldGrade` once per component — no second `foldGrade`), then a
-- single `Comp.widenGH` along `Graded.foldGrade_le` (once per component)
-- rather than a `cast` along `foldGrade_cons_ne_nil`, so the empty list
-- needs no special case at the definition site, exactly as `traverse`
-- itself needs none.

/-- The honest, un-widened composite traversal: graded by
    `(foldGrade g xs, foldGrade h xs)`, not yet widened to the uniform
    `(g, h)`. `f`'s own grade pair `(g, h)` is fixed — the same function
    at every element — so folding each component once per element is
    exactly `Graded.traverseRaw`'s own recursive shape, doubled. -/
def Comp.traverseRaw (f : α → Comp g h β) :
    (xs : List α) → Comp (foldGrade g xs) (foldGrade h xs) (List β)
  | []      => Comp.pure []
  | x :: xs => Comp.map2 (· :: ·) (f x) (Comp.traverseRaw f xs)

/-- The public composite traversal: a uniform `f : α → Comp g h β` lifts to
    `List α → Comp g h (List β)`, at the *same* grade pair regardless of
    the list's length. `Comp.widenGH` along `Graded.foldGrade_le`, applied
    once per component — the free, order-only fact — exactly mirroring
    `Graded.traverse`'s own definition. -/
def traverseComp (f : α → Comp g h β) (xs : List α) : Comp g h (List β) :=
  Comp.widenGH (foldGrade_le xs) (foldGrade_le xs) (Comp.traverseRaw f xs)

/-- The cons step of the public `traverseComp`, mirroring
    `Graded.traverse_cons` exactly — a cast along `Grade.join_idem`, once
    per component, since idempotence is what the uniform-grade collapse
    costs here just as it does for `traverse`. Proved the same way:
    pin down the outer shape of `f x` and of `traverseComp f xs`, each
    `ok`/`err`. Unlike the four applicative laws above, the inner layer
    *cannot* stay opaque here: `Comp.widenGH`'s inner step reaches inside
    the payload (`Graded.map (Graded.widen hh)`), and that step only
    reduces once the inner value's own shape is pinned down too — so the
    "both outer-`ok`" branch further cases the two inner values. -/
theorem Comp.traverseComp_cons (f : α → Comp g h β) (x : α) (xs : List α) :
    traverseComp f (x :: xs) =
      Comp.castGH (Grade.join_idem g) (Grade.join_idem h)
        (Comp.map2 (· :: ·) (f x) (traverseComp f xs)) := by
  change Comp.widenGH (foldGrade_le (x :: xs)) (foldGrade_le (x :: xs))
      (Comp.map2 (· :: ·) (f x) (Comp.traverseRaw f xs)) =
    Comp.castGH (Grade.join_idem g) (Grade.join_idem h)
      (Comp.map2 (· :: ·) (f x)
        (Comp.widenGH (foldGrade_le xs) (foldGrade_le xs) (Comp.traverseRaw f xs)))
  cases hfx : f x with
  | err e he =>
      simp only [Comp.widenGH, Comp.map2, Comp.ap, Comp.map, Graded.map2, Graded.map,
        Graded.widen, Graded.ap_err_left, Comp.castGH, Graded.cast_err]
  | ok F =>
      cases htx : Comp.traverseRaw f xs with
      | err e he =>
          simp only [Comp.widenGH, Comp.map2, Comp.ap, Comp.map, Graded.map2, Graded.map,
            Graded.widen, Graded.ap_ok_err, Comp.castGH, Graded.cast_err]
      | ok Y =>
          cases hF : F with
          | err e he =>
              simp only [Comp.widenGH, Comp.map2, Comp.ap, Comp.map, Graded.map2, Graded.map,
                Graded.widen, Graded.ap_ok_ok, Graded.ap_err_left, Comp.castGH, Graded.cast_err,
                Graded.cast_ok]
          | ok f' =>
              cases hY : Y with
              | err e he =>
                  simp only [Comp.widenGH, Comp.map2, Comp.ap, Comp.map, Graded.map2, Graded.map,
                    Graded.widen, Graded.ap_ok_ok, Graded.ap_ok_err, Comp.castGH, Graded.cast_err,
                    Graded.cast_ok]
              | ok y' =>
                  simp only [Comp.widenGH, Comp.map2, Comp.ap, Comp.map, Graded.map2, Graded.map,
                    Graded.widen, Graded.ap_ok_ok, Comp.castGH, Graded.cast_ok]

-- ---------------------------------------------------------------------
-- The law this step exists for: the classical Traversable composition
-- law, stated against the structure kept *nested* — no `flatten`, both
-- sides live in `Graded g (Graded h (List γ))` with the two grades still
-- separate. Recognisably Mathlib's `LawfulTraversable.comp_traverse`
-- (`Mathlib.Control.Traversable.Basic`): `traverse (Functor.Comp.mk ∘ map
-- f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))`, with Mathlib's
-- `g` (the first-applied function) matching this file's `f`, Mathlib's
-- `f` (the second-applied function) matching this file's `k`, and
-- `Comp.mk` — Mathlib's marker constructor for keeping two functors
-- distinct — omitted because `Comp g h α` keeps the layers apart *by its
-- indices* rather than by a wrapper.

theorem traverseComp_eq (f : α → Graded g β) (k : β → Graded h γ) (xs : List α) :
    traverseComp (fun a => Graded.map k (f a)) xs = Graded.map (traverse k) (traverse f xs) := by
  induction xs with
  | nil =>
      show traverseComp (fun a => Graded.map k (f a)) ([] : List α) =
        Graded.map (traverse k) (traverse f ([] : List α))
      rw [traverse_nil, fromEmpty_eq_ok]
      rfl
  | cons x xs' ih =>
      rw [Comp.traverseComp_cons, ih, traverse_cons]
      cases hfx : f x with
      | err e he =>
          simp only [Graded.map, Comp.map2, Comp.ap, Comp.map, Graded.map2, Graded.ap_err_left,
            Comp.castGH, Graded.cast_err]
      | ok a =>
          cases hxs : traverse f xs' with
          | err e he =>
              simp only [Graded.map, Comp.map2, Comp.ap, Comp.map, Graded.map2, Graded.ap_ok_err,
                Comp.castGH, Graded.cast_err]
          | ok l =>
              simp only [Graded.map, Comp.map2, Comp.ap, Comp.map, Graded.map2, Graded.ap_ok_ok,
                Comp.castGH, Graded.cast_ok]
              exact congrArg Graded.ok (traverse_cons k a l).symm

-- ---------------------------------------------------------------------
-- The explanation deliverable: is `flatten` an applicative morphism from
-- the product-graded composite to the union-graded carrier? The grade
-- equation needs *both* `Grade.join_assoc` and `Grade.join_comm` —
-- reassociating `(g ⊔ g') ⊔ (h ⊔ h')` into `(g ⊔ h) ⊔ (g' ⊔ h')`. This is
-- one of six theorems in the model that consume `Grade.join_comm`; see
-- `docs/laws.md` for the generated list.

/-- The grade equation `flatten_ap`'s cast needs: reassociating `(g ⊔ h) ⊔
    (g' ⊔ h')` into `(g ⊔ g') ⊔ (h ⊔ h')` needs both `Grade.join_assoc` and
    `Grade.join_comm`. One of six theorems that consume `Grade.join_comm`
    (`ap_flip`, `flatten_comm`, this one, `joinAll_perm`, `join_mem_eq`, and
    the generic `joinAllG_perm`); `docs/laws.md` is the generated list. -/
theorem Comp.grade_reassoc (g g' h h' : Grade Err) :
    Grade.join (Grade.join g h) (Grade.join g' h') =
      Grade.join (Grade.join g g') (Grade.join h h') :=
  calc Grade.join (Grade.join g h) (Grade.join g' h')
      = Grade.join g (Grade.join h (Grade.join g' h')) := Grade.join_assoc g h (Grade.join g' h')
    _ = Grade.join g (Grade.join (Grade.join h g') h') := by rw [Grade.join_assoc h g' h']
    _ = Grade.join g (Grade.join (Grade.join g' h) h') := by rw [Grade.join_comm h g']
    _ = Grade.join g (Grade.join g' (Grade.join h h')) := by rw [Grade.join_assoc g' h h']
    _ = Grade.join (Grade.join g g') (Grade.join h h') :=
        (Grade.join_assoc g g' (Grade.join h h')).symm

/-- `flatten` is an applicative morphism from the product-graded composite
    to the union-graded carrier *only* under a one-sided condition, and
    fails outright without it — this is the precise explanation for
    [compose-flatten]'s counterexample. `Comp.ap`'s own short-circuit order
    is: `ff`'s outer error first, then `xx`'s outer error, then `ff`'s
    *inner* payload's error, then `xx`'s. Flattening each side first and
    combining with the single-layer `ap` gives a *different* order: `ff`'s
    outer error first, then `ff`'s inner error (exposed immediately by
    flattening `ff` alone), then `xx`'s outer error. These two orders
    agree everywhere except one case: `ff` is `ok` at the outer layer with
    a *failing* inner payload, while `xx`'s outer layer *also* fails.
    There, `Comp.ap` reports `xx`'s outer error (it never looks past
    `xx`'s outer failure to notice `ff`'s inner one), while flatten-then-`ap`
    reports `ff`'s inner error (flattening `ff` surfaces it immediately,
    and `ap`'s function-first priority then favours it over `xx`). The
    hypothesis below is exactly "that case does not arise": `ff`'s outer
    layer fails, or `ff` succeeds all the way through, or `xx`'s outer
    layer succeeds. -/
theorem flatten_ap (ff : Comp g h (α → β)) (xx : Comp g' h' α)
    (hcond : (∃ e he, ff = Graded.err e he) ∨ (∃ f', ff = Graded.ok (Graded.ok f')) ∨
      (∃ X, xx = Graded.ok X)) :
    flatten (Comp.ap ff xx) =
      Graded.cast (Comp.grade_reassoc g g' h h') (ap (flatten ff) (flatten xx)) := by
  cases ff with
  | err e he =>
    cases xx with
    | ok Y =>
      cases Y with
      | ok a =>
        simp only [Comp.ap_err_left, flatten, ap_err_left]
        rw [Graded.cast_err]
      | err e' he' =>
        simp only [Comp.ap_err_left, flatten, ap_err_left]
        rw [Graded.cast_err]
    | err e' he' =>
      simp only [Comp.ap_err_left, flatten, ap_err_left]
      rw [Graded.cast_err]
  | ok F =>
    cases xx with
    | err e he =>
      cases F with
      | ok f' =>
        simp only [Comp.ap_ok_err, flatten, ap_ok_err]
        rw [Graded.cast_err]
      | err e' he' =>
        exfalso
        rcases hcond with ⟨_, _, hff⟩ | ⟨_, hff⟩ | ⟨_, hxx⟩ <;> simp_all
    | ok X =>
      cases F with
      | ok f' =>
        cases X with
        | ok a =>
          simp only [Comp.ap_ok_ok, flatten, ap_ok_ok]
          rw [Graded.cast_ok]
        | err e he =>
          simp only [Comp.ap_ok_ok, flatten, ap_ok_err]
          rw [Graded.cast_err]
      | err e he =>
        cases X with
        | ok a =>
          simp only [Comp.ap_ok_ok, flatten, ap_err_left]
          rw [Graded.cast_err]
        | err e' he' =>
          simp only [Comp.ap_ok_ok, flatten, ap_err_left]
          rw [Graded.cast_err]

end Graded
