import Graded.Applicative
import Graded.Widen

/-! `traverse` over `List`: the shape-fold grade, honest about what it
    costs. In C++, `traverse(f, xs)` for a uniform `f : α → expected<β,
    error_set<Es...>>` has the signature `expected<vector<β>,
    error_set<Es...>>` — a grade that does not grow with `xs`'s length.
    That signature is only writable because `error_set`'s union is
    idempotent: fold the *same* grade `g` over a runtime-length list and
    the fold only stays at `g`, rather than growing without bound, because
    `g ⊔ g = g`.

    This module states that honestly rather than assuming it. `foldGrade`
    folds `g` once per list element with `Grade.bot` at the base — so
    `foldGrade g []= ⊥` and `foldGrade g (x :: xs) = g ⊔ foldGrade g xs` —
    and two separate theorems say two separate things about it:

    - `foldGrade_le` — the fold *never exceeds* `g`, for any list, of any
      length. Free: needs only the order half of the pomonoid
      (`Grade.join_le`, `Grade.bot_le`), never idempotence.
    - `foldGrade_cons_ne_nil` — a *nonempty* list's fold *equals* `g`
      exactly, regardless of length. This is the theorem the paper wants:
      it costs `Grade.join_idem` (plus `Grade.join_bot` for the one-element
      base case), and nothing weaker proves it — a non-idempotent grade
      (e.g. counting how many times each error kind occurred) would make
      this false for lists of length ≥ 2, and `traverse`'s C++ signature
      would then have to mention the list's length, which C++ generic code
      cannot do.

    The public `traverse` is defined through `widen` and `foldGrade_le`
    rather than through `cast` and `foldGrade_cons_ne_nil`. That choice is
    itself the finding the design doc records: the *definition* of
    `traverse` only ever needs the order (`foldGrade_le` bounds every list,
    including `[]`, uniformly, so no case split on emptiness is needed to
    define it), while the *precision* claim — that grade `g` is not
    padding, that no error kind admitted by the signature is actually
    unreachable — is exactly `foldGrade_cons_ne_nil`, and that is where
    idempotence is spent. Defining `traverse` the other way (`cast` along
    `foldGrade_cons_ne_nil`) would need idempotence just to typecheck the
    empty-list case, which has no elements to be idempotent over.

    The general non-idempotent case — where each element may carry a
    genuinely different grade, or the grade's join is not idempotent — is
    not modelled here; see `docs/design.md#traverse` for that as scope, not
    as a gap. -/

namespace Graded
variable {Err : Type u} [DecidableEq Err]
variable {g : Grade Err} {α β γ : Type v}

/-- The shape-fold grade: `g` joined into itself once per list element,
    with `Grade.bot` at the base. Defined honestly, before any theorem
    about it — see the module docstring for what each of `foldGrade_le`
    and `foldGrade_cons_ne_nil` costs. -/
def foldGrade (g : Grade Err) : List α → Grade Err
  | []      => Grade.bot
  | _ :: xs => Grade.join g (foldGrade g xs)

/-- The uniform-grade traversal, at its *honest* grade: `traverseRaw f xs`
    is graded by `foldGrade g xs`, not yet widened to the uniform `g`. The
    public `traverse` below widens this along `foldGrade_le`. -/
def traverseRaw (f : α → Graded g β) : (xs : List α) → Graded (foldGrade g xs) (List β)
  | []      => pure []
  | x :: xs => map2 (· :: ·) (f x) (traverseRaw f xs)

-- ---------------------------------------------------------------------
-- Reduction lemmas: how `foldGrade` computes on each list shape, proved
-- once (each is `rfl`, since `foldGrade` is a direct pattern-match
-- definition) so the theorems below can `rw` them instead of unfolding
-- the match every time.

theorem foldGrade_nil : foldGrade g ([] : List α) = Grade.bot := rfl

theorem foldGrade_cons (x : α) (xs : List α) :
    foldGrade g (x :: xs) = Grade.join g (foldGrade g xs) := rfl

/-- **Bounded, for free.** The traversal grade never exceeds the uniform
    element grade `g`, for a list of *any* length — needs only the order
    half of the pomonoid (`Grade.join_le`, `Grade.bot_le`), never
    `Grade.join_idem`. Contrast with `foldGrade_cons_ne_nil` below, which
    needs idempotence to get all the way to *equality*. -/
theorem foldGrade_le : ∀ (xs : List α), foldGrade g xs ⊆ g
  | [] => by
      rw [foldGrade_nil]
      exact Grade.bot_le g
  | x :: xs => by
      rw [foldGrade_cons]
      exact Grade.join_le (Grade.le_refl' g) (foldGrade_le xs)

/-- **Exact, and it costs idempotence.** A *nonempty* list's traversal
    grade is not merely bounded by `g`, it *equals* `g`, regardless of how
    many elements the list has. The one-element base case costs
    `Grade.join_bot` (a unit law); every further element costs
    `Grade.join_idem` (`g ⊔ g = g`) rather than making the grade grow. This
    is the theorem that makes the C++ `traverse` signature typeable for a
    length-independent grade — see the module docstring. -/
theorem foldGrade_cons_ne_nil : (xs : List α) → xs ≠ [] → foldGrade g xs = g
  | [], h => absurd rfl h
  | [x], _ => by
      rw [foldGrade_cons, foldGrade_nil]
      exact Grade.join_bot g
  | x :: y :: ys, _ => by
      rw [foldGrade_cons, foldGrade_cons_ne_nil (y :: ys) (List.cons_ne_nil y ys)]
      exact Grade.join_idem g

/-- The public traversal: a uniform element function `f : α → Graded g β`
    lifts to `List α → Graded g (List β)` at the *same* grade `g`,
    regardless of the list's length. Defined via `widen` along
    `foldGrade_le` — the free, order-only fact — rather than via `cast`
    along `foldGrade_cons_ne_nil`, so the empty list needs no special case
    at the definition site: `foldGrade_le` bounds `foldGrade g []= ⊥`
    exactly as uniformly as it bounds any nonempty list. -/
def traverse (f : α → Graded g β) (xs : List α) : Graded g (List β) :=
  widen (foldGrade_le xs) (traverseRaw f xs)

/-- The empty list traverses to `fromEmpty []`: `traverseRaw`'s nil case
    never calls `f`, so this holds for every `f`, and the two `⊆ ∅ → g`
    inclusion proofs standing behind `widen` on each side (`foldGrade_le
    []` versus `Grade.bot_le g`, used inside `fromEmpty`) are interchangeable
    by proof irrelevance (`widen_irrel`) — here that irrelevance is strong
    enough that the two sides are the same term outright. -/
theorem traverse_nil (f : α → Graded g β) : traverse f ([] : List α) = fromEmpty [] := by
  rw [fromEmpty_eq_ok]
  rfl

/-- The cons case: traversing `x :: xs` agrees with combining `f x` and
    the traversal of `xs` via `map2`, up to a cast along `Grade.join_idem`.
    The cast is unavoidable at the type level — `map2`'s own grade is
    `Grade.join g g`, since both `f x` and `traverse f xs` are already at
    the uniform grade `g` — and collapsing `Grade.join g g` down to `g` is
    exactly what idempotence is. -/
theorem traverse_cons (f : α → Graded g β) (x : α) (xs : List α) :
    traverse f (x :: xs) = cast (Grade.join_idem g) (map2 (· :: ·) (f x) (traverse f xs)) := by
  change widen (foldGrade_le (x :: xs)) (map2 (· :: ·) (f x) (traverseRaw f xs)) =
      cast (Grade.join_idem g) (map2 (· :: ·) (f x) (widen (foldGrade_le xs) (traverseRaw f xs)))
  cases hfx : f x with
  | err e he =>
      simp only [widen, map2, map, ap_err_left, cast_err]
  | ok f' =>
      cases hxs : traverseRaw f xs with
      | err e he =>
          simp only [widen, map2, map, ap_ok_err, cast_err]
      | ok l =>
          simp only [widen, map2, map, ap_ok_ok, cast_ok]

-- ---------------------------------------------------------------------
-- Reduction lemmas for the public `traverse`, in the flavour of
-- `Applicative`'s `ap_ok_ok`/`ap_err_left`/`ap_ok_err`: how `traverse f (x
-- :: xs)` computes once `f x` and `traverse f xs` are each pinned down to
-- `ok` or `err`. Used by `traverse_length` below, and by nothing else
-- (`traverse_cons` above is proved directly).

theorem traverse_cons_ok_ok (f : α → Graded g β) (x : α) (xs : List α) (b : β) (l : List β)
    (hfx : f x = Graded.ok b) (hxs : traverse f xs = Graded.ok l) :
    traverse f (x :: xs) = Graded.ok (b :: l) := by
  rw [traverse_cons, hfx, hxs]
  simp only [map2, map, ap_ok_ok]
  exact cast_ok _ _

theorem traverse_cons_err_left (f : α → Graded g β) (x : α) (xs : List α) (e : Err) (he : e ∈ g)
    (hfx : f x = Graded.err e he) :
    ∃ he', traverse f (x :: xs) = Graded.err e he' := by
  refine ⟨?_, ?_⟩
  · exact (Grade.join_idem g) ▸ (Grade.le_join_left g g he)
  · rw [traverse_cons, hfx]
    simp only [map2, map, ap_err_left]
    exact cast_err _ _ _

theorem traverse_cons_ok_err (f : α → Graded g β) (x : α) (xs : List α) (b : β) (e : Err)
    (he : e ∈ g) (hfx : f x = Graded.ok b) (hxs : traverse f xs = Graded.err e he) :
    ∃ he', traverse f (x :: xs) = Graded.err e he' := by
  refine ⟨?_, ?_⟩
  · exact (Grade.join_idem g) ▸ (Grade.le_join_right g g he)
  · rw [traverse_cons, hfx, hxs]
    simp only [map2, map, ap_ok_err]
    exact cast_err _ _ _

/-- `traverse` composes with `List.map` on the source list: reindexing the
    input before traversing agrees with traversing the reindexed function.
    Proved by induction on the list, `traverse_nil` at the base (both
    sides ignore the function on `[]`) and `traverse_cons` at the step
    (`f (h y)` and `(f ∘ h) y` are definitionally the same value). -/
theorem traverse_map (f : α → Graded g β) (h : γ → α) (xs : List γ) :
    traverse f (xs.map h) = traverse (f ∘ h) xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      change traverse f (h y :: ys.map h) = traverse (f ∘ h) (y :: ys)
      rw [traverse_cons, traverse_cons, ih]
      rfl

/-- Identity law: traversing with the "always succeed, never touch the
    grade" function (`fromEmpty`, the ∅-collapse from `Graded.Widen`) is
    the identity, at whatever grade `g` the ambient `fromEmpty` is used at.
    The C++ reading: traversing a container with a context that cannot
    fail is the same as not traversing it. Proved by induction:
    `traverse_nil` at the base, `traverse_cons` plus `Graded.ap_ok_ok` at
    the step (both `fromEmpty y` and `fromEmpty ys` are `.ok`, so `map2`
    never has an error to propagate). -/
theorem traverse_fromEmpty (xs : List α) :
    traverse (fromEmpty : α → Graded g α) xs = fromEmpty xs := by
  induction xs with
  | nil => exact traverse_nil fromEmpty
  | cons y ys ih =>
      rw [traverse_cons, ih, fromEmpty_eq_ok, fromEmpty_eq_ok, fromEmpty_eq_ok]
      show cast (Grade.join_idem g) (map2 (· :: ·) (Graded.ok y) (Graded.ok ys)) =
        Graded.ok (y :: ys)
      simp only [map2, map, ap_ok_ok]
      exact cast_ok _ _

/-- Shape preservation, the P3200 promise: whenever `traverse f xs`
    succeeds, its payload has exactly `xs`'s length — traversal changes
    the element type, never the shape. Proved by induction using the
    three `traverse_cons_*` reduction lemmas above: an `err` at either
    position makes the whole traversal an `err`, contradicting the `.ok l`
    hypothesis, so only the `ok`/`ok` case survives to carry the induction
    forward. -/
theorem traverse_length (f : α → Graded g β) :
    ∀ (xs : List α) (l : List β), traverse f xs = Graded.ok l → l.length = xs.length
  | [], l, h => by
      rw [traverse_nil, fromEmpty_eq_ok] at h
      injection h with h'
      subst h'
      rfl
  | x :: xs, l, h => by
      cases hfx : f x with
      | err e he =>
          obtain ⟨_, hc⟩ := traverse_cons_err_left f x xs e he hfx
          rw [hc] at h
          exact absurd h (by simp)
      | ok b =>
          cases hxs : traverse f xs with
          | err e he =>
              obtain ⟨_, hc⟩ := traverse_cons_ok_err f x xs b e he hfx hxs
              rw [hc] at h
              exact absurd h (by simp)
          | ok l' =>
              rw [traverse_cons_ok_ok f x xs b l' hfx hxs] at h
              injection h with h'
              subst h'
              simpa [List.length_cons] using traverse_length f xs l' hxs

end Graded
