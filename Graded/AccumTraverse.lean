import Graded.Accum
import Graded.Sufficient

/-! Traversal for the accumulating carrier, at a caller-nominated grade.

    `Graded.Accum` has been in this model since [applicative-accumulation]
    and has never been traversed. That is the gap this module closes, and
    it is a conspicuous one: collecting every independent failure is the
    *only* reason the accumulating carrier exists, and a list of
    independent checks is the canonical place that happens. The
    short-circuiting carrier got `traverse` at [traverse-list] and
    `traverseK` at [sufficient-grade-traverse]; `Accum` got neither.

    **Why this is a separate module rather than more of `Graded/Accum.lean`.**
    `Graded.Morphism` imports `Graded.Accum`, and `Graded.Sufficient`
    imports `Graded.Morphism`, so `Graded/Accum.lean` cannot see
    `Graded.traverseK` without a cycle. The traversal needs it, to state
    the commutation theorem this module is really for. Splitting is the
    honest fix, and it is the direction `#obligations`' module-layout note
    points anyway.

    **The sufficient grade, not the union.** `Accum.ap` computes
    `Grade.join g h` exactly as `Graded.ap` does, and folding it over a
    runtime-length list has the same problem `Graded.traverse` has: the
    grade grows unless idempotence collapses it. `traverseK` takes the
    caller's `k` and one proof `g ⊆ k`, reuses them at every position, and
    lands in `Accum k (List β)` for every list regardless of length. As at
    [sufficient-grade-traverse], length-independence is then a property of
    the *signature* and not a theorem that costs `Grade.join_idem`.

    **`apK` here is primitive, and that is the point.** `Graded.apK` is
    defined through `bindK` — the applicative derived from the monad. This
    one cannot be: `Accum.notMonad` proves there is no monad to derive it
    from, and the whole difference is in the both-fail case, which a
    monad's sequencing cannot express. So `Accum.apK` matches on both
    arguments directly and concatenates.

    **What the module is for.** `toGraded_traverseK`: taking the first
    error of an accumulated traversal is the same as short-circuiting at
    the first error in the first place. `Accum.toGraded_grade'`
    ([applicative-accumulation]) already proved the projection is an
    unconditional applicative morphism; this lifts that to traversal, and
    it is the interoperability guarantee the C++ side gets for free — a
    validating `transpose` and a short-circuiting one agree on which error
    a caller sees. -/

namespace Graded
namespace Accum
variable {Err : Type u} [DecidableEq Err]
variable {g h k : Grade Err} {α β γ : Type v}

-- ---------------------------------------------------------------------
-- The sufficient-grade applicative. `pureK` lands at any `k` (an `ok`
-- carries no error, so nothing has to be shown about `k` at all), and
-- `apK` takes one inclusion per argument, using each side's own proof
-- where `ap` used `Grade.le_join_left`/`le_join_right`.

/-- `pure` at any grade `k`: an `ok` has no errors to place in the grade,
    so unlike `Graded.pureK` there is not even a widening to perform. -/
def pureK (a : α) : Accum k α := .ok a

/-- Sequence at a grade `k` containing both `g` and `h`, **accumulating**
    both error lists when both sides fail. The function's errors come
    first, matching `Accum.ap`'s own order, which is what makes
    `toGraded_apK` below unconditional.

    Defined by matching on both arguments, not through a `bindK`: there is
    no `Accum` monad to derive it from (`Accum.notMonad`), and the
    both-fail case is exactly what a monad's sequencing could not
    produce. -/
def apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Accum g (α → β)) (x : Accum h α) : Accum k β :=
  match f, x with
  | .ok f', .ok a => .ok (f' a)
  | .ok _, .errs es hne hmem => .errs es hne (fun e he => hh (hmem e he))
  | .errs es hne hmem, .ok _ => .errs es hne (fun e he => hg (hmem e he))
  | .errs es1 hne1 hmem1, .errs es2 _hne2 hmem2 =>
      .errs (es1 ++ es2) (List.append_ne_nil_of_left_ne_nil hne1 es2)
        (fun e he => (List.mem_append.mp he).elim
          (fun h1 => hg (hmem1 e h1))
          (fun h2 => hh (hmem2 e h2)))

/-- `map2` at a sufficient grade: `apK` after `map`, exactly as
    `Accum.map2` is `ap` after `map`. -/
def map2K (hg : g ⊆ k) (hh : h ⊆ k) (f : α → β → γ) (x : Accum g α) (y : Accum h β) :
    Accum k γ :=
  apK hg hh (map f x) y

-- Reduction lemmas: `apK` matches directly on both arguments, so every
-- case is `rfl`, the same footing as `Accum.ap_ok_ok` and its three
-- siblings.

theorem apK_ok_ok (hg : g ⊆ k) (hh : h ⊆ k) (f' : α → β) (a : α) :
    apK hg hh (Accum.ok f' : Accum g (α → β)) (Accum.ok a : Accum h α) = Accum.ok (f' a) := rfl

theorem apK_ok_errs (hg : g ⊆ k) (hh : h ⊆ k) (f' : α → β)
    (es : List Err) (hne : es ≠ []) (hmem : ∀ e ∈ es, e ∈ h) :
    apK hg hh (Accum.ok f' : Accum g (α → β)) (Accum.errs es hne hmem)
      = Accum.errs es hne (fun e he => hh (hmem e he)) := rfl

theorem apK_errs_ok (hg : g ⊆ k) (hh : h ⊆ k)
    (es : List Err) (hne : es ≠ []) (hmem : ∀ e ∈ es, e ∈ g) (a : α) :
    apK hg hh (Accum.errs es hne hmem : Accum g (α → β)) (Accum.ok a : Accum h α)
      = Accum.errs es hne (fun e he => hg (hmem e he)) := rfl

theorem apK_errs_errs (hg : g ⊆ k) (hh : h ⊆ k)
    (es1 : List Err) (hne1 : es1 ≠ []) (hmem1 : ∀ e ∈ es1, e ∈ g)
    (es2 : List Err) (hne2 : es2 ≠ []) (hmem2 : ∀ e ∈ es2, e ∈ h) :
    apK hg hh (Accum.errs es1 hne1 hmem1 : Accum g (α → β)) (Accum.errs es2 hne2 hmem2)
      = Accum.errs (es1 ++ es2) (List.append_ne_nil_of_left_ne_nil hne1 es2)
          (fun e he => (List.mem_append.mp he).elim
            (fun h1 => hg (hmem1 e h1)) (fun h2 => hh (hmem2 e h2))) := rfl

/-- The bridge to the union-graded `ap`, the mirror of `Graded.ap_eq_apK`:
    instantiating `k` at the exact union with the two inclusions `ap`
    already uses recovers `ap` itself. -/
theorem ap_eq_apK (f : Accum g (α → β)) (x : Accum h α) :
    ap f x = apK (Grade.le_join_left g h) (Grade.le_join_right g h) f x := by
  cases f with
  | ok f' => cases x with
    | ok a => rfl
    | errs es hne hmem => rfl
  | errs es1 hne1 hmem1 => cases x with
    | ok a => rfl
    | errs es2 hne2 hmem2 => rfl

-- ---------------------------------------------------------------------
-- The four applicative laws at a sufficient grade. `Graded.Accum` has had
-- these at the *union* grade since [applicative-accumulation], each
-- carrying a `cast`; these are the cast-free analogues, and the model
-- lacked them until [abstract-effects] asked the carrier to be a graded
-- applicative in general.

theorem apK_pure_id (hh : h ⊆ k) (x : Accum h α) :
    apK (Grade.le_refl' k) hh (pureK (@id α) : Accum k (α → α)) x = widen hh x := by
  cases x <;> rfl

theorem apK_pure_pure (f : α → β) (a : α) :
    apK (Grade.le_refl' k) (Grade.le_refl' k) (pureK f : Accum k (α → β)) (pureK a)
      = (pureK (f a) : Accum k β) := rfl

theorem apK_interchange (hg : g ⊆ k) (u : Accum g (α → β)) (a : α) :
    apK hg (Grade.le_refl' k) u (pureK a : Accum k α)
      = apK (Grade.le_refl' k) hg (pureK (fun f => f a) : Accum k ((α → β) → β)) u := by
  cases u <;> rfl

/-- (composition) **The one law here that is not `rfl`**, and the
    difference is the whole character of the accumulating carrier. For the
    short-circuiting `Graded`, `apK_comp` is a case split ending in `rfl`
    at every leaf: at most one error survives, so both sides carry the
    same one. Here every failing side contributes, and the two groupings
    accumulate `(eu ++ ev) ++ ew` against `eu ++ (ev ++ ew)`. Those are
    equal by `List.append_assoc` and not by computation, so the proof has
    to say so — through `errs_eq_of_list_eq`, since the two `errs` values
    also carry different membership proofs, which proof irrelevance makes
    irrelevant but does not make syntactically equal.

    Read against the short-circuiting version, this is where "the
    applicative is identical to the monad" stops being true: composition
    holds for both carriers, and only one of them gets it for free. -/
theorem apK_comp (hg : g ⊆ k) (hg' : g' ⊆ k) (hj : j ⊆ k)
    (u : Accum g (β → γ)) (v : Accum g' (α → β)) (w : Accum j α) :
    apK (Grade.le_refl' k) hj (apK (Grade.le_refl' k) hg'
        (apK (Grade.le_refl' k) hg (pureK Function.comp : Accum k ((β → γ) → (α → β) → α → γ)) u)
        v) w
      = apK hg (Grade.le_refl' k) u (apK hg' hj v w) := by
  cases u with
  | ok u' =>
      cases v with
      | ok v' => cases w <;> rfl
      | errs ev hnev hmemv => cases w <;> [rfl; exact errs_eq_of_list_eq rfl]
  | errs eu hneu hmemu =>
      cases v with
      | ok v' => cases w <;> [rfl; exact errs_eq_of_list_eq rfl]
      | errs ev hnev hmemv =>
          cases w <;> exact errs_eq_of_list_eq (by simp [List.append_assoc])

-- ---------------------------------------------------------------------
-- The traversal itself, shaped exactly like `Graded.traverseK`: one
-- inclusion `hg`, reused at every element, with `Grade.le_refl' k` for
-- the already-accumulated tail.

/-- Traverse a list with an accumulating check, landing at the caller's
    grade `k`. Every element's failures are appended to the failures of
    the elements after it, so a list of `n` failing checks yields all `n`
    error lists concatenated, in source order — see `errsOf_traverseK`. -/
def traverseK (hg : g ⊆ k) (f : α → Accum g β) : List α → Accum k (List β)
  | []      => pureK []
  | x :: xs => map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x) (traverseK hg f xs)

theorem traverseK_nil (hg : g ⊆ k) (f : α → Accum g β) :
    traverseK hg f ([] : List α) = pureK [] := rfl

theorem traverseK_cons (hg : g ⊆ k) (f : α → Accum g β) (x : α) (xs : List α) :
    traverseK hg f (x :: xs)
      = map2K hg (Grade.le_refl' k) (fun b bs => b :: bs) (f x) (traverseK hg f xs) := rfl

-- ---------------------------------------------------------------------
-- What came out: the error list, and the success case.

/-- The errors a result carries, as a plain list: `[]` for a success. The
    observation `errsOf_traverseK` is stated against — deliberately
    forgetting the non-emptiness proof and the grade membership, since
    neither is what the ordering claim is about. -/
def errsOf : Accum g α → List Err
  | .ok _ => []
  | .errs es _ _ => es

theorem errsOf_ok (a : α) : errsOf (Accum.ok a : Accum g α) = [] := rfl

theorem errsOf_errs (es : List Err) (hne : es ≠ []) (hmem : ∀ e ∈ es, e ∈ g) :
    errsOf (Accum.errs es hne hmem : Accum g α) = es := rfl

theorem errsOf_apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Accum g (α → β)) (x : Accum h α) :
    errsOf (apK hg hh f x) = errsOf f ++ errsOf x := by
  cases f with
  | ok f' => cases x with
    | ok a => rfl
    | errs es hne hmem => rfl
  | errs es1 hne1 hmem1 => cases x with
    | ok a => simp [apK, errsOf]
    | errs es2 hne2 hmem2 => rfl

theorem errsOf_map (f : α → β) (x : Accum g α) : errsOf (map f x) = errsOf x := by
  cases x <;> rfl

/-- **Every failing position contributes, in source order, exactly once.**
    The accumulated error list of a traversal is the concatenation of each
    element's own errors, taken left to right. Zero failures give `[]`,
    one failing position gives its list alone, and `n` failing positions
    give all `n` lists in the order the elements appear.

    This is the theorem the accumulating carrier exists for, and it is
    also the contract that makes the *order* observable: because
    `toGraded` takes the first error, the left-to-right choice here
    decides which error a short-circuiting caller sees, which is exactly
    what `toGraded_traverseK` below pins down. An unordered bag would need
    a different carrier and a different projection policy; it would not be
    this theorem with a weaker statement. -/
theorem errsOf_traverseK (hg : g ⊆ k) (f : α → Accum g β) (xs : List α) :
    errsOf (traverseK hg f xs) = xs.flatMap (fun x => errsOf (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [traverseK_cons, map2K, errsOf_apK, errsOf_map, ih, List.flatMap_cons]

/-- **Success is `List.map`.** A traversal whose every check succeeds
    returns the mapped list, at the nominated grade, with no errors. -/
theorem traverseK_ok (hg : g ⊆ k) (f : α → Accum g β) (fo : α → β)
    (hf : ∀ a, f a = Accum.ok (fo a)) (xs : List α) :
    traverseK hg f xs = Accum.ok (xs.map fo) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [traverseK_cons, map2K, ih, hf x]
      rfl

-- ---------------------------------------------------------------------
-- The payoff: the projection to the short-circuiting carrier commutes
-- with traversal. `Accum.toGraded_grade'` already proved `toGraded` is an
-- unconditional applicative morphism; this lifts it through the list.

theorem toGraded_pureK (a : α) : toGraded (pureK a : Accum k α) = Graded.pureK a := by
  rw [Graded.pureK, fromEmpty_eq_ok]; rfl

theorem toGraded_widen (h : g ⊆ k) (x : Accum g α) :
    toGraded (widen h x) = Graded.widen h (toGraded x) := by
  cases x with
  | ok a => rfl
  | errs es hne hmem => cases es with
    | nil => exact absurd rfl hne
    | cons e es' => rfl

theorem toGraded_map (f : α → β) (x : Accum g α) :
    toGraded (map f x) = Graded.map f (toGraded x) := by
  cases x with
  | ok a => rfl
  | errs es hne hmem => cases es with
    | nil => exact absurd rfl hne
    | cons e es' => rfl

/-- The sufficient-grade mirror of `toGraded_grade'`, and unconditional
    for the same reason: `apK` concatenates the function's errors first,
    and `Graded.apK` keeps the function's error whenever the function
    fails, so "first of the accumulated list" and "the error the
    short-circuiting carrier kept" are the same error by construction. -/
theorem toGraded_apK (hg : g ⊆ k) (hh : h ⊆ k) (f : Accum g (α → β)) (x : Accum h α) :
    toGraded (apK hg hh f x) = Graded.apK hg hh (toGraded f) (toGraded x) := by
  cases f with
  | ok f' =>
    cases x with
    | ok a => rfl
    | errs es hne hmem => cases es with
      | nil => exact absurd rfl hne
      | cons e es' => rfl
  | errs esf hnef hmemf =>
    cases esf with
    | nil => exact absurd rfl hnef
    | cons e esf' =>
      cases x with
      | ok a => rfl
      | errs es hne hmem => cases es with
        | nil => exact absurd rfl hne
        | cons e' es' => rfl

theorem toGraded_map2K (hg : g ⊆ k) (hh : h ⊆ k) (f : α → β → γ)
    (x : Accum g α) (y : Accum h β) :
    toGraded (map2K hg hh f x y) = Graded.map2K hg hh f (toGraded x) (toGraded y) := by
  rw [map2K, Graded.map2K, toGraded_apK, toGraded_map]

/-- **Taking the first error commutes with traversal.** Accumulate every
    failure and then keep the first, or short-circuit at the first failure
    from the start: the same error, and on success the same list.

    This is the interoperability guarantee, and it holds with no side
    condition. A C++ `transpose` that validates and a `transpose` that
    short-circuits do not have to agree by convention; they agree because
    the accumulating one appends left to right and the short-circuiting
    one keeps the leftmost, and those are the same choice made twice. -/
theorem toGraded_traverseK (hg : g ⊆ k) (f : α → Accum g β) (xs : List α) :
    toGraded (traverseK hg f xs) = Graded.traverseK hg (fun a => toGraded (f a)) xs := by
  induction xs with
  | nil => exact toGraded_pureK []
  | cons x xs ih =>
      rw [traverseK_cons, Graded.traverseK_cons, toGraded_map2K, ih]

end Accum
end Graded
