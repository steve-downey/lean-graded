import Graded.Applicative
import Graded.GradeFold

/-! `sequence` over a heterogeneous tuple: the C++ `transpose(tuple<expected<A,
    error_set<X>>, expected<B, error_set<Y>>>)` → `expected<tuple<A,B>,
    error_set<X,Y>>` case. Unlike [traverse-list]'s `List`, a tuple's
    elements carry *different* grades and *different* types, so the fold of
    grades is static — computed once, at the type level, from the list of
    element grades — rather than a runtime-length-independent fold of one
    repeated grade. That staticness is exactly why no idempotence is needed
    for the tuple case to be *typeable*: `joinAll_perm` below needs only
    `Grade.join_comm`/`Grade.join_assoc`. Idempotence resurfaces only for
    *tidiness* (`joinAll_dedup`), never for typeability.

    **`joinAll` moved out.** The fold of element grades and its three
    laws now live in `Graded.GradeFold`, imported here and — the point of
    the move — imported by `Graded.Canonical` *instead of* this module.
    Canonicalization needed one fold and one permutation theorem, and was
    pulling in `GList` and `sequence` to get them.

    `GList` is the fully heterogeneous representation the step calls for: a
    tuple of `Graded` values indexed in lockstep by a list of grades and a
    list of payload types, `Graded g α` at each position rather than a
    single uniform grade or type. It is defined as a plain recursive `def`
    over the two index lists together (`PUnit` at `[],[]`, a `Prod` at each
    `cons`, `PEmpty` at a length mismatch), the same style `HList`
    (`Graded/Prelude.lean`) uses — not as a genuine `inductive` family.
    Declaring `GList` as an `inductive` indexed by `(gs, αs)` forces the
    resultant universe up by a full level (Lean's "large inductive family"
    check: a per-constructor argument `{α : Type v}` needs the family's
    sort to dominate `Type v`'s *own* type, i.e. `Type (v+1)`, not just
    `Type v` — the standard cost of a `Type`-indexed inductive family). The
    `def`-as-nested-product route sidesteps that tax entirely, the same way
    `HList` does, since a plain recursive `Type`-valued function carries no
    such large-elimination obligation. -/

namespace Graded
open List
variable {Err : Type u} [DecidableEq Err]

/-- A heterogeneous tuple of graded values: `GList gs αs` holds one
    `Graded g α` per position, for `g` drawn from `gs` and `α` from `αs`, in
    lockstep — `PUnit` when both lists are empty, `Graded g α × GList gs αs`
    at each matched `cons`, and the uninhabited `PEmpty` at a length
    mismatch (never produced by `GList.nil`/`GList.cons`, so no consumer of
    this module ever has to eliminate it). This is the fully heterogeneous
    representation — elements may have different grades *and* different
    payload types, unlike `Graded.Traverse`'s `List`, which fixes one grade
    `g` for every element. -/
def GList : List (Grade Err) → List (Type v) → Type (max u v)
  | [], [] => PUnit
  | g :: gs, α :: αs => Graded g α × GList gs αs
  | [], _ :: _ => PEmpty
  | _ :: _, [] => PEmpty

/-- The empty tuple. -/
def GList.nil : GList ([] : List (Grade Err)) ([] : List (Type v)) := PUnit.unit

/-- Extend a tuple with one more graded element at the front. -/
def GList.cons {g : Grade Err} {gs : List (Grade Err)} {α : Type v} {αs : List (Type v)}
    (x : Graded g α) (xs : GList gs αs) : GList (g :: gs) (α :: αs) :=
  ⟨x, xs⟩


/-- Sequencing a `GList`: check every element and, if every one succeeds,
    collect the payloads into an `HList`; if any one fails, the whole
    tuple fails with that element's error, widened up to the static join
    `joinAll gs`. The result grade is *computed once from the types*
    (`joinAll gs`), not folded at runtime the way `Graded.Traverse.traverse`
    folds a single repeated grade over a runtime-length list — this is the
    sense in which "the tuple case is where the grade is really
    computed." The two length-mismatch branches are unreachable (`GList`
    is `PEmpty` there) and closed by `nomatch`. -/
def sequence : {gs : List (Grade Err)} → {αs : List (Type v)} → GList gs αs →
    Graded (joinAll gs) (HList αs)
  | [], [], _ => pure HList.nil
  | _ :: _, [], xs => nomatch xs
  | [], _ :: _, xs => nomatch xs
  | _ :: _, _ :: _, (x, xs) => map2 HList.cons x (sequence xs)

theorem sequence_nil :
    (sequence (Err := Err) GList.nil : Graded (Grade.bot : Grade Err) (HList [])) =
      pure HList.nil := rfl

theorem sequence_cons {g : Grade Err} {gs : List (Grade Err)} {α : Type v} {αs : List (Type v)}
    (x : Graded g α) (xs : GList gs αs) :
    sequence (GList.cons x xs) = map2 HList.cons x (sequence xs) := rfl

end Graded
