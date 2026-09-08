import Graded.Applicative
import Graded.Prelude

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

/-- The static fold of a tuple's element grades: `Grade.join`, once per
    slot, `Grade.bot` at the base. This is a *different* function from
    `Graded.Traverse.foldGrade` — that one folds one fixed grade `g` once
    per list element (a runtime-length-dependent fold of a single
    repeated grade); this one folds a list of *distinct* grades, one per
    tuple slot, and does not take a `g` argument at all. -/
def joinAll : List (Grade Err) → Grade Err := List.foldr Grade.join Grade.bot

theorem joinAll_nil : joinAll ([] : List (Grade Err)) = Grade.bot := rfl

theorem joinAll_cons (g : Grade Err) (gs : List (Grade Err)) :
    joinAll (g :: gs) = Grade.join g (joinAll gs) := rfl

/-- **Order-independence, the tuple's typeability fact.** Reordering the
    tuple's element grades does not change the joined grade — needs only
    `Grade.join_comm` and `Grade.join_assoc`, never `Grade.join_idem`. This
    is what licenses the C++ claim `error_set<X,Y>` ≡ `error_set<Y,X>`: the
    theorem is commutativity plus associativity, and the C++ canonical
    sorting of `error_set`'s type arguments is an *implementation* of this
    theorem, not the theorem itself. Proved by induction on the
    permutation witness `List.Perm`, the same `nil`/`cons`/`swap`/`trans`
    case shape as Mathlib's own `List.Perm.foldr_eq`, but citing
    `Grade.join_comm`/`Grade.join_assoc` by name rather than going through
    a `Std.Commutative`/`Std.Associative` instance (`List.Perm.foldr_op_eq`
    would need one), per `docs/RULES.md`'s hypothesis discipline — an
    instance would make later `simp` reach for these properties invisibly,
    the same reason `docs/design.md#grade` never registers `Grade` as a
    Mathlib lattice instance. -/
theorem joinAll_perm {gs gs' : List (Grade Err)} (h : gs ~ gs') : joinAll gs = joinAll gs' := by
  induction h with
  | nil => rfl
  | cons g _ ih => simp only [joinAll_cons, ih]
  | swap g g' gs =>
      simp only [joinAll_cons]
      rw [← Grade.join_assoc, ← Grade.join_assoc, Grade.join_comm g g']
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A grade already present in `gs` contributes nothing further once
    joined in again — the building block `joinAll_dedup` needs. Unlike
    `joinAll_perm`, this genuinely needs `Grade.join_idem`: finding `g` at
    the head collapses `Grade.join g g` down to `g` (`Grade.join_idem`);
    finding it further in first commutes it to the head (`Grade.join_comm`,
    `Grade.join_assoc`) and then falls back on the same collapse via the
    inductive hypothesis. -/
theorem join_mem_eq {g : Grade Err} :
    ∀ {gs : List (Grade Err)}, g ∈ gs → Grade.join g (joinAll gs) = joinAll gs
  | h :: t, hmem => by
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · rw [joinAll_cons, ← Grade.join_assoc, Grade.join_idem]
      · rw [joinAll_cons, ← Grade.join_assoc, Grade.join_comm g h, Grade.join_assoc,
          join_mem_eq hmem']

/-- **Dedup, tidiness rather than typeability.** Dropping the duplicate
    grades from `gs` before folding gives the same joined grade — this is
    where `Grade.join_idem` is spent (via `join_mem_eq`), exactly at the
    point where a repeated grade collapses into its single occurrence.
    Contrast with `joinAll_perm`, which reorders without dropping anything
    and needs no idempotence at all. -/
theorem joinAll_dedup [DecidableEq (Grade Err)] :
    ∀ (gs : List (Grade Err)), joinAll gs.dedup = joinAll gs
  | [] => rfl
  | g :: gs => by
      by_cases hg : g ∈ gs
      · rw [List.dedup_cons_of_mem hg, joinAll_dedup gs, joinAll_cons, join_mem_eq hg]
      · rw [List.dedup_cons_of_notMem hg, joinAll_cons g gs.dedup, joinAll_cons g gs,
          joinAll_dedup gs]

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
