import Graded.Grade
import Graded.Prelude

/-! `joinAll`: the static fold of a list of grades.

    Extracted from `Graded/Tuple.lean` by [module-split]. It lived there
    because [traverse-tuple] needed it for heterogeneous sequencing, and
    `Graded/Canonical.lean` then imported the whole tuple development —
    `GList`, `sequence`, the lot — to reuse one fold and one permutation
    theorem. That import is what this module removes.

    Nothing here mentions a carrier. `joinAll` folds a list of grades
    with `Grade.join` and `Grade.bot`, and the three facts about it are
    facts about grades: order-independence (`joinAll_perm`, needing
    commutativity and associativity), absorption of a member
    (`join_mem_eq`), and deduplication (`joinAll_dedup`, the one that
    spends idempotence). `Graded.Tuple` and `Graded.Canonical` both import
    this and neither imports the other. -/

namespace Graded
open List

variable {Err : Type u} [DecidableEq Err]

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

/-- A slot's own grade is contained in the fold of all of them. Follows
    from `join_mem_eq` and `Grade.le_join_left`, and it is what lets
    `Graded.sequenceK`'s per-slot inclusion hypothesis be discharged when
    the nominated grade *is* the computed fold — the bridge
    `sequence_eq_sequenceK` runs through this. -/
theorem joinAll_le_of_mem {g : Grade Err} {gs : List (Grade Err)} (hmem : g ∈ gs) :
    g ⊆ joinAll gs := by
  have h := join_mem_eq (g := g) hmem
  exact h ▸ Grade.le_join_left g (joinAll gs)

end Graded
