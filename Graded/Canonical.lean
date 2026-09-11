import Graded.GradeFold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Dedup

/-! The C++ `error_set` is canonicalized so that `error_set<A,B>` and
    `error_set<B,A>` are *the same type*: the public alias delegates to a
    sorted, duplicate-free detail carrier (`docs/design.md#cpp-counterpart`).
    Every other module in this codebase built on `Graded.Grade`, which is
    `Finset` — a quotient, order-free by construction — so nothing so far has
    exercised that mechanism at all. This module builds `Canon`, the sorted
    representation the C++ carrier actually uses, and proves it equivalent
    (`Equiv`) to `Finset`, carrying `Grade.join`/`Grade.bot` across as
    `Canon.union`/`Canon.ofFinset Grade.bot`.

    `Canon` is a **representation theorem about `Grade`, not a second
    grade**: it replaces `Grade` nowhere in this codebase, has no `pure`,
    `bind`, or `Graded` carrier of its own, and every consumer
    (`Examples/Validation.lean`) stays on `Finset` exactly as before. What
    it adds is a proof that a second, order-dependent spelling of the same
    data is interchangeable with the first, connected by `canonEquiv`.

    **Where this module's evidence stops.** Everything below is a fact
    about two Lean representations of one grade. None of it is evidence
    about C++ types. `canonEquiv` is a bijection, not an alias identity;
    `canon_perm` says two permutations *sort to the same representative*,
    not that a compiler gives `error_set<A,B>` and `error_set<B,A>` one
    `type_info`; and nothing here touches mangled names, ABI, or whether
    two translation units agree on the normal form. Those are
    `static_assert` and toolchain obligations, listed in
    `docs/probe-harness.md`, and they are owned by the C++ implementation
    — the division is deliberate: Lean owns the normal-form mathematics,
    C++ owns type identity. Read a sentence here that mentions
    `error_set` as naming the C++ construct being modelled, never as a
    claim proved about it.

    **The finding this module exists to record** — call it
    `canon_requires_linear_order`; it is this paragraph, not a theorem,
    since there is no false statement to refute, only a hypothesis to
    note: `Grade Err := Finset Err` needs only
    `[DecidableEq Err]`, because forming a *set* only ever needs to know
    when two elements coincide. `Canon Err` needs strictly more,
    `[LinearOrder Err]` — a decidable *total* order — because sorting needs
    to compare every pair of distinct error kinds and get a definite
    answer, not just tell them apart. In C++ terms: `Grade`'s `DecidableEq`
    is nominal typing, which C++ gets for free; `Canon`'s `LinearOrder` is
    a total order over *whatever the sorted detail carrier orders error
    types by* (e.g. `<` on `std::type_index`, or a fixed enumeration) —
    something the abstract `error_set` design never had to name, because
    nothing before this module tested the canonicalization mechanism
    itself. -/

namespace Graded
open List

/-- The C++ detail carrier behind the `error_set` alias: a list of error
    kinds that is strictly increasing under `<`. `List.SortedLT` (this
    Mathlib's name for "strictly monotonic", equivalent to
    `List.Pairwise (· < ·)` via `List.sortedLT_iff_pairwise`) is used
    rather than "sorted, plus a separate no-duplicates side condition":
    strict monotonicity already forces every element to be distinct
    (`List.SortedLT.nodup`), which is exactly "sorted, no duplicates" in
    one predicate. -/
abbrev Canon (Err : Type u) [LinearOrder Err] := { l : List Err // l.SortedLT }

namespace Canon
variable {Err : Type u} [LinearOrder Err]

/-- Sort a `Finset` into its canonical representative. `Finset.sort`'s
    default relation is `≤`; at a `LinearOrder`, sorting by `≤` on a
    duplicate-free `Finset` is automatically strict (`Finset.sortedLT_sort`),
    which is what lets `Canon`'s property be `SortedLT` rather than the
    weaker `SortedLE`. -/
def ofFinset (s : Finset Err) : Canon Err := ⟨s.sort, s.sortedLT_sort⟩

/-- Recover the `Finset` a canonical representative came from, by
    forgetting the order and deduplicating (a no-op here, since
    `SortedLT` already rules out duplicates). Note this direction's
    *proof* needs nothing beyond `[DecidableEq Err]` — `List.toFinset`
    doesn't care about order at all; the `[LinearOrder Err]` in this
    section's `variable` is present only because it is what makes the
    argument's *type*, `Canon Err`, meaningful, not because this
    definition's body uses it. -/
def toFinset (c : Canon Err) : Finset Err := c.val.toFinset

/-- `toFinset (ofFinset s) = s`: sorting a `Finset` and then reading its
    elements back out recovers the original set. The Mathlib fact doing the
    work is `Finset.sort_toFinset`, and the proof names it in its `simp
    only` set rather than letting a bare `simp` find it, so a later reader
    can see which fact this rests on. The two unfoldings in that set are
    this module's own definitions, not Mathlib facts re-proved inline. -/
theorem toFinset_ofFinset (s : Finset Err) : toFinset (ofFinset s) = s := by
  simp only [toFinset, ofFinset, Finset.sort_toFinset]

/-- `ofFinset (toFinset c) = c`: sorting the set of a canonical
    representative's elements recovers the representative itself. Proved
    via `List.SortedLT.eq_of_mem_iff` — two `SortedLT` lists with the same
    elements are the same list — rather than by converting to `Pairwise`
    and citing `Finset.sort`'s characterisation of the sorted list
    directly, since the two `SortedLT` proofs (`c.property` and
    `Finset.sortedLT_sort` applied to `toFinset c`) are exactly the
    membership-determines-the-list fact this lemma states. -/
theorem ofFinset_toFinset (c : Canon Err) : ofFinset (toFinset c) = c := by
  apply Subtype.ext
  exact (Finset.sortedLT_sort (toFinset c)).eq_of_mem_iff c.property (by simp [toFinset])

end Canon

variable {Err : Type u} [LinearOrder Err]

/-- **A representation theorem, not C++ type identity.** The quotient
    `Grade Err` (`Finset`) and its sorted canonical representative
    `Canon Err` are in bijection, via sorting (`Canon.ofFinset`) one way
    and forgetting the order (`Canon.toFinset`) the other: two Lean
    spellings of one grade carry exactly the same data, and
    `[LinearOrder Err]` is the extra datum the sorted spelling needs and
    the quotient does not.

    What it is *not*: the statement that `error_set<A,B>` and
    `error_set<B,A>` are the same C++ type. Nothing here proves alias
    identity, that any particular metaprogram computes this normal form,
    mangling stability, or agreement across translation units — those are
    `static_assert` obligations on the C++ side
    (`docs/probe-harness.md`), and this model is silent on every one of
    them. What Lean supplies is the mathematics such a normal form has to
    implement, not evidence that a compiler implements it. -/
def canonEquiv : Grade Err ≃ Canon Err where
  toFun := Canon.ofFinset
  invFun := Canon.toFinset
  left_inv := Canon.toFinset_ofFinset
  right_inv := Canon.ofFinset_toFinset

namespace Canon

/-- `union` on canonical representatives, defined by round-tripping
    through `Finset`: forget both representatives' order, union the
    underlying sets, sort the result. **This is not the C++ algorithm** —
    the C++ detail carrier merges two already-sorted lists directly
    (a linear merge, never revisiting either input's order), which is
    the computational content `canonEquiv_union` below licenses but does
    not itself perform. Defining `union` this way is enough to prove the
    theorem the step calls for; it is not a claim that this is how the
    C++ carrier is, or should be, implemented. -/
def union (c c' : Canon Err) : Canon Err := ofFinset (toFinset c ∪ toFinset c')

/-- Sort a list into its canonical representative: dedup and order,
    exactly what `Canon`'s property demands. Built from `joinAll`
    (`Graded.GradeFold`) rather than
    `List.toFinset` directly, so that `canon_perm` below can cite
    `joinAll_perm` — the tuple case's order-independence theorem — instead
    of reproving it. -/
def ofList (l : List Err) : Canon Err :=
  ofFinset (joinAll (l.map (fun e => ({e} : Grade Err))))

/-- **The normal-form fact under "`error_set<A,B>` is `error_set<B,A>`"**
    — the mathematics, not the C++ type identity, which is a
    `static_assert` this theorem does not discharge:
    two permutations of the same list of error kinds sort to the same
    canonical representative. Cites `joinAll_perm`
    (`Graded.GradeFold`, [traverse-tuple]) rather than reproving
    order-independence from `List.Perm` directly — `joinAll_perm` already
    is that proof, for the union-of-singletons grade `ofList` folds. -/
theorem canon_perm {gs gs' : List Err} (h : gs ~ gs') : ofList gs = ofList gs' :=
  congrArg ofFinset (joinAll_perm (h.map (fun e => ({e} : Grade Err))))

end Canon

/-- `canonEquiv` carries `Grade.join` (union) across to `Canon.union`:
    sorting the union of two grades agrees with sorting each grade and
    then merging (in the round-trip sense `Canon.union` is defined by,
    not the C++ linear-merge sense — see `Canon.union`'s docstring). -/
theorem canonEquiv_union (g h : Grade Err) :
    canonEquiv (Grade.join g h) = Canon.union (canonEquiv g) (canonEquiv h) := by
  change Canon.ofFinset (Grade.join g h) =
    Canon.ofFinset (Canon.toFinset (Canon.ofFinset g) ∪ Canon.toFinset (Canon.ofFinset h))
  rw [Canon.toFinset_ofFinset, Canon.toFinset_ofFinset]
  rfl

/-- `canonEquiv` carries `Grade.bot` (∅) across to the empty canonical
    representative. -/
theorem canonEquiv_bot : canonEquiv (Grade.bot : Grade Err) = Canon.ofFinset Grade.bot := rfl

end Graded
