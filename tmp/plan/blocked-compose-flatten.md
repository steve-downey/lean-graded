# blocked: compose-flatten (partial)

## Status

Partial block, per the orchestrator's ruling for this step. Everything
except the traverse composition law is proved, tested, documented, and
merged into `integration/lean-model` with no `sorry` anywhere in the
committed tree (`make verify`, `make nosorry`, `make letters` all exit
0 on the merged tree). This file covers only the one thing that did not
land: the traverse composition law.

## Judgment: design problem, not a technical proof gap

The statement is **false**, not merely unproved in the time available.
I found a concrete counterexample by direct calculation, then confirmed
it computationally with `#eval` before writing this file. No amount of
further tactic effort would prove it, because it isn't true. This is
squarely the "the statement is worth more than a weakened proof here"
case the step file names, except the finding is stronger than "couldn't
prove it": the natural single-carrier translation of Traversable's
composition law is refuted, and a faithful version needs infrastructure
(a `Compose`-aware Applicative/Traversable — an applicative for
*genuinely nested*, not flattened, functors) that is out of this step's
declared scope and looks like its own multi-step piece of work, not a
tweak.

## The exact statement attempted

```lean
theorem flatten_traverse_comp (f : α → Graded g β) (k : β → Graded h γ) (xs : List α) :
    flatten ((map (traverse k) (traverse f xs) : Graded g (Graded h (List γ)))) =
      traverse (fun a => flatten ((map k (f a) : Graded g (Graded h γ)))) xs := by
  sorry
```

Both sides typecheck at the same grade (`Grade.join g h`) with no cast
needed — this is, as the step file asked, "the cleanest form" I could
get to typecheck. It is also false.

## The counterexample

Two-element list `xs = [true, false]`, with `f : Bool → Graded g Nat`
succeeding on `true` and failing (grade `g`) on `false`, and `k : Nat →
Graded h Nat` failing (grade `h`) unconditionally. Verified by `#eval`
(reduces via `decide`-style computation, not asserted):

- LHS (`flatten (map (traverse k) (traverse f xs))`): `traverse f xs`
  fails outright at the *second* element (`f false`), before `k` is ever
  invoked on anything — `map (traverse k)` passes an already-failed
  value straight through. Result: **`f`'s error, from position 2**.
- RHS (`traverse (fun a => flatten (map k (f a))) xs`): at position 1,
  `f true` succeeds but `k` then fails, so the *combined* per-element
  result at position 1 is already an error; `traverse`'s own
  left-to-right short circuit reports it immediately, without ever
  reaching position 2. Result: **`k`'s error, from position 1**.

Different positions, different underlying failures, by construction
(the two error values can be made members of disjoint grades, e.g.
`g = {E.parse}`, `h = {E.range}` in this codebase's usual test `E`).

## The failure is not about grading (orchestrator check, after the fact)

The counterexample above uses two different grades, but it does not need
them. Re-run at a **single** grade `g = h = {ef, ek}`, so that both sides
sit at the same grade and only the *values* can differ:

```
LHS  flatten (map (traverse k) (traverse f [true, false]))   ==>  "err ef"
RHS  traverse (fun a => flatten (map k (f a))) [true, false] ==>  "err ek"
```

Same grade on both sides; different error. So the refutation survives
with grading switched off entirely, and the identical counterexample
refutes the same naive law for an ungraded nested `expected<expected<T,
E>, E>`. The mechanism below is about `flatten` destroying the
*distinction between layers*, which a plain `Either` flattening does
just as thoroughly as a graded one. This is worth knowing before
treating the result as evidence about graded traversables specifically:
it is not. It is evidence that flatten-then-traverse is the wrong shape
for a composition law, graded or not.

## Why this happens (the mechanism, not just the instance)

`map (traverse k) (traverse f xs)` commits to *all* of `f` across the
whole list before consulting `k` at all — it is "check every element's
outer stage first; only if that fully succeeds, check every element's
inner stage." `traverse (fun a => flatten (map k (f a))) xs` interleaves
`f` and `k` per element and only then walks the list — it is "check each
element's outer-then-inner stage before moving to the next element."
These are different algorithms whenever an *earlier* element's inner
stage can fail while a *later* element's outer stage also fails: the
first algorithm reports the later element's outer failure (it never
gets far enough to see the earlier inner failure); the second reports
the earlier element's inner failure first.

The classical Traversable composition law is true for a `Compose F G`
that keeps `F`'s and `G`'s effects genuinely separate until the applicative
`<*>` for the composed functor forces them together — `Compose`'s own
`<*>` combines at the `F` level first, using `F`'s `<*>`, with `G`'s
`<*>` lifted *inside* that combination, so an `F`-level check across the
whole structure is what the classical law's left side does. Our
`Graded g'` is not that: `flatten` conflates "which layer failed" into
one flat grade at construction time, so once any per-element value is
flattened, the traversal that follows has no way to prefer an outer
failure over an inner one across different list positions — it can only
short-circuit on "some grade `g'` error occurred here," first in list
order, full stop.

## What was tested, and what was not (orchestrator, after the fact)

Worth stating flatly, because the earlier sections read as a result about
graded traversables and are not one. This step tested the **flattened**
statement and refuted it. The **product-graded** statement — the classical
law's actual shape, over `Graded g ∘ Graded h` with the pair `(g, h)` in
the product pomonoid as its grade — was never built and never tested.

This step's own `## Why` names the product pomonoid as the natural grade
for a nested carrier in its first sentence, then sets the task as settling
whether the law holds *through the flattening*. Those are different
questions. Answering the second says nothing about the first.

Also: `docs/design.md#cpp-counterpart` makes no composition claim at all —
it states only that `traverse` is shape-preserving over ranges and tuples.
So nothing in the C++ design currently rests on this either way.

## What it would take to settle this properly

A genuine `Compose`-aware applicative/traversable — i.e., an `ap`-like
combinator for `Graded g ∘ Graded h` (as a distinct entity, *not*
pre-flattened via `Grade.join`) that combines the outer layers with the
outer `ap` and the inner layers with the inner `ap` lifted inside, the
way `Compose`'s own instance does — plus a `traverse` parametrised over
that. That is new carrier-and-applicative infrastructure, not a proof
about existing `flatten`, and is not something I judged safe to
improvise inside this step's declared file scope.

## What I tried

1. Stated the naive form above and attempted a five/six-case induction
   on `xs` (cons case split on `f y`, `traverse f ys`, `k b`,
   `traverse k l`), using the codebase's established `cast_ok`/`cast_err`
   + case-analysis style. The base case (`xs = []`) closed cleanly. The
   inductive step's goal, after unfolding, showed the divergence above
   directly in the proof state (not merely "stuck" — the two sides
   reduced to literally different `.err` terms with different underlying
   error values, which is what prompted the direct calculation).
2. Worked the counterexample by hand, then verified it computationally
   with a scratch `#eval` (not committed — deleted after confirming),
   using this codebase's own `E`/grade conventions.
3. Concluded further proof attempts would not succeed, since the
   statement is false, and stopped rather than searching for a "cleaner"
   restatement that would suffer the same mechanism (see the "Why this
   happens" section above — the issue is structural, not a matter of
   phrasing).

## Everything else in this step

Not blocked. `flatten` and its eight laws (`flatten_eq_bind_id`,
`flatten_map`, `flatten_pure_outer`, `flatten_pure_inner`,
`flatten_flatten`, `flatten_widen_outer`, `flatten_widen_inner`,
`flatten_comm`), `swap`, `Tests/Compose.lean`, the `lookup`/`flatten`
consumer in `Examples/Validation.lean`, `docs/design.md#compose`, and
`blog/letters/compose-flatten.org` are all committed and merged into
`integration/lean-model` — see the merge commit recorded in the final
report to the orchestrator.

## For a human to decide

Whether a `Compose`-aware applicative/traversable is worth adding as its
own step (it would be new, nontrivial infrastructure — a distinct
"composed grade" applicative, not an extension of `flatten`), or whether
the finding itself ("naive flatten-then-traverse does not satisfy the
classical composition law, and here is exactly why") is the deliverable
this branch of the plan wanted, with no further step needed on it.
