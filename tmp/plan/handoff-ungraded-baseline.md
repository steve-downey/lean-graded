# handoff → ungraded-baseline

Goal and merge criterion: fixed by `step-ungraded-baseline.md`.

## `graded-traversable-composition` is now CLOSED, not OPEN

Your step's own "Why" section narrates [compose-flatten]'s refutation as
still-live evidence that the model once conflated "fails ungraded" with
"fails because of grading." That conflation is real and your step is
still the right fix for it in general, but the specific question is no
longer open: [compose-applicative] built the product-graded composite
(`Comp g h α := Graded g (Graded h α)`, `Graded/ComposeApp.lean`, **not**
in your declared file scope, do not touch it) and proved

```lean
theorem traverseComp_eq (f : α → Graded g β) (k : β → Graded h γ) (xs : List α) :
    traverseComp (fun a => map k (f a)) xs = map (traverse k) (traverse f xs)
```

holds **unconditionally** — no `flatten`, both grades kept separate, no
`Grade.join_comm`, and exactly one `Grade.join_idem` per component (citing
`Graded.traverse_cons`, doubled). `docs/design.md#graded-traversable-composition`'s
`Status:` line now reads CLOSED. This is precisely the row your step 4
already anticipates ("the graded form [compose-applicative] tests") — cite
`traverseComp_eq` by name there, alongside Mathlib's `comp_traverse`, as
the two-grades-kept-separate law that **holds**, contrasted with the
flattened form (yours to re-confirm fails at a fixed grade) that fails in
both the graded and ungraded columns.

## The correspondence with Mathlib's `comp_traverse`, already worked out

`traverseComp_eq` is recognisably `LawfulTraversable.comp_traverse`
(`Mathlib.Control.Traversable.Basic`): `traverse (Functor.Comp.mk ∘ map f
∘ g) x = Comp.mk (map (traverse f) (traverse g x))`. Mathlib's `g`
(applied first) is this theorem's `f`; Mathlib's `f` (applied second) is
this theorem's `k`; `Comp.mk` — Mathlib's marker constructor for keeping
two functors distinct — is omitted because `Comp g h α`'s *indices*
already keep the layers apart, no wrapper needed. If your own
correspondence table (step file §3) reaches `comp_traverse`, this mapping
is already done; no need to re-derive it independently for the composed
case, only for your own `bindF`/`apF`/single-`traverse` correspondences
with `Sum`.

## `Comp` is not `Fixed` — do not conflate the two carriers

`Comp g h α` (two grades, genuinely nested, from [compose-applicative]) and
your `Fixed g A` (one grade, held still) are unrelated carriers answering
unrelated questions. Nothing in `Comp`'s laws bears on what a single fixed
grade collapses to. Do not go looking for a connection; there isn't one at
this stage.

## `flatten_ap`: a second data point on "holds only conditionally," not part of your table

[compose-applicative] also asked whether `flatten` is an applicative
morphism from `Comp` to the union-graded carrier (`flatten_ap`, same
file). It holds only under a disjunctive hypothesis and fails outright
without it, confirmed by `#eval` — a *different* law from the flattened
composition law your step 4 re-checks (that one has no `Comp` in it at
all). Do not fold `flatten_ap` into your table; it is not one of the laws
in your declared scope (`docs/design.md#grade`, `#carrier`, `#monad`,
`#applicative`, `#subsumption`, `#traverse`, `#compose`, `#morphisms`) and
mentioning it would blur the exact row your step 4 wants.

## A elaboration trap worth having in advance

Lean's dotted-declaration recursion sugar means a bare reference to a
function *inside the body of a same-named-but-dotted declaration*
resolves to the declaration being defined, not the one you meant. Concrete
case that cost real time this step: `def Comp.map (f) : ... := map (map
f)` — the outer `map` silently resolved to `Comp.map` itself (infinite
recursion, reported as a termination-checker failure, not a name-resolution
one) rather than `Graded.map`, because both live in the `Graded` namespace
once declared. If `pureF`/`bindF`/`apF` end up declared as `Fixed.pureF`-
style dotted names (rather than the bare `pureF`/`bindF`/`apF` your step
file writes them as), qualify every inner reference to `Graded.bind`/
`Graded.pure`/`Graded.ap`/`cast` fully rather than writing them bare.
Since your step file's own sketch uses bare `pureF`/`bindF`/`apF` (no
`Fixed.` prefix), this likely does not bite — but if you change that,
this is the first thing to check on a bewildering termination error.

## Casts: which were forced, which were a free choice

For what it's worth in your "second column" write-up: every cast in
[compose-applicative]'s four applicative laws was *forced* by grade
arithmetic (unit or associativity, once per component, matching
[applicative-from-monad]'s single-layer proof exactly) — none was a
stylistic choice. `traverseComp_eq` needed exactly the one `join_idem`
cast per component that `traverse_cons` already needed, doubled, and no
more. Nothing in this step found an *incidental* cast (one where the
un-cast statement would also have typechecked) — every cast site
corresponds to a real grade-arithmetic step, consistent with every prior
step's own finding.

## Do not use `git add -A` in the main checkout

The main checkout's working tree still carries an uncommitted editorial
pass across `blog/letters/*.org` (confirmed still present after this
step's merge), made by the repository's owner and deliberately left
uncommitted. Stage your own files by name in the main checkout;
`git add -A` is fine inside your own worktree only.
