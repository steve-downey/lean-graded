# Design — Lean model of graded Transpose

## toolchain

`lean-toolchain`: `leanprover/lean4:v4.34.0-rc2`, taken verbatim from the
Mathlib-recommended bootstrap (`lake +leanprover-community/mathlib4:lean-toolchain
new transpose_lean math`); not hand-picked.

Mathlib pin (from `lake-manifest.json`, `require` entry `mathlib`,
`inputRev = "v4.34.0-rc2"`): commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

Cache command: `lake exe cache get` (the `math` template also runs this as
part of `lake new`, so the very first `lake build` in this repo already had
the Mathlib oleans in place).

Build times (`make verify`, i.e. `lake build`), measured on this step:

- Cold (`.lake/build` for the project's own targets removed, Mathlib cache
  from `lake exe cache get` still present): see `tmp/plan/metrics.jsonl`,
  row `verify-floor`, field `note`.
- Warm (nothing changed, cache present): see the same row.

> **Provisional.** The exact wall-clock numbers depend on this machine and
> this network path to the Mathlib cache blob store. Revisit if a later
> step's CI run reports a materially different floor.

## cpp-counterpart

The grade is `error_set<Es...>`: a set of error *types*, ordered by
inclusion, joined by union; ∅ is the unit. It is a nominal type, not a bare
pack. Canonicalization is *type-level identity*: `error_set<A,B>` and
`error_set<B,A>` are the same type, via a public alias delegating to a
sorted detail carrier. An instance holds **one** error value, whose type is
in the set; value equality is variant-style.

The carrier at grade `Es` is `expected<T, error_set<Es...>>`; at grade ∅ it
is **bare `T`** (decided for client-API risk reasons), so ∅-grade is a
different C++ type from `expected<T, error_set<>>`.

Subsumption `Es ⊆ Es'` is an implicit conversion of the carrier.

`bind` produces the *union* grade; `pure` produces grade ∅.

The applicative typeclass instance for a monad is stated to be identical to
(not merely derivable from) the monad instance.

`traverse` is shape-preserving over ranges and over tuples.

Typeclass instances are duck-typed "gadgets" needing only a couple of
functions; no law checking exists in the C++ machinery; std types are the
intended test probes if a law harness is added.

Only `error_set` is intended as a grade for now; the design should not make
it the *only possible* grade.

## grade

`Graded.Grade Err := Finset Err`, for `[DecidableEq Err]`: a grade is a
finite set of error kinds. `Err` stands in for the universe of C++ error
types (see [cpp-counterpart](#cpp-counterpart)); `DecidableEq` is what lets
Lean form a `Finset` over it at all — the closest thing to "these are
distinct types" that Lean needs spelled out, where C++ gets it for free
from nominal typing.

`bot := ∅`, `join g h := g ∪ h`; the order is `⊆` (Finset's own
`PartialOrder`), read as "subset" rather than translated to `≤`, so a C++
reader sees the relation they already know.

Every pomonoid property `Graded.Grade.join`/`bot`/`⊆` has is a *separately
named* lemma in `Graded/Grade.lean`, each proved by one Mathlib `Finset`
lemma, never re-derived inline, so a later step can cite the property by
name:

- `join_assoc`, `join_comm`, `join_idem`
- `bot_join`, `join_bot`
- `le_join_left`, `le_join_right`, `join_le`, `join_mono`
- `le_refl'`, `le_trans'`, `bot_le`
- `join_eq_right_of_le`

Five of these carry a `/-- PROPERTY: ... -/` docstring tag —
`associative`, `commutative`, `idempotent`, `unit` (on both `bot_join` and
`join_bot`), `order` (on both `le_refl'` and `le_trans'`) — which is what
[oracle-export](../tmp/plan/step-oracle-export.md) greps to find which laws
depend on which property.

> **Provisional.** `Grade` is deliberately *not* registered as a Mathlib
> `SemilatticeSup`/`OrderedCommMonoid` instance, so that lemma use stays
> greppable: an instance would let `simp` reach for these properties
> invisibly, which defeats the point of naming them. Revisit if a later
> step needs Mathlib's lattice API for a proof that is otherwise long.

## carrier

Filled by [graded-carrier](../tmp/plan/step-graded-carrier.md).

## subsumption

Filled by [subsumption-widen](../tmp/plan/step-subsumption-widen.md).

## monad

Filled by [monad-laws](../tmp/plan/step-monad-laws.md).

## applicative

Filled by [applicative-from-monad](../tmp/plan/step-applicative-from-monad.md)
and [applicative-accumulation](../tmp/plan/step-applicative-accumulation.md).

## traverse

Filled by [traverse-list](../tmp/plan/step-traverse-list.md) and
[traverse-tuple](../tmp/plan/step-traverse-tuple.md).

## compose

Filled by [compose-flatten](../tmp/plan/step-compose-flatten.md).

## morphisms

Filled by [graded-morphism](../tmp/plan/step-graded-morphism.md).

## representation

Filled by [canonical-representation](../tmp/plan/step-canonical-representation.md).

## laws-inventory

Filled by [oracle-export](../tmp/plan/step-oracle-export.md).

## blog-series

Addressee: "Dear colleague" (a working C++ programmer who has never opened
Lean).

Letters directory: `blog/letters/`, one `<slug>.org` per step, per the
template in `docs/RULES.md#letter-template`.

Ordering and index: not decided here. [blog-series-edit] assembles the
reading order and the index page from the letters this plan produces; this
step writes only letter 0 (`blog/letters/baseline-capture.org`).

> **Provisional.** The addressee name "Dear colleague" is a placeholder.
> Revisit when [blog-series-edit] picks a final voice for the series, or
> sooner if a letter reads awkwardly addressed this way.

## provisional-decisions

Index of every `> **Provisional.**` mark in this document, by anchor:

- [#toolchain](#toolchain) — build-time numbers are machine- and
  network-dependent.
- [#blog-series](#blog-series) — addressee name "Dear colleague".
