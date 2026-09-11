# Coordination worklist — 2026-07-13

Work items for beman.transpose arising from the coordinated-set review
held in the tree_algorithms repo (see
`tree_algorithms/docs/notes/extraction-plan.md`, §3 and §7a, and the
`tree-proposals-coherence` skill there). Decisions ratified by Steve
2026-07-13: the fold family (`fold_map` + monoid as user-facing API) is
proposed in Paper D, not here; Monad is deferred (not rejected) and
acknowledged in-paper and out-of-band. This file schedules the local
consequences.

**STATUS 2026-07-14: items 1, 2, 3, and 5 executed and merged to main
(commit b21e8da, 54/54 tests). Item 4 (essay citation) remains blocked
on the essay URL; item 6 is standing. Note: the "Why not Monad" section
frames deferral, not rejection — see the refined framing in item 1
below and tree-coordination SYNC entry 4.**

## 1. Add a "Why not Monad" section to D3200R0

`papers/wg21/D3200R0.md` currently contains zero mentions of Monad while
`include/beman/transpose/monad.hpp` ships bind/join/kleisli with an
optional instance. Silence plus shipped code invites the obvious LEWG
question unprepared. Add a short section framing Monad as **deferred,
not rejected** (framing refined by Steve, 2026-07-14):

- Everything about the typeclass design leads to a consistent generic
  name for sequential composition eventually — today's
  `and_then`/`transform`/`let_value` are per-type members, not generic,
  which is exactly the gap typeclasses close — and `monad.hpp` proves
  the mechanism carries Monad without strain.
- It is omitted for one reason only: nothing being proposed calls
  `bind`. `traverse`/`transpose` need Applicative's independent
  composition; attaching the family's biggest naming discussion to a
  paper whose operations never use it buys nothing. For now.
- The slot stays open for the paper that needs generic sequential
  composition; the evidence that it slots in cleanly is in the tree.

Cite the relationships essay (item 4) once it has a URL.

Acceptance: the section exists; grep for 'monad' in D3200R0 is no longer
empty; references section gains P0798/P2505 if not present.

## 2. Label unproposed repo surface as evidence

`fold.hpp` (Foldable CRTP base, `fold_map`, ten derived ops) and
`monad.hpp` are repo surface, not paper surface — D3200R0 proposes only
Applicative and Traversable. Make the status explicit so reviewers
reading the repo don't mistake shipped code for proposed wording:

- Header-top comment in `include/beman/transpose/fold.hpp` and
  `monad.hpp`: implementation evidence, not proposed by D3200R0; the
  fold family is proposed by the recursive-tree-algorithms companion
  paper (Paper D); Monad is deliberately unproposed.
- Matching paragraph in `docs/provenance.md` (it already tracks
  intentional deviations — this is the same genre).
- One line in D3200R0's non-goals if not covered by item 1.

Acceptance: both headers and provenance.md state the status; wording
consistent with tree_algorithms extraction-plan §2 ("repo surface ≠
paper surface").

## 3. Keep Traversable free of a Foldable superclass requirement

Paper D will propose Foldable/`fold_map`. If this repo's Traversable
concept or CRTP base ever *requires* Foldable (Haskell-superclass
style), D would be proposing a concept beneath an already-reviewed one —
a dependency inversion. Verify `traverse.hpp` has no such requirement
today (believed true: `traverse` needs only Applicative + the walk);
add a comment at the Traversable base recording this as a deliberate
constraint, and cite `foldMapDefault`-style derivation as compatibility
evidence rather than a requirement.

Acceptance: comment present; no concept/requires clause ties Traversable
to Foldable; a law-test or static_assert demonstrating traverse-without-
foldable-instance on some type would pin it (simd_lanes may already be
this witness — check).

## 4. Relationships essay hook

When the out-of-band essay (the "missing Paper B" / how-the-set-fits
piece; venue sdowney.org or a sixth entry in `papers/blog/`) is
published, cite it from D3200R0's companion/roadmap text. If it becomes
blog entry six, it follows the existing org→md export flow
(`papers/blog/Makefile`, `blog-export.el`) and gets added to
`index.org`.

Blocked on: essay drafted (owned in tree_algorithms plan, item G).

## 5. Remove the pure/apply forms; `invoke` is the applicative core

Ruling (Steve, 2026-07-13): the classic `apply` formulation — a callable
held *inside* the context, applied to one argument-in-context at a time —
is a Haskell currying artifact, rooted in a misunderstanding when
transplanted to C++; it helps no one understand anything and all such
forms are removed from the public surface. The set already contains the
proof that it was never the primitive: `std::simd::vec` cannot even form
`vec<callable>`, so `apply` is unspellable exactly where the proposal's
motivation lives, while n-ary `invoke` works everywhere.

Concretely:

- **Remove from the public surface**: `apply`, `ap`, and the
  `terminating_partial` currying helper in `apply.hpp`; `monad.hpp`'s
  synthesized `apply`. `pure` **stays** (lifting a value into the
  context is genuinely primitive — traverse of an empty structure needs
  it); the Applicative primitives become `pure` + n-ary `invoke`.
- **Rewrite instance impls** that implement or route through `apply`
  (`array.hpp`, `sender.hpp`, `zip_list.hpp`, `simd_lanes.hpp`,
  `sequence.hpp`; `simd.hpp` is already invoke-only and becomes the
  model, not the exception).
- **Restate the laws in invoke form** (McBride–Paterson canonical:
  `invoke(f, u1, …, un)`); the Identity/Homomorphism/Interchange/
  Composition tests currently phrased through apply get invoke
  restatements. Where `invoke` was *implemented* by internal currying,
  implement it directly n-ary.
- **Paper text**: D3200R0 drops "`apply` as an alternate spelling" and
  gains a short "why not apply" note — the simd argument is a teaching
  moment, and this dovetails with the "Why not Monad" section (item 1):
  both cuts are the same editorial principle, C++ spellings over Haskell
  artifacts.
- Consider renaming `apply.hpp` (it holds the Applicative typeclass) to
  match; `invoke.hpp` or `applicative.hpp`.

Ripples elsewhere (tracked in their own repos): fingertree
`typeclass/applicative.hpp` mirrors pure/apply; trees/main pedagogy
(org Part 6) teaches pure+apply as primitives and needs its framing
updated on next talk revision; the fixpoint evidence repo may sweep
opportunistically (non-gating). tree_algorithms is unaffected — it has
no applicative surface.

## 6. BinaryTree example cross-check (standing item)

`examples/binary_tree.hpp` here and
`tree_algorithms/include/beman/tree_algorithms/binary_tree.hpp` are
independent ports of the same origin tree. Traversal order is
contractual (in-order). Any semantic change to either copy must be
checked against the other. No action now; recorded so it survives
context loss.
