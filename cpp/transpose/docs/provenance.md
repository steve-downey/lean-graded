# Provenance: extraction of Paper A into beman.transpose

<!-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception -->

This library is the standalone Beman-layout reference implementation of **Paper
A** of the P3200 coordinated proposal set (shape-preserving `traverse` /
`transpose` plus bundled customization). Its core was extracted from the
`trees` pedagogy/monorepo rather than written fresh, so this note records where
the code came from.

## Source

- **Source repository**: `trees` (local working copy `~/src/trees`).
- **Source commit at extraction**: `bee1a0ec8f9d20c263f458fa3d6047e5351c60fd`
  ("remove Spaces symlinks from repo").
- **Source paths**: `src/smd/typeclass/` (typeclass core) and
  `src/smd/ziplist/` (the ZipList applicative).
- **Design rationale**: `docs/notes/standardization-inverted-triangle-plan.md`
  and the `beman-extraction-*` notes in the same directory.

A `git notes` annotation on the import commit in this repository points back to
the source commit range.

## What was copied and renamed

The typeclass layer in `trees` is self-contained (no dependency on the
finger-tree or fixpoint modules), so it was lifted as a unit and mechanically
rewritten:

| Aspect            | `trees` form                          | `beman.transpose` form                |
| ----------------- | ------------------------------------- | ------------------------------------- |
| Namespace         | `smd`, `smd::typeclass`, `smd::detail`| `beman::transpose`, `::detail`        |
| Include guards    | `INCLUDED_SMD_TYPECLASS_*`            | `BEMAN_TRANSPOSE_*_HPP`               |
| Includes          | `<smd/typeclass/...>`                 | `<beman/transpose/...>`               |
| `traversable.hpp` | single header                         | `traverse.hpp` + free `transpose` in `transpose.hpp` |
| `applicative.hpp` | —                                     | `apply.hpp`                           |
| `foldable.hpp`    | —                                     | `fold.hpp`                            |
| `typeclass_base`  | top-level                             | `detail/typeclass_base.hpp`           |
| `ziplist/`        | `zip_list.hpp` + `zip_list_applicative.hpp` | merged into `zip_list.hpp`      |

## Intentional deviations

- **`beman::optional` support dropped.** The `trees` sources carried parallel
  instances for `beman::optional::optional`. To keep this a standalone unit
  whose only third-party dependency is Catch2 (for tests), only `std::optional`
  instances were ported. `std::optional` fully covers the fallible-value domain.
- **New code to close the three-domain gate.** Paper A required all three of its
  motivating domains to flow through one API. ZipList already existed; this repo
  adds `sequence.hpp` (a `std::vector` `Traversable`/`Foldable`, the shared
  structure for all three domains) and `sender.hpp` (a minimal deferred
  applicative standing in for a `std::execution` sender). Both `sender` and
  `zip_list` are non-normative demonstration types, not proposed standard types.
- **Tests rewritten, not ported verbatim.** The original Catch2/`.t.cpp` suites
  leaned on `beman::optional` and on tree types that are out of scope here.
  Fresh, namespace-correct tests were written, including an explicit
  three-domain proof in `tests/beman/transpose/transpose.test.cpp`.
- **`.copier-answers.yml` re-pointed to the Beman copier exemplar.** The repo
  was originally stamped from a different (cookiecutter-style) `example`
  template. The answers file was rewritten in Copier's format to track the
  Beman exemplar copier template
  (`https://github.com/steve-downey/exemplar.git`, `_commit
  v2.4.1-35-g2313d70`), with answers matching this repo (`project_name:
  transpose`, `minimum_cpp_build_version: '23'`, `unit_test_library: catch2`,
  `paper: P3200`). The template currently lives on the `copier` branch (PR not
  yet merged upstream), so updates use `copier update --trust --vcs-ref copier`.
  Only the answers file was re-pointed; template-managed files (CMake, presets,
  CI) were not regenerated, to preserve this repo's hand-built layout and
  custom Makefile workflow.

## Synchronization policy

`trees` remains the pedagogy/exploration repository; `beman.transpose` is the
production reference implementation for Paper A. The intended relationship is a
one-way extraction with deliberate divergence: API evolution tracking paper
revisions happens here, and is not back-ported to `trees`.

## 2026-07-14: the pure/apply forms removed; evidence labels added

Coordinated-set ruling (recorded in the tree-coordination meta-repo, SYNC
entry 3): the classic contextual-application forms — `apply`, `ap`, the
`terminating_partial` currying helper, Monad's synthesized `apply` — are
removed from the public surface. Curried application of a
callable-in-context is a Haskell artifact, and `std::simd::vec` (which
cannot form `vec<callable>`) proves `apply` was never the primitive.
Applicative's single core is `pure` + n-ary `invoke`; the law suite is
stated in invoke form, and tests pin the *absence* of apply forms on every
instance. See D3200R0 "Why not `apply`".

At the same time, unproposed repo surface was labeled explicitly (repo
surface ≠ paper surface): `fold.hpp` carries the fold family, proposed by
the recursive-tree-algorithms companion paper, not by D3200R0; `monad.hpp`
is evidence that the mechanism carries Monad, which is deferred — not
rejected — because nothing currently proposed calls `bind`. See D3200R0
"Why not Monad" and the header-top notes
in both files. Traversable's freedom from any Foldable superclass
requirement is now a documented deliberate constraint in `traverse.hpp`.
