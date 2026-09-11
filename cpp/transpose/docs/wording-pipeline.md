# The wording pipeline

<!-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception -->

P3200's normative wording is generated from the headers, not written by hand.
`beman.specgen` lowers the specgen markup on each in-scope header to a semantic
IR and renders mpark/wg21 markdown; `papers/D3200R0.md` splices the
fragments in at build time. See [`decisions.md#wording-generation`](decisions.md).

## The loop

```sh
make wording        # regenerate papers/wording from the headers
make wording-check  # fail if the checked-in fragments have drifted
make papers         # regenerate, then build the PDF
```

`make wording` runs [`scripts/gen-wording.sh`](../scripts/gen-wording.sh),
which needs `specgen` on `PATH` (or `SPECGEN=` pointing at it) and a Clang 22
development install. The generated fragments are checked in, so the paper
builds without either.

## What generates what

`specgen` reads only the main file's declaration/comment interleave, so each
header is rendered on its own and contributes its own synopsis subclause.
`--root` names that synopsis, which keeps the root fragments distinct in the
shared output directory.

| header | `--root` | subclauses |
| ------ | -------- | ---------- |
| `apply.hpp` | `transpose.applicative.syn` | `.basis` `.derived` `.grade` `.delegate` `.optional` |
| `traverse.hpp` | `transpose.traversable.syn` | `.ops` `.delegate`, plus `transpose.alg.traverse` |
| `transpose.hpp` | `transpose.alg.syn` | `transpose.alg.transpose` |
| `sequence.hpp` | `transpose.range.syn` | `.traverse` |
| `array.hpp` | `transpose.array.syn` | `.applicative` `.tuple` |
| `grade.hpp` | `transpose.grade.syn` | `.subsume` |
| `error_set.hpp` | `transpose.errset.syn` | `.cons` `.obs` `.ops` `.empty` `.lattice` `.recover` |
| `expected.hpp` | `transpose.expected.syn` | `.applicative` `.accumulating` |

`--split` never deletes files an earlier run left behind, so each header's
ordered manifest is written beside the fragments; it is the record the paper's
include order is reconciled against.

Headers outside the proposal carry no markup and are not generated from:
`fold.hpp`, `monad.hpp`, `monoid.hpp`, `dual_monoid.hpp`, `functor.hpp`,
`sender.hpp`, `zip_list.hpp`, `simd*.hpp`, `config.hpp`. `sender` and
`zip_list` are non-normative demonstration types (see
[`provenance.md`](provenance.md)); Monad and Foldable are stated non-goals, so
their instances inside generated headers are `\omit`ted.

## Rules for marking up a header

Comment spelling is significant. `//!` and `/*! */` are specgen docblocks and
become wording; `///` and `/** */` are Doxygen and are stripped; plain `//`
survives as a draft comment where the corresponding source is rendered. Design
commentary belongs in `///` so that it does not land in a rendered synopsis.
A trailing `// NOLINT(...)` on a declaration renders too, so spell those
`/// NOLINT(...)`: clang-tidy honours the marker in any comment form.

**Declare members in-class, define them out of line.** specgen now splices an
in-class body out of the synopsis whichever entities it names, so this is
recommended rather than required: the definition's lexical position is what
places its wording, which is the reason to keep doing it. Out-of-line
definitions of members with an explicit object parameter are accepted by
GCC 14/15/16 and Clang 21/22, so the pattern costs nothing.

A constraint on an out-of-line definition must be spelled with the *same
tokens* as the in-class declaration's. Class scope is not in effect where the
out-of-line requires-clause appears, so a constraint that names a member
(`contains<E>()`) or the injected class name (`error_set_of`) cannot be
repeated there. Give such a constraint a namespace-scope spelling that works
in both positions -- `error_set_has_v` in `error_set.hpp` is the worked
example.

**`\omit` the implementation machinery a header declares.** A record
definition in the main file lands in the synopsis whether or not it is
documented and whether or not it sits in `detail`, so an unmarked helper
publishes itself as specification. The type-list machinery in `error_set.hpp`,
the grade-lifting helpers in `grade.hpp`, and the Monad and Foldable instances
are all `\omit`ted for this reason. An omitted class also takes its private
members with it, which is what keeps a private alias from being named by a
declaration the elision leaves behind.

**Route members to sections** with a `// \ref{stable.name}, group` comment in
the class body, and declare the section with a `// \rSec3[stable.name]{Title}`
marker at namespace scope. A long `\rSec` title may wrap onto following
plain `//` lines -- specgen joins them back -- but a `\ref{...}` group header
must stay on one line.

**Mark a `detail` entity `\expos` where it is defined**, and its uses render
as the exposition-only spelling with no qualifier -- in the header that defines
it or in any header that includes it. Bodies may name `detail` freely. The
leakage check reports a surviving qualifier wherever the namespace was
declared, so moving machinery into a header under `detail/` does not hide one,
and nothing has to move into the specified namespace to be named by a
declaration. See
[`decisions.md#wording-visible-internals`](decisions.md#wording-visible-internals),
which used to say the opposite.

An exposition-only entity's chain has to stop somewhere. Expose a helper the
entity names when its own definition explains more than it costs -- a
specialization follows its primary's exposition name without a marker of its
own, so a two-case helper like `carrier_value` is exposed whole -- and mask the
definition with `\seebelow` where it does not: `mixed_result_t` renders
`= see below` rather than opening four levels of grade algebra. Either way no
raw implementation name should reach the wording; the audit for that is
grepping the fragments for the helper names.

**Masking is available where the entity cannot move.** Bare `\seebelow` masks
a deduced or an explicit trailing return type, the whole right-hand side of a
type alias, and a namespace-scope variable's declared type -- `error_set` and
`recover` use the first two, `applicative_eval` the third, which is how the
draft spells an object whose type is not specified. A *reference*-typed
variable does not mask cleanly yet (steve-downey/specgen#33), so a forwarding
object is declared rather than a forwarding reference. Both verbatim
markers now *replace* the extracted declaration rather than emitting a second
copy of it, so `\verbatim-synopsis` on a class definition and
`\verbatim-itemdecl` on a declaration are usable; neither is used here, since
an authored synopsis is a hand-maintained one and reintroduces exactly the
drift this pipeline exists to prevent.

**Document namespace-scope entities.** A `//!` docblock on an alias, alias
template, variable, variable template, or concept at namespace scope becomes a
wording item, and `\expos` on one renames it to its kebab-case exposition
spelling at every use -- `traverse-context-t` and `error-set-has-v` are the
worked examples. A docblock on a kind that would produce no wording is an
error rather than a silent drop, unless `\omit`, `\merge` or `\expos` says
the silence is deliberate.

**Describe a class in its own docblock.** A `//!` block on a class or
class-template definition becomes the type's description, rendered as an
itemdescr with no itemdecl after the synopsis -- how the draft writes a general
subclause. An authored `\mandates` there replaces the paragraph derived from
the class's `static_assert`s; `error_set_of` is the worked example. The
`*-equiv` extraction markers and `\verbatim-itemdecl` mean nothing on a class
and are errors.

## Transclusion

[`papers/filters/transclude.py`](../papers/filters/transclude.py)
replaces a fenced div carrying the `include` class with the parsed blocks of
the file it names:

```markdown
::: {.include file="wording/transpose.applicative.basis.md"}
:::
```

It is selected by [`papers/defaults.yaml`](../papers/defaults.yaml), which
MPark.WG21's `base.mk` already layers after its own `doc` and `formatting`
defaults.
A defaults file *replaces* a list-valued key rather than merging into it, so
that file restates the whole filter chain; transclusion runs first, so the
`[x]{.pnum}` and `[stable.name]{- .sref}` spans inside a fragment reach
`wg21.py` exactly as if they had been typed into the paper.

The fragments must not become prerequisites of the paper: `base.mk` computes
its pandoc inputs as `$(filter %.md, $^)` and would hand each fragment to
pandoc as a further input file. [`papers/Makefile`](../papers/Makefile) depends
on `wording/.stamp` instead, which `make wording` writes.

Building the paper prints `mpark/wg21: stable name transpose.* not found` for
every new subclause. That is expected: the names are not in the C++ draft's
stable-name database, so they render as plain bracketed text rather than as a
link.

One cosmetic defect is open upstream: an exposition-only rename does not
re-flow a continuation line, so a wrapped definition's second line can sit
short of the arguments it should align under (steve-downey/specgen#67, visible
in `mixes-with-model` in `transpose.grade.syn.md`). It is not worked around,
because the workaround would be reformatting the library to suit the generator
-- the thing
[`decisions.md#wording-visible-internals`](decisions.md#wording-visible-internals)
now refuses.

## The vendored framework

MPark.WG21 is a squashed subtree at `papers/wg21`, so it updates with

```sh
git subtree pull --prefix=papers/wg21 wg21-upstream master --squash
```

given a `wg21-upstream` remote pointing at <https://github.com/mpark/wg21>.
The subtree is unpatched, and should stay that way: everything this project
adds lives beside it in `papers/`, which is the layout `wg21/flat.mk`
documents.

[`papers/filters/bibliography-header.py`](../papers/filters/bibliography-header.py)
is the one shim. `wg21.py` removes an `unnumbered` class from the generated
references header unconditionally, and pandoc 3.9's citeproc does not set it,
so every paper carrying a citation aborts the filter with `ValueError`. A
twelve-line paper with one `[@Pnnnn]` reproduces it. The shim runs between
citeproc and `wg21.py` and puts the class back; delete it once upstream guards
the removal.
