# beman.transpose: Shape-Preserving Traversal and Transposition for Contextual Computations

<!-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception -->

<!-- markdownlint-disable line-length -->
[![Library Status](https://raw.githubusercontent.com/bemanproject/beman/refs/heads/main/images/badges/beman_badge-beman_library_under_development.svg)](https://github.com/bemanproject/beman/blob/main/docs/beman_library_maturity_model.md#the-beman-library-maturity-model)
[![Continuous Integration Tests](https://github.com/bemanproject/transpose/actions/workflows/ci_tests.yml/badge.svg)](https://github.com/bemanproject/transpose/actions/workflows/ci_tests.yml)
[![Lint Check (pre-commit)](https://github.com/bemanproject/transpose/actions/workflows/pre-commit-check.yml/badge.svg)](https://github.com/bemanproject/transpose/actions/workflows/pre-commit-check.yml)
[![Coverage](https://coveralls.io/repos/github/bemanproject/transpose/badge.svg?branch=main)](https://coveralls.io/github/bemanproject/transpose?branch=main)
![Standard Target](https://github.com/bemanproject/beman/blob/main/images/badges/cpp29.svg)
<!-- markdownlint-restore -->

**Implements**: shape-preserving `traverse` / `transpose` plus a bundled
customization (typeclass-object) mechanism, proposed in *Shape-Preserving
Traversal and Transposition for Contextual Computations* (P3200, draft).

**Status**: [Under development and not yet ready for production use.](https://github.com/bemanproject/beman/blob/main/docs/beman_library_maturity_model.md#under-development-and-not-yet-ready-for-production-use)

## The problem

C++ has many vocabulary types and computational contexts that are individually
well understood, but no uniform way to traverse a structure while producing
contextual results and then *transpose* the result into a single outer context:

### Build

You can build transpose using a CMake workflow preset:

```bash
cmake --workflow --preset gcc-release
```
structure<context<T>>  ->  context<structure<T>>
```

`beman.transpose` provides one front-door API — `traverse` and `transpose` —
that works across three independent contexts over the same structure:

| Before                                   | After (`beman::transpose::transpose`)      |
| ---------------------------------------- | ------------------------------------------ |
| ad-hoc loops over `vector<optional<T>>`  | `optional<vector<T>>` (fallible value)     |
| bespoke async result gathering           | `sender<vector<T>>`  (deferred result)     |
| hand-written lanewise reshaping          | `zip_list<vector<T>>` (lanewise / SIMD)    |

All three flow through the same verbs:

```cpp
#include <beman/transpose/transpose.hpp>
namespace bt = beman::transpose;

bt::transpose(std::vector<std::optional<int>>{...}); // -> optional<vector<int>>
bt::transpose(std::vector<bt::sender<int>>{...});    // -> sender<vector<int>>
bt::transpose(std::vector<bt::zip_list<int>>{...});  // -> zip_list<vector<int>>
```

`std::optional` is the only standard context that ships with a registered
instance; `sender` and `zip_list` are deliberately minimal, non-normative
demonstration types proving the front door is context-agnostic.

## Public surface

Headers live under `include/beman/transpose/`:

- `transpose.hpp` — umbrella header and the front-door `transpose` verb
- `traverse.hpp` — the `Traversable` customization base and free `traverse`
- `apply.hpp`, `functor.hpp`, `fold.hpp`, `monoid.hpp`, `dual_monoid.hpp`,
  `monad.hpp` — the bundled customization core (applicative / functor /
  foldable / monoid / monad typeclass objects)
- `sequence.hpp` — `Foldable`/`Traversable` instances for `std::vector`
- `zip_list.hpp`, `sender.hpp` — non-normative demonstration contexts
- `detail/typeclass_base.hpp` — shared support

The customization mechanism supports three lookup modes: implicit
(`*_typeclass<T>` variable template), explicit object argument, and NTTP-pinned.

## License

`beman.transpose` is licensed under the Apache License v2.0 with LLVM Exceptions.

## Building

The top-level `Makefile` drives the workflow; its default target builds and runs
all tests:

```sh
make            # configure, build, and run the test suite (Asan by default)
make compile    # build only
make ctest      # run tests on the current build
```

Tooling (CMake, Catch2, etc.) is provisioned via `uv` into a local `.venv`.
`make TOOLCHAIN=gcc-15` selects `etc/gcc-15-toolchain.cmake`; `CONFIG=RelWithDebInfo`
selects a non-sanitized configuration. CMake presets (`gcc-debug`, `llvm-debug`,
...) are also provided for Beman tooling.

The library is header-only (`beman::transpose` is an `INTERFACE` target requiring
C++23) and consumable via `find_package`/`add_subdirectory`.

## Provenance

The traversal machinery was extracted and renamed from the `trees` pedagogy
repository; see [`docs/provenance.md`](docs/provenance.md). The WG21 paper
framework, [MPark.WG21](https://github.com/mpark/wg21), is a squashed subtree
under `papers/wg21`, with the papers beside it in `papers/`; the `infra/`
directory is vendored from the
[Beman Project infra](https://github.com/bemanproject/infra).

P3200's wording is generated from the headers rather than written by hand; see
[`docs/wording-pipeline.md`](docs/wording-pipeline.md).
