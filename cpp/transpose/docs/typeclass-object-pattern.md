<!-- markdownlint-disable MD013 -->

# Typeclass Object Pattern in This Repository

This repository approximates the intent of C++03 concept maps — approximates, not reproduces — with a typeclass-object lookup.

The short version:

- A concept is represented by a typeclass object interface.
- A concrete type chooses behavior by specializing a lookup object.
- Generic algorithms call through that lookup object instead of relying on ADL overload sets.

## Why this exists

The goal is open extension with static dispatch:

- no virtual dispatch
- no mandatory type erasure
- explicit instance selection when needed
- predictable, testable instance lookup by type

This is close to the old concept-map idea.
For a given type and concept, pick a specific implementation map.

## The surface in this repo

This repository uses one implementation surface:

- Per-concept variable templates (`functor_typeclass<T>`, `foldable_typeclass<T>`,
  `applicative_typeclass<T>`, `traversable_typeclass<T>`, `monad_typeclass<T>`) for lookup.
- Generic algorithms dispatch through those looked-up objects.
- Headers live under `include/beman/transpose/`.
- Tests live under `tests/beman/transpose/`.
- Examples live under `examples/`.

## Lookup modes (important)

The typeclass implementation object is, true to its name, an object — and should be usable in three ways:

1. Implicit lookup by variable template.

- Example shape: `functor_typeclass<T>` in `include/beman/transpose/`.

1. Explicit object argument.

- Call a generic algorithm with a specific typeclass object when you want local policy control.

1. Non-type template parameter (NTTP) pinning.

- A generic function can bind the looked-up typeclass object as an NTTP default and use it directly.

This is not a cosmetic detail.
It keeps instance selection explicit, testable, and overridable while preserving static dispatch.

The NTTP style in practice:

- `template <typename P, const auto& functor = beman::transpose::functor_typeclass<P>>`
- See `examples/lookup_modes_example.cpp` for NTTP pinning examples.

In `include/beman/transpose/`, preserve this spirit through `*_typeclass<T>` lookup objects.
If additional wrapper APIs are introduced, they should keep explicit object override and NTTP pinning available for generic code.

In the current typeclass headers this is exposed directly via helper APIs such as:

- `invoke_with(map, ...)` and `invoke_with<map>(...)` in Applicative
- `traverse_with(map, ...)` in Traversable
- NTTP-pinned helper templates in foldable tests and tree tests

Current naming convention is `*_typeclass<T>` for implementation objects.

## Core mechanics

### Concept side

A concept contributes:

- a per-concept lookup variable template in `include/beman/transpose/`
- generic user-facing algorithms (`fmap`, `length`, `invoke`, `traverse`)

### Type side

A type participates by specializing the per-concept lookup object:

- specialize `*_typeclass<T>` to an instance object

### Call side

Generic code calls through the looked-up typeclass object, not type members directly:

- `functor_typeclass<T>.fmap(f, value)` — via looked-up object
- `foldable_typeclass<T>.fold_map(f, value)` — via looked-up object
- `applicative_typeclass<T>.invoke(fn, ax, ay)` — via looked-up object
- `beman::transpose::traverse(f, container)` — free function entry point

That call performs compile-time lookup to the right typeclass object specialization.

## How to add a new instance

1. Decide the concept and the concrete type or type family.
1. Implement the `*_typeclass<T>` specialization close to the type adapter header.
1. Keep operation names aligned with existing concept APIs.
1. Add a `.test.cpp` test file with at least:

- a breathing test
- one semantic behavior test
- one type-level expectation when meaningful

1. If an example is needed, add a source file in `examples/`.

## How to add a new concept

1. Add a new tag and generic entry-point API in `include/beman/transpose/<concept>.hpp`.
1. Add `*_typeclass<T>` specializations for at least one concrete type.
1. Add tests in `tests/beman/transpose/<concept>.test.cpp`.
1. Add the header to `beman.transpose` header file set in `CMakeLists.txt`.
1. If needed, add an examples source file in `examples/`.

## Testing and build wiring expectations

- Catch2 is the only test framework in active code paths.
- Typeclass-object behavior is tested in `tests/beman/transpose/*.test.cpp` and in example programs under `examples/` that instantiate and use `*_typeclass<T>` maps.
- The compatibility shim used during migration has been removed.
- Tests should use native Catch2 includes and macros.

## Algorithm objects: Inheriting from typeclass instances

An algorithm that composes multiple typeclass operations can inherit from the typeclass instance, bringing those operations into unqualified scope as inherited members.

The typeclass objects are stateless empty structs, so inheritance adds no data and slicing is not a concern.

### Pattern

```cpp
namespace detail {

template <class T,
          const auto& TC = beman::transpose::traversable_typeclass<beman::transpose::remove_cvref_t<T>>>
struct validate_impl : beman::transpose::remove_cvref_t<decltype(TC)> {
    template <class Pred>
    auto call(Pred&& pred, const T& value) const {
        // for_each is an inherited member — no qualification needed
        return this->for_each(value, [&](const auto& elem) -> std::optional<...> {
            if (pred(elem)) return {elem};
            return std::nullopt;
        });
    }
};

} // namespace detail

// Public CPO: single object, deduces T from argument
struct validate_fn {
    template <class Pred, class T>
    auto operator()(Pred&& pred, T&& value) const {
        return detail::validate_impl<beman::transpose::remove_cvref_t<T>>{}.call(
            std::forward<Pred>(pred), std::forward<T>(value));
    }
};
inline constexpr validate_fn validate{};
```

### Multi-typeclass composition

When an algorithm needs both Foldable and Traversable, inherit from both:

```cpp
template <class T,
          const auto& FC = beman::transpose::foldable_typeclass<beman::transpose::remove_cvref_t<T>>,
          const auto& TC = beman::transpose::traversable_typeclass<beman::transpose::remove_cvref_t<T>>>
struct transform_if_large_impl
    : beman::transpose::remove_cvref_t<decltype(FC)>,
      beman::transpose::remove_cvref_t<decltype(TC)> {
    using foldable_base    = beman::transpose::remove_cvref_t<decltype(FC)>;
    using traversable_base = beman::transpose::remove_cvref_t<decltype(TC)>;

    template <class F>
    auto call(std::size_t min_size, F&& f, const T& value) const {
        if (this->foldable_base::length(value) < min_size)
            return std::optional<T>{};
        return this->traversable_base::for_each(value, ...);
    }
};
```

### Key points

- The implementation is in `detail` — callers see only the deducing `operator()` on the CPO.
- `decltype` on a `const auto&` NTTP gives a reference type; use `remove_cvref_t<decltype(TC)>` at base specifiers, nested type extraction, and qualified disambiguation calls.
- ADL is suppressed because the CPO is an object, not a function.
- The NTTP defaults pin the typeclass lookup; callers can override if needed.
- Working example: see `examples/algorithm_object_example.cpp`.

## Applicative: Derived invoke via terminating partial application

In Haskell, Applicative is minimal (`pure` and `(<*>)`).
`sequenceA` and `traverse` style usage is naturally expressed by applying pure functions to effectful arguments.

In this C++ codebase, we model the same intent by deriving `invoke` from `pure` and `apply` using a terminating partial-application adapter:

```text
invoke(f, a, b, c) == ap(ap(ap(pure(partial(f)), a), b), c)
```

The helper object stores already-bound values.
On each call it either invokes `f` when enough arguments have been collected, or returns a new callable waiting for the next argument.

That gives us a practical equivalent of Ben Deane's terminating partial-application technique while preserving the object-lookup model.

Contract summary:

- Minimal required operations for Applicative impl are `pure` and `apply`.
- `invoke` is provided by the base `Applicative<Impl>`.
- Implementations may still override `invoke` for custom semantics or performance, for example shape-aware structures.

## Traps and corrections from tree-instance implementation

1. Keep effect sequencing and shape preservation explicit in Traversable.

- For tree traversals, tests caught regressions where effects were accidentally duplicated or shape changed.
- Practical rule: recurse structurally, combine in one place, and assert both shape and value behavior in tests.

1. Prefer explicit map lookup in tests for readability and diagnostics.

- `const auto& map = beman::transpose::traversable_typeclass<Tree>;` gives clearer compile errors than deeply nested generic calls.
- NTTP pinning earns its keep when proving lookup stability in generic helpers.

1. Be deliberate about fold-order semantics.

- `fold_map` on trees depends on traversal order chosen by the instance.
- Derived `fold_left` and `fold_right` behavior should be validated with tests that would fail if order flips.

1. Distinguish required operations from convenience operations.

- Applicative contract is `pure` plus `apply`.
- Everything else is derived unless explicitly overridden.
- Do not silently add alternative dispatch paths, for example ADL customizations, that bypass lookup objects.

1. Migration lesson: convert tests directly to native Catch2.

- Mixed macro styles in one file are easy to miss and produce confusing build failures.
- During migration, convert includes and assertion or test-case macros in the same edit pass.

## Notes for future cleanup

- Prefer explicit object lookup usage in tests when comparing alternate semantics.
- Preserve the lookup-first model.
- Avoid introducing parallel ADL-only customization paths for the same concept.
