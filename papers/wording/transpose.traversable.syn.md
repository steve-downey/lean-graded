::: add

```cpp
template<class Impl>
struct Traversable : protected Impl {
  // Alternate-core: Impl::traverse is the primitive; transpose is derived
  // from it. A transpose-primitive Impl would shadow transpose instead.
  using Impl::traverse;
  using element_type = typename Impl::element_type;

  // @[transpose.traversable.ops]{- .sref}@, traversal operations
  template<class T, class F> auto for_each(this auto&& self, T&& value, F&& function);

  template<class T> auto transpose(this auto&& self, T&& value);

  // @[transpose.traversable.delegate]{- .sref}@, delegated traversal
  template<class TRAVERSABLE_MAP, class T, class F>
  auto traverse_with(this auto&&, const TRAVERSABLE_MAP& traversable_map, F&& function,
                     T&& value);

  template<class TRAVERSABLE_MAP, class APPLICATIVE_MAP, class T, class F>
  auto traverse_with(this auto&&, const TRAVERSABLE_MAP& traversable_map,
                     const APPLICATIVE_MAP& applicative_map, F&& function, T&& value);

  template<class TRAVERSABLE_MAP, class T>
  auto transpose_with(this auto&& self, const TRAVERSABLE_MAP& traversable_map,
                      T&& value);
};
```

::: wording

[x]{.pnum} A program that instantiates `Traversable<Impl>` is ill-formed unless `is_same_v<Impl, false_type>` is `false` and `requires { typename Impl::element_type; }` is `true`.

:::

::: wording

```cpp
template<class T> inline constexpr auto traversable_typeclass = false_type{};
```

[x+1]{.pnum} *Remarks*: This variable template is the lookup point for the Traversable object of a structure type. A program may specialize it for a program-defined structure. The primary template names no traversable object.

:::

```cpp
template<class F, class T>
using $traverse-context-t$ = remove_cvref_t<invoke_result_t<
    F,
    const typename remove_cvref_t<decltype(traversable_typeclass<remove_cvref_t<T>>)>::
        element_type&>>; // exposition only
```

::: wording

```cpp
template<class POLICY, class CONTEXT>
concept applicative_object_for =
    applicative_object<POLICY, CONTEXT> && requires(const POLICY& policy) {
      { policy.pure(declval<applicative_value_t<CONTEXT>>()) } -> same_as<CONTEXT>;
    };
```

[x+2]{.pnum} *Remarks*: This concept is satisfied when `POLICY` is an `applicative_object` over `CONTEXT` whose `pure` returns exactly `CONTEXT` from `CONTEXT`'s element type. The exact-return-type requirement is stronger than `applicative_object` itself makes -- that concept only asks that `pure` exist -- and it is what `traverse`'s trailing policy parameter needs: composing element results into anything other than `CONTEXT` itself would not preserve `traverse`'s "shape of `value` held in context" contract. Constraining the policy parameter on the full deep concept, not merely on `pure`, is what makes an argument that is not a real applicative object -- a further container, say -- ill-formed rather than silently accepted.

:::

::: wording

```cpp
template <class OBJ, class STRUCTURE>
concept traversable_object =
    requires(const OBJ &obj, const STRUCTURE &structure) {
        obj.traverse(
            applicative_typeclass<optional<applicative_value_t<STRUCTURE>>>,
            probe_witness<optional<applicative_value_t<STRUCTURE>>>{},
            structure);
        obj.for_each(
            structure,
            probe_witness<optional<applicative_value_t<STRUCTURE>>>{});
        obj.traverse_with(
            obj, probe_witness<optional<applicative_value_t<STRUCTURE>>>{},
            structure);
    } &&
    (!requires(const OBJ &) {
        applicative_typeclass<typename OBJ::element_type>.pure(
            declval<typename OBJ::element_type>());
    } || requires(const OBJ &obj, const STRUCTURE &structure) {
        obj.transpose(structure);
        obj.transpose_with(obj, structure);
    });
```

[x+3]{.pnum} *Remarks*: This concept is satisfied when `OBJ` provides the full Traversable object surface over `STRUCTURE`: `traverse`, `for_each` and `traverse_with`, each probed with a representative witness callable that lifts an element into `std::optional` (always a registered applicative context, for any element type). `transpose` and `transpose_with` are required only where `OBJ::element_type` itself names a registered applicative context: both are hard-wired to `applicative_typeclass<element_type>`, which names no applicative object for a structure like `std::vector<int>` whose elements are not themselves an applicative context -- transposing such a structure is not a meaningful operation, not a missing one, so this concept treats `transpose`/`transpose_with` as conditional the same way `applicative_object` treats `ap` and `subsume`. This concept does not require a Foldable object: Traversable needs only an Applicative and the walk, the DELIBERATE CONSTRAINT `Traversable` itself carries.

:::

:::
