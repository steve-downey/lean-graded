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
concept applicative_object_for = requires(const POLICY& policy) {
  { policy.pure(declval<applicative_value_t<CONTEXT>>()) } -> same_as<CONTEXT>;
};
```

[x+2]{.pnum} *Remarks*: This concept is satisfied when `POLICY` names an applicative object over `CONTEXT`: it provides `pure`, returning exactly `CONTEXT`, from `CONTEXT`'s element type. It is the minimal signature every applicative object has, and constraining the trailing `traverse` policy on it is what makes an argument that is not an applicative object -- a further container, say -- ill-formed rather than silently accepted.

:::

:::
