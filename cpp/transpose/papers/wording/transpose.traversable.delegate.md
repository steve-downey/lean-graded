::: add

::: wording

## Delegated traversal [transpose.traversable.delegate]{- .sref} {-}

```cpp
template<class TRAVERSABLE_MAP, class T, class F>
auto traverse_with(this auto&&, const TRAVERSABLE_MAP& traversable_map, F&& function,
                   T&& value);
```

[x]{.pnum} *Effects*: Traverses `value` using the traversable object `traversable_map` rather than `*this`. The applicative object is the one `applicative_typeclass` names for the context `function` returns.

[x+1]{.pnum} *Returns*: The result of that traversal.

```cpp
template<class TRAVERSABLE_MAP, class APPLICATIVE_MAP, class T, class F>
auto traverse_with(this auto&&, const TRAVERSABLE_MAP& traversable_map,
                   const APPLICATIVE_MAP& applicative_map, F&& function, T&& value);
```

[x+2]{.pnum} *Effects*: Equivalent to:

```cpp
return traversable_map.traverse(applicative_map, forward<F>(function),
                                forward<T>(value));
```

```cpp
template<class TRAVERSABLE_MAP, class T>
auto transpose_with(this auto&& self, const TRAVERSABLE_MAP& traversable_map,
                    T&& value);
```

[x+3]{.pnum} *Effects*: Equivalent to:

```cpp
return self.traverse_with(
    traversable_map, [](auto&& x) { return forward<decltype(x)>(x); },
    forward<T>(value));
```

:::

:::
