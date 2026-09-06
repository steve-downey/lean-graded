::: add

```cpp
template<class VALUE_TYPE>
struct VectorTraversableImpl {
  using element_type = VALUE_TYPE;

  // @[transpose.range.traverse]{- .sref}@, traversable instance for vector
  template<class APPLICATIVE, class FUNCTION>
  auto traverse(this auto&&, const APPLICATIVE& applicative, FUNCTION&& function,
                const vector<VALUE_TYPE>& values);
};
```

```cpp
template<class VALUE_TYPE>
struct VectorTraversableMap : Traversable<VectorTraversableImpl<VALUE_TYPE>> {
  using VectorTraversableImpl<VALUE_TYPE>::traverse;
};
```

:::
