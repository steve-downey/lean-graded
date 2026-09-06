::: add

```cpp
template<class T, size_t N>
struct ArrayApplicativeImpl {
  // @[transpose.array.applicative]{- .sref}@, applicative instance for array
  template<class VALUE> auto pure(this auto&&, VALUE&& value);

  template<class FUNCTION, class FIRST, class... REST>
  auto invoke(this auto&&, FUNCTION&& function, const FIRST& first,
              const REST&... rest);
};
```

```cpp
template<class T, size_t N>
struct ArrayApplicativeMap : Applicative<ArrayApplicativeImpl<T, N>> {
  using ArrayApplicativeImpl<T, N>::invoke;
  using ArrayApplicativeImpl<T, N>::pure;
};
```

:::
