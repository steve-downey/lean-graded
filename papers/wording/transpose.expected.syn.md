::: add

```cpp
template<class EXPECTED, class ERROR_TYPE>
inline constexpr bool $is-expected-with-error-v$ = false; // exposition only
```

```cpp
template<class VALUE_TYPE, class ERROR_TYPE>
inline constexpr bool $is-expected-with-error-v$<expected<VALUE_TYPE, ERROR_TYPE>, ERROR_TYPE> =
    true; // exposition only
```

```cpp
template<class CARRIER>
struct $carrier-value$ {
  using type = CARRIER;
}; // exposition only
```

```cpp
template<class VALUE, class ERROR>
struct $carrier-value$<expected<VALUE, ERROR>> {
  using type = VALUE;
}; // exposition only
```

```cpp
template<class CARRIER>
using $carrier-value-t$ =
    typename $carrier-value$<remove_cvref_t<CARRIER>>::type; // exposition only
```

```cpp
template<class F, class A>
using $bind-result-t$ = remove_cvref_t<invoke_result_t<F, const A&>>; // exposition only
```

```cpp
template<class ERROR_TYPE, class... CARRIERS>
inline constexpr bool $all-declare-v$ =
    ($is-expected-with-error-v$<remove_cvref_t<CARRIERS>, ERROR_TYPE> && ...); // exposition only
```

```cpp
template<class ERROR_TYPE, class CARRIER>
inline constexpr bool $declares-or-bare-v$ =
    (!graded_context<remove_cvref_t<CARRIER>>) ||
    $is-expected-with-error-v$<remove_cvref_t<CARRIER>, ERROR_TYPE>; // exposition only
```

```cpp
template<class ERROR_TYPE, class... CARRIERS>
inline constexpr bool $all-declare-or-bare-v$ =
    ($declares-or-bare-v$<ERROR_TYPE, CARRIERS> && ...); // exposition only
```

```cpp
template<class VALUE_TYPE, class ERROR_TYPE>
struct ExpectedApplicativeImpl {
  // @[transpose.expected.applicative]{- .sref}@, applicative instance for expected
  template<class VALUE>
  auto pure(this auto&&, VALUE&& value) -> expected<remove_cvref_t<VALUE>, ERROR_TYPE>;

  template<class FUNCTION, class FIRST, class... REST>
  auto invoke(this auto&&, FUNCTION&& function,
              const expected<FIRST, ERROR_TYPE>& first,
              const expected<REST, ERROR_TYPE>&... rest)
      -> expected<
          remove_cvref_t<invoke_result_t<FUNCTION&, const FIRST&, const REST&...>>,
          ERROR_TYPE>;

  template<class FUNCTION, class... CARRIERS>
    requires(sizeof...(CARRIERS) > 0) &&
            ($is-expected-v$<remove_cvref_t<CARRIERS>> || ...) &&
            (!$all-declare-v$<ERROR_TYPE, CARRIERS...>) &&
            $all-declare-or-bare-v$<ERROR_TYPE, CARRIERS...>
  auto invoke(this auto&&, FUNCTION&& function, const CARRIERS&... operands)
      -> expected<remove_cvref_t<
                      invoke_result_t<FUNCTION&, const $carrier-value-t$<CARRIERS>&...>>,
                  ERROR_TYPE>;

  template<class FUNCTION, class... CARRIERS>
    requires(sizeof...(CARRIERS) > 0) &&
            ($is-expected-v$<remove_cvref_t<CARRIERS>> || ...) &&
            (!$all-declare-or-bare-v$<ERROR_TYPE, CARRIERS...>) &&
            ($mixes-with-model$<grade_of_t<expected<VALUE_TYPE, ERROR_TYPE>>, CARRIERS> &&
             ...)
  auto invoke(this auto&&, FUNCTION&& function, const CARRIERS&... operands)
      -> $mixed-result-t$<grade_of_t<expected<VALUE_TYPE, ERROR_TYPE>>,
                        expected<remove_cvref_t<invoke_result_t<
                                     FUNCTION&, const $carrier-value-t$<CARRIERS>&...>>,
                                 ERROR_TYPE>,
                        CARRIERS...>;
};
```

```cpp
template<class VALUE_TYPE, class ERROR_TYPE>
struct ExpectedApplicativeMap : Applicative<ExpectedApplicativeImpl<VALUE_TYPE, ERROR_TYPE>> {
  using ExpectedApplicativeImpl<VALUE_TYPE, ERROR_TYPE>::invoke;
  using ExpectedApplicativeImpl<VALUE_TYPE, ERROR_TYPE>::pure;
};
```

```cpp
template<class VALUE_TYPE, class ERROR_TYPE>
struct AccumulatingExpectedApplicativeImpl {
  // @[transpose.expected.accumulating]{- .sref}@, accumulating instance
  template<class VALUE>
  auto pure(this auto&&, VALUE&& value) -> expected<remove_cvref_t<VALUE>, ERROR_TYPE>;

  template<class FUNCTION, class FIRST, class... REST>
  auto invoke(this auto&&, FUNCTION&& function,
              const expected<FIRST, ERROR_TYPE>& first,
              const expected<REST, ERROR_TYPE>&... rest)
      -> expected<
          remove_cvref_t<invoke_result_t<FUNCTION&, const FIRST&, const REST&...>>,
          ERROR_TYPE>;

  template<class FUNCTION, class... CARRIERS>
    requires(sizeof...(CARRIERS) > 0) &&
            ($is-expected-v$<remove_cvref_t<CARRIERS>> || ...) &&
            (!$all-declare-v$<ERROR_TYPE, CARRIERS...>) &&
            $all-declare-or-bare-v$<ERROR_TYPE, CARRIERS...>
  auto invoke(this auto&&, FUNCTION&& function, const CARRIERS&... operands)
      -> expected<remove_cvref_t<
                      invoke_result_t<FUNCTION&, const $carrier-value-t$<CARRIERS>&...>>,
                  ERROR_TYPE>;

  template<class FUNCTION, class... CARRIERS>
    requires(sizeof...(CARRIERS) > 0) &&
            ($is-expected-v$<remove_cvref_t<CARRIERS>> || ...) &&
            (!$all-declare-or-bare-v$<ERROR_TYPE, CARRIERS...>) &&
            ($mixes-with-model$<grade_of_t<expected<VALUE_TYPE, ERROR_TYPE>>, CARRIERS> &&
             ...)
  auto invoke(this auto&&, FUNCTION&& function, const CARRIERS&... operands)
      -> $mixed-result-t$<grade_of_t<expected<VALUE_TYPE, ERROR_TYPE>>,
                        expected<remove_cvref_t<invoke_result_t<
                                     FUNCTION&, const $carrier-value-t$<CARRIERS>&...>>,
                                 ERROR_TYPE>,
                        CARRIERS...>;
};
```

```cpp
template<class VALUE_TYPE, class ERROR_TYPE>
struct AccumulatingExpectedApplicativeMap
    : Applicative<AccumulatingExpectedApplicativeImpl<VALUE_TYPE, ERROR_TYPE>> {
  using AccumulatingExpectedApplicativeImpl<VALUE_TYPE, ERROR_TYPE>::invoke;
  using AccumulatingExpectedApplicativeImpl<VALUE_TYPE, ERROR_TYPE>::pure;
};
```

:::
