::: add

::: wording

## Delegated application [transpose.applicative.delegate]{- .sref} {-}

```cpp
template<class APPLICATIVE_MAP, class FUNCTION, class FIRST_ARGUMENT,
         class... REST_ARGUMENTS>
auto invoke_with(this auto&&, const APPLICATIVE_MAP& applicative_map,
                 FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
                 REST_ARGUMENTS&&... rest_arguments);
```

[x]{.pnum} *Effects*: Equivalent to:

```cpp
return applicative_map.invoke(forward<FUNCTION>(function),
                              forward<FIRST_ARGUMENT>(first_argument),
                              forward<REST_ARGUMENTS>(rest_arguments)...);
```

```cpp
template<const auto& APPLICATIVE_MAP, class FUNCTION, class FIRST_ARGUMENT,
         class... REST_ARGUMENTS>
auto invoke_with(this auto&&, FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
                 REST_ARGUMENTS&&... rest_arguments);
```

[x+1]{.pnum} *Effects*: Equivalent to:

```cpp
return APPLICATIVE_MAP.invoke(forward<FUNCTION>(function),
                              forward<FIRST_ARGUMENT>(first_argument),
                              forward<REST_ARGUMENTS>(rest_arguments)...);
```

:::

:::
