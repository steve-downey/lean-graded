::: add

::: wording

## recover [transpose.errset.recover]{- .sref} {-}

```cpp
template<class... HANDLED, class VALUE, class... ERRORS, class HANDLER>
constexpr auto recover(const expected<VALUE, error_set_of<ERRORS...>>& computation,
                       HANDLER&& handler) -> $see below$;
```

[x]{.pnum} *Mandates*: `HANDLED` is not empty; every type in `HANDLED` is one of the computation's alternatives; and for each such type `handler` returns either `VALUE` or a `std::expected<VALUE, error_set<...>>`.

[x+1]{.pnum} *Effects*: For each type in `HANDLED` that the computation's error witnesses, invokes `handler` with that witness. A handler either recovers a value or raises an error set of its own. Witnesses for types outside `HANDLED`, and any a handler raises, survive into the result.

[x+2]{.pnum} *Returns*: The computation at the narrowed grade: the alternatives it may raise, less those handled, plus any a handler raises. The result holds a value when every witness present was recovered, and otherwise the surviving witnesses.

[x+3]{.pnum} *Remarks*: The handled set is annotated rather than inferred: it is given as explicit template arguments and checked against the computation's grade. Recovering one alternative from a value that raised two leaves the other, which is still an error. If more than one handled type is witnessed and each independently recovers a value, the first in canonical order is the result, matching the tie-break of `combined_with`.

```cpp
template<class T> inline constexpr bool $is-expected-v$ = false; // exposition only
```

```cpp
template<class VALUE, class ERROR>
inline constexpr bool $is-expected-v$<expected<VALUE, ERROR>> = true; // exposition only
```

```cpp
struct error_set_model {};
```

[x+4]{.pnum} *Remarks*: `error_set_model` names the model that the error-set grades belong to. It is what makes two grades comparable: grades of different models do not mix.

```cpp
template<class... ERRORS>
struct grade_model<error_set_of<ERRORS...>> {
  using type = error_set_model;
};
```

```cpp
template<class... LEFT, class... RIGHT>
struct grade_join<error_set_of<LEFT...>, error_set_of<RIGHT...>> {
  using type =
      error_set_join_t<error_set_of<LEFT...>, error_set_of<RIGHT...>>;
};
```

```cpp
template<class... ERRORS>
struct grade_bottom<error_set_of<ERRORS...>> {
  using type = error_set_bottom;
};
```

```cpp
template<class... LEFT, class... RIGHT>
struct grade_subsumes<error_set_of<LEFT...>, error_set_of<RIGHT...>>
    : bool_constant<
          error_set_subsumes_v<error_set_of<LEFT...>, error_set_of<RIGHT...>>> {};
```

```cpp
template<class VALUE, class ERROR>
struct grade_of<expected<VALUE, ERROR>> {
  using type = error_set<ERROR>;
};
```

```cpp
template<class VALUE, class... ERRORS>
struct grade_of<expected<VALUE, error_set_of<ERRORS...>>> {
  using type = error_set_of<ERRORS...>;
};
```

```cpp
template<class VALUE, class ERROR, class HEAD, class... TAIL>
struct rebind_grade<expected<VALUE, ERROR>, error_set_of<HEAD, TAIL...>> {
  using type = expected<VALUE, error_set_of<HEAD, TAIL...>>;
};
```

```cpp
template<class VALUE, class HEAD, class... TAIL>
  requires(!$is-expected-v$<VALUE>)
struct rebind_grade<VALUE, error_set_of<HEAD, TAIL...>> {
  using type = expected<VALUE, error_set_of<HEAD, TAIL...>>;
};
```

```cpp
template<class VALUE>
  requires(!$is-expected-v$<VALUE>)
struct rebind_grade<VALUE, error_set_of<>> {
  using type = VALUE;
};
```

```cpp
template<class VALUE, class ERROR>
struct rebind_grade<expected<VALUE, ERROR>, error_set_of<>> {
  using type = VALUE;
};
```

:::

:::
