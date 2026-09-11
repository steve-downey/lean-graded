::: add

::: wording

## Applicative instance for optional [transpose.applicative.optional]{- .sref} {-}

```cpp
template<class VALUE>
auto pure(this auto&&, VALUE&& value) -> optional<remove_cvref_t<VALUE>>;
```

[x]{.pnum} *Returns*: An engaged `optional` holding `value`.

```cpp
template<class FUNCTION, class FIRST, class... REST>
auto invoke(this auto&&, FUNCTION&& function, const optional<FIRST>& first,
            const optional<REST>&... rest)
    -> optional<
        remove_cvref_t<invoke_result_t<FUNCTION&, const FIRST&, const REST&...>>>;
```

[x+1]{.pnum} *Returns*: If every operand is engaged, an engaged `optional` holding the result of invoking `function` with the contained values, in the order written; otherwise a disengaged `optional`.

[x+2]{.pnum} *Remarks*: `function` is invoked at most once.

:::

:::
