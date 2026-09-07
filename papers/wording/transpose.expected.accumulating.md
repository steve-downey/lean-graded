::: add

::: wording

## Accumulating instance [transpose.expected.accumulating]{- .sref} {-}

```cpp
template<class VALUE>
auto pure(this auto&&, VALUE&& value) -> expected<remove_cvref_t<VALUE>, ERROR_TYPE>;
```

[x]{.pnum} *Returns*: An `expected` holding `value`.

```cpp
template<class FUNCTION, class FIRST, class... REST>
auto invoke(this auto&&, FUNCTION&& function, const expected<FIRST, ERROR_TYPE>& first,
            const expected<REST, ERROR_TYPE>&... rest)
    -> expected<
        remove_cvref_t<invoke_result_t<FUNCTION&, const FIRST&, const REST&...>>,
        ERROR_TYPE>;
```

[x+1]{.pnum} *Returns*: If every operand holds a value, an `expected` holding the result of invoking `function` with those values, in the order written; otherwise an `expected` holding the combination of every operand's error, combined in that same order.

[x+2]{.pnum} *Remarks*: `function` is invoked at most once. Composition accumulates: every error is observed, not only the first.

```cpp
template<class FUNCTION, class... CARRIERS>
  requires(sizeof...(CARRIERS) > 0) &&
          ($is-expected-v$<remove_cvref_t<CARRIERS>> || ...) &&
          (!$all-declare-v$<ERROR_TYPE, CARRIERS...>) &&
          $all-declare-or-bare-v$<ERROR_TYPE, CARRIERS...>
auto invoke(this auto&&, FUNCTION&& function, const CARRIERS&... operands) -> expected<
    remove_cvref_t<invoke_result_t<FUNCTION&, const $carrier-value-t$<CARRIERS>&...>>,
    ERROR_TYPE>;
```

[x+3]{.pnum} *Constraints*: At least one operand is an `expected`; the operands do not all declare `ERROR_TYPE`; and every operand either declares `ERROR_TYPE` or is a bare value.

[x+4]{.pnum} *Returns*: As for the preceding overload, treating a bare operand as holding itself.

```cpp
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
```

[x+5]{.pnum} *Constraints*: At least one operand is an `expected`; the operands do not all declare `ERROR_TYPE` or a bare value; and every operand's grade belongs to this instance's grade model.

[x+6]{.pnum} *Returns*: As for the preceding overloads, at the grade that is the join of the operands' grades, holding the combination of every failing operand's evidence.

[x+7]{.pnum} *Remarks*: Errors are combined in the order the operands are written.

:::

:::
