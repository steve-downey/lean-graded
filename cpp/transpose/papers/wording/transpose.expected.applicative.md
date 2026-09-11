::: add

::: wording

## Applicative instance for expected [transpose.expected.applicative]{- .sref} {-}

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

[x+1]{.pnum} *Returns*: If every operand holds a value, an `expected` holding the result of invoking `function` with those values, in the order written; otherwise an `expected` holding the error of the first operand, in that same order, that does not hold a value.

[x+2]{.pnum} *Remarks*: `function` is invoked at most once. Composition short-circuits: only the first error is observed.

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

[x+5]{.pnum} *Remarks*: This is not a mixing point. A bare operand is ungraded, lifts to the model bottom, and leaves no trace in the deduced type.

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

[x+6]{.pnum} *Constraints*: At least one operand is an `expected`; the operands do not all declare `ERROR_TYPE` or a bare value; and every operand's grade belongs to this instance's grade model.

[x+7]{.pnum} *Returns*: As for the preceding overloads, at the grade that is the join of the operands' grades.

[x+8]{.pnum} *Remarks*: This is the mixing point, reached exactly when the preceding overload's constraint does not hold; the two are complementary, so the choice is never a matter of overload ranking. Carrier spelling stays lazy: operands that declare the same error alternative keep that spelling, only genuinely different ones join into an error set, and a bare operand lifts to the model bottom without trace. Combinations that were previously ill-formed become well-formed; nothing that deduced a type before deduces a different one now.

:::

:::
