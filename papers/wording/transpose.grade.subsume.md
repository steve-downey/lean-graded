::: add

::: wording

## Subsumption [transpose.grade.subsume]{- .sref} {-}

```cpp
template<class TARGET_GRADE, class CARRIER>
  requires grade_semilattice<TARGET_GRADE> &&
           (is_same_v<grade_of_t<remove_cvref_t<CARRIER>>, unit_grade> ||
            grade_subsumes_v<grade_of_t<remove_cvref_t<CARRIER>>, TARGET_GRADE>) &&
           constructible_from<rebind_grade_t<remove_cvref_t<CARRIER>, TARGET_GRADE>,
                              CARRIER>
constexpr auto grade_subsume(CARRIER&& value)
    -> rebind_grade_t<remove_cvref_t<CARRIER>, TARGET_GRADE>;
```

[x]{.pnum} *Constraints*: `TARGET_GRADE` satisfies `grade_semilattice`; the grade `value` carries is either `unit_grade` or subsumes into `TARGET_GRADE`; and `value`'s carrier re-indexed at `TARGET_GRADE` is constructible from `value`.

[x+1]{.pnum} *Effects*: Equivalent to:

```cpp
return rebind_grade_t<remove_cvref_t<CARRIER>, TARGET_GRADE>(forward<CARRIER>(value));
```

[x+2]{.pnum} *Returns*: `value`'s carrier re-indexed at `TARGET_GRADE`, holding the same computation.

[x+3]{.pnum} *Remarks*: The coercion is the carrier's own converting constructor. No separate machinery is needed: because the order is read off the join, the inclusion between two grades is unique, so there is exactly one coercion and the carrier already provides it. The source grade may be `unit_grade`; the target must be a model grade.

:::

:::
