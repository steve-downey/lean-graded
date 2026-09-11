::: add

::: wording

## Grade re-indexing [transpose.applicative.grade]{- .sref} {-}

```cpp
template<class TARGET_GRADE, class CARRIER>
constexpr auto subsume(this auto&&, CARRIER&& value);
```

[x]{.pnum} *Constraints*: `value` can be re-indexed to `TARGET_GRADE`.

[x+1]{.pnum} *Effects*: Equivalent to:

```cpp
return grade_subsume<TARGET_GRADE>(forward<CARRIER>(value));
```

[x+2]{.pnum} *Remarks*: An instance that does not participate in grading still provides this member. Such a carrier is graded by the empty set, the only licensed target is the empty set, and the re-indexing is the identity. Grade participation is therefore never something an instance declares.

:::

:::
