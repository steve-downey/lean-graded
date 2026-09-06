::: add

```cpp
struct unit_grade {};
```

::: wording

[x]{.pnum} *Remarks*: `unit_grade` is the sentinel for an ungraded computation. It is deliberately not a grade in any model's lattice: a framework default that were some model's bottom would name that model in order to say "in no grade family at all". Where an ungraded operand meets a graded one, the model lifts the ungraded operand to its own bottom.

:::

::: wording

```cpp
template<class LEFT, class RIGHT>
struct grade_join;
```

[x+1]{.pnum} *Remarks*: `grade_join<LEFT, RIGHT>::type` is the least upper bound of `LEFT` and `RIGHT`. The primary template is not defined: a type is a grade exactly when a model has registered these operations for it, so an unregistered type fails `grade_semilattice` rather than behaving as a grade.

:::

::: wording

```cpp
template<class GRADE>
struct grade_bottom;
```

[x+2]{.pnum} *Remarks*: `grade_bottom<GRADE>::type` is the identity of join in `GRADE`'s algebra. The primary template is not defined.

:::

::: wording

```cpp
template<class LEFT, class RIGHT>
struct grade_subsumes;
```

[x+3]{.pnum} *Remarks*: `grade_subsumes<LEFT, RIGHT>::value` is `true` when `LEFT` subsumes into `RIGHT`. The order is read off the join: it holds exactly when `grade_join_t<LEFT, RIGHT>` is `RIGHT`. Reading the order off the join is what makes the inclusion between two grades unique, and therefore makes a subsumption coercion canonical. The primary template is not defined.

:::

::: wording

```cpp
template<class GRADE>
struct grade_model;
```

[x+4]{.pnum} *Remarks*: `grade_model<GRADE>::type` names the model `GRADE` belongs to. A model specializes this for its own grades. The primary template is not defined.

:::

::: wording

```cpp
template<class GRADE>
concept grade_semilattice = requires {
  typename grade_model<GRADE>::type;
  typename grade_join<GRADE, GRADE>::type;
  typename grade_bottom<GRADE>::type;
  { grade_subsumes<GRADE, GRADE>::value } -> convertible_to<bool>;
};
```

[x+5]{.pnum} *Remarks*: `grade_semilattice<GRADE>` is satisfied when a model has given `GRADE` a model identity and the three algebra operations. The concept is syntactic. That join is commutative, idempotent and associative, and that bottom is its unit, are semantic requirements on a model, not part of the concept: making them part of it would evaluate a law check in every constraint that mentions a grade.

:::

```cpp
template<class CONTEXT>
struct grade_of {
  using type = unit_grade;
};
```

::: wording

[x+6]{.pnum} *Remarks*: `grade_of<CONTEXT>::type` is the grade `CONTEXT` carries. The primary template answers `unit_grade`, so a context that knows nothing about grading is treated as ungraded and behaves exactly as it did before grading existed. A model specializes this for the carriers it grades.

:::

::: wording

```cpp
template<class CONTEXT, class GRADE>
struct rebind_grade;
```

[x+7]{.pnum} *Remarks*: `rebind_grade<CONTEXT, GRADE>::type` is `CONTEXT` re-indexed at `GRADE`. The primary template is not defined: only a model knows how its grade is spelled into a carrier, and `unit_grade` is not a grade and has no carrier of its own.

:::

::: wording

```cpp
template<class CONTEXT>
concept graded_context = !is_same_v<grade_of_t<CONTEXT>, unit_grade>;
```

[x+8]{.pnum} *Remarks*: `graded_context<CONTEXT>` is satisfied when `CONTEXT` carries a model grade rather than `unit_grade`. Graded and ungraded paths are kept mutually exclusive by this constraint rather than by overload ranking.

:::

```cpp
template<class MODEL_GRADE, class RAW_GRADE>
struct $mixes-with-model-impl$
    : bool_constant<is_same_v<grade_model_t<RAW_GRADE>, grade_model_t<MODEL_GRADE>>> {
}; // exposition only
```

```cpp
template<class MODEL_GRADE>
struct $mixes-with-model-impl$<MODEL_GRADE, unit_grade> : true_type {}; // exposition only
```

```cpp
template<class MODEL_GRADE, class OPERAND>
concept $mixes-with-model$ =
    $mixes-with-model-impl$<MODEL_GRADE,
                   grade_of_t<remove_cvref_t<OPERAND>>>::value; // exposition only
```

```cpp
template<class MODEL_GRADE, class CARRIER, class... OPERANDS>
using $mixed-result-t$ = $see below$; // exposition only
```

:::
