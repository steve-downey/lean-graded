::: add

::: wording

```cpp
inline constexpr $unspecified$ applicative_eval;
```

[x]{.pnum} *Remarks*: `applicative_eval` applies a callable to one argument. It is the evaluator that recovers one-step application from the n-ary core: `ap(f, x)` is `invoke(applicative_eval, f, x)`. Naming it is what makes `ap`'s second alternative expressible, and that alternative is satisfied only where the context can hold a callable.

:::

```cpp
template<class Impl>
struct Applicative : protected Impl {
  using Impl::pure;

  // @[transpose.applicative.basis]{- .sref}@, basis operations
  template<class FUNCTION, class FIRST_ARGUMENT, class... REST_ARGUMENTS>
  auto invoke(this auto&& self, FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
              REST_ARGUMENTS&&... rest_arguments);

  template<class FUNCTION_IN_CONTEXT, class ARGUMENT_IN_CONTEXT>
  auto ap(this auto&& self, FUNCTION_IN_CONTEXT&& function,
          ARGUMENT_IN_CONTEXT&& argument)
    requires requires(const Impl& impl) {
      impl.ap(forward<FUNCTION_IN_CONTEXT>(function),
              forward<ARGUMENT_IN_CONTEXT>(argument));
    } || requires(const Impl& impl) {
      impl.invoke(applicative_eval, forward<FUNCTION_IN_CONTEXT>(function),
                  forward<ARGUMENT_IN_CONTEXT>(argument));
    };

  // @[transpose.applicative.derived]{- .sref}@, derived operations
  template<class FUNCTION, class ARGUMENT>
  auto map(this auto&& self, FUNCTION&& function, ARGUMENT&& argument);

  template<class VALUE> auto lift(this auto&& self, VALUE&& value);

  template<class FUNCTION, class FIRST_ARGUMENT, class SECOND_ARGUMENT>
  auto zip_with(this auto&& self, FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
                SECOND_ARGUMENT&& second_argument);

  template<class FIRST_ARGUMENT, class SECOND_ARGUMENT>
  auto discard_first(this auto&& self, FIRST_ARGUMENT&& first_argument,
                     SECOND_ARGUMENT&& second_argument);

  template<class FIRST_ARGUMENT, class SECOND_ARGUMENT>
  auto discard_second(this auto&& self, FIRST_ARGUMENT&& first_argument,
                      SECOND_ARGUMENT&& second_argument);

  // @[transpose.applicative.grade]{- .sref}@, grade re-indexing
  template<class TARGET_GRADE, class CARRIER>
  constexpr auto subsume(this auto&&, CARRIER&& value)
    requires requires { grade_subsume<TARGET_GRADE>(forward<CARRIER>(value)); };

  // @[transpose.applicative.delegate]{- .sref}@, delegated application
  template<class APPLICATIVE_MAP, class FUNCTION, class FIRST_ARGUMENT,
           class... REST_ARGUMENTS>
  auto invoke_with(this auto&&, const APPLICATIVE_MAP& applicative_map,
                   FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
                   REST_ARGUMENTS&&... rest_arguments);

  template<const auto& APPLICATIVE_MAP, class FUNCTION, class FIRST_ARGUMENT,
           class... REST_ARGUMENTS>
  auto invoke_with(this auto&&, FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
                   REST_ARGUMENTS&&... rest_arguments);
};
```

::: wording

[x+1]{.pnum} A program that instantiates `Applicative<Impl>` is ill-formed unless `is_same_v<Impl, false_type>` is `false`.

:::

::: wording

```cpp
template<class T> inline constexpr auto applicative_typeclass = false_type{};
```

[x+2]{.pnum} *Remarks*: This variable template is the lookup point for the Applicative object of a context type. A program may specialize it for a program-defined context. The primary template names no applicative object.

:::

::: wording

```cpp
template<class T>
inline constexpr auto accumulating_applicative_typeclass = false_type{};
```

[x+3]{.pnum} *Remarks*: This variable template is a second lookup point, over the same carrier and grade algebra as `applicative_typeclass`, naming the accumulating Applicative object. Where the object named by `applicative_typeclass` stops at the first failing operand, this object combines the evidence of every failing operand. Neither object is selected automatically for a carrier: the context type alone does not determine which composition discipline a caller wants. This object has no Monad instance, because sequencing requires a value from a computation that accumulation admits may have failed.

:::

```cpp
template<class VALUE_TYPE>
struct OptionalApplicativeImpl {
  // @[transpose.applicative.optional]{- .sref}@, applicative instance for optional
  template<class VALUE>
  auto pure(this auto&&, VALUE&& value) -> optional<remove_cvref_t<VALUE>>;

  template<class FUNCTION, class FIRST, class... REST>
  auto invoke(this auto&&, FUNCTION&& function, const optional<FIRST>& first,
              const optional<REST>&... rest)
      -> optional<
          remove_cvref_t<invoke_result_t<FUNCTION&, const FIRST&, const REST&...>>>;
};
```

```cpp
template<class VALUE_TYPE>
struct OptionalApplicativeMap : Applicative<OptionalApplicativeImpl<VALUE_TYPE>> {
  using OptionalApplicativeImpl<VALUE_TYPE>::invoke;
  using OptionalApplicativeImpl<VALUE_TYPE>::pure;
};
```

:::
