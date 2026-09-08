::: add

::: wording

```cpp
inline constexpr $unspecified$ applicative_eval;
```

[x]{.pnum} *Remarks*: `applicative_eval` applies a callable to one argument. It is the evaluator that recovers one-step application from the n-ary core: `ap(f, x)` is `invoke(applicative_eval, f, x)`. Naming it is what makes `ap`'s second alternative expressible, and that alternative is satisfied only where the context can hold a callable.

:::

::: wording

```cpp
inline constexpr $unspecified$ discard_first_eval;
```

[x+1]{.pnum} *Remarks*: `discard_first_eval` discards its first argument and returns its second. It is the evaluator `discard_first`'s second alternative probes, and that alternative is satisfied exactly when `discard_first`'s own `invoke`-based derivation would be.

:::

::: wording

```cpp
inline constexpr $unspecified$ discard_second_eval;
```

[x+2]{.pnum} *Remarks*: `discard_second_eval` discards its second argument and returns its first. It is the evaluator `discard_second`'s second alternative probes, and that alternative is satisfied exactly when `discard_second`'s own `invoke`-based derivation would be.

:::

::: wording

```cpp
template <class IMPL, class CONTEXT>
concept applicative_impl =
    requires(const IMPL &impl, const applicative_value_t<CONTEXT> &element) {
        impl.pure(element);
    } &&
    (requires(const IMPL &impl, const CONTEXT &context) {
        impl.invoke(probe_witness<applicative_value_t<CONTEXT>>{}, context);
    } || requires(const IMPL &impl, const CONTEXT &context) {
        impl.ap(impl.pure(probe_witness<applicative_value_t<CONTEXT>>{}),
                context);
    });
```

[x+3]{.pnum} *Remarks*: This concept is satisfied when `IMPL` supplies the minimal complete basis the `Applicative` CRTP base needs: `pure`, together with either `invoke` or `ap`. This is the `MINIMAL` pragma to `applicative_object`'s class declaration -- an `IMPL` may satisfy this concept and still fail `applicative_object`, which is exactly the bargain the CRTP base exists to keep. `map`, `lift`, `zip_with`, `discard_first`, `discard_second`, `invoke_with` and `subsume` are all derived and belong to `applicative_object` alone. `pure` is checked for existence only, matching `applicative_object`'s own treatment.

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
  auto map(this auto&& self, FUNCTION&& function, ARGUMENT&& argument)
    requires requires(const Impl& impl) {
      impl.map(forward<FUNCTION>(function), forward<ARGUMENT>(argument));
    } || requires {
      self.invoke(forward<FUNCTION>(function), forward<ARGUMENT>(argument));
    };

  template<class VALUE>
  auto lift(this auto&& self, VALUE&& value)
    requires requires(const Impl& impl) { impl.lift(forward<VALUE>(value)); } ||
             requires { self.pure(forward<VALUE>(value)); };

  template<class FUNCTION, class FIRST_ARGUMENT, class SECOND_ARGUMENT>
  auto zip_with(this auto&& self, FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
                SECOND_ARGUMENT&& second_argument)
    requires requires(const Impl& impl) {
      impl.zip_with(forward<FUNCTION>(function),
                    forward<FIRST_ARGUMENT>(first_argument),
                    forward<SECOND_ARGUMENT>(second_argument));
    } || requires {
      self.invoke(forward<FUNCTION>(function), forward<FIRST_ARGUMENT>(first_argument),
                  forward<SECOND_ARGUMENT>(second_argument));
    };

  template<class FIRST_ARGUMENT, class SECOND_ARGUMENT>
  auto discard_first(this auto&& self, FIRST_ARGUMENT&& first_argument,
                     SECOND_ARGUMENT&& second_argument)
    requires requires(const Impl& impl) {
      impl.discard_first(forward<FIRST_ARGUMENT>(first_argument),
                         forward<SECOND_ARGUMENT>(second_argument));
    } || requires {
      self.invoke(discard_first_eval, forward<FIRST_ARGUMENT>(first_argument),
                  forward<SECOND_ARGUMENT>(second_argument));
    };

  template<class FIRST_ARGUMENT, class SECOND_ARGUMENT>
  auto discard_second(this auto&& self, FIRST_ARGUMENT&& first_argument,
                      SECOND_ARGUMENT&& second_argument)
    requires requires(const Impl& impl) {
      impl.discard_second(forward<FIRST_ARGUMENT>(first_argument),
                          forward<SECOND_ARGUMENT>(second_argument));
    } || requires {
      self.invoke(discard_second_eval, forward<FIRST_ARGUMENT>(first_argument),
                  forward<SECOND_ARGUMENT>(second_argument));
    };

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

[x+4]{.pnum} A program that instantiates `Applicative<Impl>` is ill-formed unless `is_same_v<Impl, false_type>` is `false`.

:::

::: wording

```cpp
template<class T> inline constexpr auto applicative_typeclass = false_type{};
```

[x+5]{.pnum} *Remarks*: This variable template is the lookup point for the Applicative object of a context type. A program may specialize it for a program-defined context. The primary template names no applicative object.

:::

::: wording

```cpp
template<class T>
inline constexpr auto accumulating_applicative_typeclass = false_type{};
```

[x+6]{.pnum} *Remarks*: This variable template is a second lookup point, over the same carrier and grade algebra as `applicative_typeclass`, naming the accumulating Applicative object. Where the object named by `applicative_typeclass` stops at the first failing operand, this object combines the evidence of every failing operand. Neither object is selected automatically for a carrier: the context type alone does not determine which composition discipline a caller wants. This object has no Monad instance, because sequencing requires a value from a computation that accumulation admits may have failed.

:::

::: wording

```cpp
template <class OBJ, class CONTEXT>
concept applicative_object =
    requires(const OBJ &obj, const CONTEXT &context,
             const applicative_value_t<CONTEXT> &element) {
        obj.pure(element);
        obj.invoke(probe_witness<applicative_value_t<CONTEXT>>{}, context);
        obj.map(probe_witness<applicative_value_t<CONTEXT>>{}, context);
        obj.lift(element);
        obj.zip_with(probe_witness2<applicative_value_t<CONTEXT>>{}, context,
                     context);
        obj.discard_first(context, context);
        obj.discard_second(context, context);
        obj.invoke_with(obj, probe_witness<applicative_value_t<CONTEXT>>{},
                        context);
    } &&
    (!requires(const OBJ &obj) {
        obj.pure(probe_witness<applicative_value_t<CONTEXT>>{});
    } || requires(const OBJ &obj, const CONTEXT &context) {
        obj.ap(obj.pure(probe_witness<applicative_value_t<CONTEXT>>{}),
               context);
    }) &&
    (!graded_context<CONTEXT> ||
     requires(const OBJ &obj, const CONTEXT &context) {
         obj.template subsume<grade_of_t<CONTEXT>>(context);
     });
```

[x+7]{.pnum} *Remarks*: This concept is satisfied when `OBJ` provides the full Applicative object surface over `CONTEXT`: `pure`, the `invoke` basis, and the derived `map`, `lift`, `zip_with`, `discard_first`, `discard_second` and `invoke_with`. `ap` and `subsume` are required only where their own condition -- the same one their own declarations carry, not a second spelling of it -- licenses them: `ap` where `CONTEXT` can hold a callable (probed by lifting a witness callable through `OBJ`'s own `pure`, the same mechanism the library's own ap-from-invoke derivation uses), `subsume` where `CONTEXT` participates in grading. Operations templated over an arbitrary callable are probed with one representative witness (`probe_witness`/`probe_witness2`): this checks that the operation exists, not that it holds for every callable. Conformance here is structural, so a hand-implemented object that never derives from `Applicative<Impl>` can satisfy this concept.

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
