::: add

::: wording

## Basis operations [transpose.applicative.basis]{- .sref} {-}

```cpp
template<class FUNCTION, class FIRST_ARGUMENT, class... REST_ARGUMENTS>
auto invoke(this auto&& self, FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
            REST_ARGUMENTS&&... rest_arguments);
```

[x]{.pnum} *Constraints*: `Impl` provides either an `invoke` accepting `function` and the arguments, or an `ap` accepting a callable in context and one argument in context.

[x+1]{.pnum} *Effects*: Lifts `function` into the context and applies it to the arguments, left to right. If `Impl` provides `invoke`, the effect is that of `Impl`'s own `invoke`; otherwise `function` is embedded with `pure` and applied one argument at a time using `ap`.

[x+2]{.pnum} *Returns*: The single value in context holding the result of applying `function` to the values held by the arguments.

[x+3]{.pnum} *Remarks*: The arguments are evaluated in the order written. No argument's context depends on another argument's value.

```cpp
template<class FUNCTION_IN_CONTEXT, class ARGUMENT_IN_CONTEXT>
auto ap(this auto&& self, FUNCTION_IN_CONTEXT&& function,
        ARGUMENT_IN_CONTEXT&& argument);
```

[x+4]{.pnum} *Constraints*: `Impl` provides either an `ap` accepting `function` and `argument`, or an `invoke` able to apply a callable held in the context to one argument in the context. The second alternative is satisfied only where the context can hold a callable, so `ap` does not participate in overload resolution for a context that cannot.

[x+5]{.pnum} *Effects*: Applies the callable held by `function` to the value held by `argument`. If `Impl` provides `ap`, the effect is that of `Impl`'s own `ap`; otherwise the application is expressed through `Impl`'s `invoke`.

[x+6]{.pnum} *Returns*: The single value in context holding the result of that application.

[x+7]{.pnum} *Remarks*: This is the classic one-step application, retained as a secondary operation and as an instance basis. Both alternatives address `Impl` directly, so no derivation cycle with `invoke` arises.

:::

:::
