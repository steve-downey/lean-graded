::: add

::: wording

## Derived operations [transpose.applicative.derived]{- .sref} {-}

```cpp
template<class FUNCTION, class ARGUMENT>
auto map(this auto&& self, FUNCTION&& function, ARGUMENT&& argument);
```

[x]{.pnum} *Effects*: Equivalent to:

```cpp
return self.invoke(forward<FUNCTION>(function), forward<ARGUMENT>(argument));
```

```cpp
template<class VALUE> auto lift(this auto&& self, VALUE&& value);
```

[x+1]{.pnum} *Effects*: Equivalent to:

```cpp
return self.pure(forward<VALUE>(value));
```

```cpp
template<class FUNCTION, class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto zip_with(this auto&& self, FUNCTION&& function, FIRST_ARGUMENT&& first_argument,
              SECOND_ARGUMENT&& second_argument);
```

[x+2]{.pnum} *Effects*: Equivalent to:

```cpp
return self.invoke(forward<FUNCTION>(function), forward<FIRST_ARGUMENT>(first_argument),
                   forward<SECOND_ARGUMENT>(second_argument));
```

```cpp
template<class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto discard_first(this auto&& self, FIRST_ARGUMENT&& first_argument,
                   SECOND_ARGUMENT&& second_argument);
```

[x+3]{.pnum} *Effects*: Equivalent to:

```cpp
return self.invoke([](const auto&, auto&& rhs) { return forward<decltype(rhs)>(rhs); },
                   forward<FIRST_ARGUMENT>(first_argument),
                   forward<SECOND_ARGUMENT>(second_argument));
```

```cpp
template<class FIRST_ARGUMENT, class SECOND_ARGUMENT>
auto discard_second(this auto&& self, FIRST_ARGUMENT&& first_argument,
                    SECOND_ARGUMENT&& second_argument);
```

[x+4]{.pnum} *Effects*: Equivalent to:

```cpp
return self.invoke([](auto&& lhs, const auto&) { return forward<decltype(lhs)>(lhs); },
                   forward<FIRST_ARGUMENT>(first_argument),
                   forward<SECOND_ARGUMENT>(second_argument));
```

:::

:::
