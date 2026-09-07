::: add

::: wording

## Constructors [transpose.errset.cons]{- .sref} {-}

```cpp
template<class ERROR>
  requires($error-set-has-v$<remove_cvref_t<ERROR>, ERRORS...>)
constexpr error_set_of(ERROR&& error);
```

[x]{.pnum} *Constraints*: `ERROR`, with cv-qualification and references removed, is one of the alternatives.

[x+1]{.pnum} *Effects*: Constructs a value witnessing exactly the alternative `ERROR` names, holding `error` as that witness. Every other slot is empty.

[x+2]{.pnum} *Remarks*: This is the injection of an error value into the set it belongs to. It is not explicit: a raised error is usable as the set that may raise it.

```cpp
template<class... NARROWER>
  requires(sizeof...(NARROWER) > 0) &&
          (!is_same_v<error_set_of<NARROWER...>, error_set_of<ERRORS...>>) &&
          ($error-set-has-v$<NARROWER, ERRORS...> && ...)
constexpr error_set_of(const error_set_of<NARROWER...>& narrower);
```

[x+3]{.pnum} *Constraints*: `NARROWER` is non-empty, names a different set, and every one of its alternatives is an alternative of `*this`.

[x+4]{.pnum} *Effects*: Constructs a value witnessing exactly what `narrower` witnesses. Slots for alternatives `NARROWER` cannot name are empty.

[x+5]{.pnum} *Remarks*: This is subsumption, and widening along inclusion is the only conversion there is: there is none in the other direction, and none between incomparable sets. There is deliberately no conversion from the empty set, which is uninhabited, so no value ever needs one.

:::

:::
