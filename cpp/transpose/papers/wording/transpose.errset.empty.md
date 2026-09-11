::: add

::: wording

## The empty error set [transpose.errset.empty]{- .sref} {-}

```cpp
error_set_of() = delete;
```

[x]{.pnum} *Remarks*: The empty error set is uninhabited: a computation graded by it raises nothing, so there is no value to construct.

```cpp
template<class ERROR> static constexpr auto contains() noexcept -> bool;
```

[x+1]{.pnum} *Returns*: `false`.

```cpp
template<class... ERRORS> using error_set = $see below$;
```

[x+2]{.pnum} *Remarks*: `error_set<ERRORS...>` is the canonicalizing spelling of an error set: the pack is sorted and deduplicated, so `error_set<A, B>` and `error_set<B, A, A>` denote the same type. A grade is therefore normalized by type identity, not by source spelling or alternative position, and every inclusion has one canonical target.

:::

:::
