::: add

::: wording

## Lattice operations [transpose.errset.lattice]{- .sref} {-}

```cpp
template<class LEFT, class RIGHT>
struct error_set_join;
```

[x]{.pnum} *Remarks*: `error_set_join<LEFT, RIGHT>::type` is the union of two error sets. Canonicalization reduces the union to pack concatenation.

```cpp
template<class... LEFT, class... RIGHT>
struct error_set_join<error_set_of<LEFT...>, error_set_of<RIGHT...>> {
  using type = error_set<LEFT..., RIGHT...>;
};
```

```cpp
using error_set_bottom = error_set<>;
```

[x+1]{.pnum} *Remarks*: `error_set_bottom` is the identity of join: the empty set.

```cpp
template<class LEFT, class RIGHT> inline constexpr bool error_set_subsumes_v = false;
```

[x+2]{.pnum} *Remarks*: `error_set_subsumes_v<LEFT, RIGHT>` is `true` when every alternative of `LEFT` is an alternative of `RIGHT`. By order-from-join this holds exactly when the join of `LEFT` and `RIGHT` is `RIGHT`, so the only implicit widenings are subset inclusions: an error set can widen to a superset and never the other way.

```cpp
template<class... ERRORS>
constexpr auto error_set_combine(const error_set_of<ERRORS...>& lhs,
                                 const error_set_of<ERRORS...>& rhs)
    -> error_set_of<ERRORS...>;
```

[x+3]{.pnum} *Effects*: Equivalent to:

```cpp
return lhs.combined_with(rhs);
```

[x+4]{.pnum} *Returns*: The combination of `lhs` and `rhs` at their common grade.

[x+5]{.pnum} *Remarks*: Combination is left-biased per alternative: where both operands witness the same error type, `lhs`'s witness is kept. The type-level join above is a commutative union and needs no semigroup; this value-level combination is what the accumulating applicative object uses.

```cpp
template<class FROM_LIST>
struct list_subtract<type_list<>, FROM_LIST> {
  using type = FROM_LIST;
};
```

```cpp
template<class HEAD, class... TAIL, class FROM_LIST>
struct list_subtract<type_list<HEAD, TAIL...>, FROM_LIST> {
  using type =
      typename list_subtract<type_list<TAIL...>,
                             typename list_remove<HEAD, FROM_LIST>::type>::type;
};
```

```cpp
template<>
struct list_concat_all<> {
  using type = type_list<>;
};
```

```cpp
template<class... ERRORS>
struct list_concat_all<type_list<ERRORS...>> {
  using type = type_list<ERRORS...>;
};
```

```cpp
template<class... LEFT, class... RIGHT, class... REST>
struct list_concat_all<type_list<LEFT...>, type_list<RIGHT...>, REST...>
    : list_concat_all<type_list<LEFT..., RIGHT...>, REST...> {};
```

```cpp
template<class RESULT, class VALUE>
struct raised_by_result {
  using type = type_list<>;
};
```

```cpp
template<class VALUE, class... RS>
struct raised_by_result<expected<VALUE, error_set_of<RS...>>, VALUE> {
  using type = type_list<RS...>;
};
```

```cpp
template<class HANDLER, class VALUE, class H>
struct handler_result_of {
  using type = remove_cvref_t<invoke_result_t<HANDLER, const H&>>;
};
```

```cpp
template<class HANDLER, class VALUE, class... ERRORS, class... HANDLED>
struct recover_final_grade<HANDLER, VALUE, error_set_of<ERRORS...>, HANDLED...> {
  using remainder = list_subtract_t<type_list<HANDLED...>, type_list<ERRORS...>>;
  using raised = list_concat_all_t<typename raised_by_result<
      typename handler_result_of<HANDLER, VALUE, HANDLED>::type, VALUE>::type...>;
  using type = error_set_of_list_t<list_concat_all_t<remainder, raised>>;
};
```

```cpp
template<class HANDLER, class VALUE, class GRADE, class... HANDLED>
using $recover-return-t$ = rebind_grade_t<
    VALUE, recover_final_grade_t<HANDLER, VALUE, GRADE, HANDLED...>>; // exposition only
```

:::

:::
