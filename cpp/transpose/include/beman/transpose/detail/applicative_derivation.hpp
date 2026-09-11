// include/beman/transpose/detail/applicative_derivation.hpp          -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_DETAIL_APPLICATIVE_DERIVATION_HPP
#define BEMAN_TRANSPOSE_DETAIL_APPLICATIVE_DERIVATION_HPP

// Machinery for the Applicative dual-basis derivations. It lives here rather
// than in apply.hpp so that apply.hpp -- the header the wording is generated
// from -- contains only entities the specification describes.

#include <beman/transpose/detail/typeclass_base.hpp>

#include <concepts>
#include <functional>
#include <tuple>
#include <type_traits>
#include <utility>

namespace beman::transpose {

namespace detail {

// Currying support for the invoke-from-ap derivation: wraps a plain n-ary
// function so it can be fed through one-step contextual application,
// consuming one argument at a time and invoking when saturated. This cost
// exists only in the derivation direction -- C++ is not natively curried --
// and never at invoke-native call sites.
template <class FUNCTION, class... BOUND_ARGS>
struct terminating_partial {
    FUNCTION function;
    std::tuple<BOUND_ARGS...> bound_args;

    template <class NEXT_ARG>
    auto operator()(NEXT_ARG &&next_arg) {
        return invoke_or_extend(std::forward<NEXT_ARG>(next_arg),
                                std::index_sequence_for<BOUND_ARGS...>{});
    }

    template <class NEXT_ARG>
    auto operator()(NEXT_ARG &&next_arg) const {
        return invoke_or_extend_const(std::forward<NEXT_ARG>(next_arg),
                                      std::index_sequence_for<BOUND_ARGS...>{});
    }

  private:
    template <class NEXT_ARG, std::size_t... IDX>
    auto invoke_or_extend(NEXT_ARG &&next_arg, std::index_sequence<IDX...>) {
        if constexpr (std::invocable<FUNCTION &, BOUND_ARGS &..., NEXT_ARG>) {
            return std::invoke(function, std::get<IDX>(bound_args)...,
                               std::forward<NEXT_ARG>(next_arg));
        } else {
            using NEXT_PARTIAL = terminating_partial<FUNCTION, BOUND_ARGS...,
                                                     remove_cvref_t<NEXT_ARG>>;
            return NEXT_PARTIAL{
                function,
                std::tuple_cat(std::move(bound_args),
                               std::tuple<remove_cvref_t<NEXT_ARG>>{
                                   std::forward<NEXT_ARG>(next_arg)})};
        }
    }

    template <class NEXT_ARG, std::size_t... IDX>
    auto invoke_or_extend_const(NEXT_ARG &&next_arg,
                                std::index_sequence<IDX...>) const {
        if constexpr (std::invocable<const FUNCTION &, const BOUND_ARGS &...,
                                     NEXT_ARG>) {
            return std::invoke(function, std::get<IDX>(bound_args)...,
                               std::forward<NEXT_ARG>(next_arg));
        } else {
            using NEXT_PARTIAL = terminating_partial<FUNCTION, BOUND_ARGS...,
                                                     remove_cvref_t<NEXT_ARG>>;
            return NEXT_PARTIAL{
                function,
                std::tuple_cat(bound_args,
                               std::tuple<remove_cvref_t<NEXT_ARG>>{
                                   std::forward<NEXT_ARG>(next_arg)})};
        }
    }
};

template <class FUNCTION>
auto make_terminating_partial(FUNCTION &&function) {
    using STORED_FUNCTION = remove_cvref_t<FUNCTION>;
    return terminating_partial<STORED_FUNCTION>{
        std::forward<FUNCTION>(function), std::tuple<>{}};
}

// The evaluator that recovers one-step application (ap) from the n-ary
// core: ap(cf, cx) = invoke(applicative_eval, cf, cx) -- GHC's
// (<*>) = liftA2 id. The trailing return type keeps it SFINAE-visible so
// the derived ap's constraint fails cleanly -- never hard-errors -- for
// contexts that cannot hold callables.
struct applicative_eval_t {
    template <class FUNCTION, class ARGUMENT>
    constexpr auto operator()(FUNCTION &&function, ARGUMENT &&argument) const
        -> std::invoke_result_t<FUNCTION, ARGUMENT> {
        return std::invoke(std::forward<FUNCTION>(function),
                           std::forward<ARGUMENT>(argument));
    }
};
inline constexpr applicative_eval_t applicative_eval{};

// Free-function form for generic internal use.
template <class APPLICATIVE_MAP, class FUNCTIONS_IN_CONTEXT,
          class ARGUMENTS_IN_CONTEXT>
constexpr auto ap(const APPLICATIVE_MAP &map, FUNCTIONS_IN_CONTEXT &&functions,
                  ARGUMENTS_IN_CONTEXT &&arguments) {
    return map.invoke(applicative_eval,
                      std::forward<FUNCTIONS_IN_CONTEXT>(functions),
                      std::forward<ARGUMENTS_IN_CONTEXT>(arguments));
}

} // namespace detail

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_DETAIL_APPLICATIVE_DERIVATION_HPP
