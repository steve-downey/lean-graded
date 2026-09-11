// include/beman/transpose/zip_list.hpp                               -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_ZIP_LIST_HPP
#define BEMAN_TRANSPOSE_ZIP_LIST_HPP

// Non-normative demonstration type. zip_list models the SIMD/lanewise
// applicative context for Paper A's third motivating domain: traversing a
// structure whose elements are lanewise (zip) computations transposes into a
// lanewise computation over the structure, e.g. vector<zip_list<T>> becomes
// zip_list<vector<T>>. It is illustrative, not a proposed standard type.

#include <beman/transpose/apply.hpp>

#include <algorithm>
#include <cstddef>
#include <functional>
#include <optional>
#include <type_traits>
#include <utility>
#include <vector>

namespace beman::transpose {

/** List with positional (zip) applicative semantics that can represent an
 * infinite repetition of a single value.
 *
 * A zip_list is either finite (elements stored in @c data) or infinite
 * (a single @c repeated value that logically occupies every position). The
 * ZipList applicative applies functions positionally and truncates to the
 * shortest finite operand; pure(x) yields the infinite repetition of x so
 * that it acts as an identity for truncation.
 *
 * Invariant: when @c repeated has a value, @c data is ignored and the
 * zip_list models an infinite repetition of @c repeated.
 * @tparam T element type
 */
template <class T>
struct zip_list {
    using value_type = T;

    // Invariant: when repeated has a value, this zip_list models an infinite
    // repetition of that value and data is ignored.
    std::vector<T> data;
    std::optional<T> repeated{};

    /** Construct an infinite zip_list repeating @p value at every position. */
    static auto repeat(T value) -> zip_list {
        return zip_list{{}, std::move(value)};
    }

    /** True when this zip_list represents an infinite repetition. */
    auto is_repeating() const -> bool { return repeated.has_value(); }

    /** Number of elements in the finite representation; 0 for infinite lists.
     */
    auto finite_size() const -> std::size_t { return data.size(); }

    /** Equality: two infinite lists are equal iff they repeat the same value;
     * two finite lists use element-wise comparison; mixed always false.
     */
    friend auto operator==(const zip_list &left, const zip_list &right)
        -> bool {
        if (left.is_repeating() || right.is_repeating()) {
            return left.repeated == right.repeated;
        }
        return left.data == right.data;
    }
};

namespace detail {

template <class T>
auto zip_list_finite_length(const zip_list<T> &list)
    -> std::optional<std::size_t> {
    if (list.is_repeating()) {
        return std::nullopt;
    }
    return list.finite_size();
}

template <class T>
auto zip_list_value_at(const zip_list<T> &list, std::size_t index)
    -> const T & {
    if (list.is_repeating()) {
        return *list.repeated;
    }
    return list.data[index];
}

template <class FIRST, class... REST>
auto zip_list_result_size(const FIRST &first, const REST &...rest)
    -> std::optional<std::size_t> {
    auto count = zip_list_finite_length(first);
    ((count = count
                  ? std::optional<std::size_t>{std::min(
                        *count, zip_list_finite_length(rest).value_or(*count))}
                  : zip_list_finite_length(rest)),
     ...);
    return count;
}

} // namespace detail

/** Applicative typeclass instance for zip_list<T> with positional (zip)
 * semantics.
 *
 * pure(x) = infinite repetition of x (zip_list::repeat(x)).
 * invoke(f, xs...) zips the argument lists positionally under the plain
 * function f, truncating to the length of the shortest finite operand. If
 * all operands are infinite the result is also infinite.
 * @tparam T element type of the zip_list
 */
template <class T>
struct ZipListApplicativeImpl {
    /** Lift a value into an infinite zip_list repeating that value. */
    template <class VALUE>
    auto pure(this auto &&, VALUE &&value) {
        using U = remove_cvref_t<VALUE>;
        return zip_list<U>::repeat(U(std::forward<VALUE>(value)));
    }

    /**
     * @brief N-ary positional application: apply @p function over all zip_lists
     *        element-wise, truncating to the shortest finite operand.
     * @param function  callable accepting one element from each input list
     * @param first     first zip_list
     * @param rest      remaining zip_lists
     * @return zip_list of results
     */
    template <class FUNCTION, class FIRST, class... REST>
    auto invoke(this auto &&, FUNCTION &&function, const FIRST &first,
                const REST &...rest) {
        using Result =
            std::invoke_result_t<FUNCTION, const typename FIRST::value_type &,
                                 const typename REST::value_type &...>;

        using U = remove_cvref_t<Result>;
        auto callable = std::forward<FUNCTION>(function);
        const auto count = detail::zip_list_result_size(first, rest...);

        if (!count.has_value()) {
            return zip_list<U>::repeat(
                std::invoke(callable, detail::zip_list_value_at(first, 0),
                            detail::zip_list_value_at(rest, 0)...));
        }

        zip_list<U> result;
        result.data.reserve(*count);

        for (std::size_t index = 0; index < *count; ++index) {
            result.data.push_back(
                std::invoke(callable, detail::zip_list_value_at(first, index),
                            detail::zip_list_value_at(rest, index)...));
        }

        return result;
    }
};

/** Applicative map for zip_list<T>: the native n-ary invoke core. */
template <class T>
struct ZipListApplicativeMap : Applicative<ZipListApplicativeImpl<T>> {
    using ZipListApplicativeImpl<T>::invoke;
    using ZipListApplicativeImpl<T>::pure;
};

/** Registers ZipListApplicativeMap as the Applicative instance for zip_list<T>.
 */
template <class T>
inline constexpr auto applicative_typeclass<zip_list<T>> =
    ZipListApplicativeMap<T>{};

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_ZIP_LIST_HPP
