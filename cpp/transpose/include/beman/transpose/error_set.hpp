// include/beman/transpose/error_set.hpp                              -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_ERROR_SET_HPP
#define BEMAN_TRANSPOSE_ERROR_SET_HPP

// error_set: the set of error types a computation may raise.
//
// NOMINAL, not a structural sum. `error_set_of<Es...>` is its own type. The
// public surface is deliberately impoverished -- injection, subsumption,
// membership, visitation -- because "the set of errors this computation may
// raise" is an interpretation, not a representation, and interpretations
// need names. See docs/decisions.md#error-set-identity.
//
// VALUE LEVEL: a WITNESSED SUBSET, not a one-of union. The TYPE says "may
// raise {A,B}"; a VALUE says "did raise", and did-raise is a non-empty subset
// of may-raise: one witness per raised type, at most. Storage is per-type
// slots (a tuple of `std::optional<Es>...`) bounded by |grade|, never
// allocation, never a discriminated one-of. This is the amendment recorded
// at docs/decisions.md#error-set-identity, made by
// docs/decisions.md#accumulation-evidence: the short-circuit applicative
// object only ever produces a singleton witness (exactly the old "one
// alternative" behavior, preserved as a special case); the accumulating
// object (docs/transpose-grading-plan.md#accumulating-object) combines
// witnesses from multiple failures, left-biased per type via
// `error_set_combine` -- two witnesses of the SAME type keep the leftmost,
// which is deterministic only because left-to-right traversal is already
// normative (docs/decisions.md#applicative-objects).
//
// CANONICAL BY CONSTRUCTION. `error_set<Es...>` is the spelling users and the
// framework write; it is an alias that sorts and deduplicates its pack, so
// `error_set<A,B>` and `error_set<B,A>` are THE SAME TYPE. That is what makes
// grade arithmetic well-defined and inclusions unique -- sorted normalization
// is names-not-positions. `error_set_of` accepts only an already-canonical
// pack and says so with a static_assert; forming a non-canonical one is the
// invariant violation the class exists to prevent.
//
// The conversions are exactly the ⊆ widenings and nothing else. There is no
// narrowing conversion, no conversion between incomparable sets, and no
// accessor that hands out the underlying variant. Having only the subset
// conversions is the coherence argument compiled into the overload set.
//
// TYPE ORDERING is P2830's job. Until it is available this header uses an
// interim ordering read out of the compiler's own function signature, valid
// only for the documented restrictions: named types, external linkage,
// stable spelling. Two distinct types that render to the same name would be
// silently conflated, so that case is a hard error rather than a wrong
// answer -- see the static_assert in error_set_of.

#include <beman/transpose/detail/typeclass_base.hpp>
#include <beman/transpose/grade.hpp>

#include <array>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <expected>
#include <functional>
#include <optional>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>
#include <variant>

namespace beman::transpose {

template <class... ERRORS>
class error_set_of;

namespace detail {

// -- Interim type ordering (P2830 fallback) -------------------------------

/** The compiler's spelling of T, extracted from the enclosing signature.
 * Valid as an ordering key only under the documented restrictions: named
 * types with external linkage and a stable spelling.
 */
template <class T>
consteval auto type_name() -> std::string_view {
#if defined(_MSC_VER) && !defined(__clang__)
    // MSVC has no __PRETTY_FUNCTION__. __FUNCSIG__ spells the specialization
    // as `... type_name<T>(void)`, so the name is what sits between the
    // template argument list and the last `>`. Should that spelling ever
    // change, fall back to the whole signature, which still names T and so
    // is still an injective key -- a duller order, not a broken one.
    const std::string_view signature{__FUNCSIG__};
    constexpr std::string_view marker{"type_name<"};

    const auto found = signature.find(marker);
    const auto stop = signature.rfind('>');
    if (found == std::string_view::npos || stop == std::string_view::npos ||
        stop <= found + marker.size()) {
        return signature;
    }
    const auto start = found + marker.size();
    return signature.substr(start, stop - start);
#else
    const std::string_view signature{__PRETTY_FUNCTION__};
    constexpr std::string_view marker{"T = "};

    const auto start = signature.find(marker) + marker.size();
    auto stop = signature.find(';', start);
    if (stop == std::string_view::npos) {
        stop = signature.rfind(']');
    }
    return signature.substr(start, stop - start);
#endif
}

/** Strict total order on types, by name. Interim stand-in for P2830. */
template <class LEFT, class RIGHT>
inline constexpr bool type_precedes_v = type_name<LEFT>() < type_name<RIGHT>();

// -- Type list machinery --------------------------------------------------

//! \omit
template <class... ERRORS>
struct type_list {};

template <class T, class LIST>
inline constexpr bool list_contains_v = false;

template <class T, class... ERRORS>
inline constexpr bool list_contains_v<T, type_list<ERRORS...>> =
    (std::is_same_v<T, ERRORS> || ...);

template <class T, class LIST>
struct list_prepend;

//! \omit
template <class T, class... ERRORS>
struct list_prepend<T, type_list<ERRORS...>> {
    using type = type_list<T, ERRORS...>;
};

template <class T, class LIST>
using list_prepend_t = typename list_prepend<T, LIST>::type;

template <class T, class LIST>
struct list_remove;

//! \omit
template <class T>
struct list_remove<T, type_list<>> {
    using type = type_list<>;
};

//! \omit
template <class T, class HEAD, class... TAIL>
struct list_remove<T, type_list<HEAD, TAIL...>> {
  private:
    using rest = typename list_remove<T, type_list<TAIL...>>::type;

  public:
    using type = std::conditional_t<std::is_same_v<T, HEAD>, rest,
                                    list_prepend_t<HEAD, rest>>;
};

/** Deduplicate by type identity, keeping the first occurrence. Identity is
 * std::is_same, never the name: names are an ordering key, not an equality. */
template <class LIST>
struct list_dedupe;

//! \omit
template <>
struct list_dedupe<type_list<>> {
    using type = type_list<>;
};

//! \omit
template <class HEAD, class... TAIL>
struct list_dedupe<type_list<HEAD, TAIL...>> {
    using type =
        list_prepend_t<HEAD, typename list_dedupe<typename list_remove<
                                 HEAD, type_list<TAIL...>>::type>::type>;
};

template <class T, class LIST>
struct list_insert_sorted;

//! \omit
template <class T>
struct list_insert_sorted<T, type_list<>> {
    using type = type_list<T>;
};

//! \omit
template <class T, class HEAD, class... TAIL>
struct list_insert_sorted<T, type_list<HEAD, TAIL...>> {
    using type = std::conditional_t<
        type_precedes_v<T, HEAD>, type_list<T, HEAD, TAIL...>,
        list_prepend_t<
            HEAD, typename list_insert_sorted<T, type_list<TAIL...>>::type>>;
};

template <class LIST>
struct list_sort;

//! \omit
template <>
struct list_sort<type_list<>> {
    using type = type_list<>;
};

//! \omit
template <class HEAD, class... TAIL>
struct list_sort<type_list<HEAD, TAIL...>> {
    using type = typename list_insert_sorted<
        HEAD, typename list_sort<type_list<TAIL...>>::type>::type;
};

/** The canonical form of a pack: deduplicated, then sorted. */
template <class... ERRORS>
using canonical_t =
    typename list_sort<typename list_dedupe<type_list<ERRORS...>>::type>::type;

/** False when two DISTINCT types render to the same name, which is exactly
 * the case the interim ordering cannot handle. */
template <class... ERRORS>
consteval auto names_are_distinct() -> bool {
    constexpr std::size_t count = sizeof...(ERRORS);
    const std::array<std::string_view, count> names{type_name<ERRORS>()...};
    for (std::size_t i = 0; i < count; ++i) {
        for (std::size_t j = i + 1; j < count; ++j) {
            if (names[i] == names[j]) {
                return false;
            }
        }
    }
    return true;
}

template <class LIST>
struct error_set_from_list;

//! \omit
template <class... ERRORS>
struct error_set_from_list<type_list<ERRORS...>> {
    using type = error_set_of<ERRORS...>;
};

/** A precondition violation the type system cannot catch.
 *
 * Deliberately NOT constexpr. During constant evaluation, calling a
 * non-constexpr function makes the evaluation non-constant, so a violated
 * precondition becomes a COMPILE ERROR naming this function -- which is where
 * most of this library's code runs, and where the contract is therefore not
 * merely documented but enforced. At runtime it stops the program instead of
 * letting a silently-wrong answer escape.
 *
 * This library has no assertion vocabulary and is not acquiring one. The
 * point is narrower: a narrow contract whose violation returns a plausible
 * wrong answer is worse than one that stops, because the plausible answer is
 * the one that reaches a user.
 */
[[noreturn]] inline void error_set_precondition_violated(const char *what) {
    std::fputs(what, stderr);
    std::fputs("\n", stderr);
    std::abort();
}

// -- Per-type witness storage ----------------------------------------------
// One std::optional slot per alternative, never a discriminated one-of. See
// docs/decisions.md#accumulation-evidence for why: the grade join needs no
// monoid, but accumulating VALUE-level evidence does, and the semigroup it
// needs is "per type, keep one witness" -- which a tuple of optionals gives
// for free, with no allocation and no extra discriminant to keep in sync.

/** The slot for ERROR, set from `error` when it is the injected alternative,
 * empty otherwise. Called once per member of the target pack, so exactly one
 * instantiation actually forwards-constructs from `error`; the others never
 * touch it.
 */
template <class ERROR, class INJECTED>
constexpr auto witness_slot(INJECTED &&error) -> std::optional<ERROR> {
    if constexpr (std::is_same_v<ERROR, remove_cvref_t<INJECTED>>) {
        return std::optional<ERROR>(std::forward<INJECTED>(error));
    } else {
        return std::optional<ERROR>{};
    }
}

/** The slot for ERROR when widening from a narrower witnessed subset: the
 * narrower value's own witness if it names ERROR among its alternatives,
 * empty otherwise. This is the value-level half of the ⊆ conversion --
 * copying over whichever witnesses the narrower value actually carries. */
template <class ERROR, class... NARROWER>
constexpr auto widen_slot(const error_set_of<NARROWER...> &narrower)
    -> std::optional<ERROR> {
    if constexpr (error_set_of<NARROWER...>::template contains<ERROR>()) {
        return narrower.template witness<ERROR>();
    } else {
        return std::optional<ERROR>{};
    }
}

/// Whether ERRORS is already canonical -- sorted and deduplicated. Named by
/// the class's Mandates, which state the requirement in prose.
//! \expos
template <class... ERRORS>
inline constexpr bool error_set_is_canonical_v =
    std::is_same_v<canonical_t<ERRORS...>, type_list<ERRORS...>>;

/// Whether no two of ERRORS render to the same name. Named by the class's
/// Mandates.
//! \expos
template <class... ERRORS>
inline constexpr bool error_set_names_distinct_v =
    names_are_distinct<ERRORS...>();

} // namespace detail

/// Whether T is one of ERRORS. Exposition-only: it exists so that the
/// membership constraint has one spelling usable both inside the class and on
/// an out-of-line definition, where class scope is not yet in effect.
//! \expos
template <class T, class... ERRORS>
inline constexpr bool error_set_has_v = (std::is_same_v<T, ERRORS> || ...);

/// The set of error types a computation may raise, at a canonical pack.
///
/// Write `error_set<...>` rather than naming this template directly: the
/// alias canonicalizes, this template only accepts an already-canonical pack.
///
/// VALUE-LEVEL INVARIANT: a non-empty witnessed subset of {ERRORS...} -- for
/// each raised type, at most one witness.
//! \mandates The pack is canonical: sorted and deduplicated. Spell
//! `error_set<ERRORS...>`, which canonicalizes, rather than naming this
//! template directly. No two alternatives render to the same name.
//! \remarks A value of this type witnesses a non-empty subset of the
//! alternatives, with at most one witness per raised type. The set says what
//! a computation may raise; a value records what it did raise.
template <class... ERRORS>
class error_set_of {
    static_assert(
        detail::error_set_is_canonical_v<ERRORS...>,
        "error_set_of requires a canonical (sorted, deduplicated) pack. "
        "Spell error_set<...> instead, which canonicalizes for you.");
    static_assert(
        detail::error_set_names_distinct_v<ERRORS...>,
        "Two distinct error types render to the same name, so the interim "
        "type ordering cannot separate them. The P2830 fallback is valid "
        "only for named types with external linkage and a stable spelling; "
        "this is outside those restrictions.");

  public:
    // \ref{transpose.errset.obs}, observers
    template <class ERROR>
    static constexpr auto contains() noexcept -> bool;

    // \ref{transpose.errset.cons}, constructors
    template <class ERROR>
        requires(error_set_has_v<remove_cvref_t<ERROR>, ERRORS...>)
    constexpr error_set_of(ERROR &&error); /// NOLINT(*-explicit-constructor)

    template <class... NARROWER>
        requires(sizeof...(NARROWER) > 0) &&
                (!std::is_same_v<error_set_of<NARROWER...>,
                                 error_set_of<ERRORS...>>) &&
                (error_set_has_v<NARROWER, ERRORS...> && ...)
    constexpr error_set_of(
        const error_set_of<NARROWER...> &narrower); /// NOLINT(*-explicit-*)

    // \ref{transpose.errset.obs}, observers
    template <class ERROR>
        requires(error_set_has_v<ERROR, ERRORS...>)
    constexpr auto holds() const noexcept -> bool;

    template <class ERROR>
        requires(error_set_has_v<ERROR, ERRORS...>)
    constexpr auto witness() const -> const std::optional<ERROR> &;

    constexpr auto witness_count() const noexcept -> std::size_t;

    template <class HANDLER>
    constexpr auto visit(HANDLER &&handler) const -> decltype(auto);

    // \ref{transpose.errset.ops}, operations
    //! \returns `true` if and only if both operands witness the same set of
    //! alternatives and the corresponding witnesses compare equal.
    //! \remarks Equality is what keeps a graded carrier as usable as an
    //! ungraded one: `expected<T, E>` compares equal whenever `E` does, and a
    //! graded `expected` would silently lose that were this absent. Defaulted,
    //! so it is deleted rather than ill-formed when an alternative is not
    //! equality-comparable.
    friend auto operator==(const error_set_of &, const error_set_of &)
        -> bool = default;

    constexpr auto combined_with(const error_set_of &other) const
        -> error_set_of;

  private:
    //! \omit
    explicit constexpr error_set_of(
        std::tuple<std::optional<ERRORS>...> witnesses)
        : d_witnesses(std::move(witnesses)) {}

    //! \omit
    template <std::size_t... IDX>
    constexpr auto combine_witnesses(const error_set_of &other,
                                     std::index_sequence<IDX...>) const
        -> std::tuple<std::optional<ERRORS>...> {
        return std::tuple<std::optional<ERRORS>...>{
            (std::get<IDX>(d_witnesses).has_value()
                 ? std::get<IDX>(d_witnesses)
                 : std::get<IDX>(other.d_witnesses))...};
    }

    //! \omit
    constexpr auto to_variant() const -> std::variant<ERRORS...> {
        if (witness_count() != 1) {
            detail::error_set_precondition_violated(
                "beman::transpose::error_set::visit requires exactly one "
                "witness, but this value witnesses a different number. Use "
                "witness<E>() per alternative for a multi-witness subset; "
                "see docs/decisions.md#accumulation-evidence.");
        }

        std::optional<std::variant<ERRORS...>> found;
        auto try_slot = [&found](const auto &slot) {
            if (!found.has_value() && slot.has_value()) {
                found = std::variant<ERRORS...>{*slot};
            }
        };
        std::apply(
            [&try_slot](const auto &...slots) { (try_slot(slots), ...); },
            d_witnesses);
        return *found;
    }

    //! \expos
    std::tuple<std::optional<ERRORS>...> d_witnesses;
};

// \rSec3[transpose.errset.cons]{Constructors}

//! \constraints `ERROR`, with cv-qualification and references removed, is one
//! of the alternatives.
//! \effects Constructs a value witnessing exactly the alternative `ERROR`
//! names, holding `error` as that witness. Every other slot is empty.
//! \remarks This is the injection of an error value into the set it belongs
//! to. It is not explicit: a raised error is usable as the set that may raise
//! it.
template <class... ERRORS>
template <class ERROR>
    requires(error_set_has_v<remove_cvref_t<ERROR>, ERRORS...>)
constexpr error_set_of<ERRORS...>::error_set_of(ERROR &&error)
    : d_witnesses(detail::witness_slot<ERRORS>(std::forward<ERROR>(error))...) {
}

//! \constraints `NARROWER` is non-empty, names a different set, and every one
//! of its alternatives is an alternative of `*this`.
//! \effects Constructs a value witnessing exactly what `narrower` witnesses.
//! Slots for alternatives `NARROWER` cannot name are empty.
//! \remarks This is subsumption, and widening along inclusion is the only
//! conversion there is: there is none in the other direction, and none
//! between incomparable sets. There is deliberately no conversion from the
//! empty set, which is uninhabited, so no value ever needs one.
template <class... ERRORS>
template <class... NARROWER>
    requires(sizeof...(NARROWER) > 0) &&
            (!std::is_same_v<error_set_of<NARROWER...>,
                             error_set_of<ERRORS...>>) &&
            (error_set_has_v<NARROWER, ERRORS...> && ...)
constexpr error_set_of<ERRORS...>::error_set_of(
    const error_set_of<NARROWER...> &narrower)
    : d_witnesses(detail::widen_slot<ERRORS>(narrower)...) {}

// \rSec3[transpose.errset.obs]{Observers}

//! \returns `true` if and only if `ERROR` is one of the alternatives.
//! \remarks This is a type-level question -- what the computation *may*
//! raise -- not a question about the value.
template <class... ERRORS>
template <class ERROR>
constexpr auto error_set_of<ERRORS...>::contains() noexcept -> bool {
    return error_set_has_v<ERROR, ERRORS...>;
}

//! \constraints `ERROR` is one of the alternatives.
//! \returns `true` if and only if this value witnesses `ERROR`.
//! \remarks This is a value-level question -- what was actually raised.
template <class... ERRORS>
template <class ERROR>
    requires(error_set_has_v<ERROR, ERRORS...>)
constexpr auto error_set_of<ERRORS...>::holds() const noexcept -> bool {
    return std::get<std::optional<ERROR>>(d_witnesses).has_value();
}

//! \constraints `ERROR` is one of the alternatives.
//! \returns The witness for `ERROR` if this value raised it, and a disengaged
//! `optional` otherwise.
template <class... ERRORS>
template <class ERROR>
    requires(error_set_has_v<ERROR, ERRORS...>)
constexpr auto error_set_of<ERRORS...>::witness() const
    -> const std::optional<ERROR> & {
    return std::get<std::optional<ERROR>>(d_witnesses);
}

//! \returns The number of alternatives this value witnesses.
//! \remarks Always at least one, by the class invariant. Short-circuiting
//! composition produces exactly one; accumulating composition may produce
//! more. It is an observer rather than an implementation detail so that a
//! caller can check `visit`'s precondition instead of tripping it.
template <class... ERRORS>
constexpr auto error_set_of<ERRORS...>::witness_count() const noexcept
    -> std::size_t {
    return (static_cast<std::size_t>(
                std::get<std::optional<ERRORS>>(d_witnesses).has_value()) +
            ... + std::size_t{0});
}

//! \expects `witness_count()` is 1.
//! \effects Invokes `handler` with the single witnessed value.
//! \returns The result of that invocation.
//! \remarks The precondition is checked rather than assumed. Every value
//! produced by short-circuiting composition satisfies it; a subset with more
//! than one witness, which only accumulating composition produces, has no
//! single value to hand back, and answering with the leftmost would turn a
//! dropped error into a quiet wrong answer. For such a value, use `witness`
//! per alternative, guarded by `holds` or `witness_count`.
template <class... ERRORS>
template <class HANDLER>
constexpr auto error_set_of<ERRORS...>::visit(HANDLER &&handler) const
    -> decltype(auto) {
    return std::visit(std::forward<HANDLER>(handler), to_variant());
}

// \rSec3[transpose.errset.ops]{Operations}

//! \returns A value at the same grade witnessing every alternative either
//! operand witnesses.
//! \remarks Combination is left-biased per alternative: where both operands
//! witness the same error type, `*this`'s witness is kept. This is the
//! evidence-combining step of accumulating composition.
template <class... ERRORS>
constexpr auto
error_set_of<ERRORS...>::combined_with(const error_set_of &other) const
    -> error_set_of<ERRORS...> {
    return error_set_of(
        combine_witnesses(other, std::index_sequence_for<ERRORS...>{}));
}

/// The empty error set: bottom of the lattice, and uninhabited.
///
/// A computation graded 0 raises nothing, so there is no value to hold. Note
/// that 0 as a *grade* is spelled by the bare value type, not by this; this
/// type is the lattice bottom and the explicit uniform spelling, never
/// something the framework deduces on a user's behalf.
template <>
class error_set_of<> {
  public:
    // \ref{transpose.errset.empty}, the empty error set
    //! \remarks The empty error set is uninhabited: a computation graded by
    //! it raises nothing, so there is no value to construct.
    error_set_of() = delete;

    //! \returns `false`.
    template <class ERROR>
    static constexpr auto contains() noexcept -> bool {
        return false;
    }
};

// \rSec3[transpose.errset.empty]{The empty error set}

//! \seebelow
//! \remarks `error_set<ERRORS...>` is the canonicalizing spelling of an
//! error set: the pack is sorted and deduplicated, so `error_set<A, B>` and
//! `error_set<B, A, A>` denote the same type. A grade is therefore normalized
//! by type identity, not by source spelling or alternative position, and
//! every inclusion has one canonical target.
template <class... ERRORS>
using error_set =
    typename detail::error_set_from_list<detail::canonical_t<ERRORS...>>::type;

// -- Semilattice operations, in error vocabulary --------------------------
// The framework layer speaks grade vocabulary and gets these through a model
// registration; that indirection arrives with the grade concept. Here they
// are the native API of the model itself.

// \rSec3[transpose.errset.lattice]{Lattice operations}

//! \remarks `error_set_join<LEFT, RIGHT>::type` is the union of two error
//! sets. Canonicalization reduces the union to pack concatenation.
template <class LEFT, class RIGHT>
struct error_set_join;

template <class... LEFT, class... RIGHT>
struct error_set_join<error_set_of<LEFT...>, error_set_of<RIGHT...>> {
    using type = error_set<LEFT..., RIGHT...>;
};

template <class LEFT, class RIGHT>
using error_set_join_t = typename error_set_join<LEFT, RIGHT>::type;

//! \remarks `error_set_bottom` is the identity of join: the empty set.
using error_set_bottom = error_set<>;

//! \remarks `error_set_subsumes_v<LEFT, RIGHT>` is `true` when every
//! alternative of `LEFT` is an alternative of `RIGHT`. By order-from-join
//! this holds exactly when the join of `LEFT` and `RIGHT` is `RIGHT`, so the
//! only implicit widenings are subset inclusions: an error set can widen to a
//! superset and never the other way.
template <class LEFT, class RIGHT>
inline constexpr bool error_set_subsumes_v = false;

template <class... LEFT, class... RIGHT>
inline constexpr bool
    error_set_subsumes_v<error_set_of<LEFT...>, error_set_of<RIGHT...>> =
        (detail::list_contains_v<LEFT, detail::type_list<RIGHT...>> && ...);

// -- Evidence combination, in error vocabulary -----------------------------
// VALUE level, not grade level: the grade join above is type-level union and
// needs no semigroup at all. What the accumulating applicative object needs
// is a semigroup on the witnessed evidence, which is what this section
// supplies. See docs/decisions.md#accumulation-evidence.

//! \effects-equiv
//! \returns The combination of `lhs` and `rhs` at their common grade.
//! \remarks Combination is left-biased per alternative: where both operands
//! witness the same error type, `lhs`'s witness is kept. The type-level join
//! above is a commutative union and needs no semigroup; this value-level
//! combination is what the accumulating applicative object uses.
template <class... ERRORS>
constexpr auto error_set_combine(const error_set_of<ERRORS...> &lhs,
                                 const error_set_of<ERRORS...> &rhs)
    -> error_set_of<ERRORS...> {
    return lhs.combined_with(rhs);
}

namespace detail {

template <class... ERRORS>
constexpr auto combine_grade_evidence(const error_set_of<ERRORS...> &lhs,
                                      const error_set_of<ERRORS...> &rhs)
    -> error_set_of<ERRORS...> {
    return error_set_combine(lhs, rhs);
}

} // namespace detail

// -- recover: narrowing the grade by set difference ------------------------
// Stage recover-narrowing (docs/transpose-grading-plan.md#recover-narrowing).
// Error vocabulary, per grade.hpp's own comment that `recover` lives in the
// model's header, not the framework's.
//
// docs/decisions.md#recover-grade-inference: the handled set {H} is
// ANNOTATED -- explicit template arguments, never inferred from the
// handler's shape -- and CHECKED: one static_assert enforces H is a subset
// of the computation's grade (reusing error_set_of::contains, the same
// membership primitive docs/decisions.md#multi-witness-elimination names),
// another enforces the handler's result shape. The resulting grade
// `(e \ H) ∪ raised` is then a direct, non-recursive computation -- no
// lattice fixpoint, because one recover call is not a recursive fold
// ("inference only where no fixpoint is required").
//
// docs/decisions.md#multi-witness-elimination: recover needs no new public
// verb. Elimination is a static fold over H with runtime presence
// filtering, built entirely from the existing public API --
// error_set_of's injecting constructor and `combined_with` -- never from
// private access to the representation.

namespace detail {

// -- Type-level: set difference and list concatenation --------------------

/** FROM_LIST with every member of REMOVE_LIST taken out. */
template <class REMOVE_LIST, class FROM_LIST>
struct list_subtract;

template <class FROM_LIST>
struct list_subtract<type_list<>, FROM_LIST> {
    using type = FROM_LIST;
};

template <class HEAD, class... TAIL, class FROM_LIST>
struct list_subtract<type_list<HEAD, TAIL...>, FROM_LIST> {
    using type = typename list_subtract<
        type_list<TAIL...>, typename list_remove<HEAD, FROM_LIST>::type>::type;
};

template <class REMOVE_LIST, class FROM_LIST>
using list_subtract_t = typename list_subtract<REMOVE_LIST, FROM_LIST>::type;

/** Concatenates any number of type_lists, left to right. */
template <class... LISTS>
struct list_concat_all;

template <>
struct list_concat_all<> {
    using type = type_list<>;
};

template <class... ERRORS>
struct list_concat_all<type_list<ERRORS...>> {
    using type = type_list<ERRORS...>;
};

template <class... LEFT, class... RIGHT, class... REST>
struct list_concat_all<type_list<LEFT...>, type_list<RIGHT...>, REST...>
    : list_concat_all<type_list<LEFT..., RIGHT...>, REST...> {};

template <class... LISTS>
using list_concat_all_t = typename list_concat_all<LISTS...>::type;

/** The canonical error_set for an arbitrary (possibly unsorted, possibly
 * duplicate-bearing) type_list -- the type_list-input counterpart of the
 * canonicalizing `error_set<...>` alias, which takes a flat pack instead. */
template <class LIST>
using error_set_of_list_t = typename error_set_from_list<
    typename list_sort<typename list_dedupe<LIST>::type>::type>::type;

// -- What a handler call may return ----------------------------------------
// Exactly two shapes are licensed: unconditional recovery (the handler
// returns VALUE directly) or a recovery attempt that can itself raise
// (`std::expected<VALUE, error_set<...>>`). A bare-error result is not
// licensed: error vocabulary is confined to error_set, so a handler wanting
// to raise a plain type wraps it in a singleton error_set itself.

template <class RESULT, class VALUE>
inline constexpr bool is_valid_recover_result_v = std::is_same_v<RESULT, VALUE>;

template <class VALUE, class... RS>
inline constexpr bool is_valid_recover_result_v<
    std::expected<VALUE, error_set_of<RS...>>, VALUE> = true;

/** The elements a handler call for H may contribute to the joined "raised"
 * grade: none, for unconditional recovery; the raised error_set's own
 * elements otherwise. */
template <class RESULT, class VALUE>
struct raised_by_result {
    using type = type_list<>;
};

template <class VALUE, class... RS>
struct raised_by_result<std::expected<VALUE, error_set_of<RS...>>, VALUE> {
    using type = type_list<RS...>;
};

template <class HANDLER, class VALUE, class H>
struct handler_result_of {
    using type = remove_cvref_t<std::invoke_result_t<HANDLER, const H &>>;
};

/** The final grade `recover<HANDLED...>` produces: `(GRADE \ HANDLED) ∪
 * raised`, where `raised` is the join, over every HANDLED type, of what a
 * handler call for it may contribute. Computed once and shared between the
 * function's trailing return type and its body. */
template <class HANDLER, class VALUE, class GRADE, class... HANDLED>
struct recover_final_grade;

template <class HANDLER, class VALUE, class... ERRORS, class... HANDLED>
struct recover_final_grade<HANDLER, VALUE, error_set_of<ERRORS...>,
                           HANDLED...> {
    using remainder =
        list_subtract_t<type_list<HANDLED...>, type_list<ERRORS...>>;
    using raised = list_concat_all_t<typename raised_by_result<
        typename handler_result_of<HANDLER, VALUE, HANDLED>::type,
        VALUE>::type...>;
    using type = error_set_of_list_t<list_concat_all_t<remainder, raised>>;
};

template <class HANDLER, class VALUE, class GRADE, class... HANDLED>
using recover_final_grade_t =
    typename recover_final_grade<HANDLER, VALUE, GRADE, HANDLED...>::type;

// -- Value level: carrying witnesses forward through the PUBLIC API only ---
// No private access, no friendship: exactly the injecting constructor and
// `combined_with` that any user of error_set already has. This is what makes
// the multi-witness-elimination fence a fence rather than an oversight --
// recover's mechanism is not privileged.

/** If SOURCE currently witnesses E, E is not in HANDLED_LIST, and TARGET can
 * name E, injects that witness into `accumulated` (creating it if absent,
 * combining left-biased if already present). A no-op otherwise, including
 * when TARGET cannot name E at all -- which is exactly the case for a
 * HANDLED type once it has left the result grade. */
template <class E, class HANDLED_LIST, class TARGET, class SOURCE>
constexpr void carry_witness(std::optional<TARGET> &accumulated,
                             const SOURCE &source) {
    if constexpr (!list_contains_v<E, HANDLED_LIST> &&
                  TARGET::template contains<E>()) {
        if (source.template holds<E>()) {
            TARGET injected(*source.template witness<E>());
            accumulated = accumulated.has_value()
                              ? accumulated->combined_with(injected)
                              : injected;
        }
    }
}

/** Folds every witness a raised error_set carries into `accumulated`,
 * unconditionally (nothing is excluded -- these are freshly raised, not
 * being narrowed away). */
template <class TARGET, class VALUE, class... RS>
constexpr void
carry_raised(std::optional<TARGET> &accumulated,
             const std::expected<VALUE, error_set_of<RS...>> &result) {
    (carry_witness<RS, type_list<>>(accumulated, result.error()), ...);
}

/** If `error` witnesses H, invokes `handler` on that witness: records the
 * recovered VALUE (first one wins, leftmost by canonical order, matching
 * error_set_of::combined_with's own tie-break), or folds a raised error_set
 * into `accumulated`. A no-op when H is not witnessed. */
template <class H, class HANDLER, class VALUE, class TARGET, class SOURCE>
constexpr void apply_handler(HANDLER &handler, std::optional<VALUE> &recovered,
                             std::optional<TARGET> &accumulated,
                             const SOURCE &error) {
    if (error.template holds<H>()) {
        auto result = std::invoke(handler, *error.template witness<H>());
        if constexpr (std::is_same_v<remove_cvref_t<decltype(result)>, VALUE>) {
            if (!recovered.has_value()) {
                recovered = std::move(result);
            }
        } else {
            if (result.has_value()) {
                if (!recovered.has_value()) {
                    recovered = *result;
                }
            } else {
                carry_raised(accumulated, result);
            }
        }
    }
}

/// The type `recover` returns: the computation re-indexed at the narrowed
/// grade. Named by `recover`'s definition; the declaration masks it and the
/// wording states the narrowing in prose.
//! \expos
template <class HANDLER, class VALUE, class GRADE, class... HANDLED>
using recover_return_t =
    rebind_grade_t<VALUE,
                   recover_final_grade_t<HANDLER, VALUE, GRADE, HANDLED...>>;

} // namespace detail

// \rSec3[transpose.errset.recover]{recover}

//! \seebelow
//! \mandates `HANDLED` is not empty; every type in `HANDLED` is one of the
//! computation's alternatives; and for each such type `handler` returns
//! either `VALUE` or a `std::expected<VALUE, error_set<...>>`.
//! \effects For each type in `HANDLED` that the computation's error
//! witnesses, invokes `handler` with that witness. A handler either recovers
//! a value or raises an error set of its own. Witnesses for types outside
//! `HANDLED`, and any a handler raises, survive into the result.
//! \returns The computation at the narrowed grade: the alternatives it may
//! raise, less those handled, plus any a handler raises. The result holds a
//! value when every witness present was recovered, and otherwise the
//! surviving witnesses.
//! \remarks The handled set is annotated rather than inferred: it is given
//! as explicit template arguments and checked against the computation's
//! grade. Recovering one alternative from a value that raised two leaves the
//! other, which is still an error. If more than one handled type is
//! witnessed and each independently recovers a value, the first in canonical
//! order is the result, matching the tie-break of `combined_with`.
template <class... HANDLED, class VALUE, class... ERRORS, class HANDLER>
constexpr auto
recover(const std::expected<VALUE, error_set_of<ERRORS...>> &computation,
        HANDLER &&handler)
    -> detail::recover_return_t<HANDLER, VALUE, error_set_of<ERRORS...>,
                                HANDLED...> {
    static_assert(sizeof...(HANDLED) > 0,
                  "recover needs at least one HANDLED type.");
    static_assert(
        (error_set_of<ERRORS...>::template contains<HANDLED>() && ...),
        "recover's HANDLED types must be members of the computation's grade "
        "-- CHECKED, per docs/decisions.md#recover-grade-inference. The "
        "handled set is ANNOTATED (explicit template arguments on recover), "
        "never inferred.");
    static_assert(
        (detail::is_valid_recover_result_v<
             typename detail::handler_result_of<HANDLER, VALUE, HANDLED>::type,
             VALUE> &&
         ...),
        "recover's handler must return either the recovered VALUE directly, "
        "or std::expected<VALUE, error_set<...>> if the recovery attempt can "
        "itself raise. See docs/decisions.md#recover-grade-inference.");

    using Grade = error_set_of<ERRORS...>;
    using FinalGrade =
        detail::recover_final_grade_t<HANDLER, VALUE, Grade, HANDLED...>;
    using Return = detail::recover_return_t<HANDLER, VALUE, Grade, HANDLED...>;

    if (computation.has_value()) {
        return Return(*computation);
    }

    const Grade &error = computation.error();
    std::optional<VALUE> recovered;
    std::optional<FinalGrade> accumulated;

    (detail::carry_witness<ERRORS, detail::type_list<HANDLED...>>(accumulated,
                                                                  error),
     ...);
    (detail::apply_handler<HANDLED>(handler, recovered, accumulated, error),
     ...);

    if constexpr (std::is_same_v<Return, VALUE>) {
        // FinalGrade is ∅: every carry_witness/carry_raised call above was a
        // no-op by construction (TARGET::contains<E>() is unconditionally
        // false for error_set_of<>), so `accumulated` can never actually hold
        // a value here -- every present witness was necessarily HANDLED and
        // recovered.
        return *recovered;
    } else {
        if (accumulated.has_value()) {
            return Return(std::unexpect, *accumulated);
        }
        return Return(*recovered);
    }
}

// -- Registration as a model of the grade algebra -------------------------
// The direction of dependency is the point: the model knows about the
// framework, never the reverse. Everything above this line is error
// vocabulary; everything below translates it into grade vocabulary, and is
// the only place the two meet. A second algebra registers the same way and
// needs nothing from here -- which is the claim the law harness exists to
// test (docs/decisions.md#grade-generality).

/// Whether T is a specialization of std::expected. Exposition-only: it is
/// named by the re-indexing constraints below and by the expected instance's
/// own, where a `detail`-qualified spelling would reach the wording.
//! \expos
template <class T>
inline constexpr bool is_expected_v = false;

//! \also
template <class VALUE, class ERROR>
inline constexpr bool is_expected_v<std::expected<VALUE, ERROR>> = true;

//! \remarks `error_set_model` names the model that the error-set grades
//! belong to. It is what makes two grades comparable: grades of different
//! models do not mix.
struct error_set_model {};

template <class... ERRORS>
struct grade_model<error_set_of<ERRORS...>> {
    using type = error_set_model;
};

template <class... LEFT, class... RIGHT>
struct grade_join<error_set_of<LEFT...>, error_set_of<RIGHT...>> {
    using type =
        error_set_join_t<error_set_of<LEFT...>, error_set_of<RIGHT...>>;
};

template <class... ERRORS>
struct grade_bottom<error_set_of<ERRORS...>> {
    using type = error_set_bottom;
};

template <class... LEFT, class... RIGHT>
struct grade_subsumes<error_set_of<LEFT...>, error_set_of<RIGHT...>>
    : std::bool_constant<
          error_set_subsumes_v<error_set_of<LEFT...>, error_set_of<RIGHT...>>> {
};

/** Semantic grade detection for expected in the error_set model.
 *
 * A plain error alternative contributes the singleton grade `error_set<E>`;
 * an explicit error_set alternative reports that set directly. Lazy join is
 * a discipline on the carrier spelling deduced by expected's typeclass
 * operations, not on this type-level grade reading.
 */
template <class VALUE, class ERROR>
struct grade_of<std::expected<VALUE, ERROR>> {
    using type = error_set<ERROR>;
};

template <class VALUE, class... ERRORS>
struct grade_of<std::expected<VALUE, error_set_of<ERRORS...>>> {
    using type = error_set_of<ERRORS...>;
};

/** Re-indexing an expected at a non-empty error set replaces its error
 * alternative. */
template <class VALUE, class ERROR, class HEAD, class... TAIL>
struct rebind_grade<std::expected<VALUE, ERROR>, error_set_of<HEAD, TAIL...>> {
    using type = std::expected<VALUE, error_set_of<HEAD, TAIL...>>;
};

/** Re-indexing a BARE value at a non-empty error set is the promotion into a
 * carrier: the ∅ fiber is the ungraded type itself, so this is where a
 * pipeline first acquires an error alternative. */
template <class VALUE, class HEAD, class... TAIL>
    requires(!is_expected_v<VALUE>)
struct rebind_grade<VALUE, error_set_of<HEAD, TAIL...>> {
    using type = std::expected<VALUE, error_set_of<HEAD, TAIL...>>;
};

/** Re-indexing at the EMPTY error set yields the bare value, never
 * `expected<T, error_set<>>`.
 *
 * This is the mechanized form of the sentinel in
 * docs/decisions.md#empty-grade-spelling: the uniform degenerate-expected
 * form stays available as an explicit spelling, and no framework path
 * materializes it on a user's behalf.
 */
template <class VALUE>
    requires(!is_expected_v<VALUE>)
struct rebind_grade<VALUE, error_set_of<>> {
    using type = VALUE;
};

template <class VALUE, class ERROR>
struct rebind_grade<std::expected<VALUE, ERROR>, error_set_of<>> {
    using type = VALUE;
};

} // namespace beman::transpose

#endif // BEMAN_TRANSPOSE_ERROR_SET_HPP
