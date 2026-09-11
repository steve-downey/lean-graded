// tests/beman/transpose/laws.hpp                                     -*-C++-*-
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#ifndef BEMAN_TRANSPOSE_TEST_LAWS_HPP
#define BEMAN_TRANSPOSE_TEST_LAWS_HPP

// The graded-law harness: semantic requirements, checked on demand.
//
// A TEST DELIVERABLE, NOT A REGISTRATION GATE. Nothing in the shipped headers
// includes this one, and no concept or `requires` clause anywhere calls
// `check_graded_laws`. That is deliberate and is the standard's own posture:
// semantic requirements are stated in prose, and checking them is opt-in. A
// bool-returning law checker that shipped alongside the concept would migrate
// into `requires` clauses -- it is one token to add and it looks like rigour
// -- and every constraint that merely MENTIONS a grade would then drag a full
// law check behind it, at every overload-resolution site, forever. The
// economics of a law check are pay-once-per-model; the economics of a
// constraint are pay-per-use. See `grade_semilattice` in
// include/beman/transpose/grade.hpp, which says the same thing from the other
// side, and the deliberate-omissions item in
// docs/transpose-grading-plan.md#paper-revision.
//
// FRAMEWORK VOCABULARY ONLY. This header includes grade.hpp and nothing else
// from the library. It never names `error_set`, `recover`, or `expected`. If
// it ever has to, the claim of
// docs/decisions.md#grade-generality -- that the framework layer speaks only
// grade vocabulary and `error_set` is merely one model -- is false, and the
// right response is to log the leak, not to add the include.
//
// A MODEL UNDER TEST supplies two type lists and nothing else:
//   - `grades`: a `grade_sample<...>` of elements to quantify over. For a
//     free semilattice on n generators the full 2^n subsets exercise every
//     law shape; a smaller sample is a weaker test, not a different one.
//   - `values`: a `value_sample<...>` of ordinary value types to instantiate
//     carriers at, via `rebind_grade`. A move-only probe is worth including:
//     the value-level laws run inside `consteval`, so a stray copy on the
//     subsumption path is a compile error rather than a performance note.
//
// Laws are checked with `static_assert` INSIDE the checkers rather than only
// by the returned bool, so a violation names the law and the offending grades
// instead of collapsing to `static_assert(false)` at the call site. The bool
// is returned anyway, because the plan's surface is
// `static_assert(check_graded_laws<Model>())` and a checker that cannot be
// used that way is not the deliverable.

#include <beman/transpose/grade.hpp>

#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>

namespace beman::transpose::test::laws {

// -- What a model under test supplies -------------------------------------

/** The grade elements to quantify the algebra laws over. */
template <class... GRADES>
struct grade_sample {};

/** The value types to instantiate carriers at, for the carrier laws. */
template <class... VALUES>
struct value_sample {};

/** A model under test: a grade sample and a value sample. Deliberately not a
 * description of the algebra itself -- that is what `grade_semilattice`
 * already is, and the harness is written against the concept. This says only
 * WHICH elements to try. */
template <class MODEL>
concept graded_model = requires {
    typename MODEL::grades;
    typename MODEL::values;
};

/** A distinguishable value of a probe type. The default builds one from an
 * int; specialize for a probe that cannot be built that way. */
template <class VALUE>
struct probe_value {
    static constexpr auto make() -> VALUE;
};

template <class VALUE>
constexpr auto probe_value<VALUE>::make() -> VALUE {
    return VALUE(42);
}

template <class VALUE>
struct probe_value<std::unique_ptr<VALUE>> {
    static constexpr auto make() -> std::unique_ptr<VALUE>;
};

template <class VALUE>
constexpr auto probe_value<std::unique_ptr<VALUE>>::make()
    -> std::unique_ptr<VALUE> {
    return std::make_unique<VALUE>(42);
}

// -- Declarations ---------------------------------------------------------

template <grade_semilattice GRADE>
consteval auto check_unary_grade_laws() -> bool;

template <grade_semilattice LEFT, grade_semilattice RIGHT>
consteval auto check_binary_grade_laws() -> bool;

template <grade_semilattice LEFT, grade_semilattice MIDDLE,
          grade_semilattice RIGHT>
consteval auto check_ternary_grade_laws() -> bool;

template <class VALUE, grade_semilattice GRADE>
consteval auto check_carrier_at() -> bool;

template <class VALUE, grade_semilattice FROM, grade_semilattice TO>
consteval auto check_subsumption_coherence() -> bool;

template <class... GRADES>
consteval auto check_grade_algebra(grade_sample<GRADES...>) -> bool;

template <class LEFT, class... GRADES>
consteval auto check_grade_algebra_from(grade_sample<GRADES...>) -> bool;

template <class LEFT, class MIDDLE, class... GRADES>
consteval auto check_grade_algebra_through(grade_sample<GRADES...>) -> bool;

template <class... GRADES, class... VALUES>
consteval auto check_carriers(grade_sample<GRADES...>, value_sample<VALUES...>)
    -> bool;

template <class VALUE, class... GRADES>
consteval auto check_carriers_for(grade_sample<GRADES...>) -> bool;

template <class VALUE, class FROM, class... GRADES>
consteval auto check_coherence_from(grade_sample<GRADES...>) -> bool;

template <graded_model MODEL>
consteval auto check_graded_laws() -> bool;

// -- The algebra laws, one grade at a time --------------------------------
//
// Idempotence and the unit are the two properties
// docs/decisions.md#grade-generality calls load-bearing on their own:
// idempotent makes fold grades shape-independent, so recursive data types
// stay ungraded while effects are graded; the unit is what lets an ungraded
// computation sit in a graded pipeline unchanged.

template <grade_semilattice GRADE>
consteval auto check_unary_grade_laws() -> bool {
    static_assert(std::is_same_v<grade_join_t<GRADE, GRADE>, GRADE>,
                  "Idempotence: join(g, g) == g. Without it, fold grades "
                  "depend on the runtime shape of the structure being "
                  "folded, which is the case grade-generality excludes.");
    static_assert(
        std::is_same_v<grade_join_t<grade_bottom_t<GRADE>, GRADE>, GRADE>,
        "Left unit: join(bottom, g) == g.");
    static_assert(
        std::is_same_v<grade_join_t<GRADE, grade_bottom_t<GRADE>>, GRADE>,
        "Right unit: join(g, bottom) == g.");
    static_assert(std::is_same_v<grade_bottom_t<grade_bottom_t<GRADE>>,
                                 grade_bottom_t<GRADE>>,
                  "Bottom is its own bottom: the model has one ∅, and "
                  "asking ∅ for its ∅ does not move.");
    static_assert(std::is_same_v<grade_model_t<GRADE>,
                                 grade_model_t<grade_bottom_t<GRADE>>>,
                  "A grade and its bottom belong to the same model.");
    static_assert(grade_subsumes_v<GRADE, GRADE>,
                  "Reflexivity: every grade subsumes into itself. Follows "
                  "from idempotence by order-from-join; checked separately "
                  "so a hand-written order that disagrees is caught.");
    static_assert(grade_subsumes_v<grade_bottom_t<GRADE>, GRADE>,
                  "Bottom is least: a computation that raises nothing is "
                  "usable wherever one that may raise something is.");

    return true;
}

// -- The algebra laws, two grades at a time -------------------------------

template <grade_semilattice LEFT, grade_semilattice RIGHT>
consteval auto check_binary_grade_laws() -> bool {
    static_assert(
        std::is_same_v<grade_join_t<LEFT, RIGHT>, grade_join_t<RIGHT, LEFT>>,
        "Commutativity: join(a, b) == join(b, a). This is what "
        "makes grade arithmetic order-free, so the order operands "
        "are written in cannot change a deduced type.");
    static_assert(grade_subsumes_v<LEFT, RIGHT> ==
                      std::is_same_v<grade_join_t<LEFT, RIGHT>, RIGHT>,
                  "Order from join: a ⊑ b exactly when join(a, b) == b. The "
                  "order must be READ OFF the join rather than declared "
                  "beside it -- that is what makes the inclusion between two "
                  "grades unique, hence the coercion canonical, hence "
                  "subsumption coherently implicit.");
    static_assert(grade_subsumes_v<LEFT, grade_join_t<LEFT, RIGHT>>,
                  "The join is an upper bound of its left operand.");
    static_assert(grade_subsumes_v<RIGHT, grade_join_t<LEFT, RIGHT>>,
                  "The join is an upper bound of its right operand.");
    static_assert(
        !(grade_subsumes_v<LEFT, RIGHT> && grade_subsumes_v<RIGHT, LEFT>) ||
            std::is_same_v<LEFT, RIGHT>,
        "Antisymmetry: two grades that subsume into each other are "
        "the same TYPE. A model whose canonical forms are not "
        "decidable fails here, which is the requirement "
        "grade-generality places on any future algebra.");
    static_assert(
        std::is_same_v<grade_bottom_t<LEFT>, grade_bottom_t<RIGHT>>,
        "One model, one bottom: every grade in a sample must agree on ∅.");
    static_assert(std::is_same_v<grade_model_t<LEFT>, grade_model_t<RIGHT>>,
                  "One sample, one model: law checks quantify within a "
                  "single grade model.");
    return true;
}

// -- The algebra laws, three grades at a time -----------------------------

template <grade_semilattice LEFT, grade_semilattice MIDDLE,
          grade_semilattice RIGHT>
consteval auto check_ternary_grade_laws() -> bool {
    static_assert(
        std::is_same_v<grade_join_t<grade_join_t<LEFT, MIDDLE>, RIGHT>,
                       grade_join_t<LEFT, grade_join_t<MIDDLE, RIGHT>>>,
        "Associativity: join(join(a, b), c) == join(a, join(b, c)). With "
        "commutativity this makes a fold of joins independent of how the "
        "fold was bracketed.");
    static_assert(
        !(grade_subsumes_v<LEFT, MIDDLE> && grade_subsumes_v<MIDDLE, RIGHT>) ||
            grade_subsumes_v<LEFT, RIGHT>,
        "Transitivity of the order.");
    return true;
}

// -- Carrier laws ---------------------------------------------------------
//
// These are where the algebra meets a type that holds values. They run inside
// `consteval`: every carrier below is actually constructed during constant
// evaluation, so a subsumption path that allocates, copies a move-only value,
// or reaches a non-constexpr function fails to compile.

template <class VALUE, grade_semilattice GRADE>
consteval auto check_carrier_at() -> bool {
    static_assert(std::is_same_v<grade_of_t<VALUE>, unit_grade>,
                  "A value probe must be an ORDINARY type -- ∅-graded, "
                  "unknown to any model. A probe the model already grades "
                  "would test the model against itself.");

    using carrier = rebind_grade_t<VALUE, GRADE>;

    // grade_of ∘ rebind_grade is the identity, with ONE licensed exception:
    // at the model's bottom the carrier is the bare value again
    // (docs/decisions.md#empty-grade-spelling), and a bare value reports the
    // framework's ungraded sentinel rather than a model grade.
    static_assert(
        std::is_same_v<grade_of_t<carrier>, GRADE> ||
            (std::is_same_v<GRADE, grade_bottom_t<GRADE>> &&
             std::is_same_v<grade_of_t<carrier>, unit_grade>),
        "Round trip: re-indexing a value at a grade and then asking for its "
        "grade returns what was asked for -- except at the model's bottom, "
        "where the carrier is the bare value and reports the framework's ∅.");

    // Re-indexing is REPLACEMENT, never nesting: asking a carrier for the
    // grade it already has changes nothing, and narrowing it to the model's ∅
    // hands back the bare value rather than a degenerate carrier. The second
    // of these is the mechanized form of
    // docs/decisions.md#empty-grade-spelling's sentinel, generalized off the
    // shipped model: NO model's framework path may materialize an ∅-graded
    // carrier the user did not write.
    static_assert(std::is_same_v<rebind_grade_t<carrier, GRADE>, carrier>,
                  "Re-indexing a carrier at its own grade is the identity. A "
                  "model that nests here builds carrier<carrier<T>> the first "
                  "time a grade is recomputed.");
    static_assert(
        std::is_same_v<rebind_grade_t<carrier, grade_bottom_t<GRADE>>, VALUE>,
        "Narrowing a carrier to the model's ∅ yields the BARE value.");

    static_assert(
        std::is_same_v<decltype(grade_subsume<GRADE>(
                           probe_value<VALUE>::make())),
                       carrier>,
        "Promotion: subsuming a bare value into a grade produces that "
        "grade's carrier. The bare value IS the ∅ fiber, so promotion is "
        "just subsumption from ∅ -- there is no separate lifting operation "
        "for the framework to get wrong.");

    // Actually run it, in a constant expression.
    auto promoted = grade_subsume<GRADE>(probe_value<VALUE>::make());
    static_assert(std::is_same_v<decltype(promoted), carrier>);
    return true;
}

template <class VALUE, grade_semilattice FROM, grade_semilattice TO>
consteval auto check_subsumption_coherence() -> bool {
    if constexpr (grade_subsumes_v<FROM, TO>) {
        using narrow = rebind_grade_t<VALUE, FROM>;
        using wide = rebind_grade_t<VALUE, TO>;

        static_assert(
            std::is_same_v<decltype(grade_subsume<TO>(grade_subsume<FROM>(
                               probe_value<VALUE>::make()))),
                           wide>,
            "Composed subsumption lands in the same carrier as the direct "
            "one. A licensed widening must stay licensed after another "
            "widening has already happened.");

        // COHERENCE, the payoff law: going ∅ → FROM → TO and going ∅ → TO
        // directly produce the same value. Two different coercion paths
        // between the same pair of grades must agree, or "subsumption is
        // implicit" is a promise the type system cannot keep. Skipped for a
        // move-only probe: comparing two independently-built values there
        // compares identities, not contents.
        if constexpr (std::copy_constructible<VALUE> &&
                      std::equality_comparable<wide>) {
            const wide direct = grade_subsume<TO>(probe_value<VALUE>::make());
            const wide composed = grade_subsume<TO>(
                grade_subsume<FROM>(probe_value<VALUE>::make()));
            if (!(direct == composed)) {
                return false;
            }
        } else {
            // Still exercise the path, for the move-only probe: it runs in a
            // constant expression, so a stray copy is a compile error.
            auto composed = grade_subsume<TO>(
                grade_subsume<FROM>(probe_value<VALUE>::make()));
            static_assert(std::is_same_v<decltype(composed), wide>);
        }
        static_assert(std::is_same_v<narrow, rebind_grade_t<VALUE, FROM>>);
    }
    return true;
}

// -- Quantification -------------------------------------------------------

template <class... GRADES>
consteval auto check_grade_algebra(grade_sample<GRADES...> sample) -> bool {
    return (check_unary_grade_laws<GRADES>() && ...) &&
           (check_grade_algebra_from<GRADES>(sample) && ...);
}

template <class LEFT, class... GRADES>
consteval auto check_grade_algebra_from(grade_sample<GRADES...> sample)
    -> bool {
    return (check_binary_grade_laws<LEFT, GRADES>() && ...) &&
           (check_grade_algebra_through<LEFT, GRADES>(sample) && ...);
}

template <class LEFT, class MIDDLE, class... GRADES>
consteval auto check_grade_algebra_through(grade_sample<GRADES...>) -> bool {
    return (check_ternary_grade_laws<LEFT, MIDDLE, GRADES>() && ...);
}

template <class VALUE, class FROM, class... GRADES>
consteval auto check_coherence_from(grade_sample<GRADES...>) -> bool {
    return (check_subsumption_coherence<VALUE, FROM, GRADES>() && ...);
}

template <class VALUE, class... GRADES>
consteval auto check_carriers_for(grade_sample<GRADES...> sample) -> bool {
    return (check_carrier_at<VALUE, GRADES>() && ...) &&
           (check_coherence_from<VALUE, GRADES>(sample) && ...);
}

template <class... GRADES, class... VALUES>
consteval auto check_carriers(grade_sample<GRADES...> grades,
                              value_sample<VALUES...>) -> bool {
    return (check_carriers_for<VALUES>(grades) && ...);
}

/** Checks every graded law for MODEL, over the grade and value samples it
 * names. Usable as `static_assert(check_graded_laws<Model>())`. */
template <graded_model MODEL>
consteval auto check_graded_laws() -> bool {
    return check_grade_algebra(typename MODEL::grades{}) &&
           check_carriers(typename MODEL::grades{}, typename MODEL::values{});
}

} // namespace beman::transpose::test::laws

#endif // BEMAN_TRANSPOSE_TEST_LAWS_HPP
