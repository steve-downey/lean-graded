# tests/beman/transpose/CMakeLists.txt                              -*-cmake-*-
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

set(transpose_tests
    baseline_deduction
    monoid
    dual_monoid
    error_set
    crtp_absorption
    accumulating_object
    functor
    apply
    expected
    fold
    grade
    laws
    monad
    objects
    traverse
    transpose
    sequence
    sender
    simd_lanes
    zip_list
)

# The simd test self-gates on C++26 + <simd>; only build it when the header
# exists at all (mirrors examples/CMakeLists.txt).
include(CheckIncludeFileCXX)
check_include_file_cxx(simd BEMAN_TRANSPOSE_TESTS_HAS_SIMD)
if(BEMAN_TRANSPOSE_TESTS_HAS_SIMD)
    list(APPEND transpose_tests simd)
endif()

foreach(test ${transpose_tests})
    add_executable(beman.transpose.tests.${test})
    target_sources(beman.transpose.tests.${test} PRIVATE ${test}.test.cpp)
    target_include_directories(
        beman.transpose.tests.${test}
        PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}
    )
    target_link_libraries(
        beman.transpose.tests.${test}
        PRIVATE beman::transpose Catch2::Catch2WithMain
    )
    catch_discover_tests(beman.transpose.tests.${test})
endforeach()

# detail/ support headers carry their own tests.
add_executable(beman.transpose.tests.detail.typeclass_base)
target_sources(
    beman.transpose.tests.detail.typeclass_base
    PRIVATE detail/typeclass_base.test.cpp
)
target_link_libraries(
    beman.transpose.tests.detail.typeclass_base
    PRIVATE beman::transpose Catch2::Catch2WithMain
)
catch_discover_tests(beman.transpose.tests.detail.typeclass_base)
