# CMakeLists.txt                                                     -*-cmake-*-
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

cmake_minimum_required(VERSION 3.30...4.3)

project(
    beman.transpose
    DESCRIPTION
        "Shape-preserving traversal and transposition for contextual computations (Paper A / P3200)"
    LANGUAGES CXX
    VERSION 0.0.0
)

include(CTest)

option(
    BEMAN_TRANSPOSE_BUILD_TESTS
    "Enable building tests and test infrastructure. Default: ${PROJECT_IS_TOP_LEVEL}. Values: { ON, OFF }."
    ${PROJECT_IS_TOP_LEVEL}
)

option(
    BEMAN_TRANSPOSE_BUILD_EXAMPLES
    "Enable building examples. Default: ${PROJECT_IS_TOP_LEVEL}. Values: { ON, OFF }."
    ${PROJECT_IS_TOP_LEVEL}
)

configure_file(
    "${PROJECT_SOURCE_DIR}/include/beman/transpose/config_generated.hpp.in"
    "${PROJECT_BINARY_DIR}/include/beman/transpose/config_generated.hpp"
    @ONLY
)

# beman.transpose is a header-only library.
add_library(beman.transpose INTERFACE)
add_library(beman::transpose ALIAS beman.transpose)

target_compile_features(beman.transpose INTERFACE cxx_std_23)

target_sources(
    beman.transpose
    INTERFACE
        FILE_SET HEADERS
            BASE_DIRS
                "${PROJECT_SOURCE_DIR}/include"
                "${PROJECT_BINARY_DIR}/include"
)

set_target_properties(
    beman.transpose
    PROPERTIES VERIFY_INTERFACE_HEADER_SETS ${PROJECT_IS_TOP_LEVEL}
)

add_subdirectory(include/beman/transpose)

include(infra/cmake/beman-install-library.cmake)
beman_install_library(beman.transpose TARGETS beman.transpose)

if(BEMAN_TRANSPOSE_BUILD_TESTS)
    find_package(Catch2 3 REQUIRED)
    include(Catch)
    enable_testing()
    add_subdirectory(tests/beman/transpose)
endif()

if(BEMAN_TRANSPOSE_BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()

# Coverage helper retained for the Makefile Gcov configuration.
configure_file("cmake/gcovr.cfg.in" gcovr.cfg @ONLY)

add_custom_target(
    process_coverage
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Running gcovr to process coverage results"
    COMMAND mkdir -p coverage
    COMMAND gcovr --config gcovr.cfg .
)
