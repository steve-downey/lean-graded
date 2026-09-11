# installtest/CMakeLists.txt                                        -*-CMake-*-
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

cmake_minimum_required(VERSION 3.27)
project(TestInstalledTranspose LANGUAGES CXX)

# Enable testing in this separate project
enable_testing()

# Find the installed package
set(NAME_INSTALL_DIR
    "${CMAKE_CURRENT_LIST_DIR}/../.install/lib/cmake/beman.transpose"
)
find_package(beman.transpose REQUIRED PATHS ${NAME_INSTALL_DIR} NO_DEFAULT_PATH)

# Add the test executable
add_executable(TestInstalledLibrary test.cpp)
target_compile_features(TestInstalledLibrary PRIVATE cxx_std_23)

# Link against the imported target
target_link_libraries(TestInstalledLibrary beman::transpose)

# Register the test with CTest
add_test(NAME RunInstalledTest COMMAND TestInstalledLibrary)

# Ensure 'make test' first builds the 'all' target
set(CMAKE_SKIP_TEST_ALL_DEPENDENCY FALSE)
