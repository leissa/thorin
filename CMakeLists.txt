cmake_minimum_required(VERSION 3.4.3 FATAL_ERROR)
project(Thorin VERSION 2.0 DESCRIPTION "the higher-order intermediate representation")

include(CTest)
option(BUILD_SHARED_LIBS "Build shared libraries" ON)
option(THORIN_PROFILE "profile complexity in thorin::HashTable - only works in Debug build" ON)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)
set(CMAKE_CONFIGURATION_TYPES "Debug;Release" CACHE STRING "limited config" FORCE)
set(CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS 1)

if(CMAKE_BUILD_TYPE STREQUAL "")
    set(CMAKE_BUILD_TYPE Debug CACHE STRING "Debug or Release" FORCE)
endif()

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules")

# configure thorin preprocessor definitions
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    set(THORIN_ENABLE_CHECKS TRUE)
endif()
if(THORIN_PROFILE)
    set(THORIN_ENABLE_PROFILING TRUE)
endif()

add_subdirectory(src)

if(BUILD_TESTING)
    include(GoogleTest)
    add_subdirectory(googletest)
    add_subdirectory(gtest)

    # keep cache clean
    mark_as_advanced(
        BUILD_GMOCK BUILD_GTEST BUILD_SHARED_LIBS
        gmock_build_tests gtest_build_samples gtest_build_tests
        gtest_disable_pthreads gtest_force_shared_crt gtest_hide_internal_symbols
    )

    # keep IDEs folders clean
    set_target_properties(gtest      PROPERTIES FOLDER extern)
    set_target_properties(gtest_main PROPERTIES FOLDER extern)
    set_target_properties(gmock      PROPERTIES FOLDER extern)
    set_target_properties(gmock_main PROPERTIES FOLDER extern)
endif()

export(TARGETS thorin FILE ${CMAKE_BINARY_DIR}/share/anydsl/cmake/thorin-exports.cmake)
configure_file(cmake/thorin-config.cmake.in ${CMAKE_BINARY_DIR}/share/anydsl/cmake/thorin-config.cmake @ONLY)
message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
