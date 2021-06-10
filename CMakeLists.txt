cmake_minimum_required(VERSION 3.4.3 FATAL_ERROR)
project(Thorin VERSION 2.0 DESCRIPTION "the higher-order intermediate representation")

option(BUILD_SHARED_LIBS "Build shared libraries" ON)
option(THORIN_PROFILE "profile complexity in thorin::HashTable - only works in Debug build" ON)
option(PACKAGE_TESTS "Build the tests" ON)

set(CMAKE_CONFIGURATION_TYPES "Debug;Release" CACHE STRING "limited config" FORCE)
set(CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS 1)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

if(CMAKE_BUILD_TYPE STREQUAL "")
    set(CMAKE_BUILD_TYPE Debug CACHE STRING "Debug or Release" FORCE)
endif()

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules")

message(STATUS "Using Debug flags: ${CMAKE_CXX_FLAGS_DEBUG}")
message(STATUS "Using Release flags: ${CMAKE_CXX_FLAGS_RELEASE}")
message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")

# configure thorin preprocessor definitions
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    set(THORIN_ENABLE_CHECKS TRUE)
endif()
if(THORIN_PROFILE)
    set(THORIN_ENABLE_PROFILING TRUE)
endif()

configure_file(src/thorin/config.h.in ${CMAKE_BINARY_DIR}/include/thorin/config.h @ONLY)
include_directories(${CMAKE_BINARY_DIR}/include)

add_subdirectory(src)

if(PACKAGE_TESTS)
    enable_testing()
    include(GoogleTest)
    add_subdirectory(gtest)
endif()

export(TARGETS thorin FILE ${CMAKE_BINARY_DIR}/share/anydsl/cmake/thorin-exports.cmake)
configure_file(cmake/thorin-config.cmake.in ${CMAKE_BINARY_DIR}/share/anydsl/cmake/thorin-config.cmake @ONLY)
