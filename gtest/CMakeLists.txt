enable_testing()
include(GoogleTest)

add_subdirectory("${PROJECT_SOURCE_DIR}/googletest" "googletest")

# keep cache clean
mark_as_advanced(
    BUILD_GMOCK BUILD_GTEST BUILD_SHARED_LIBS
    gmock_build_tests gtest_build_samples gtest_build_tests
    gtest_disable_pthreads gtest_force_shared_crt gtest_hide_internal_symbols
)

# keep IDEs folders clean
set_target_properties(gtest PROPERTIES FOLDER extern)
set_target_properties(gtest_main PROPERTIES FOLDER extern)
set_target_properties(gmock PROPERTIES FOLDER extern)
set_target_properties(gmock_main PROPERTIES FOLDER extern)

add_executable(thorin-gtest
    test.cpp
)

target_include_directories(thorin-gtest PRIVATE ${PROJECT_SOURCE_DIR}/src ${PROJECT_SOURCE_DIR}/half/include)
target_link_libraries(thorin-gtest gtest_main thorin)

gtest_discover_tests(thorin-gtest TEST_PREFIX "thorin.")
