add_executable(thorin-gtest
    test.cpp
)

target_link_libraries(thorin-gtest gtest_main thorin)
gtest_discover_tests(thorin-gtest TEST_PREFIX "thorin.")
