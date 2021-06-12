add_executable(thorin-gtest
    test.cpp
)

target_compile_options(thorin PRIVATE -Wall -Wextra)
target_link_libraries (thorin-gtest gtest_main thorin)
gtest_discover_tests  (thorin-gtest TEST_PREFIX "thorin.")
