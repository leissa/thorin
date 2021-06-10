add_subdirectory(thorin)

if(MSVC)
    add_definitions(-D_SCL_SECURE_NO_WARNINGS)
    add_definitions(-D_CRT_SECURE_NO_WARNINGS)
    add_compile_options("/wd4800" "/wd4520")
    add_compile_options("/experimental:external" "/external:anglebrackets" "/external:W0")
else()
    add_compile_options("-Wall" "-Wextra")
endif()

set_target_properties(thorin PROPERTY CXX_STANDARD 20)

# check for Half library
find_package(Half REQUIRED PATHS ${PROJECT_SOURCE_DIR}/half/)
message(STATUS "Building with Half library from ${Half_INCLUDE_DIRS}.")
target_include_directories(thorin PRIVATE ${Half_INCLUDE_DIRS} ${CMAKE_CURRENT_SOURCE_DIR})

# check for colored terminal
set(COLOR_TTY_AVAILABLE TRUE)
if(WIN32)
    # Windows console does not support ANSI escape codes
    set(COLOR_TTY_AVAILABLE FALSE)
endif()
set(COLORIZE_OUTPUT ${COLOR_TTY_AVAILABLE} CACHE BOOL "Set to true to enable colored error messages")
if(COLORIZE_OUTPUT)
    add_definitions(-DCOLORIZE_LOG)
endif()

