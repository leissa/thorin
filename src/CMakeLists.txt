add_library(thorin
    axiom.cpp
    check.cpp
    debug.cpp
    def.cpp
    error.cpp
    lam.cpp
    lattice.cpp
    normalize.cpp
    rewrite.cpp
    stream.cpp
    tuple.cpp
    world.cpp
    analyses/cfg.cpp
    analyses/deptree.cpp
    analyses/domfrontier.cpp
    analyses/domtree.cpp
    analyses/looptree.cpp
    analyses/schedule.cpp
    analyses/scope.cpp
    pass/optimize.cpp
    pass/pass.cpp
    pass/fp/eta_conv.cpp
    pass/fp/beta_red.cpp
    pass/fp/copy_prop.cpp
    pass/fp/scalarize.cpp
    pass/fp/ssa_constr.cpp
    pass/rw/partial_eval.cpp
    pass/rw/ret_wrap.cpp
    pass/rw/bound_elim.cpp
    util/bitset.cpp
    util/hash.cpp
    util/stream.cpp
)

if(MSVC)
    target_compile_definitions(thorin PUBLIC _SCL_SECURE_NO_WARNINGS _CRT_SECURE_NO_WARNINGS)
    target_compile_options    (thorin PUBLIC /wd4800 /wd4520 /experimental:external /external:anglebrackets /external:W0)
else()
    target_compile_options    (thorin PUBLIC -fno-rtti PRIVATE -Wall -Wextra)
endif()

# check for colored terminal
set(COLOR_TTY_AVAILABLE TRUE)
if(WIN32)
    # Windows console does not support ANSI escape codes
    set(COLOR_TTY_AVAILABLE FALSE)
endif()
set(COLORIZE_OUTPUT ${COLOR_TTY_AVAILABLE} CACHE BOOL "Set to true to enable colored error messages")
if(COLORIZE_OUTPUT)
    target_compile_definitions(thorin PRIVATE COLORIZE_LOG)
endif()

find_package(Half REQUIRED PATHS ${PROJECT_SOURCE_DIR}/half/)
message(STATUS "Building with Half library from ${Half_INCLUDE_DIRS}.")

configure_file(${PROJECT_SOURCE_DIR}/config.h.in ${CMAKE_BINARY_DIR}/include/thorin/config.h @ONLY)
target_include_directories(thorin PUBLIC ${Half_INCLUDE_DIRS} ${PROJECT_SOURCE_DIR}/include ${CMAKE_BINARY_DIR}/include)
