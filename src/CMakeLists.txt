add_library(thorin
    thorin/axiom.cpp
    thorin/check.cpp
    thorin/debug.cpp
    thorin/def.cpp
    thorin/error.cpp
    thorin/lam.cpp
    thorin/lattice.cpp
    thorin/normalize.cpp
    thorin/rewrite.cpp
    thorin/stream.cpp
    thorin/tuple.cpp
    thorin/world.cpp
    thorin/analyses/cfg.cpp
    thorin/analyses/deptree.cpp
    thorin/analyses/domfrontier.cpp
    thorin/analyses/domtree.cpp
    thorin/analyses/looptree.cpp
    thorin/analyses/schedule.cpp
    thorin/analyses/scope.cpp
    thorin/pass/optimize.cpp
    thorin/pass/pass.cpp
    thorin/pass/fp/eta_conv.cpp
    thorin/pass/fp/beta_red.cpp
    thorin/pass/fp/copy_prop.cpp
    thorin/pass/fp/scalarize.cpp
    thorin/pass/fp/ssa_constr.cpp
    thorin/pass/rw/partial_eval.cpp
    thorin/pass/rw/ret_wrap.cpp
    thorin/pass/rw/bound_elim.cpp
    thorin/util/bitset.cpp
    thorin/util/hash.cpp
    thorin/util/stream.cpp
)

find_package(Half REQUIRED PATHS ${PROJECT_SOURCE_DIR}/half/)
message(STATUS "Building with Half library from ${Half_INCLUDE_DIRS}.")

if(MSVC)
    target_compile_definitions(thorin PUBLIC _SCL_SECURE_NO_WARNINGS _CRT_SECURE_NO_WARNINGS)
    target_compile_options    (thorin PUBLIC /wd4800 /wd4520 /experimental:external /external:anglebrackets /external:W0)
else()
    target_compile_options    (thorin PUBLIC -fno-rtti PRIVATE -Wall -Wextra)
endif()

configure_file(thorin/config.h.in ${CMAKE_BINARY_DIR}/include/thorin/config.h @ONLY)
target_include_directories(thorin PUBLIC ${Half_INCLUDE_DIRS} ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_BINARY_DIR}/include)

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
