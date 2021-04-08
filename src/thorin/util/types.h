#ifndef THORIN_UTIL_TYPES_H
#define THORIN_UTIL_TYPES_H

#include <cmath>
#include <cstdint>
#include <limits>
#include <ostream>
#include <type_traits>

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wmismatched-tags"
#endif
#define HALF_ROUND_STYLE 1
#define HALF_ROUND_TIES_TO_EVEN 1
#include <half.hpp>
#ifdef __clang__
#pragma clang diagnostic pop
#endif

#define THORIN_STRINGIFY(x) #x
#define THORIN_TOSTRING(x) THORIN_STRINGIFY(x)

#define THORIN_1_8_16_32_64(m) m(1) m(8) m(16) m(32) m(64)
#define THORIN_8_16_32_64(m)        m(8) m(16) m(32) m(64)
#define THORIN_16_32_64(m)               m(16) m(32) m(64)

namespace thorin {

using half_float::half;

namespace types {

typedef bool   u1;
typedef half   f16;
typedef float  f32;
typedef double f64;

#define CODE(i)                                                                         \
    typedef  int ## i ##_t s ## i;                                                      \
    typedef uint ## i ##_t u ## i;                                                      \
    constexpr s ## i operator"" _s ## i(unsigned long long int s) { return s ## i(s); } \
    constexpr u ## i operator"" _u ## i(unsigned long long int u) { return u ## i(u); }
THORIN_8_16_32_64(CODE)
#undef CODE

/// A @c size_t literal. Use @c 0_s to disambiguate @c 0 from @c nullptr.
constexpr size_t operator""_s(unsigned long long int i) { return size_t(i); }
inline /*constexpr*/ f16 operator""_f16(long double d) { return f16(d); } // wait till fixed upstream
constexpr f32 operator""_f32(long double d) { return f32(d); }
constexpr f64 operator""_f64(long double d) { return f64(d); }

}

using namespace types;

template<class T>
bool get_sign(T val) {
    static_assert(std::is_integral<T>(), "get_sign only supported for signed and unsigned integer types");
    if constexpr(std::is_signed<T>())
        return val < 0;
    else
        return val >> (T(sizeof(val)) * T(8) - T(1));
}

template<int> struct w2u_ {};
template<int> struct w2s_ {};
template<int> struct w2f_ {};

#define CODE(i)                                                                         \
    template<> struct w2u_<i> { typedef u ## i type; };                                 \
    template<> struct w2s_<i> { typedef s ## i type; };
THORIN_8_16_32_64(CODE)
#undef CODE

// Map both signed 1 and unsigned 1 to bool
template<> struct w2u_<1> { typedef bool type; };
template<> struct w2s_<1> { typedef bool type; };

inline half        rem(half        a, half        b) { return      fmod(a, b); }
inline float       rem(float       a, float       b) { return std::fmod(a, b); }
inline double      rem(double      a, double      b) { return std::fmod(a, b); }
inline long double rem(long double a, long double b) { return std::fmod(a, b); }

#define CODE(i) \
    template<> struct w2f_<i> { typedef f ## i type; };
THORIN_16_32_64(CODE)
#undef CODE

template<int w> using w2u = typename w2u_<w>::type;
template<int w> using w2s = typename w2s_<w>::type;
template<int w> using w2f = typename w2f_<w>::type;

}

#endif
