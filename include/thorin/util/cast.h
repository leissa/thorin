#ifndef THORIN_UTIL_CAST_H
#define THORIN_UTIL_CAST_H

#include <cassert>
#include <cstring>

namespace thorin {

/// A bitcast.
template<class D, class S>
inline D bitcast(const S& src) {
    D dst;
    auto s = reinterpret_cast<const void*>(&src);
    auto d = reinterpret_cast<void*>(&dst);

    if constexpr(sizeof(D) == sizeof(S)) memcpy(d, s, sizeof(D));
    if constexpr(sizeof(D)  < sizeof(S)) memcpy(d, s, sizeof(D));
    if constexpr(sizeof(D)  > sizeof(S)) {
        memset(d, 0, sizeof(D));
        memcpy(d, s, sizeof(S));
    }
    return dst;
}

template<class D, class S>       D* isa(      S* s) { return s->node() == D::Node ? static_cast<      D*>(s) : nullptr; } ///< Dynamic cast.
template<class D, class S> const D* isa(const S* s) { return s->node() == D::Node ? static_cast<const D*>(s) : nullptr; } ///< Dynamic cast. @c const version.
template<class D, class S>       D* as (      S* s) { assert(isa<D>(s)); return static_cast<      D*>(s); }               ///< Static cast with debug check.
template<class D, class S> const D* as (const S* s) { assert(isa<D>(s)); return static_cast<const D*>(s); }               ///< Static cast with debug check. @c const version.
template<class D, class S>       D* isa(const std::unique_ptr<S      >& s) { return s->node() == D::Node ? static_cast<      D*>(s.get()) : nullptr; } ///< Dynamic cast.
template<class D, class S> const D* isa(const std::unique_ptr<const S>& s) { return s->node() == D::Node ? static_cast<const D*>(s.get()) : nullptr; } ///< Dynamic cast. @c const version.
template<class D, class S>       D* as (const std::unique_ptr<S      >& s) { assert(isa<D>(s)); return static_cast<      D*>(s.get()); }               ///< Static cast with debug check.
template<class D, class S> const D* as (const std::unique_ptr<const S>& s) { assert(isa<D>(s)); return static_cast<const D*>(s.get()); }               ///< Static cast with debug check. @c const version.

}

#endif
