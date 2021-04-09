#include "thorin/error.h"

#include "thorin/lam.h"
#include "thorin/util/stream.h"

namespace thorin {

template<class... Args> void err(const char* fmt, Args&&... args) { errf(fmt, std::forward<Args&&>(args)...); std::abort(); }

void ErrorHandler::expected_shape(const Def* def) {
    errln("exptected shape but got '{}' of type '{}'", def, def->type());
}

void ErrorHandler::index_out_of_range(const Def* arity, const Def* index) {
    errln("index '{}' does not fit within arity '{}'", index, arity);
}

void ErrorHandler::ill_typed_app(const Def* callee, const Def* arg) {
    errln("cannot pass argument '{} of type '{}' to '{}' of domain '{}'", arg, arg->type(), callee, callee->type()->as<Pi>()->dom());
}

}
