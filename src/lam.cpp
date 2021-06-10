#include "thorin/lam.h"

#include "thorin/world.h"

namespace thorin {

Lam* Lam::set_filter(bool filter) { return set_filter(world().lit_bool(filter)); }

const Def* Lam::mem_var(const Def* dbg) {
    return thorin::isa<Tag::Mem>(var(0_s)->type()) ? var(0, dbg) : nullptr;
}

const Def* Lam::ret_var(const Def* dbg) {
    if (num_vars() > 0) {
        auto p = var(num_vars() - 1, dbg);
        if (auto pi = isa<Pi>(p->type()); pi != nullptr && pi->is_cn()) return p;
    }
    return nullptr;
}

bool Lam::is_basicblock() const { return type()->is_basicblock(); }
bool Lam::is_returning() const { return type()->is_returning(); }

void Lam::app(const Def* callee, const Def* arg, const Def* dbg) {
    assert(isa_nom());
    auto filter = world().lit_false();
    set(filter, world().app(callee, arg, dbg));
}

void Lam::app(const Def* callee, Defs args, const Def* dbg) { app(callee, world().tuple(args), dbg); }

void Lam::branch(const Def* cond, const Def* t, const Def* f, const Def* mem, const Def* dbg) {
    return app(world().select(t, f, cond), mem, dbg);
}

void Lam::test(const Def* value, const Def* index, const Def* match, const Def* clash, const Def* mem, const Def* dbg) {
    return app(world().test(value, index, match, clash), {mem}, dbg);
}

/*
 * Pi
 */

Pi* Pi::set_dom(Defs doms) { return as<Pi>(Def::set(0, world().sigma(doms))); }

bool Pi::is_cn() const { return isa<Bot>(codom()); }

bool Pi::is_returning() const {
    bool ret = false;
    for (auto op : ops()) {
        switch (op->order()) {
            case 1:
                if (!ret) {
                    ret = true;
                    continue;
                }
                return false;
            default: continue;
        }
    }
    return ret;
}

}
