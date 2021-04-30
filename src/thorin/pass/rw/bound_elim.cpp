#include "thorin/pass/rw/bound_elim.h"

namespace thorin {

const Def* BoundElim::rewrite(Def* old_nom, const Def* new_type, const Def* new_dbg) {
    if (auto bound = isa_bound(old_nom)) {
        if (auto sigma = bound->convert()) return sigma;
    }

    if (old_nom->type() != new_type) {
        auto new_nom = old_nom->stub(world(), new_type, new_dbg);
        new_nom->set(old_nom->apply(proxy(old_nom->var()->type(), {new_nom->var()}, 0)));

        if (old_nom->is_external()) {
            old_nom->make_internal();
            new_nom->make_external();
        }

        return new_nom;
    }

    return old_nom;
}

const Def* BoundElim::rewrite(const Def* old_def, const Def*, Defs new_ops, const Def* new_dbg) {
    if (auto vel = isa<Vel>(old_def)) {
        auto join  = as<Join>(vel->type());
        auto value = new_ops[0];
        auto sigma = join->convert();
        auto val   = world().op_bitcast(sigma->op(1), value, new_dbg);
        return world().tuple(sigma, {world().lit_i(join->num_ops(), join->find(vel->value()->type())), val});
    } else if (auto test = isa<Test>(old_def)) {
        auto [value, probe, match, clash] = new_ops.to_array<4>();
        auto [index, box] = value->split<2>();

        auto join = as<Join>(test->value()->type());
        auto mpi = as<Pi>(match->type());
        auto dom = mpi->dom()->out(0);
        auto wpi = world().pi(dom, mpi->codom());
        auto wrap = world().nom_lam(wpi, world().dbg("wrap_match"));
        auto probe_i = join->index(probe);
        wrap->app(match, {wrap->var(), world().op_bitcast(probe, box)});
        auto cmp = world().op(ICmp::e, index, probe_i);
        return world().select(wrap, clash, cmp, new_dbg);
    } else if (auto et = isa<Et>(old_def)) {
        return world().tuple(as<Meet>(et->type())->convert(), new_ops, new_dbg);
    } else if (auto pick = isa<Pick>(old_def)) {
        auto meet = as<Meet>(pick->value()->type());
        auto index = meet->index(pick->type());
        return world().extract(new_ops[0], index, new_dbg);
    }

    return old_def;
}

const Def* BoundElim::rewrite(const Def* def) {
    if (auto proxy = isa_proxy(def)) {
        return proxy->op(0);
    } else if (auto bound = isa_bound(def)) {
        if (auto sigma = bound->convert()) return sigma;
    }

    return def;
}

}
