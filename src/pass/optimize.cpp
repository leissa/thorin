#include "thorin/pass/fp/beta_red.h"
#include "thorin/pass/fp/copy_prop.h"
#include "thorin/pass/fp/eta_conv.h"
#include "thorin/pass/fp/scalarize.h"
#include "thorin/pass/fp/ssa_constr.h"
#include "thorin/pass/rw/partial_eval.h"
#include "thorin/pass/rw/ret_wrap.h"
#include "thorin/pass/rw/bound_elim.h"

namespace thorin {

void optimize(World& world) {
    PassMan(world)
    .add<PartialEval>()
    .add<EtaConv>()
    .add<BetaRed>()
    .add<SSAConstr>()
    .add<CopyProp>()
    //.add<Scalerize>()
    .run();

    PassMan(world)
    .add<BoundElim>()
    .add<RetWrap>()
    .run();
}

}
