#ifndef THORIN_TUPLE_H
#define THORIN_TUPLE_H

#include "thorin/def.h"

namespace thorin {

class Agg : public Def {
public:
    /// Constructor for a @em structural Agg.
    Agg(node_t node, const Def* type, Defs ops, const Def* dbg)
        : Def(node, type, ops, 0, dbg)
    {}
    /// Constructor for a @em nom Agg.
    Agg(node_t node, const Def* type, size_t size, const Def* dbg)
        : Def(node, type, size, 0, dbg)
    {}
};

class Sigma : public Agg {
private:
    /// Constructor for a @em structural Sigma.
    Sigma(const Def* type, Defs ops, const Def* dbg)
        : Agg(Node, type, ops, dbg)
    {}
    /// Constructor for a @em nom Sigma.
    Sigma(const Def* type, size_t size, const Def* dbg)
        : Agg(Node, type, size, dbg)
    {}

public:
    /// @name setters
    //@{
    Sigma* set(size_t i, const Def* def) { return as<Sigma>(Def::set(i, def)); }
    Sigma* set(Defs ops) { return as<Sigma>(Def::set(ops)); }
    //@}
    /// @name virtual methods
    //@{
    const Def* rebuild(World&, const Def*, Defs, const Def*) const override;
    Sigma* stub(World&, const Def*, const Def*) override;
    //@}

    static constexpr auto Node = Node::Sigma;
    friend class World;
};

class Tie : public Def {
public:
    /// Constructor for a @em structural Tie.
    Tie(node_t node, const Def* type, Defs ops, const Def* dbg)
        : Def(node, type, ops, 0, dbg)
    {}
    /// Constructor for a @em nom Tie.
    Tie(node_t node, const Def* type, size_t size, const Def* dbg)
        : Def(node, type, size, 0, dbg)
    {}
};

/// Data constructor for a @p Sigma.
class Tuple : public Tie {
private:
    Tuple(const Def* type, Defs args, const Def* dbg)
        : Tie(Node, type, args, dbg)
    {}

public:
    /// @name virtual methods
    //@{
    const Def* rebuild(World&, const Def*, Defs, const Def*) const override;
    //@}

    static constexpr auto Node = Node::Tuple;
    friend class World;
};

class Arr : public Tie {
private:
    /// Constructor for a @em structural Arr.
    Arr(const Def* type, const Def* shape, const Def* body, const Def* dbg)
        : Tie(Node, type, {shape, body}, dbg)
    {}
    /// Constructor for a @em nom Arr.
    Arr(const Def* type, const Def* shape, const Def* dbg)
        : Tie(Node, type, 2, dbg)
    {
        Def::set(0, shape);
    }

public:
    /// @name ops
    //@{
    const Def* shape() const { return op(0); }
    const Def* body() const { return op(1); }
    //@}
    /// @name methods for noms
    //@{
    Arr* set(const Def* body) { return as<Arr>(Def::set(1, body)); }
    //@}
    /// @name virtual methods
    //@{
    const Def* rebuild(World&, const Def*, Defs, const Def*) const override;
    Arr* stub(World&, const Def*, const Def*) override;
    const Def* restructure();
    //@}

    static constexpr auto Node = Node::Arr;
    friend class World;
};

class Pack : public Def {
private:
    Pack(const Def* type, const Def* body, const Def* dbg)
        : Def(Node, type, {body}, 0, dbg)
    {}

public:
    /// @name getters
    //@{
    const Def* body() const { return op(0); }
    const Arr* type() const { return as<Arr>(Def::type()); }
    const Def* shape() const { return type()->shape(); }
    //@}
    /// @name virtual methods
    //@{
    const Def* rebuild(World&, const Def*, Defs, const Def*) const override;
    //@}

    static constexpr auto Node = Node::Pack;
    friend class World;
};

inline       Agg* isa_agg(      Def* def) { return isa<Sigma>(def) || isa<Arr >(def) ? static_cast<      Agg*>(def) : nullptr; }
inline const Agg* isa_agg(const Def* def) { return isa<Sigma>(def) || isa<Arr >(def) ? static_cast<const Agg*>(def) : nullptr; }
inline       Tie* isa_tie(      Def* def) { return isa<Tuple>(def) || isa<Pack>(def) ? static_cast<      Tie*>(def) : nullptr; }
inline const Tie* isa_tie(const Def* def) { return isa<Tuple>(def) || isa<Pack>(def) ? static_cast<const Tie*>(def) : nullptr; }

/// Extracts from a @p Agg typed @p Def (a @p Tie) the element at position @p idx.
class Extract : public Def {
private:
    Extract(const Def* type, const Def* agg, const Def* idx, const Def* dbg)
        : Def(Node, type, {agg, idx}, 0, dbg)
    {}

public:
    /// @name ops
    //@{
    const Def* agg() const { return op(0); }
    const Def* idx() const { return op(1); }
    //@}
    /// @name virtual methods
    //@{
    const Def* rebuild(World&, const Def*, Defs, const Def*) const override;
    //@}

    static constexpr auto Node = Node::Extract;
    friend class World;
};

/**
 * Creates a new @p Def by inserting @p value at position @p idx into @p agg.
 * @attention { This is a @em functional insert.
 *              The @p agg itself remains untouched.
 *              The @p Insert itself is a @em new @p Agg -typed @p Def which contains the inserted @p value. }
 */
class Insert : public Def {
private:
    Insert(const Def* agg, const Def* idx, const Def* value, const Def* dbg)
        : Def(Node, agg->type(), {agg, idx, value}, 0, dbg)
    {}

public:
    /// @name ops
    //@{
    const Def* agg() const { return op(0); }
    const Def* idx() const { return op(1); }
    const Def* val() const { return op(2); }
    //@}
    /// @name virtual methods
    //@{
    const Def* rebuild(World&, const Def*, Defs, const Def*) const override;
    //@}

    static constexpr auto Node = Node::Insert;
    friend class World;
};

/// Flattens a sigma/array/pack/tuple.
const Def* flatten(const Def* def);

/// Applies the reverse transformation on a pack/tuple, given the original type.
const Def* unflatten(const Def* def, const Def* type);
/// Same as unflatten, but uses the operands of a flattened pack/tuple directly.
const Def* unflatten(Defs ops, const Def* type);

Array<const Def*> merge(const Def* def, Defs defs);
const Def* merge_sigma(const Def* def, Defs defs);
const Def* merge_tuple(const Def* def, Defs defs);

bool is_unit(const Def*);
bool is_tuple_arg_of_app(const Def*);

std::string tuple2str(const Def*);

}

#endif
