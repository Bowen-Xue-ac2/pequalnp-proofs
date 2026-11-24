"""L-meta-1768 Card 1: read multiplicity and first-order backpropagation.

Reuses SharedBirth1768.build(p, bridge); no other file is touched.

Part 1 (read multiplicity).  For an incidence edge e = {u, v} (u a line, v a point on
it), evaluate the circuit on the edge assignment (only u, v true).  At every wire keep
the exact set of capped occurrence pairs (c_u, c_v) over certificates of the wire
value: c_x in {0, 1, 2} with 2 meaning ">= 2"; OR takes the union over true operands,
AND takes the capped componentwise sum of the two operands.  The output state set is
the set of multiplicities realisable by a certificate of F(pair u v) = 1.

Part 2 (first-order backpropagation).  For the anchor u of the edge,
    testInput T(u) = {u} + (all points not adjacent to u).
The base assignment is T(u) with every anchor (every line input) set to 0.  Forward
base values are computed, then a backward first-order pass from the output: an OR
passes its flag unchanged, an AND sends flag & base[other operand], and fan-out ORs
all incoming contributions.  A live input is one with flag true at the end.  The
five "first-order" edges are the ones with a single-occurrence certificate; we check
their anchor-all-non-neighbour test and whether the anchor changes F there.
"""

from collections import Counter

from SharedBirth1768 import build


# ---------------------------------------------------------------- states
# state (a, b) <-> bit a*3+b, a = capped occurrences of u, b = capped of v.
def state_mask(states):
    return sum(1 << (a * 3 + b) for a, b in states)


def state_list(mask):
    return [(i // 3, i % 3) for i in range(9) if mask >> i & 1]


_AND_CACHE = {}


def and_states(ml, mr):
    """Capped componentwise sum of two state sets."""
    if ml == 0 or mr == 0:
        return 0
    key = (ml, mr)
    if key in _AND_CACHE:
        return _AND_CACHE[key]
    out = set()
    for i in range(9):
        if ml >> i & 1:
            a, b = i // 3, i % 3
            for j in range(9):
                if mr >> j & 1:
                    c, d = j // 3, j % 3
                    out.add((min(2, a + c), min(2, b + d)))
    _AND_CACHE[key] = state_mask(out)
    return _AND_CACHE[key]


def certificate_states(gates, inputs, u, v):
    """Output state set on the edge assignment pair(u, v), with certificates."""
    val = {x: (x == u or x == v) for x in inputs}
    st = {}
    for x in inputs:
        if x == u and x == v:
            st[x] = state_mask({(1, 1)})
        elif x == u:
            st[x] = state_mask({(1, 0)})
        elif x == v:
            st[x] = state_mask({(0, 1)})
        else:
            st[x] = state_mask({(0, 0)}) if val[x] else 0
    for name, op, left, right in gates:
        if op == "or":
            val[name] = val[left] or val[right]
            st[name] = (st[left] if val[left] else 0) | (st[right] if val[right] else 0)
        else:
            val[name] = val[left] and val[right]
            st[name] = and_states(st[left], st[right]) if val[name] else 0
    return st


# ---------------------------------------------------------------- forward / backward
def forward(gates, inputs, true_inputs):
    val = {x: (x in true_inputs) for x in inputs}
    for name, op, left, right in gates:
        val[name] = (val[left] or val[right]) if op == "or" else (val[left] and val[right])
    return val


def first_order(gates, inputs, base, root):
    """Live first-order inputs at the base assignment (fan-out OR)."""
    live = {x: False for x in inputs}
    for name, _, _, _ in gates:
        live[name] = False
    live[root] = True
    for name, op, left, right in reversed(gates):
        if not live[name]:
            continue
        if op == "or":
            live[left] = True
            live[right] = True
        else:
            live[left] = live[left] or base[right]
            live[right] = live[right] or base[left]
    return live


def coefficient_network(gates, inputs, root, partners):
    """Build all coefficient outputs in a common circuit, folding symbolic constants."""
    network = []

    def combine(op, left, right):
        if op == "and":
            if left is False or right is False:
                return False
            if left is True:
                return right
            if right is True:
                return left
        else:
            if left is True or right is True:
                return True
            if left is False:
                return right
            if right is False:
                return left
        if left == right:
            return left
        name = f"@coefficient.{len(network)}"
        network.append((name, op, left, right))
        return name

    primal = {x: (x if x in partners else False) for x in inputs}
    for name, op, left, right in gates:
        primal[name] = combine(op, primal[left], primal[right])

    adjoint = {root: True}
    for name, op, left, right in reversed(gates):
        current = adjoint.get(name, False)
        if current is False:
            continue
        for child, other in ((left, right), (right, left)):
            term = combine("and", current, primal[other]) if op == "and" else current
            adjoint[child] = combine("or", adjoint.get(child, False), term)
    assert len(network) <= 5 * len(gates)
    return network, {x: adjoint.get(x, False) for x in inputs}


def check_network(gates, inputs, root, anchors, partners, singleton_coefficients):
    network, outputs = coefficient_network(gates, inputs, root, partners)
    for v in partners:
        values = forward(network, inputs, {v})
        for u in anchors:
            out = outputs[u]
            assert (out if isinstance(out, bool) else values[out]) == singleton_coefficients[v][u]
    return len(network)


def classify(states):
    once = any(a == 1 or b == 1 for a, b in states)
    only_double = all(a == 2 and b == 2 for a, b in states)
    return once, only_double


def part1(p, bridge):
    inputs, gates, edges, neighborhoods, _, _, _, root = build(p, bridge)
    points = {v for ns in neighborhoods.values() for v in ns}
    assert points <= set(inputs)
    singleton_coefficients = {
        w: first_order(gates, inputs, forward(gates, inputs, {w}), root)
        for w in points | set(neighborhoods)
    }
    network_sizes = [
        check_network(gates, inputs, root, side, inputs_side, singleton_coefficients)
        for side, inputs_side in ((neighborhoods, points), (points, set(neighborhoods)))
    ]
    dist = Counter()
    once_edges, double_edges = [], []
    for u, partners in neighborhoods.items():
        for v in partners:
            st = certificate_states(gates, inputs, u, v)
            states = tuple(state_list(st[root]))
            assert states, (p, bridge, u, v)
            assert singleton_coefficients[v][u] == any(a == 1 for a, _ in states)
            assert singleton_coefficients[u][v] == any(b == 1 for _, b in states)
            dist[states] += 1
            once, only_double = classify(states)
            if once:
                once_edges.append((u, v, states))
            if only_double:
                double_edges.append((u, v))
    total = sum(dist.values())
    assert all(classify(states)[0] or classify(states)[1] for states in dist)
    print(f"p={p} bridge={bridge}: {total} incidence edges")
    print(f"  two coefficient networks: {network_sizes} gates (budget {5 * len(gates)} each)")
    for states, count in sorted(dist.items(), key=lambda kv: (len(kv[0]), kv[0])):
        print(f"  state set {states}: {count} edges")
    print(f"  single-read at an end: {len(once_edges)}; double-read only: {len(double_edges)}"
          f" (single-read + double-only = {len(once_edges) + len(double_edges)})")
    if once_edges:
        anchors = sorted({u for u, _, _ in once_edges})
        assert len(anchors) == 1, anchors
        for u, v, states in once_edges:
            print(f"  one-read edge ({u}, {v}) -> {states}")
    return once_edges, double_edges


def part2(p, bridge, once_edges):
    inputs, gates, edges, neighborhoods, _, _, _, root = build(p, bridge)
    assert gates[-1][0] == root
    points = sorted({v for ns in neighborhoods.values() for v in ns})
    lines = list(neighborhoods)
    network, outputs = coefficient_network(gates, inputs, root, set(points))

    rows = []
    for u, partners in neighborhoods.items():
        test = {u} | (set(points) - set(partners))
        base = test - set(lines)
        base_values = forward(gates, inputs, base)
        base_val = base_values[root]
        test_val = forward(gates, inputs, test)[root]
        live = first_order(gates, inputs, base_values, root)
        coefficients = forward(network, inputs, base)
        out = outputs[u]
        assert live[u] == (out if isinstance(out, bool) else coefficients[out])
        live_set = tuple(sorted(x for x in inputs if live[x]))
        for v in partners:
            rows.append({
                "u": u, "v": v, "base": base_val, "test": test_val,
                "lin_u": live[u], "lin_v": live[v], "live": live_set,
            })

    print(f"p={p} bridge={bridge}: first-order backpropagation "
          f"({len(rows)} edges, root {root})")
    print(f"  F(T) true: {sum(r['test'] for r in rows)}/{len(rows)}; "
          f"F(base) true: {sum(r['base'] for r in rows)}/{len(rows)}")
    print(f"  F(T) == F(base): "
          f"{sum(r['test'] == r['base'] for r in rows)}/{len(rows)}")
    pairs = Counter((r["lin_u"], r["lin_v"]) for r in rows)
    print(f"  (lin_u, lin_v) distribution: {dict(pairs)}")
    print(f"  live-set distribution: {dict(Counter(r['live'] for r in rows))}")

    if once_edges:
        keys = {(u, v) for u, v, _ in once_edges}
        assert all(r["test"] and r["base"] and r["lin_u"]
                   for r in rows if (r["u"], r["v"]) in keys)
        print("  five first-order (single-read) edges:")
        for r in rows:
            if (r["u"], r["v"]) in keys:
                print(f"    ({r['u']}, {r['v']}): F(T)={int(r['test'])} "
                      f"F(base)={int(r['base'])} lin_u={int(r['lin_u'])} "
                      f"lin_v={int(r['lin_v'])} live={r['live']}")
        print("  test truth with the anchor: "
              f"{sum(r['test'] for r in rows if (r['u'], r['v']) in keys)}/"
              f"{len(keys)} tests true; "
              f"same without the anchor: "
              f"{sum(r['base'] for r in rows if (r['u'], r['v']) in keys)}/"
              f"{len(keys)}")
    return rows


def main():
    cases = [(5, False), (7, False), (5, True)]
    once_by_case = {}
    for p, bridge in cases:
        once_by_case[(p, bridge)] = part1(p, bridge)
        print()
    for p, bridge in cases:
        part2(p, bridge, once_by_case[(p, bridge)][0])
        print()


if __name__ == "__main__":
    main()
