"""Slot-free bipartite cores in circuits irreducible by one earlier-wire bypass."""

from itertools import combinations, product

from SharedStop1768 import evaluate, graph_output, indicators, or_leaves


def incidence_graph(p):
    lines = [(a, b) for a, b in product(range(p), repeat=2)]
    points = [f"P{x},{y}" for x, y in lines]
    neighborhoods = {
        f"U{a},{b}": [f"P{x},{(a * x + b) % p}" for x in range(p)]
        for a, b in lines
    }
    return points, neighborhoods


def gadget(u, neighbors):
    w, z, t = (f"{u}.{suffix}" for suffix in ("w", "z", "t"))
    gates = []

    def gate(suffix, op, left, right):
        name = f"{u}.{suffix}"
        gates.append((name, op, left, right))
        return name

    def biased_or(suffix, bias):
        value = bias
        for i, leaf in enumerate(neighbors):
            value = gate(f"{suffix}{i}", "or", value, leaf)
        return value

    left = gate("L", "or", u, w)
    right = biased_or("R", w)
    h = gate("h", "and", left, right)
    r = biased_or("r", z)
    g = gate("g", "and", h, r)
    s = gate("s", "or", u, z)
    a = gate("a", "and", s, g)
    b = gate("b", "and", t, h)
    out = gate("out", "or", a, b)
    original = {frozenset((u, v)) for v in neighbors}
    return (w, z, t), gates, out, original, original | {frozenset((w, z)), frozenset((w, t))}


def verify(p):
    points, neighborhoods = incidence_graph(p)
    assert all(len(set(a) & set(b)) <= 1 for a, b in combinations(neighborhoods.values(), 2))
    inputs = points + list(neighborhoods)
    gates, outputs = [], []
    edges, original = set(), set()
    for u, neighbors in neighborhoods.items():
        private, local_gates, local_out, local_original, local_edges = gadget(u, neighbors)
        local_inputs = [u, *neighbors, *private]
        local_assignments = [frozenset(xs) for k in range(len(local_inputs) + 1)
                             for xs in combinations(local_inputs, k)]
        local = evaluate(local_gates, indicators(local_inputs, local_assignments))
        expected = graph_output(local_edges, local_assignments)
        assert local[local_out] == expected
        assert all(not local[f"{u}.{i}"] & ~expected for i in ("a", "b"))
        assert all(local[f"{u}.{i}"] & ~expected for i in ("h", "g"))
        inputs.extend(private)
        gates.extend(local_gates)
        outputs.append(local_out)
        original.update(local_original)
        edges.update(local_edges)
    root = outputs[0]
    for i, item in enumerate(outputs[1:], start=1):
        name = f"overall.{i}"
        gates.append((name, "or", root, item))
        root = name

    assignments = [frozenset(xs) for k in range(3) for xs in combinations(inputs, k)]
    signals = indicators(inputs, assignments)
    expected = graph_output(edges, assignments)
    actual = evaluate(gates, signals)
    assert actual[root] == expected
    index = {xs: i for i, xs in enumerate(assignments)}
    table = {name: (op, p, q) for name, op, p, q in gates}
    nodes = {name: or_leaves(table, inputs, name) for name, _, _, _ in gates}
    nodes.update({name: {name} for name in inputs})
    neighbors = {name: {next(iter(e - {name})) for e in edges if name in e} for name in inputs}
    tops = [(name, p, q) for name, op, p, q in gates if op == "and" and not actual[name] & ~expected]
    junks = {name for name, op, _, _ in gates if op == "and" and actual[name] & ~expected}

    slots = set()
    for name, _, p, q in gates:
        support = nodes[name] & neighbors.keys()
        if len(support) < 2:
            continue
        children = [nodes[child] & neighbors.keys() for child in (p, q)]
        for center, allowed in neighbors.items():
            if support <= allowed:
                for child in children:
                    if len(child) == 1:
                        slots.add(frozenset({center} | child))

    for edge in original:
        assert edge not in slots
        mask = 1 << index[edge]
        witnessed = False
        for _, p, q in tops:
            for left, right in [(p, q), (q, p)]:
                assert not any(v in nodes[left] and (edge - {v}) <= nodes[right] for v in edge)
                if not edge & nodes[left]:
                    continue
                for lower in nodes[right] & junks:
                    _, first, second = table[lower]
                    assert not (edge & nodes[first] and edge & nodes[second])
                    witnessed |= bool(actual[lower] & mask)
        assert witnessed

    prior = list(inputs)
    substitutions = 0
    for name, _, _, _ in gates:
        for wire in prior:
            assert evaluate(gates, signals, (name, wire))[root] != expected, (p, name, wire)
            substitutions += 1
        prior.append(name)
    return len(inputs), len(gates), len(original), substitutions


if __name__ == "__main__":
    for p in (2, 3):
        n, m, edges, bypasses = verify(p)
        print(f"p={p}: n={n}, m={m}, {edges} slot-free residual incidences of degree {p}; "
              f"{bypasses} earlier-wire bypasses fail")
