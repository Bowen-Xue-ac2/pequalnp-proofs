"""A single first joint AND can witness every edge of a filtered 3-core."""

from itertools import combinations, product

from SharedStop1768 import evaluate, indicators
from SlotFreeCoreExample1768 import incidence_graph


def build(p, bridge=False):
    points, neighborhoods = incidence_graph(p)
    lines = list(neighborhoods)
    inputs = points + lines
    gates = []
    edges = {frozenset((u, v)) for u, ns in neighborhoods.items() for v in ns}

    def gate(name, op, left, right):
        gates.append((name, op, left, right))
        return name

    def fold(name, op, children):
        value, *rest = children
        for i, child in enumerate(rest, 1):
            value = gate(f"{name}.{i}", op, value, child)
        return value

    def disjunction_with_pairs(name, partners, pairs):
        clauses = [fold(f"{name}.clause{i}", "or", [*choice, *partners])
                   for i, choice in enumerate(product(*pairs))]
        return fold(f"{name}.support", "and", clauses)

    # No point lies on two of the parallel prefix lines.
    # Each line meets the point prefix in exactly one point.
    left = fold("left", "or", lines)
    right = fold("right", "or", points)
    birth = gate("birth", "and", left, right)
    tops = set()
    starts = {}
    for u, partners in neighborhoods.items():
        pairs = [(f"{u}.a{i}", f"{u}.b{i}") for i in range(3)]
        inputs.extend(vertex for pair in pairs for vertex in pair)
        support = disjunction_with_pairs(u, partners, pairs)
        masked = gate(f"{u}.masked", "and", birth, support)
        top = gate(f"{u}.top", "and", u, masked)
        tops.add(top)
        starts[u] = (top, masked)
        for i, (a, b) in enumerate(pairs):
            edges.add(frozenset((a, b)))
            tops.add(gate(f"{u}.private{i}", "and", a, b))
    if bridge:
        u = "U0,2"
        internal_edge = ("P0,0", "P0,1")
        pairs = [(f"{u}.a{i}", f"{u}.b{i}") for i in range(3)]
        support = disjunction_with_pairs("bridge", neighborhoods[u], [*pairs, internal_edge])
        tops.add(gate("bridge.top", "and", u, support))
        tops.add(gate("bridge.internal", "and", *internal_edge))
        edges.add(frozenset(internal_edge))
    root = fold("output", "or", sorted(tops))
    return inputs, gates, edges, neighborhoods, starts, birth, tops, root


def verify(p, bridge=False):
    assert p >= 5
    inputs, gates, edges, neighborhoods, starts, birth, tops, root = build(p, bridge)
    assignments = [frozenset(xs) for size in range(3) for xs in combinations(inputs, size)]
    positions = {a: i for i, a in enumerate(assignments)}
    values = evaluate(gates, indicators(inputs, assignments))
    edge_mask = sum(1 << positions[e] for e in edges)
    assert values[root] == edge_mask

    table = {name: (op, left, right) for name, op, left, right in gates}
    raw = {v: {v} for v in inputs}
    for name, op, left, right in gates:
        raw[name] = raw[left] | raw[right] if op == "or" else set()
        if op == "and":
            assert (values[name] & ~edge_mask == 0) == (name in tops)
            assert left not in tops and right not in tops
        if op == "or" and (left in tops or right in tops):
            assert name.startswith("output.")

    # Check both the common-neighbor bound and the absence of triangles.
    neighbors = {v: set() for v in inputs}
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    assert all(len(neighbors[a] & neighbors[b]) <= 1 for a, b in combinations(inputs, 2))
    assert all(not (neighbors[a] & neighbors[b]) for a, b in edges)

    for u, partners in neighborhoods.items():
        assert len(partners) == p
        top, masked = starts[u]
        _, _, support = table[masked]
        assert table[top] == ("and", u, masked)
        assert table[masked] == ("and", birth, support)
        assert raw[birth] == raw[support] == set()
        for v in partners:
            e = frozenset((u, v))
            bit = 1 << positions[e]
            assert values[masked] & bit
            assert values[birth] & bit
            for endpoint in e:
                assert not values[birth] & (1 << positions[frozenset({endpoint})])
            assert all(not (raw[left] & e and raw[right] & e)
                       for name, op, left, right in gates if name in tops)
            for a, b in ((u, v), (v, u)):
                for s in raw.values():
                    if b in s and len(s) > 1:
                        assert not s <= neighbors[a]
                        misses = len(s - neighbors[a])
                        assert not (len(s) >= 4 and misses <= 1)
                        assert not (len(s) >= 5 and misses <= 2)
    assert next(name for name, op, _, _ in gates if op == "and") == birth
    core_degrees = {v: 0 for v in inputs}
    for u, partners in neighborhoods.items():
        for v in partners:
            core_degrees[u] += 1
            core_degrees[v] += 1
    assert all(d in (0, p) for d in core_degrees.values())
    if bridge:
        u = "U0,2"
        cycle = ["P0,0", "U0,0", "P1,0", f"U{p - 1},1", "P0,1"]
        assert all(frozenset((a, b)) in edges for a, b in zip(cycle, cycle[1:] + cycle[:1]))
        outside_neighbors = {v for v in inputs if v.startswith("P") and v not in neighbors[u]}
        assert {"P0,0", "P0,1"} <= outside_neighbors
        test = {u} | outside_neighbors
        result = evaluate(gates, {v: int(v in test) for v in inputs})
        support = table["bridge.top"][2]
        assert result[root] == result[support] == 1
        for v in neighborhoods[u]:
            assert values[support] & (1 << positions[frozenset({v})])
    return len(gates), sum(len(ns) for ns in neighborhoods.values())


if __name__ == "__main__":
    for p in (5, 7):
        gates, edges = verify(p)
        print(f"p={p}: {edges} filtered core edges, first joint AND=birth, {gates} gates")
    gates, edges = verify(5, bridge=True)
    print(f"p=5: {edges} filtered bipartite core edges in the non-bipartite host, "
          f"{gates} gates, shared singleton test accepts")
