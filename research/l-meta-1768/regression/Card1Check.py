"""Card 1 independent check of SharedBirth1768.verify(5, bridge=True).

Checks, without trusting the verify block: IsAO2, TopForm, the H2/Ustar status of the
125 incidence edges, the failing independent-set test, and the non-minimality bound.
"""

from collections import defaultdict
from functools import cache
from itertools import combinations

from SharedBirth1768 import build
from SharedStop1768 import evaluate, indicators


def main(p=5):
    inputs, gates, edges, neighborhoods, starts, birth, tops, root = build(p, bridge=True)
    inputset = set(inputs)
    order = {name: i for i, (name, _, _, _) in enumerate(gates)}
    table = {name: (op, l, r) for name, op, l, r in gates}

    assignments = [frozenset(xs) for k in range(3) for xs in combinations(inputs, k)]
    pos = {a: i for i, a in enumerate(assignments)}
    values = evaluate(gates, indicators(inputs, assignments))
    edge_mask = sum(1 << pos[e] for e in edges)

    # IsAO2: binary AND/OR, every wire earlier.
    for name, op, l, r in gates:
        assert op in ("and", "or")
        for w in (l, r):
            assert w in inputset or (w in order and order[w] < order[name])

    # BelowF among AND gates, exactly the tops (checked on supports of size <= 2).
    below = {n for n, op, _, _ in gates if op == "and" and values[n] & ~edge_mask == 0}
    assert below == tops, (len(below), len(tops))

    # TopForm: no below-F AND lies strictly inside the cone of an AND gate.
    readers = defaultdict(list)
    for name, op, l, r in gates:
        readers[l].append(name)
        readers[r].append(name)
    def descendants(x):
        seen, stack = set(), [x]
        while stack:
            for y in readers[stack.pop()]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen
    assert not [(t, j) for t in tops for j, op, _, _ in gates
                if op == "and" and j in descendants(t)]

    # OR-closure side of a wire (and = empty, or = union, input = itself).
    @cache
    def side(x):
        if x in inputset:
            return {x}
        op, l, r = table[x]
        return set() if op == "and" else side(l) | side(r)

    @cache
    def reached_junk(x):
        if x in inputset:
            return set()
        op, l, r = table[x]
        if op == "or":
            return reached_junk(l) | reached_junk(r)
        return {x} if x in junk else set()

    junk = {n for n, op, _, _ in gates if op == "and" and values[n] & ~edge_mask}
    cross = {frozenset((a, b)) for t in tops for a in side(table[t][1])
             for b in side(table[t][2])}
    inc = {frozenset((u, v)) for u, ns in neighborhoods.items() for v in ns}

    # All 125 incidence edges: in G, in Ustar, and in H2Edges through masked.
    witnessed = 0
    for u, ns in neighborhoods.items():
        top, masked = starts[u]
        assert table[top] == ("and", u, masked) and masked in junk
        assert side(u) == {u} and side(masked) == set()
        gl, gr = table[masked][1], table[masked][2]
        for v in ns:
            e = frozenset((u, v))
            assert e in edges and e not in cross  # Ustar
            assert values[masked] >> pos[e] & 1
            assert not ((u in side(gl) or v in side(gl)) and
                        (u in side(gr) or v in side(gr)))  # not exposed
            witnessed += 1
    assert witnessed == 125

    # Inspect all witnesses, including the additional bridge.top.
    singleton_edges = set()
    for e in inc:
        for t in tops:
            _, left, right = table[t]
            for anchor_wire, partner_wire in ((left, right), (right, left)):
                for anchor in e & side(anchor_wire):
                    partner = next(iter(e - {anchor}))
                    for g in reached_junk(partner_wire):
                        _, first, second = table[g]
                        assert not (e & side(first) and e & side(second))
                        if values[g] >> pos[frozenset({partner})] & 1:
                            assert values[g] >> pos[e] & 1
                            singleton_edges.add(e)
    assert singleton_edges == {frozenset(("U0,2", v)) for v in neighborhoods["U0,2"]}

    # The bridge test: {u} + K-point-side non-neighbours of u is not independent.
    u = "U0,2"
    outside = {v for v in inputs if v.startswith("P") and v not in neighborhoods[u]}
    test = {u} | outside
    result = evaluate(gates, {v: int(v in test) for v in inputs})
    support = table["bridge.top"][2]
    assert support in junk and support in reached_junk(table["bridge.top"][2])
    assert frozenset(("P0,0", "P0,1")) <= test
    assert result[root] == 1 and result[support] == 1
    assert any(e <= test for e in edges)
    assert sum(1 for v in neighborhoods[u]
               if values[support] >> pos[frozenset({v})] & 1) == 5
    assert sum(1 for v in inputs
               if values[starts[u][1]] >> pos[frozenset({v})] & 1) == 0

    # Non-bipartite host: the 5-cycle through the added point-side edge.
    cycle = ["P0,0", "U0,0", "P1,0", f"U{p-1},1", "P0,1"]
    assert all(frozenset((a, b)) in edges for a, b in zip(cycle, cycle[1:] + cycle[:1]))

    # Not IsLeastAO: direct edge-AND + OR-tree circuit is far smaller.
    direct = len(edges) + (len(edges) - 1)
    assert direct < len(gates)

    print(f"IsAO2 ok | TopForm ok | H2+Ustar {witnessed} | G non-bipartite (5-cycle)")
    print(f"test F={result[root]} support={result[support]} | support singletons=5"
          f" | H2 with singleton witness={len(singleton_edges)}"
          f" | H2 with only joint witnesses={witnessed - len(singleton_edges)}")
    print(f"this circuit {len(gates)} gates; direct circuit {direct} gates -> IsLeastAO fails")


if __name__ == "__main__":
    main()
