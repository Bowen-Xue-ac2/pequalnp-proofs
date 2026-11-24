"""Build a shared bounded marked-degree projection and check affine regressions."""

from collections import Counter
from itertools import combinations

from BatchExceptions1768 import rewrite
from SharedBirth1768 import build
from SharedStop1768 import evaluate, graph_output, indicators


ZERO = "truncation.false"


def project(inputs, gates, retained, marked, cap=2):
    assert marked <= retained
    states = {}
    raw = {}
    compiled = []
    for wire in inputs:
        if wire not in retained:
            states[wire] = [ZERO] * (cap + 1)
        else:
            states[wire] = [ZERO if d == 0 and wire in marked else wire for d in range(cap + 1)]
        raw[wire] = wire if wire in marked else ZERO

    def append(name, op, left, right):
        compiled.append((name, op, left, right))
        return name

    for i, (wire, op, left, right) in enumerate(gates):
        prefix = f"truncation.{i}"
        if op == "or":
            raw[wire] = append(f"{prefix}.raw", "or", raw[left], raw[right])
            states[wire] = [
                append(f"{prefix}.{d}", "or", states[left][d], states[right][d])
                for d in range(cap + 1)
            ]
        else:
            raw[wire] = ZERO
            states[wire] = []
            for d in range(cap + 1):
                terms = [
                    append(f"{prefix}.{d}.and.{k}", "and", states[left][k], states[right][d - k])
                    for k in range(d + 1)
                ]
                head = terms[0]
                for k, term in enumerate(terms[1:], 1):
                    head = append(f"{prefix}.{d}.or.{k}", "or", head, term)
                states[wire].append(head)
    return compiled, states, raw


def costs(gates, inputs, active, marked):
    values = {i: (int(i in marked) if i in active else float("inf")) for i in inputs}
    for wire, op, left, right in gates:
        a, b = values[left], values[right]
        values[wire] = a + b if op == "and" else min(a, b)
    return values


def verify(p, extra_marks=False, internal_edge=False):
    inputs, gates, edges, neighbors, starts, birth, tops, root = build(p, bridge=internal_edge)
    marked = set(neighbors)
    points = {v for v in inputs if v.startswith("P")}
    retained = marked | points
    core = {frozenset((u, v)) for u, ns in neighbors.items() for v in ns}
    specs = {u: (u, masked) for u, (_, masked) in starts.items()}
    bad = "U0,2"
    if internal_edge:
        # The new branch's sole live top for this row requires the real pair birth.
        # The base masked term for the row is set to false only in the output OR.
        with_bridge = []
        for name, op, left, right in gates:
            if name == "bridge.top":
                with_bridge.append(("bridge.masked", "and", birth, right))
                right = "bridge.masked"
            with_bridge.append((name, op, left, right))
        gates, root = rewrite(with_bridge, root, {starts[bad][0]: False})
        tops.remove(starts[bad][0])
        specs[bad] = (bad, "bridge.masked")
    junk_samples = []
    if extra_marks:
        z, d = "truncation.extra.z", "truncation.extra.d"
        inputs.extend([z, d])
        modified = []
        for name, op, left, right in gates:
            if left in starts and name == starts[left][0]:
                a, b, mask = (f"{name}.traced.{part}" for part in ("z", "d", "mask"))
                masked = f"{name}.traced.both"
                modified.extend([(a, "or", left, z), (b, "or", left, d),
                                 (mask, "and", right, a), (masked, "and", mask, b)])
                partner = neighbors[left][0]
                other = next(u for u in neighbors if partner not in neighbors[u])
                witness = frozenset({z, d, partner, other})
                assert not any(edge <= witness for edge in edges)
                junk_samples.append(witness)
                specs[left] = (left, masked)
                right = masked
            modified.append((name, op, left, right))
        gates = modified

    compiled, states, raw = project(inputs, gates, retained, marked)
    assert len(compiled) + 1 <= 9 * len(gates) + 1
    degrees = {v: int(v in marked) for v in retained}
    degrees[ZERO] = 0
    for name, op, left, right in compiled:
        degrees[name] = degrees[left] + degrees[right] if op == "and" else max(degrees[left], degrees[right])
    assert all(degrees[state] <= d for branches in states.values() for d, state in enumerate(branches))
    assert all(degrees[w] <= 1 for w in raw.values())

    graph_pairs = sorted(edges, key=lambda e: tuple(sorted(e)))
    graph_values = evaluate(gates, indicators(inputs, graph_pairs))
    assert graph_values[root] == (1 << len(graph_pairs)) - 1
    all_non_edges = [frozenset(pair) for pair in combinations(inputs, 2) if frozenset(pair) not in edges]
    nonedge_values = evaluate(gates, indicators(inputs, all_non_edges + junk_samples))
    assert nonedge_values[root] == 0
    assert all(bool(nonedge_values[name]) == (name not in tops)
               for name, op, _, _ in gates if op == "and")
    assert all(left not in tops and right not in tops for _, op, left, right in gates if op == "and")
    assert all(name.startswith("output.") for name, op, left, right in gates
               if op == "or" and (left in tops or right in tops))
    graph_neighbors = {v: set() for v in inputs}
    for a, b in edges:
        graph_neighbors[a].add(b)
        graph_neighbors[b].add(a)
    assert all(len(graph_neighbors[a] & graph_neighbors[b]) <= 1 for a, b in combinations(inputs, 2))
    assert all(not graph_neighbors[a] & graph_neighbors[b] for a, b in edges)
    supports = {v: [] for v in inputs}
    literal_support = {v: {v} for v in inputs}
    for name, op, left, right in gates:
        support = literal_support[left] | literal_support[right] if op == "or" else set()
        literal_support[name] = support
        if len(support) > 1:
            for x in support:
                supports[x].append(support)
    unsafe_test = frozenset({bad} | (points - set(neighbors[bad])))
    samples = sorted(core, key=lambda e: tuple(sorted(e))) + [unsafe_test]
    values = evaluate(compiled, {**indicators(retained, samples), ZERO: 0})
    occurrences = Counter()
    for i, edge in enumerate(samples[:-1]):
        u, = edge & marked
        v, = edge & points
        oppos = specs[u][1]
        for a, b in ((u, v), (v, u)):
            for support in supports[b]:
                misses = len(support - graph_neighbors[a])
                assert misses > 0
                assert not (len(support) >= 4 and misses <= 1)
                assert not (len(support) >= 5 and misses <= 2)
        minimum = costs(gates, inputs, edge, marked)[oppos]
        occurrences[minimum] += 1
        assert all(bool(values[state] & (1 << i)) == (minimum <= d)
                   for d, state in enumerate(states[oppos]))
        standalone = evaluate(gates, indicators(inputs, [{u}, {v}]))
        assert standalone[oppos] == 0
    assert occurrences == Counter({3 if extra_marks else 1: p ** 3})
    if internal_edge:
        # The pair-birth branch passes this assignment with no cross edge. Both
        # endpoints of the same-column edge remain in the support of the core.
        assert any(edge <= unsafe_test for edge in edges)
        assert not any(edge <= unsafe_test for edge in core)
        assert values[states[specs[bad][1]][2]] >> (len(samples) - 1) & 1
        assert graph_output(core, [unsafe_test]) == 0
        supports = [frozenset(s) for size in (1, 2, 3) for s in combinations(sorted(marked), size)]
        neighbors = {u: set(ns) for u, ns in neighbors.items()}
        tests = [support | {v for v in points if all(v not in neighbors[u] for u in support)}
                 for support in supports]
        signals = {**indicators(retained, tests), ZERO: 0}
        test_values = evaluate(compiled, signals)
        ineligible = {u for u, (_, w) in specs.items() if signals[u] & test_values[states[w][2]]}
        assert ineligible == {bad}
    else:
        ineligible = set()
    covered = 0
    for i, edge in enumerate(samples[:-1]):
        u, = edge & marked
        _, w = specs[u]
        if u not in ineligible and values[states[w][2]] & (1 << i):
            covered += 1
    assert covered == (0 if extra_marks else p ** 3 - p * int(internal_edge))
    print(f"p={p}, extra marked occurrences={extra_marks}, internal edge={internal_edge}: "
          f"minimum marked occurrences {dict(occurrences)}, "
          f"pairs retained by the sound degree-two projection={covered}")


if __name__ == "__main__":
    verify(5)
    verify(7)
    verify(5, extra_marks=True)
    verify(7, extra_marks=True)
    verify(5, internal_edge=True)
