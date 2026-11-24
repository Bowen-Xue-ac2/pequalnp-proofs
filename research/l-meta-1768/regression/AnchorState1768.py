"""Regression for charging all safe OR states reached inside a witness cone."""

from SharedBirth1768 import build
from SharedStop1768 import evaluate, indicators


def fold(gates, prefix, op, wires):
    head, *tail = wires
    for i, wire in enumerate(tail, 1):
        name = f"{prefix}.{i}"
        gates.append((name, op, head, wire))
        head = name
    return head


def build_prefix(p):
    inputs, base, edges, neighborhoods, starts, _, base_tops, _ = build(p)
    table = {w: (op, a, b) for w, op, a, b in base}
    clauses = [gate for gate in base if ".clause" in gate[0]
               or ".support" in gate[0] or ".private" in gate[0]]
    leaves = {u: f"leaf.{u}" for u in neighborhoods}
    inputs.extend(leaves.values())
    gates = clauses
    poison = fold(gates, "poison", "and", list(leaves.values()))
    junctions = []
    for u in neighborhoods:
        guard = f"guard.{u}"
        dirty = f"branch.{u}"
        _, _, support = table[starts[u][1]]
        gates.append((guard, "or", u, poison))
        gates.append((dirty, "and", guard, support))
        junctions.append(dirty)
    aggregate = fold(gates, "prefix", "or", junctions)
    points = fold(gates, "any_point", "or", [v for v in inputs if v.startswith("P")])
    shared = "shared.junk"
    gates.append((shared, "and", aggregate, points))

    tops = sorted(w for w in base_tops if ".private" in w)
    for u, leaf in leaves.items():
        top, pendant = f"top.{u}", f"pendant.{u}"
        gates.append((top, "and", u, shared))
        gates.append((pendant, "and", u, leaf))
        tops.extend((top, pendant))
        edges.add(frozenset((u, leaf)))
    output = fold(gates, "output", "or", tops)
    return inputs, gates, edges, neighborhoods, leaves, points, shared, output


def verify(p):
    inputs, gates, edges, neighborhoods, leaves, any_point, shared, output = build_prefix(p)
    points = {v for v in inputs if v.startswith("P")}
    anchors = list(neighborhoods)
    samples = list(edges)
    # For each anchor, use a large negative assignment and all partner singletons
    # after specializing the anchor to true and the other anchors to false.
    pairs_for = {}
    tests = {}
    with_poison = frozenset(leaves.values())
    for u in anchors:
        pairs_for[u] = [frozenset((u, v)) for v in sorted(points)]
        tests[u] = frozenset({u} | (points - set(neighborhoods[u])))
        samples.extend([*pairs_for[u], tests[u]])
    samples.extend(with_poison | {v} for v in points)
    samples = list(dict.fromkeys(samples))
    ids = {x: i for i, x in enumerate(samples)}
    values = evaluate(gates, indicators(inputs, samples))
    truth = sum(1 << i for i, x in enumerate(samples) if any(e <= x for e in edges))
    assert values[output] == truth
    assert all(values[shared] >> ids[with_poison | {v}] & 1 for v in points)
    pair_masks = {u: sum(1 << ids[x] for x in pairs_for[u]) for u in anchors}
    neighbor_masks = {u: sum(1 << ids[frozenset((u, v))] for v in ns)
                      for u, ns in neighborhoods.items()}
    for u, test in tests.items():
        assert values[any_point] >> ids[test] & 1
        assert not values[shared] >> ids[test] & 1

    states = 0
    persistent = 0
    prefixes = [(name, next_branch) for name, _, _, next_branch in gates
                if name.startswith("prefix.")]
    for j, (wire, added) in enumerate(prefixes, start=2):
        for i, u in enumerate(anchors, start=1):
            pair_bits = pair_masks[u]
            active = values[wire] & pair_bits
            assert not values[wire] >> ids[tests[u]] & 1
            assert active == (neighbor_masks[u] if i <= j else 0)
            if i <= j:
                states += 1
                # Only the entry state for u introduces its support.
                if values[added] & pair_bits and i < j:
                    persistent += 1
    a = len(anchors)
    assert states == a * (a + 1) // 2 - 1
    assert persistent == 0
    assert len(gates) == a * (8 * p + 38) - 3
    return len(gates), states


def verify_disjoint_stars(a):
    inputs, gates, tops, pairs, tests = [], [], [], [], []
    leaves = {f"u{i}": (f"v{i}.0", f"v{i}.1") for i in range(a)}
    partners = {v for ns in leaves.values() for v in ns}
    for u, ns in leaves.items():
        inputs.extend([u, *ns])
        fan, top = f"fan.{u}", f"top.{u}"
        gates.extend([(fan, "or", *ns), (top, "and", u, fan)])
        tops.append(top)
        pairs.extend(frozenset((u, v)) for v in ns)
        tests.append(frozenset({u} | (partners - set(ns))))
    root = fold(gates, "prefix", "or", tops)
    values = evaluate(gates, indicators(inputs, pairs + tests))
    assert values[root] == (1 << (2 * a)) - 1
    states = 0
    for i in range(1, a):
        mask = values[f"prefix.{i}"]
        assert mask == (1 << (2 * (i + 1))) - 1
        states += i + 1
    assert states == a * (a + 1) // 2 - 1
    # All 3a inputs are essential, so any binary circuit needs at least 3a-1 gates.
    assert len(gates) == len(inputs) - 1 == 3 * a - 1
    return len(gates), states


if __name__ == "__main__":
    gates, states = verify_disjoint_stars(16)
    print(f"16 disjoint two-leaf stars: {gates} gates; {states} safe prefix states")
    for p in (5, 7, 11):
        gates, states = verify(p)
        print(f"p={p}: {gates} gates; {states} safe multipartner prefix states")
