"""Release-certificate size and full-graph loss regressions for literal edits."""

from AnchorState1768 import build_prefix, fold
from BatchExceptions1768 import rewrite
from SharedStop1768 import evaluate, indicators


def build_release_case(p):
    inputs, old, edges, ns, leaves, _, inner, output = build_prefix(p)
    z, ctrl = "release.z", "release.control"
    inputs.extend((z, ctrl))
    edges.add(frozenset((z, ctrl)))
    h, pin_z = "release.shared", "release.pin_z"
    gates = []
    edits = {}
    for gate in old:
        name, op, left, right = gate
        if right == inner and name == f"top.{left}":
            gates.append((name, op, left, h))
            edits[name] = (op, left, inner)
        else:
            gates.append(gate)
        if name == inner:
            q = fold(gates, "release.selectors", "or", [*ns, z])
            gates.extend([(h, "and", inner, q), (pin_z, "and", q, z)])
    gates.extend([("release.control_top", "and", ctrl, pin_z),
                  ("release.output", "or", output, "release.control_top")])
    return inputs, gates, edges, ns, leaves, inner, h, edits


def verify_release_case(p):
    inputs, gates, edges, ns, leaves, inner, h, edits = build_release_case(p)
    graph_pairs = sorted(edges, key=lambda e: tuple(sorted(e)))
    sample_index = {e: i for i, e in enumerate(graph_pairs)}
    points = [v for v in inputs if v.startswith("P")]
    # H and its predecessor are junk: the independent assignment has no line
    # anchor and no control vertex, but includes all pendants, a point, and z.
    witness = frozenset([*leaves.values(), points[0], "release.z"])
    assert all(not edge <= witness for edge in edges)
    signals = indicators(inputs, [*graph_pairs, witness])
    values = evaluate(gates, signals)
    all_edges = (1 << len(graph_pairs)) - 1
    assert values["release.output"] == all_edges
    assert values[h] >> len(graph_pairs) & 1
    assert values[inner] >> len(graph_pairs) & 1

    inputs_and_names = {name for name, _, _, _ in gates}
    readers = {name for name, _, left, right in gates if h in (left, right)}
    assert readers == edits.keys()
    raw = {v: {v} for v in inputs}
    supports = {v: [] for v in inputs}
    for name, op, left, right in gates:
        raw[name] = (raw[left] | raw[right]) if op == "or" else set()
        if len(raw[name]) > 1:
            for v in raw[name]:
                supports[v].append(raw[name])
    neighbors = {v: set() for v in inputs}
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)

    accepted = 0
    for u, ns_u in ns.items():
        top = f"top.{u}"
        assert values[top] & accepted == 0
        accepted |= values[top]
        for v in ns_u:
            pair_bit = 1 << sample_index[frozenset((u, v))]
            assert values[h] & pair_bit and values[top] & pair_bit
            for anchor, partner in ((u, v), (v, u)):
                for support in supports[partner]:
                    misses = len(support - neighbors[anchor])
                    assert misses > 0
                    assert not (len(support) >= 4 and misses <= 1)
                    assert not (len(support) >= 5 and misses <= 2)

    # On every input, u implies Q. Every permitted edit is an equality.
    # H remains live whenever at least one reachable top still reads H.
    for omitted in edits:
        chosen = {name: repl for name, repl in edits.items() if name != omitted}
        partial, out = rewrite(gates, "release.output", chosen)
        assert {name for name, _, _, _ in partial} == inputs_and_names
        assert evaluate(partial, signals)[out] == all_edges

    final, out = rewrite(gates, "release.output", edits)
    dead = inputs_and_names - {name for name, _, _, _ in final}
    assert dead == {h}
    assert len(gates) - len(final) == 1
    assert evaluate(final, signals)[out] == all_edges
    print(f"p={p}, filtered core={p ** 3}, all edges={len(edges)}, gates={len(gates)}")
    print(f"  smallest release certificate for H in these actions: {len(edits)} consumers; "
          f"distinct gates saved=1, all graph losses=0")


def verify_matching_losses(r):
    inputs = [f"match.{i}.{k}" for i in range(r) for k in ("u", "v")]
    gates, edges, tops = [], [], []
    for i in range(r):
        u, v = inputs[2 * i:2 * i + 2]
        top = f"match.edge.{i}"
        gates.append((top, "and", u, v))
        tops.append(top)
        edges.append(frozenset((u, v)))
    output = fold(gates, "match.or", "or", tops)
    full = (1 << r) - 1
    signals = indicators(inputs, edges)
    assert evaluate(gates, signals)[output] == full
    assert len(gates) == len(inputs) - 1  # Every input is essential: this size is least.
    union, total = 0, 0
    for i in range(1, r):
        # The left operand of the i-th OR is the whole earlier prefix.
        out_gates, out = rewrite(gates, output, {f"match.or.{i}": tops[i]})
        lost = full ^ evaluate(out_gates, signals)[out]
        assert lost == (1 << i) - 1
        assert len(gates) - len(out_gates) == 2 * lost.bit_count()
        union |= lost
        total += lost.bit_count()
    assert total == r * (r - 1) // 2
    print(f"least matching with {r} edges, m={len(gates)}: "
          f"distinct losses={union.bit_count()}, sum of losses={total}")


if __name__ == "__main__":
    for p in (5, 7, 11):
        verify_release_case(p)
    for r in (16, 32, 64):
        verify_matching_losses(r)
