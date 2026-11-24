"""A dense filtered core where each OR operand slot is needed on some graph edge."""

from BatchExceptions1768 import build_essential_regression, critical_gates_by_edge, rewrite
from AnchorState1768 import fold
from SharedStop1768 import evaluate, indicators


def necessary_or_slots(gates, output, values, edge_count):
    """A slot is critical iff its gate is critical and only that operand is true."""
    or_mask = sum(1 << j for j, gate in enumerate(gates) if gate[1] == "or")
    all_critical = 0
    slots = set()
    for i, critical in enumerate(critical_gates_by_edge(gates, output, values, edge_count)):
        all_critical |= critical
        bit = 1 << i
        selected = critical & or_mask
        while selected:
            lowest = selected & -selected
            name, _, left, right = gates[lowest.bit_length() - 1]
            left_true, right_true = bool(values[left] & bit), bool(values[right] & bit)
            if left_true != right_true:
                slots.add((name, int(right_true)))
            selected ^= lowest
    return all_critical, slots


def hide_literal_guards(inputs, gates, edges, ns):
    """Replace each principal term by (u OR z) AND (u OR d) AND (W OR z).

    This is (u AND W) OR (u AND z) OR (z AND d). The added edges form a
    pendant path. A principal term has no input-literal operand afterward.
    """
    expanded = []
    for name, op, u, w in gates:
        if name == f"{u}.essential.top" and u in ns:
            z, d, left, guard, side, inner = (
                f"{u}.implicit.{part}" for part in ("z", "d", "left", "guard", "side", "inner")
            )
            inputs.extend((z, d))
            edges.update((frozenset((u, z)), frozenset((z, d))))
            expanded.extend([(left, "or", u, z), (guard, "or", u, d), (side, "or", w, z),
                             (inner, "and", guard, side), (name, "and", left, inner)])
        else:
            expanded.append((name, op, u, w))
    return expanded


def verify_slot_saturation(p, implicit_guard=False):
    inputs, gates, edges, core, ns, tops, output, _, _ = build_essential_regression(p)
    definitions = {name: (op, left, right) for name, op, left, right in gates}
    connectors = [
        (name, group, partner)
        for name, (op, group, partner) in definitions.items()
        if op == "or" and group.startswith("group.") and ".essential." in name
    ]
    assert len(connectors) == 50 * len(ns)

    new_tops = []
    bypasses = {}
    pin_partner = {}
    for i, (connector, group, partner) in enumerate(connectors):
        anchor = connector.split(".essential.", 1)[0]
        assert partner in ns[anchor]
        assert definitions[group][0] == "or"
        leaf = definitions[group][2]
        assert leaf in inputs and leaf.startswith("copy.")
        pendant, masked, top = (f"slotkeeper.{i}.{part}" for part in ("pendant", "mask", "top"))
        inputs.append(pendant)
        edges.add(frozenset((pendant, leaf)))
        gates.extend([(masked, "and", connector, leaf), (top, "and", pendant, masked)])
        new_tops.append(top)
        bypasses[masked] = leaf
        pin_partner[connector] = partner
    output = fold(gates, "slotkeeper.output", "or", [output, *new_tops])
    if implicit_guard:
        gates = hide_literal_guards(inputs, gates, edges, ns)

    # Only pendant edges were added, at vertices outside the core. They preserve
    # the cycle restrictions and the core's raw-support filters.
    samples = sorted(edges, key=lambda e: tuple(sorted(e)))
    edge_index = {edge: i for i, edge in enumerate(samples)}
    junk_tests = []
    for u, partners in ns.items():
        v = partners[0]
        other = next(a for a in ns if v not in ns[a])
        test = {other, v}
        if implicit_guard:
            test.add(f"{u}.implicit.d")
        assert all(not edge <= test for edge in edges)
        junk_tests.append(frozenset(test))
    signals = indicators(inputs, samples + junk_tests)
    full = (1 << len(edges)) - 1
    values = evaluate(gates, signals)
    assert values[output] == full
    coverage = 0
    for t in [*tops, *new_tops]:
        assert not coverage & values[t]
        coverage |= values[t]
    assert coverage == full
    new_definitions = {name: (op, left, right) for name, op, left, right in gates}
    raw = {x: {x} for x in inputs}
    for name, op, left, right in gates:
        raw[name] = raw[left] | raw[right] if op == "or" else set()
    for i, (u, partners) in enumerate(ns.items()):
        top = f"{u}.essential.top"
        _, left, junk = new_definitions[top]
        if implicit_guard:
            assert left in new_definitions and junk in new_definitions
        assert u in raw[left] and not raw[junk]
        assert values[junk] & (1 << (len(edges) + i))
        _, a, b = new_definitions[junk]
        for v in partners:
            bit = 1 << edge_index[frozenset((u, v))]
            assert values[top] & bit
            assert not ({u, v} & raw[a] and {u, v} & raw[b])

    neighbors = {v: set() for v in inputs}
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    for u, partners in ns.items():
        for v in partners:
            for anchor, partner in ((u, v), (v, u)):
                for support in raw.values():
                    if len(support) <= 1 or partner not in support:
                        continue
                    misses = len(support - neighbors[anchor])
                    assert misses > 0
                    assert not (len(support) >= 4 and misses <= 1)
                    assert not (len(support) >= 5 and misses <= 2)
    critical, slots = necessary_or_slots(gates, output, values, len(edges))
    assert critical.bit_count() == len(gates)
    assert len(slots) == 2 * sum(op == "or" for _, op, _, _ in gates)

    # The chosen leaf already implies connector. Bypass is equal on all inputs.
    after_and, out_and = rewrite(gates, output, bypasses)
    assert evaluate(after_and, signals)[out_and] == full
    assert len(gates) - len(after_and) == len(connectors)

    # After that bypass a common choice of proof for every edge avoids all of
    # these poison slots. Dropping them is pointwise downward and keeps all edges.
    after_or, out_or = rewrite(after_and, out_and, pin_partner)
    assert evaluate(after_or, signals)[out_or] == full
    assert len(after_and) - len(after_or) == len(connectors)

    print(f"p={p}, implicit_guard={implicit_guard}: core={len(core)}, "
          f"graph edges={len(edges)}, gates={len(gates)}, "
          f"necessary OR slots={len(slots)}, edge-critical gates={critical.bit_count()}")
    print(f"  first exact AND rewiring saves {len(gates) - len(after_and)}; "
          f"then OR-slot pruning saves {len(after_and) - len(after_or)}; "
          f"net {len(gates) - len(after_or)}, all graph losses=0")


if __name__ == "__main__":
    verify_slot_saturation(5)
    verify_slot_saturation(5, implicit_guard=True)
