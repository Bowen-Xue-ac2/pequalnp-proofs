"""Scalable regression for both global bypasses of a shared AND."""

from collections import defaultdict

from AnchorState1768 import fold
from SharedBirth1768 import build
from SharedStop1768 import evaluate, indicators


def rewrite(gates, output, edits):
    aliases = {}
    kept = []
    for name, op, left, right in gates:
        replacement = edits.get(name, (op, left, right))
        if not isinstance(replacement, tuple):
            aliases[name] = aliases.get(replacement, replacement)
            continue
        op, left, right = replacement
        left, right = aliases.get(left, left), aliases.get(right, right)
        if left is False or right is False:
            aliases[name] = False if op == "and" else (right if left is False else left)
        else:
            kept.append((name, op, left, right))
    output = aliases.get(output, output)
    live = {output}
    retained = []
    for gate in reversed(kept):
        name, _, left, right = gate
        if name in live:
            retained.append(gate)
            live.update((left, right))
    return list(reversed(retained)), output


def build_exceptions(p, b, active_poison=False):
    inputs, gates, edges, ns, _, birth, tops, output = build(p)
    anchors = list(ns)
    points = [v for v in inputs if v.startswith("P")]
    matching = [
        (f"U{a},{t}", f"P{a},{(a * a + t) % p}")
        for a in range(p) for t in range(p)
    ]
    chosen = matching[:2 * (b + 1)]
    assert len(chosen) == 2 * (b + 1)
    assert len({v for _, v in chosen}) == len(chosen)
    assert all(v in ns[u] for u, v in chosen)
    omitted = dict(chosen)
    edits = {}
    for name, op, left, right in gates:
        if ".clause" in name and op == "or":
            u = name.split(".clause", 1)[0]
            if omitted.get(u) == right:
                edits[name] = left
    gates, output = rewrite(gates, output, edits)
    left, right = next((a, c) for name, _, a, c in gates if name == birth)

    leaf_top = []
    test_leaves = []
    guards = []
    control_edges = []
    for side, vertices in (("line", anchors), ("point", points)):
        leaves = [f"leaf.{v}" for v in vertices]
        inputs.extend(leaves)
        test_leaves.append(frozenset(leaves))
        terms = leaves
        control_edge = None
        if active_poison:
            r, s = f"control.{side}.r", f"control.{side}.s"
            inputs.extend((r, s))
            control_edge = frozenset((r, s))
            edges.add(control_edge)
            terms = []
            for i, leaf in enumerate(leaves):
                lr, ls, term = (f"guard.{side}.{i}.{k}" for k in ("r", "s", "and"))
                gates.extend([(lr, "or", leaf, r), (ls, "or", leaf, s),
                              (term, "and", lr, ls)])
                terms.append(term)
        guard = fold(gates, f"all_leaves.{side}", "and", terms)
        guards.append(guard)
        control_edges.append(control_edge)
        if active_poison:
            top, direct = f"control.{side}.top", f"control.{side}.pendant"
            gates.extend([(top, "and", r, guard), (direct, "and", r, leaves[0])])
            leaf_top.extend((top, direct))
            edges.add(frozenset((r, leaves[0])))
        for v, leaf in zip(vertices, leaves):
            name = f"pendant.{v}"
            gates.append((name, "and", v, leaf))
            leaf_top.append(name)
            edges.add(frozenset((v, leaf)))

    exceptions = ([], [])
    for i, (u, v) in enumerate(chosen):
        name = f"exception.{i}"
        group = int(i >= b + 1)
        a, c, both = f"{name}.a", f"{name}.b", f"{name}.inputs"
        gates.extend([(a, "or", u, guards[group]), (c, "or", v, guards[group]),
                      (both, "and", a, c), (name, "and", birth, both)])
        exceptions[group].append((name, u, v))

    new_tops = [name for group in exceptions for name, _, _ in group]
    output = fold(gates, "extended_output", "or", [output, *leaf_top, *new_tops])
    tests = [test_leaves[0] | {points[0]}, test_leaves[1] | {anchors[0]}]
    core = {frozenset((u, v)) for u, ns_u in ns.items() for v in ns_u}
    core.difference_update(frozenset(edge) for edge in chosen)
    return (inputs, gates, edges, tops | set(leaf_top) | set(new_tops), core, birth,
            (right, left), tests, exceptions, guards, control_edges, output)


def verify(p, b, active_poison=False):
    (inputs, gates, edges, tops, core, birth, replacements, tests,
     exceptions, guards, control_edges, output) = build_exceptions(p, b, active_poison)
    neighbors = {v: set() for v in inputs}
    for a, c in edges:
        neighbors[a].add(c)
        neighbors[c].add(a)
    assert all(not (neighbors[a] & neighbors[c]) for a, c in edges)
    raw = {v: {v} for v in inputs}
    supports_for = defaultdict(list)
    table = {}
    for name, op, left, right in gates:
        table[name] = (op, left, right)
        raw[name] = raw[left] | raw[right] if op == "or" else set()
        if len(raw[name]) > 1:
            for v in raw[name]:
                supports_for[v].append(raw[name])

    edge_samples = sorted(edges, key=lambda e: tuple(sorted(e)))
    edge_indices = {e: i for i, e in enumerate(edge_samples)}
    junk_samples = {}
    for e in core:
        u = next(x for x in e if x.startswith("U"))
        v = next(iter(e - {u}))
        assert table[f"{u}.top"][2] == f"{u}.masked"
        assert all(not raw[child] for child in table[f"{u}.masked"][1:])
        if u not in junk_samples:
            other = next(x for x in inputs if x.startswith("U") and x not in neighbors[v])
            junk_samples[u] = frozenset((other, v))
            assert junk_samples[u] not in edges
        for a, c in ((u, v), (v, u)):
            for support in supports_for[c]:
                misses = len(support - neighbors[a])
                assert misses > 0
                assert not (len(support) >= 4 and misses <= 1)
                assert not (len(support) >= 5 and misses <= 2)
    samples = edge_samples + tests + list(junk_samples.values())
    edge_mask = (1 << len(edges)) - 1
    values = evaluate(gates, indicators(inputs, samples))
    assert values[output] == edge_mask
    union = 0
    for top in tops:
        assert not (union & values[top])
        union |= values[top]
    assert union == edge_mask
    for offset, u in enumerate(junk_samples):
        assert values[f"{u}.masked"] >> (len(edges) + len(tests) + offset) & 1
    for e in core:
        u = next(x for x in e if x.startswith("U"))
        bit = 1 << edge_indices[e]
        assert values[f"{u}.top"] & bit
        assert values[f"{u}.masked"] & bit
    degrees = {v: 0 for e in core for v in e}
    for a, c in core:
        degrees[a] += 1
        degrees[c] += 1
    assert min(degrees.values()) == p - 1

    savings = []
    shared_cut_savings = []
    for side, replacement in enumerate(replacements):
        negative = 1 << (len(edges) + side)
        broken, out = rewrite(gates, output, {birth: replacement})
        signals = indicators(inputs, samples)
        broken_values = evaluate(broken, signals)
        assert broken_values[out] & negative
        assert all(broken_values[top] & negative for top, _, _ in exceptions[side])

        repair = {top: ("and", u, v) for top, u, v in exceptions[side]}
        patch, out = rewrite(gates, output, repair | {birth: replacement})
        assert evaluate(patch, signals)[out] == edge_mask
        assert len(patch) < len(gates)
        savings.append(len(gates) - len(patch))

        # Silence the shared source of the blocking conditions and measure the
        # lost graph edges before repairing anything at the output.
        source_cut, out = rewrite(gates, output, {birth: replacement, guards[side]: False})
        covered = evaluate(source_cut, signals)[out]
        control_edge = control_edges[side]
        loss = (1 << edge_indices[control_edge]) if control_edge is not None else 0
        assert covered == edge_mask ^ loss
        if control_edge is not None:
            r, s = sorted(control_edge)
            source_cut.extend([("repair.control", "and", r, s),
                               ("repair.output", "or", out, "repair.control")])
            out = "repair.output"
        assert evaluate(source_cut, signals)[out] == edge_mask
        assert len(source_cut) < len(gates)
        shared_cut_savings.append(len(gates) - len(source_cut))
    return len(core), min(degrees.values()), savings, shared_cut_savings


def three_choice_obstruction():
    """A 7-regular, diameter-two graph with independence number at most 15."""
    vertices = [(side, a, b) for side in range(2) for a in range(5) for b in range(5)]
    neighbors = {v: set() for v in vertices}
    for side, a, b in vertices:
        v = (side, a, b)
        step = side + 1
        neighbors[v].update((side, a, (b + d) % 5) for d in (step, -step))
        neighbors[v].update(
            (1 - side, c, (b + (1 - 2 * side) * a * c) % 5) for c in range(5)
        )
    for v, ns in neighbors.items():
        assert len(ns) == 7 and v not in ns
        assert all(v in neighbors[w] for w in ns)
        for w in vertices:
            if w != v:
                assert len(ns & neighbors[w]) == int(w not in ns)
    # For an independent set of size s, Cauchy applied to the outside neighbor
    # counts gives 49*s <= (50-s)*(s+6), so s <= 15. Three colors cover at most 45.
    return vertices, {
        tuple(sorted((v, w))) for v, ns in neighbors.items() for w in ns
    }


def critical_gates_by_edge(gates, output, edge_values, edge_count):
    """Yield the gates whose forced zero blocks each graph edge."""
    own = [1 << i for i in range(len(gates))]
    for i in range(edge_count):
        bit = 1 << i
        removed = {}
        for own_bit, (name, op, left, right) in zip(own, gates):
            if not edge_values[name] & bit:
                continue
            l_loss, r_loss = removed.get(left, 0), removed.get(right, 0)
            if op == "and":
                children = l_loss | r_loss
            elif not edge_values[left] & bit:
                children = r_loss
            elif not edge_values[right] & bit:
                children = l_loss
            else:
                children = l_loss & r_loss
            removed[name] = own_bit | children
        yield removed[output]


def critical_gates(gates, output, edge_values, edge_count):
    """Union the gates whose forced zero blocks some graph edge."""
    critical = 0
    for edge_critical in critical_gates_by_edge(gates, output, edge_values, edge_count):
        critical |= edge_critical
    return critical


def build_essential_regression(p):
    from SlotFreeCoreExample1768 import incidence_graph

    points, ns = incidence_graph(p)
    anchors = list(ns)
    vertices, links = three_choice_obstruction()
    names = {v: tuple(f"copy.{v}.{j}" for j in range(3)) for v in vertices}
    centers = {v: f"center.{v}" for v in vertices}
    inputs = points + anchors + list(centers.values())
    inputs += [name for group in names.values() for name in group]
    gates, support, top = [], [], []
    edges = {frozenset((u, v)) for u, partners in ns.items() for v in partners}
    core = set(edges)
    for v, group in names.items():
        raw_group = fold(gates, f"group.{v}", "or", group)
        support.append(raw_group)
        name = f"star.{v}"
        gates.append((name, "and", centers[v], raw_group))
        top.append(name)
        edges.update(frozenset((centers[v], w)) for w in group)
    for a, b in sorted(links):
        for color, (u, v) in enumerate(zip(names[a], names[b])):
            name = f"copy_edge.{a}.{b}.{color}"
            gates.append((name, "and", u, v))
            top.append(name)
            edges.add(frozenset((u, v)))

    base = gates.copy()
    old_top = top.copy()
    left = fold(gates, "essential.left", "or", anchors)
    right = fold(gates, "essential.right", "or", points)
    gates.append(("essential.birth", "and", left, right))
    for u, partners in ns.items():
        clauses = [fold(gates, f"{u}.essential.{i}", "or", [g, *partners])
                   for i, g in enumerate(support)]
        packed = fold(gates, f"{u}.essential.support", "and", clauses)
        mask, apex = f"{u}.essential.mask", f"{u}.essential.top"
        gates.extend([(mask, "and", "essential.birth", packed), (apex, "and", u, mask)])
        top.append(apex)
    output = fold(gates, "essential.output", "or", top)
    return inputs, gates, edges, core, ns, top, output, base, old_top


def verify_essential_regression(p):
    from itertools import combinations

    inputs, gates, edges, core, ns, _, output, base, old_top = build_essential_regression(p)

    # Confirm the pair witnesses, and use a false pair to witness each mask as junk.
    edge_list = sorted(edges, key=lambda e: tuple(sorted(e)))
    edge_index = {edge: i for i, edge in enumerate(edge_list)}
    junk_tests = []
    for u, partners in ns.items():
        v = partners[0]
        other = next(w for w, w_partners in ns.items() if v not in w_partners)
        junk_tests.append(frozenset((other, v)))
    signals = indicators(inputs, edge_list + junk_tests)
    values = evaluate(gates, signals)
    full = (1 << len(edges)) - 1
    assert values[output] == full
    for i, (u, partners) in enumerate(ns.items()):
        mask = values[f"{u}.essential.mask"]
        assert mask & (1 << (len(edges) + i))
        for v in partners:
            bit = 1 << edge_index[frozenset((u, v))]
            assert mask & bit and values[f"{u}.essential.top"] & bit
    assert critical_gates(gates, output, values, len(edges)).bit_count() == len(gates)

    # Verify the raw OR filters and the two short-cycle conditions.
    neighbors = {v: set() for v in inputs}
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    assert all(not neighbors[a] & neighbors[b] for a, b in edges)
    assert all(len(neighbors[a] & neighbors[b]) <= 1 for a, b in combinations(inputs, 2))
    directed_core = [(u, v) for u, partners in ns.items() for v in partners]
    directed_core += [(v, u) for u, v in directed_core]
    raw = {v: {v} for v in inputs}
    for name, op, a, b in gates:
        raw[name] = raw[a] | raw[b] if op == "or" else set()
        if len(raw[name]) <= 1:
            continue
        for anchor, partner in directed_core:
            if partner in raw[name]:
                misses = len(raw[name] - neighbors[anchor])
                assert misses > 0
                assert not (len(raw[name]) >= 4 and misses <= 1)
                assert not (len(raw[name]) >= 5 and misses <= 2)

    # The conjunction of the fifty group disjunctions implies a copy edge:
    # selecting a true variable in each group would otherwise 3-color the base graph.
    # Therefore replacing each packed support by its pure neighbor disjunction
    # and pruning the common birth preserves the output on every assignment.
    for u, partners in ns.items():
        star = fold(base, f"{u}.reduced.star", "or", partners)
        apex = f"{u}.reduced.top"
        base.append((apex, "and", u, star))
        old_top.append(apex)
    repaired_output = fold(base, "reduced.output", "or", old_top)
    assert evaluate(base, signals)[repaired_output] == full
    assert len(base) < len(gates)
    return len(core), len(gates), len(gates) - len(base)


if __name__ == "__main__":
    for p in (5, 7, 11):
        b = p - 2
        edges, degree, savings, cuts = verify(p, b)
        print(f"p={p}: {edges} filtered incidences, min degree {degree}; "
              f"{b + 1} blockers per bypass; top repairs save {savings}, shared cuts save {cuts} gates")
    edges, degree, savings, cuts = verify(5, 3, active_poison=True)
    print(f"p=5 active poison: {edges} filtered incidences, min degree {degree}; "
          f"top repairs save {savings}, shared cuts plus one edge repair save {cuts} gates")
    edges, gates, saving = verify_essential_regression(5)
    print(f"p=5 essential-gate example: {edges} filtered incidences; all {gates} gates "
          f"critical for some edge; simultaneous rewrite saves {saving} gates")
