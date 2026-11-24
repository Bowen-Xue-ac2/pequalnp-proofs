from itertools import combinations


def model(degree):
    leaves = [f"v{i}" for i in range(degree)]
    inputs = ["u", "w", "z", "t", *leaves]
    gates = []
    y = leaves[0]
    for i, leaf in enumerate(leaves[1:], start=2):
        name = f"Y{i}"
        gates.append((name, "or", y, leaf))
        y = name
    gates.extend([
        ("L", "or", "u", "w"),
        ("R", "or", y, "w"),
        ("h", "and", "L", "R"),
        ("r", "or", y, "z"),
        ("g", "and", "h", "r"),
        ("s", "or", "u", "z"),
        ("a", "and", "s", "g"),
        ("b", "and", "t", "h"),
        ("out", "or", "a", "b"),
    ])
    edges = {frozenset(("u", v)) for v in leaves}
    edges.update([frozenset(("w", "z")), frozenset(("w", "t"))])
    return inputs, gates, edges


def indicators(inputs, assignments):
    masks = {name: 0 for name in inputs}
    for i, assignment in enumerate(assignments):
        for name in assignment:
            masks[name] |= 1 << i
    return masks


def evaluate(gates, signals, bypass=None):
    values = signals.copy()
    for name, op, left, right in gates:
        if bypass is not None and name == bypass[0]:
            values[name] = values[bypass[1]]
        elif op == "and":
            values[name] = values[left] & values[right]
        else:
            values[name] = values[left] | values[right]
    return values


def graph_output(edges, assignments):
    return sum(1 << i for i, assignment in enumerate(assignments)
               if any(edge <= assignment for edge in edges))


def or_leaves(gates, inputs, root):
    if root in inputs:
        return {root}
    op, left, right = gates[root]
    if op == "and":
        return {root}
    return or_leaves(gates, inputs, left) | or_leaves(gates, inputs, right)


def verify(degree, exhaustive=False):
    inputs, gates, edges = model(degree)
    width = len(inputs) if exhaustive else 2
    assignments = [frozenset(group) for k in range(width + 1)
                   for group in combinations(inputs, k)]
    indices = {group: i for i, group in enumerate(assignments)}
    signals = indicators(inputs, assignments)
    actual = evaluate(gates, signals)
    target = graph_output(edges, assignments)
    assert actual["out"] == target
    top = [name for name, op, _, _ in gates if op == "and" and not actual[name] & ~target]
    junk = [name for name, op, _, _ in gates if op == "and" and actual[name] & ~target]
    assert set(top) == {"a", "b"} and set(junk) == {"g", "h"}

    table = {name: (op, left, right) for name, op, left, right in gates}
    residual = []
    for edge in edges:
        witnessed = False
        exposed = False
        at_pair = 1 << indices[edge]
        for name in top:
            _, p, q = table[name]
            for left, right in [(p, q), (q, p)]:
                anchors = edge & or_leaves(table, inputs, left)
                for lower in junk:
                    if (anchors and lower in or_leaves(table, inputs, right)
                            and actual[lower] & at_pair):
                        witnessed = True
                        _, child_l, child_r = table[lower]
                        exposed |= bool(edge & or_leaves(table, inputs, child_l)
                                        and edge & or_leaves(table, inputs, child_r))
        if witnessed and not exposed:
            residual.append(edge)
    assert len(residual) == degree + 1

    independently_anchored = signals["u"] & ~target
    assert actual["h"] & independently_anchored
    assert actual["r"] & independently_anchored
    assert not actual["g"] & independently_anchored
    assert all(actual["g"] & (1 << indices[frozenset(("u", leaf))])
               for leaf in inputs if leaf.startswith("v"))

    prior = list(inputs)
    checked = 0
    for name, _, _, _ in gates:
        for other in prior:
            observed = evaluate(gates, signals, (name, other))["out"]
            assert observed != target, (degree, name, other)
            checked += 1
        prior.append(name)
    return checked, len(residual)


if __name__ == "__main__":
    for degree in [2, 3, 4, 8, 16, 32, 64]:
        exhaustive = degree <= 8
        checked, residual = verify(degree, exhaustive)
        domain = "all assignments" if exhaustive else "supports of size at most 2"
        print(f"d={degree}: {residual} residual edges, {checked} bypasses, {domain}")
